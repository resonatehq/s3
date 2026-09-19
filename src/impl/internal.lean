import impl.state

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)

def retryDelay : Nat := 5000

def Commands.merge (c d : Commands) : Commands :=
  { arm  := c.arm.filter (· ∉ d.del) ++ d.arm,
    add  := c.add ++ d.add,
    del  := c.del.filter (· ∉ d.arm) ++ d.del,
    send := c.send ++ d.send }

def promiseTimeouts (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      c.merge { add := [o.project now], del := o.timers }
    else
      c

def listeners (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      c.merge
        { add  := [{ o with promise := { o.promise with listeners := [] } }],
          send := o.promise.listeners.map fun a => (a, .unblock (o.promise.toRecord o.id)) }
    else
      c

def resumeOne (now : Nat) (awaited : Ident) (org : Origin) (c : Commands) (awaiter : Ident) : Commands :=
  match ((c.doc org).get awaiter now).bind fun w => w.task.map (w, ·) with
  | none =>
      c
  | some (w, t) =>
      match t.state with
      | .suspended =>
          c.merge
            { arm := [⟨now, w.id, .taskRetryTimeout⟩],
              add := [{ w with task := some { t with state := .pending, resumes := [awaited],
                                                     retryTimeoutAt := some now } }] }
      | .pending | .acquired | .halted =>
          if t.resumes.contains awaited then
            c.merge { add := [w] }
          else
            c.merge { add := [{ w with task := some { t with resumes := t.resumes ++ [awaited] } }] }
      | .fulfilled =>
          c.merge { add := [w] }

def callbacks (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    if o.promise.state != .pending then
      o.promise.callbacks.foldl (init := c) fun c awaiter =>
        match (c.doc org).get o.id now with
        | some cur =>
            resumeOne now o.id org
              (c.merge { add := [{ cur with promise :=
                { cur.promise with callbacks := cur.promise.callbacks.filter (· != awaiter) } }] })
              awaiter
        | none =>
            c
    else
      c

def leaseTimeouts (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    match o.task with
    | some t =>
        if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now)
            ∧ o.promise.state == .pending then
          c.merge
            { arm := [⟨now, o.id, .taskRetryTimeout⟩],
              add := [{ o with task := some { t with state := .pending, pid := none, ttl := none,
                                                     leaseTimeoutAt := none,
                                                     retryTimeoutAt := some now } }],
              del := t.timers o.id }
        else
          c
    | none =>
        c

def retryTimeouts (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    match o.task, o.promise.type with
    | some t, .runnable target =>
        if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now)
            ∧ o.promise.state == .pending then
          c.merge
            { arm  := [⟨now + retryDelay, o.id, .taskRetryTimeout⟩],
              add  := [{ o with task := some { t with retryTimeoutAt := some (now + retryDelay) } }],
              del  := t.timers o.id,
              send := [(target, .execute o.id t.version)] }
        else
          c
    | _, _ =>
        c

def sweep (now : Nat) (org : Origin) : Commands :=
  let c := promiseTimeouts now org
  let c := c.merge (listeners now (c.doc org))
  let c := c.merge (callbacks now (c.doc org))
  let c := c.merge (leaseTimeouts now (c.doc org))
  let c := c.merge (retryTimeouts now (c.doc org))
  c

end Concrete
