import refinement.store
import «02-abstract».«system»

namespace Chain

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)
open Concrete (Origin Commands Timer)

def promiseTimeouts (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      { c with add := c.add ++ [o.project now], del := c.del ++ o.timers }
    else
      c

def listeners (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      { c with
        add := c.add ++ [{ o with promise := { o.promise with listeners := [] } }],
        send := c.send ++ o.promise.listeners.map fun a => (a, .unblock (o.promise.toRecord o.id)) }
    else
      c

def resumeOne (now : Nat) (awaited : Ident) (org : Origin) (c : Commands) (awaiter : Ident) : Commands :=
  match ((c.doc org).get awaiter now).bind fun w => w.task.map (w, ·) with
  | none =>
      c
  | some (w, t) =>
      match t.state with
      | .suspended =>
          { c with
            arm := c.arm ++ [⟨now, w.id, .taskRetryTimeout⟩],
            add := c.add ++ [{ w with task := some { t with state := .pending, resumes := [awaited],
                                                                retryTimeoutAt := some now } }] }
      | .pending | .acquired | .halted =>
          if t.resumes.contains awaited then
            { c with add := c.add ++ [w] }
          else
            { c with add := c.add ++ [{ w with task := some { t with resumes := t.resumes ++ [awaited] } }] }
      | .fulfilled =>
          { c with add := c.add ++ [w] }

def callbacks (now : Nat) (org : Origin) : Commands :=
  org.current.objects.foldl (init := {}) fun c o =>
    let o := o.project now
    if o.promise.state != .pending then
      o.promise.callbacks.foldl (init := c) fun c awaiter =>
        match (c.doc org).get o.id now with
        | some cur =>
            resumeOne now o.id org
              { c with add := c.add ++ [{ cur with promise :=
                  { cur.promise with callbacks := cur.promise.callbacks.filter (· != awaiter) } }] }
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
          { c with
            arm := c.arm ++ [⟨now, o.id, .taskRetryTimeout⟩],
            add := c.add ++ [{ o with task := some { t with state := .pending, pid := none, ttl := none,
                                                                leaseTimeoutAt := none,
                                                                retryTimeoutAt := some now } }],
            del := c.del ++ t.timers o.id }
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
          { c with
            arm := c.arm ++ [⟨now + Concrete.retryDelay, o.id, .taskRetryTimeout⟩],
            add := c.add ++ [{ o with task := some { t with retryTimeoutAt := some (now + Concrete.retryDelay) } }],
            del := c.del ++ t.timers o.id,
            send := c.send ++ [(target, .execute o.id t.version)] }
        else
          c
    | _, _ =>
        c

def sweep (now : Nat) (org : Origin) : Commands :=
  let c1 := promiseTimeouts now org
  let c2 := c1.merge (listeners now (c1.doc org))
  let c3 := c2.merge (callbacks now (c2.doc org))
  let c4 := c3.merge (leaseTimeouts now (c3.doc org))
  c4.merge (retryTimeouts now (c4.doc org))

def promiseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      some (.promiseTimeout ⟨o.id⟩)
    else
      none

def listenerTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      o.promise.listeners.map fun a => .listener ⟨o.id, a⟩
    else
      []

def callbackTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending then
      o.promise.callbacks.map fun w => .callback ⟨o.id, w⟩
    else
      []

def leaseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    let o := o.project now
    match o.task with
    | some t =>
        if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
          some (.taskLeaseTimeout ⟨o.id⟩)
        else
          none
    | none =>
        none

def retryTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    let o := o.project now
    match o.task, o.promise.type with
    | some t, .runnable _ =>
        if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
          some (.taskRetryTimeout ⟨o.id⟩)
        else
          none
    | _, _ =>
        none

def sweepTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  let c1 := promiseTimeouts now org
  let c2 := c1.merge (listeners now (c1.doc org))
  let c3 := c2.merge (callbacks now (c2.doc org))
  let c4 := c3.merge (leaseTimeouts now (c3.doc org))
  promiseTimeoutTriggers now org ++ listenerTriggers now (c1.doc org) ++ callbackTriggers now (c2.doc org)
    ++ leaseTimeoutTriggers now (c3.doc org) ++ retryTimeoutTriggers now (c4.doc org)

end Chain
