import impl.external

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)

def retryTimeout : Nat := 5000

def Commands.merge (c d : Commands) : Commands :=
  { arm := c.arm ++ d.arm, put := d.put, del := c.del ++ d.del, send := c.send ++ d.send }

def promiseTimeouts (now : Nat) (org : Origin) : Commands :=
  org.objects.foldl (init := { put := org }) fun c o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      { c with put := c.put.write (o.project now), del := c.del ++ o.timers }
    else
      c

def listeners (_now : Nat) (org : Origin) : Commands :=
  org.objects.foldl (init := { put := org }) fun c o =>
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      { c with
        put := c.put.write { o with promise := { o.promise with listeners := [] } },
        send := c.send ++ o.promise.listeners.map fun a => (a, .unblock (o.promise.toRecord o.id)) }
    else
      c

def callbacks (now : Nat) (org : Origin) : Commands :=
  org.objects.foldl (init := { put := org }) fun c o =>
    if o.promise.state != .pending ∧ !o.promise.callbacks.isEmpty then
      let struck := { c with put := c.put.write { o with promise := { o.promise with callbacks := [] } } }
      o.promise.callbacks.foldl (init := struck) fun c awaiter =>
        match (c.put.get awaiter now).bind fun w => w.task.map (w, ·) with
        | none =>
            c
        | some (w, t) =>
            match t.state with
            | .suspended =>
                { c with
                  arm := c.arm ++ [⟨now, w.id, .retry⟩],
                  put := c.put.write { w with task := some { t with state := .pending, resumes := [o.id],
                                                                    retryTimeoutAt := some now } } }
            | .pending | .acquired | .halted =>
                if t.resumes.contains o.id then
                  c
                else
                  { c with put := c.put.write { w with task := some { t with resumes := t.resumes ++ [o.id] } } }
            | .fulfilled =>
                c
    else
      c

def leaseTimeouts (now : Nat) (org : Origin) : Commands :=
  org.objects.foldl (init := { put := org }) fun c o =>
    match o.task with
    | some t =>
        if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now)
            ∧ o.promise.state == .pending then
          { c with
            arm := c.arm ++ [⟨now, o.id, .retry⟩],
            put := c.put.write { o with task := some { t with state := .pending, pid := none, ttl := none,
                                                              leaseTimeoutAt := none,
                                                              retryTimeoutAt := some now } },
            del := c.del ++ t.timers o.id }
        else
          c
    | none =>
        c

def retryTimeouts (now : Nat) (org : Origin) : Commands :=
  org.objects.foldl (init := { put := org }) fun c o =>
    match o.task, o.promise.type with
    | some t, .runnable target =>
        if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now)
            ∧ o.promise.state == .pending then
          { c with
            arm := c.arm ++ [⟨now + retryTimeout, o.id, .retry⟩],
            put := c.put.write { o with task := some { t with retryTimeoutAt := some (now + retryTimeout) } },
            del := c.del ++ t.timers o.id,
            send := c.send ++ [(target, .execute o.id t.version)] }
        else
          c
    | _, _ =>
        c

def sweep (now : Nat) (org : Origin) : Commands :=
  let c1 := promiseTimeouts now org
  let c2 := c1.merge (listeners now c1.put)
  let c3 := c2.merge (callbacks now c2.put)
  let c4 := c3.merge (leaseTimeouts now c3.put)
  c4.merge (retryTimeouts now c4.put)

end Concrete
