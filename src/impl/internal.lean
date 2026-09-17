import impl.state

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)

def retryDelay : Nat := 5000

def Commands.merge (c d : Commands) : Commands :=
  { arm := c.arm ++ d.arm, org := d.org, del := c.del ++ d.del, send := c.send ++ d.send }

def promiseTimeout (now : Nat) (o : Object) : Option Object :=
  if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
    some (o.project now)
  else
    none

def listener (now : Nat) (o : Object) : Option (Object × List (String × Message)) :=
  let o := o.project now
  if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
    some ({ o with promise := { o.promise with listeners := [] } },
          o.promise.listeners.map fun a => (a, .unblock (o.promise.toRecord o.id)))
  else
    none

def awaiting (now : Nat) (objects : List Object) (id : Ident) : List Ident :=
  objects.filterMap fun s =>
    let s := s.project now
    if s.promise.state != .pending ∧ s.promise.callbacks.contains id then
      some s.id
    else
      none

def _root_.Protocol.TaskObject.resume (now : Nat) (t : TaskObject) (awaited : Ident) : TaskObject :=
  match t.state with
  | .suspended =>
      { t with state := .pending, resumes := [awaited], retryTimeoutAt := some now }
  | .pending | .acquired | .halted =>
      if t.resumes.contains awaited then t else { t with resumes := t.resumes ++ [awaited] }
  | .fulfilled =>
      t

def callback (now : Nat) (org : Origin) (o : Object) : Option Object :=
  let o := o.project now
  let struck := o.promise.state != .pending ∧ !o.promise.callbacks.isEmpty
  let awaited := awaiting now org.objects o.id
  if struck ∨ (o.task.isSome ∧ !awaited.isEmpty) then
    some { o with promise := if struck then { o.promise with callbacks := [] } else o.promise,
                  task := o.task.map (awaited.foldl (·.resume now ·)) }
  else
    none

def leaseTimeout (now : Nat) (o : Object) : Option Object :=
  let o := o.project now
  match o.task with
  | some t =>
      if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
        some { o with task := some { t with state := .pending, pid := none, ttl := none,
                                             leaseTimeoutAt := none, retryTimeoutAt := some now } }
      else
        none
  | none =>
      none

def retryTimeout (now : Nat) (o : Object) : Option (Object × List (String × Message)) :=
  let o := o.project now
  match o.task, o.promise.type with
  | some t, .runnable target =>
      if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
        some ({ o with task := some { t with retryTimeoutAt := some (now + retryDelay) } },
              [(target, .execute o.id t.version)])
      else
        none
  | _, _ =>
      none

structure Change where
  obj      : Object
  unblocks : List (String × Message)
  executes : List (String × Message)

def sweepObject (now : Nat) (org : Origin) (o : Object) : Change :=
  let o := (promiseTimeout now o).getD o
  let (o, unblocks) := (listener now o).getD (o, [])
  let o := (callback now org o).getD o
  let o := (leaseTimeout now o).getD o
  let (o, executes) := (retryTimeout now o).getD (o, [])
  { obj := o, unblocks, executes }

def sweep (now : Nat) (org : Origin) : Commands :=
  let changes := org.objects.map (sweepObject now org)
  let before := org.objects.flatMap (·.timers)
  let after := (changes.map (·.obj)).flatMap (·.timers)
  { arm  := after.filter (!before.contains ·),
    org  := ⟨changes.map (·.obj)⟩,
    del  := before.filter (!after.contains ·),
    send := changes.flatMap (·.unblocks) ++ changes.flatMap (·.executes) }

end Concrete
