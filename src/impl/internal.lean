import impl.state

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)

def retryDelay : Nat := 5000

def Commands.merge (c d : Commands) : Commands :=
  { arm := c.arm ++ d.arm, org := d.org, del := c.del ++ d.del, send := c.send ++ d.send }

def processPromiseTimeout (now : Nat) (o : Object) : Option Object :=
  if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
    some (o.project now)
  else
    none

def processListener (now : Nat) (o : Object) : Option (Object × List (String × Message)) :=
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

def _root_.Protocol.TaskObject.resumeOne (now : Nat) (t : TaskObject) (awaited : Ident) : TaskObject :=
  match t.state with
  | .suspended =>
      { t with state := .pending, resumes := [awaited], retryTimeoutAt := some now }
  | .pending | .acquired | .halted =>
      if t.resumes.contains awaited then t else { t with resumes := t.resumes ++ [awaited] }
  | .fulfilled =>
      t

def processCallback (now : Nat) (org : Origin) (o : Object) : Option Object :=
  let o := o.project now
  let struck := o.promise.state != .pending ∧ !o.promise.callbacks.isEmpty
  let awaited := awaiting now org.objects o.id
  if struck ∨ (o.task.isSome ∧ !awaited.isEmpty) then
    some { o with promise := if struck then { o.promise with callbacks := [] } else o.promise,
                  task := o.task.map (awaited.foldl (·.resumeOne now ·)) }
  else
    none

def processLeaseTimeout (now : Nat) (o : Object) : Option Object :=
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

def processRetryTimeout (now : Nat) (o : Object) : Option (Object × List (String × Message)) :=
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
  let o := (processPromiseTimeout now o).getD o
  let (o, unblocks) := (processListener now o).getD (o, [])
  let o := (processCallback now org o).getD o
  let o := (processLeaseTimeout now o).getD o
  let (o, executes) := (processRetryTimeout now o).getD (o, [])
  { obj := o, unblocks, executes }

def sweep (now : Nat) (org : Origin) : Commands :=
  let changes := org.objects.map (sweepObject now org)
  let before := org.objects.flatMap (·.timers)
  let after := (changes.map (·.obj)).flatMap (·.timers)
  { arm  := after.filter (!before.contains ·),
    org  := ⟨org.objects ++ (changes.map (·.obj)).filter (· ∉ org.objects)⟩,
    del  := before.filter (!after.contains ·),
    send := changes.flatMap (·.unblocks) ++ changes.flatMap (·.executes) }

end Concrete
