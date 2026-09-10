import «02-abstract».«system»

namespace Impl

open ServerModel (Ident Message PromiseState TaskState OType PromiseCreateReq)
open AbstractModel (Object PromiseObject TaskObject ServerState)

structure Origin where
  objects : List Object := []
  deriving Repr

def Origin.toState (o : Origin) : ServerState := { objects := o.objects }

def Origin.find? (o : Origin) (id : Ident) : Option Object :=
  o.objects.find? (·.id == id)

def Object.deadlines (ob : Object) : List Nat :=
  (if ob.promise.state == .pending
      ∧ (ob.promise.otype == .runnable
         ∨ !ob.promise.callbacks.isEmpty
         ∨ !ob.promise.listeners.isEmpty)
   then [ob.promise.timeoutAt] else [])
  ++ (match ob.task with
      | some t => t.leaseTimeoutAt.toList ++ t.retryTimeoutAt.toList
      | none   => [])

def Origin.deadlines (o : Origin) : List Nat :=
  (o.objects.flatMap Object.deadlines).eraseDups

structure Tx where
  origin : Origin
  sends  : List (String × Message) := []
  deriving Repr

def Tx.start (o : Origin) : Tx := { origin := o }

def Tx.putPromise (tx : Tx) (id : Ident) (p : PromiseObject) : Tx :=
  { tx with origin := ⟨Object.withPromise id p (tx.origin.find? id)
                         :: tx.origin.objects.filter (·.id != id)⟩ }

def Tx.putTask (tx : Tx) (id : Ident) (t : TaskObject) : Tx :=
  { tx with origin := ⟨tx.origin.objects.map fun ob =>
                         if ob.id == id then { ob with task := some t } else ob⟩ }

def Tx.send (tx : Tx) (address : String) (msg : Message) : Tx :=
  { tx with sends := tx.sends ++ [(address, msg)] }

def Tx.settle (tx : Tx) (ob : Object) (p : PromiseObject) : Tx :=
  let tx := tx.putPromise ob.id p
  if p.state != .pending then
    match ob.task with
    | some t => if t.state != .fulfilled then tx.putTask ob.id t.fulfill else tx
    | none   => tx
  else tx

def Tx.createPromise (tx : Tx) (req : PromiseCreateReq) (now : Nat) : Object × Tx :=
  if req.timeoutAt > now then
    let p : PromiseObject :=
      { state := .pending, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := now }
    let tx := tx.putPromise req.id p
    if p.otype == .runnable then
      let due :=
        match p.tags.get? "resonate:delay" with
        | some d => max (ServerModel.parseNat d) now
        | none   => now
      let t : TaskObject := { state := .pending, version := 0, retryTimeoutAt := some due }
      ({ id := req.id, promise := p, task := some t }, tx.putTask req.id t)
    else
      ({ id := req.id, promise := p }, tx)
  else
    let state := if req.tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout
    let p : PromiseObject :=
      { state := state, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
        settledAt := some req.timeoutAt }
    let tx := tx.putPromise req.id p
    if p.otype == .runnable then
      let t : TaskObject := { state := .fulfilled, version := 0 }
      ({ id := req.id, promise := p, task := some t }, tx.putTask req.id t)
    else
      ({ id := req.id, promise := p }, tx)

def Tx.materialise (tx : Tx) (id : Ident) (ob ob' : Object) : Tx :=
  let tx := if ob'.promise.state != ob.promise.state then tx.putPromise id ob'.promise else tx
  match ob.task, ob'.task with
  | some t, some u => if u.state != t.state then tx.putTask id u else tx
  | _, _           => tx

def read (o : Origin) (tx : Tx) (id : Ident) (now : Nat) : Option Object × Tx :=
  match o.find? id with
  | none    => (none, tx)
  | some ob =>
      let ob' := ob.project now
      (some ob', tx.materialise id ob ob')

def readTask (o : Origin) (tx : Tx) (id : Ident) (now : Nat) : Option Object × Tx :=
  match o.find? id with
  | none    => (none, tx)
  | some ob => if ob.task.isSome then read o tx id now else (none, tx)

def view (o : Origin) (id : Ident) (now : Nat) : Option Object :=
  (o.find? id).map (·.project now)

def viewTask (o : Origin) (id : Ident) (now : Nat) : Option Object :=
  match o.find? id with
  | none    => none
  | some ob => if ob.task.isSome then view o id now else none

structure Commit where
  arm  : List Nat
  put  : Origin
  del  : List Nat
  send : List (String × Message)
  deriving Repr

def Tx.commit (o : Origin) (tx : Tx) : Commit :=
  { arm  := tx.origin.deadlines.filter (fun d => !o.deadlines.contains d)
    put  := tx.origin
    del  := o.deadlines.filter (fun d => !tx.origin.deadlines.contains d)
    send := tx.sends }

end Impl
