import impl.monad

namespace Impl

open ServerModel (Ident Message PromiseState TaskState)
open AbstractModel (Object PromiseObject TaskObject ServerState)
open Equivalence (Request Response)
open Abstraction (InternalStep)

def _root_.Equivalence.Request.origin? : Request → Option String
  | .promiseGet r              => some r.id.origin
  | .promiseCreate r           => some r.id.origin
  | .promiseSettle r           => some r.id.origin
  | .promiseRegisterCallback r => some r.awaited.origin
  | .promiseRegisterListener r => some r.awaited.origin
  | .promiseSearch _           => none
  | .scheduleGet _             => none
  | .scheduleCreate _          => none
  | .scheduleDelete _          => none
  | .scheduleSearch _          => none
  | .taskGet r                 => some r.id.origin
  | .taskCreate r              => some r.action.id.origin
  | .taskAcquire r             => some r.id.origin
  | .taskFence r               => some r.id.origin
  | .taskHeartbeat r           =>
      match r.tasks with
      | []       => none
      | t :: ts  => if ts.all (fun u => u.id.origin == t.id.origin) then some t.id.origin else none
  | .taskSuspend r             => some r.id.origin
  | .taskFulfill r             => some r.id.origin
  | .taskRelease r             => some r.id.origin
  | .taskHalt r                => some r.id.origin
  | .taskContinue r            => some r.id.origin
  | .taskSearch _              => none

def sendsOf : List AbstractModel.Effect → List (String × Message)
  | []                      => []
  | .setMessage a m :: rest => (a, m) :: sendsOf rest
  | _ :: rest               => sendsOf rest

def dueAt (now : Nat) : Option Nat → Bool
  | some dl => dl ≤ now
  | none    => false

def stepDoc (mat : Bool) (st : Abstraction.Step) (now : Nat) (d : OriginDoc) :
    Response × OriginDoc × List (String × Message) :=
  let (res, fx) := Abstraction.handle st now { state := d.toState, mat := mat }
  (res, OriginDoc.ofState (AbstractModel.applyAll d.toState fx) d.timerAt, sendsOf fx)

def stepDocs (mat : Bool) (now : Nat) :
    OriginDoc → List InternalStep → OriginDoc × List (String × Message)
  | d, []       => (d, [])
  | d, st :: sts =>
      let (_, d', sends) := stepDoc mat (.internal st) now d
      let (d'', sends') := stepDocs mat now d' sts
      (d'', sends ++ sends')

def timeoutSteps (d : OriginDoc) (now : Nat) : List InternalStep :=
  (d.objects.filterMap fun o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now
    then some (.promiseTimeout ⟨o.id⟩) else none)
  ++ (d.objects.filterMap fun o =>
    match o.task with
    | some t =>
        if t.state == .acquired ∧ dueAt now t.leaseTimeoutAt
        then some (.taskLeaseTimeout ⟨o.id⟩) else none
    | none => none)

def obligationSteps (origin : String) (d : OriginDoc) : List InternalStep :=
  d.objects.flatMap fun o =>
    if o.promise.state != .pending then
      (o.promise.callbacks.filterMap fun awaiter =>
        if awaiter.origin == origin
        then some (.callback ⟨o.id, awaiter⟩) else none)
      ++ o.promise.listeners.map (fun a => .listener ⟨o.id, a⟩)
    else []

def retrySteps (d : OriginDoc) (now : Nat) : List InternalStep :=
  d.objects.filterMap fun o =>
    match o.task with
    | some t =>
        if t.state == .pending ∧ dueAt now t.retryTimeoutAt
        then some (.taskRetryTimeout ⟨o.id⟩) else none
    | none => none

def drainSteps (mat : Bool) (origin : String) (d : OriginDoc) (now : Nat) : List InternalStep :=
  let p1 := timeoutSteps d now
  let d1 := (stepDocs mat now d p1).1
  let p2 := obligationSteps origin d1
  let d2 := (stepDocs mat now d1 p2).1
  let p3 := retrySteps d2 now
  p1 ++ p2 ++ p3

def drain (mat : Bool) (origin : String) (d : OriginDoc) (now : Nat) :
    OriginDoc × List (String × Message) :=
  stepDocs mat now d (drainSteps mat origin d now)

inductive Work
  | request (rq : Request)

  | sweep (fired : Option Nat)
  deriving Repr

def Work.origin? (declared : String) : Work → Option String
  | .request rq => rq.origin?
  | .sweep _    => some declared

def decide (mat : Bool) (origin : String) (work : Work) (now : Nat) (old : OriginDoc) :
    Response × OriginDoc × List (String × Message) :=
  let (res, d1, sends1) :=
    match work with
    | .request rq => stepDoc mat (.external rq) now old
    | .sweep _    => (Response.silent, old, [])
  let (d2, sends2) := drain mat origin d1 now
  (res, { d2 with timerAt := d2.minDeadline }, sends1 ++ sends2)

def armFx (old new : OriginDoc) : List Effect :=
  if new.timerAt != old.timerAt then
    match new.timerAt with
    | some dl => [.armTimer dl]
    | none    => []
  else []

def delFx (old new : OriginDoc) (work : Work) : List Effect :=
  (if new.timerAt != old.timerAt then
    match old.timerAt with
    | some dl => [.delTimer dl]
    | none    => []
  else [])
  ++ (match work with
      | .sweep (some fired) => if new.timerAt != some fired then [.delTimer fired] else []
      | _                   => [])

def sendFx (sends : List (String × Message)) : List Effect :=
  sends.map fun (a, m) => .send a m

def emitAll : List Effect → C Unit
  | []      => pure ()
  | f :: fs => do emit f; emitAll fs

def transact (mat : Bool) (work : Work) (now : Nat) : C Response := do
  let e ← ask
  let (res, new, sends) := decide mat e.origin work now e.doc
  emitAll (armFx e.doc new)
  putDoc new
  emitAll (delFx e.doc new work)
  emitAll (sendFx sends)
  return res

end Impl
