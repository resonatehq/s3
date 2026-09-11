import impl.handlers
import impl.monad

namespace Impl

open ServerModel (Ident Message PromiseState TaskState)
open AbstractModel (Object PromiseObject TaskObject ServerState)
open Abstract (Request Response Reply Trigger)

def _root_.Abstract.Request.origin? : Request → Option String
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

def triggers (now : Nat) : Origin → List Trigger → Origin × List (String × Message)
  | o, []          => (o, [])
  | o, trg :: rest =>
      let c := Handle.trigger trg now o
      let (o', sends) := triggers now c.put rest
      (o', c.send ++ sends)

def timeoutSteps (o : Origin) (now : Nat) : List Trigger :=
  (o.objects.filterMap fun ob =>
    if ob.promise.state == .pending ∧ ob.promise.timeoutAt ≤ now
    then some (.promiseTimeout ⟨ob.id⟩) else none)
  ++ (o.objects.filterMap fun ob =>
    match ob.task with
    | some t =>
        if t.state == .acquired ∧ dueAt now t.leaseTimeoutAt
        then some (.taskLeaseTimeout ⟨ob.id⟩) else none
    | none => none)

def obligationSteps (name : String) (o : Origin) : List Trigger :=
  o.objects.flatMap fun ob =>
    if ob.promise.state != .pending then
      (ob.promise.callbacks.filterMap fun awaiter =>
        if awaiter.origin == name
        then some (.callback ⟨ob.id, awaiter⟩) else none)
      ++ ob.promise.listeners.map (fun a => .listener ⟨ob.id, a⟩)
    else []

def retrySteps (o : Origin) (now : Nat) : List Trigger :=
  o.objects.filterMap fun ob =>
    match ob.task with
    | some t =>
        if t.state == .pending ∧ dueAt now t.retryTimeoutAt
        then some (.taskRetryTimeout ⟨ob.id⟩) else none
    | none => none

def drainSteps (name : String) (o : Origin) (now : Nat) : List Trigger :=
  let p1 := timeoutSteps o now
  let o1 := (triggers now o p1).1
  let p2 := obligationSteps name o1
  let o2 := (triggers now o1 p2).1
  let p3 := retrySteps o2 now
  p1 ++ p2 ++ p3

def drain (name : String) (o : Origin) (now : Nat) : Origin × List (String × Message) :=
  triggers now o (drainSteps name o now)

inductive Work
  | request (rq : Request)
  | sweep (fired : Nat)
  deriving Repr

def Work.origin? (declared : String) : Work → Option String
  | .request rq => rq.origin?
  | .sweep _    => some declared

def Work.licensed (declared : String) (now : Nat) (w : World) : Work → Bool
  | .request _  => true
  | .sweep dl   => (w.store.get (.timer dl declared)).isSome && decide (dl ≤ now)

def decide (name : String) (work : Work) (now : Nat) (old : Origin) : Reply × Commit :=
  let (r, o1, sends1) :=
    match work with
    | .request rq =>
        let (res, c) := Handle.external rq now old
        (Reply.external res, c.put, c.send)
    | .sweep _    => (Reply.stutter, old, [])
  let (o2, sends2) := drain name o1 now
  (r, Tx.commit old { origin := o2, sends := sends1 ++ sends2 })

def armFx (c : Commit) : List Effect :=
  c.arm.map .armTimer

def delFx (c : Commit) (work : Work) : List Effect :=
  c.del.map .delTimer
  ++ (match work with
      | .sweep fired => if c.put.deadlines.contains fired then [] else [.delTimer fired]
      | .request _   => [])

def sendFx (sends : List (String × Message)) : List Effect :=
  sends.map fun (a, m) => .send a m

def emitAll : List Effect → C Unit
  | []      => pure ()
  | f :: fs => do emit f; emitAll fs

def transact (work : Work) (now : Nat) : C Reply := do
  let e ← ask
  let (r, c) := decide e.origin work now e.snap
  emitAll (armFx c)
  putOrigin c.put
  emitAll (delFx c work)
  emitAll (sendFx c.send)
  return r

end Impl
