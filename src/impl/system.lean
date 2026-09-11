import impl.external
import «02-abstract».«system»

namespace Concrete

open ServerModel (Message OutboxEntry)
open Abstract (Request Response)

inductive Path
  | origin (name : String)
  | timer (t : Timer)
  deriving Repr, DecidableEq

inductive Blob
  | origin (org : Origin)
  | timer
  deriving Repr

structure State where
  bucket : List (Path × Blob) := []
  outbox : List OutboxEntry := []
  deriving Repr

def State.init : State := {}

def State.origin (s : State) (name : String) : Origin :=
  match s.bucket.find? (·.1 == .origin name) with
  | some (_, .origin org) =>
      org
  | _ =>
      {}

def State.has (s : State) (p : Path) : Bool :=
  s.bucket.any (·.1 == p)

inductive Effect
  | put (path : Path) (blob : Blob)
  | del (path : Path)
  | send (address : String) (msg : Message)
  deriving Repr

def Effect.apply (s : State) : Effect → State
  | .put p b =>
      { s with bucket := (p, b) :: s.bucket.filter (·.1 != p) }
  | .del p =>
      { s with bucket := s.bucket.filter (·.1 != p) }
  | .send a m =>
      let entry := OutboxEntry.mk a m
      { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def Commands.effects (name : String) (c : Commands) : List Effect :=
  c.arm.map (fun t => .put (.timer t) .timer)
  ++ [.put (.origin name) (.origin c.put)]
  ++ c.del.map (fun t => .del (.timer t))
  ++ c.send.map (fun (a, m) => .send a m)

def _root_.Abstract.Request.origin? : Request → Option String
  | .promiseGet req =>
      some req.id.origin
  | .promiseCreate req =>
      some req.id.origin
  | .promiseSettle req =>
      some req.id.origin
  | .promiseRegisterCallback req =>
      some req.awaited.origin
  | .promiseRegisterListener req =>
      some req.awaited.origin
  | .promiseSearch _ =>
      none
  | .scheduleGet _ =>
      none
  | .scheduleCreate _ =>
      none
  | .scheduleDelete _ =>
      none
  | .scheduleSearch _ =>
      none
  | .taskGet req =>
      some req.id.origin
  | .taskCreate req =>
      some req.action.id.origin
  | .taskAcquire req =>
      some req.id.origin
  | .taskFence req =>
      some req.id.origin
  | .taskHeartbeat req =>
      match req.tasks with
      | [] =>
          none
      | t :: ts =>
          if ts.all (·.id.origin == t.id.origin) then some t.id.origin else none
  | .taskSuspend req =>
      some req.id.origin
  | .taskFulfill req =>
      some req.id.origin
  | .taskRelease req =>
      some req.id.origin
  | .taskHalt req =>
      some req.id.origin
  | .taskContinue req =>
      some req.id.origin
  | .taskSearch _ =>
      none

inductive Event
  | external (req : Request)
  | internal (timer : Timer)
  | stutter
  deriving Repr

inductive Reply
  | external (res : Response)
  | internal
  | stutter
  deriving Repr, BEq

def handleExternal (now : Nat) (org : Origin) : Request → Response × Commands
  | .promiseGet req =>
      let (res, c) := promiseGet now org req
      (.promiseGet res, c)
  | .promiseCreate req =>
      let (res, c) := promiseCreate now org req
      (.promiseCreate res, c)
  | .promiseSettle req =>
      let (res, c) := promiseSettle now org req
      (.promiseSettle res, c)
  | .promiseRegisterCallback req =>
      let (res, c) := promiseRegisterCallback now org req
      (.promiseRegisterCallback res, c)
  | .promiseRegisterListener req =>
      let (res, c) := promiseRegisterListener now org req
      (.promiseRegisterListener res, c)
  | .promiseSearch req =>
      let (res, c) := promiseSearch now org req
      (.promiseSearch res, c)
  | .scheduleGet req =>
      let (res, c) := scheduleGet now org req
      (.scheduleGet res, c)
  | .scheduleCreate req =>
      let (res, c) := scheduleCreate now org req
      (.scheduleCreate res, c)
  | .scheduleDelete req =>
      let (res, c) := scheduleDelete now org req
      (.scheduleDelete res, c)
  | .scheduleSearch req =>
      let (res, c) := scheduleSearch now org req
      (.scheduleSearch res, c)
  | .taskGet req =>
      let (res, c) := taskGet now org req
      (.taskGet res, c)
  | .taskCreate req =>
      let (res, c) := taskCreate now org req
      (.taskCreate res, c)
  | .taskAcquire req =>
      let (res, c) := taskAcquire now org req
      (.taskAcquire res, c)
  | .taskFence req =>
      let (res, c) := taskFence now org req
      (.taskFence res, c)
  | .taskHeartbeat req =>
      let (res, c) := taskHeartbeat now org req
      (.taskHeartbeat res, c)
  | .taskSuspend req =>
      let (res, c) := taskSuspend now org req
      (.taskSuspend res, c)
  | .taskFulfill req =>
      let (res, c) := taskFulfill now org req
      (.taskFulfill res, c)
  | .taskRelease req =>
      let (res, c) := taskRelease now org req
      (.taskRelease res, c)
  | .taskHalt req =>
      let (res, c) := taskHalt now org req
      (.taskHalt res, c)
  | .taskContinue req =>
      let (res, c) := taskContinue now org req
      (.taskContinue res, c)
  | .taskSearch req =>
      let (res, c) := taskSearch now org req
      (.taskSearch res, c)

def handleInternal (_now : Nat) (org : Origin) (_t : Timer) : Commands :=
  { put := org }

def step (ev : Event) (now : Nat) (s : State) : Reply × State :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (res, c) := handleExternal now (s.origin name) req
          (.external res, (c.effects name).foldl Effect.apply s)
      | none =>
          (.external (handleExternal now {} req).1, s)
  | .internal t =>
      if s.has (.timer t) ∧ t.deadline ≤ now then
        let c := handleInternal now (s.origin t.id.origin) t
        (.internal, (c.effects t.id.origin).foldl Effect.apply s)
      else
        (.stutter, s)
  | .stutter =>
      (.stutter, s)

def exec : List (Event × Nat) → State → List Reply × State
  | [], s =>
      ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step ev n s
      let (rs, s'') := exec w s'
      (r :: rs, s'')

structure Frame where
  state : State
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (tr : Trace) : Prop :=
  ∀ t : Nat,
    step (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).reply = (step (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr (t + 1)).state = (step (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

end Concrete
