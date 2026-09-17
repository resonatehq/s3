import impl.external
import impl.internal

namespace Concrete

open Protocol (Request Response)

def _root_.Protocol.Request.origin? : Request → Option String
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

def handle (now : Nat) (org : Origin) : Event → Reply × Commands
  | .external req =>
      let swept := sweep now org
      let (res, c) := handleExternal now swept.org req
      (.external res, swept.merge c)
  | .internal _ =>
      (.internal, sweep now org)
  | .stutter =>
      (.stutter, { org })

def step (H : Hasher) (ev : Event) (now : Nat) (s : State) : Reply × State :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (r, s', ok) := run H name (fun org => handle now org ev) s
          (if ok then r else .stutter, s')
      | none =>
          (.stutter, s)
  | .internal t =>
      if (s.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, s', ok) := run H t.id.origin (fun org => handle now org ev) s
        (if ok then r else .stutter, s')
      else
        (.stutter, s)
  | .stutter =>
      (.stutter, s)

def exec (H : Hasher) : List (Event × Nat) → State → List Reply × State
  | [], s =>
      ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step H ev n s
      let (rs, s'') := exec H w s'
      (r :: rs, s'')

structure Frame where
  state : State
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (H : Hasher) (tr : Trace) : Prop :=
  ∀ t : Nat,
    step H (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr t).reply = (step H (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr (t + 1)).state = (step H (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

end Concrete
