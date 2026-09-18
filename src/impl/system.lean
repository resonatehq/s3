import impl.external
import impl.internal

namespace Concrete

open Protocol (Request Response)

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

def handleExternal (req : Request) (now : Nat) (org : Origin) : Response × Commands :=
  match req with
  | .promiseGet req =>
      let (res, c) := promiseGet req now org
      (.promiseGet res, c)
  | .promiseCreate req =>
      let (res, c) := promiseCreate req now org
      (.promiseCreate res, c)
  | .promiseSettle req =>
      let (res, c) := promiseSettle req now org
      (.promiseSettle res, c)
  | .promiseRegisterCallback req =>
      let (res, c) := promiseRegisterCallback req now org
      (.promiseRegisterCallback res, c)
  | .promiseRegisterListener req =>
      let (res, c) := promiseRegisterListener req now org
      (.promiseRegisterListener res, c)
  | .promiseSearch req =>
      let (res, c) := promiseSearch req now org
      (.promiseSearch res, c)
  | .scheduleGet req =>
      let (res, c) := scheduleGet req now org
      (.scheduleGet res, c)
  | .scheduleCreate req =>
      let (res, c) := scheduleCreate req now org
      (.scheduleCreate res, c)
  | .scheduleDelete req =>
      let (res, c) := scheduleDelete req now org
      (.scheduleDelete res, c)
  | .scheduleSearch req =>
      let (res, c) := scheduleSearch req now org
      (.scheduleSearch res, c)
  | .taskGet req =>
      let (res, c) := taskGet req now org
      (.taskGet res, c)
  | .taskCreate req =>
      let (res, c) := taskCreate req now org
      (.taskCreate res, c)
  | .taskAcquire req =>
      let (res, c) := taskAcquire req now org
      (.taskAcquire res, c)
  | .taskFence req =>
      let (res, c) := taskFence req now org
      (.taskFence res, c)
  | .taskHeartbeat req =>
      let (res, c) := taskHeartbeat req now org
      (.taskHeartbeat res, c)
  | .taskSuspend req =>
      let (res, c) := taskSuspend req now org
      (.taskSuspend res, c)
  | .taskFulfill req =>
      let (res, c) := taskFulfill req now org
      (.taskFulfill res, c)
  | .taskRelease req =>
      let (res, c) := taskRelease req now org
      (.taskRelease res, c)
  | .taskHalt req =>
      let (res, c) := taskHalt req now org
      (.taskHalt res, c)
  | .taskContinue req =>
      let (res, c) := taskContinue req now org
      (.taskContinue res, c)
  | .taskSearch req =>
      let (res, c) := taskSearch req now org
      (.taskSearch res, c)

def handle (ev : Event) (now : Nat) (org : Origin) : Reply × Commands :=
  match ev with
  | .external req =>
      let swept := sweep now org
      let (res, c) := handleExternal req now swept.org
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
          let (r, s', ok) := run H name (fun org => handle ev now org) s
          (if ok then r else .stutter, s')
      | none =>
          (.stutter, s)
  | .internal t =>
      if (s.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, s', ok) := run H t.id.origin (fun org => handle ev now org) s
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
