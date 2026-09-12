import «02-abstract».«internal»

namespace Abstract

open Protocol

open Protocol (Ident)

inductive Trigger
  | promiseTimeout   (req : Protocol.PromiseTimeoutReq)
  | callback         (req : Protocol.PromiseRegisterCallbackReq)
  | listener         (req : Protocol.PromiseRegisterListenerReq)
  | taskLeaseTimeout (req : Protocol.TaskLeaseTimeoutReq)
  | taskRetryTimeout (req : Protocol.TaskRetryTimeoutReq)
  | scheduleTimeout  (req : Protocol.ScheduleTimeoutReq)
  deriving Repr, DecidableEq

inductive Event
  | external (req : Request)
  | internal (trg : Trigger)
  | stutter
  deriving Repr

inductive Reply
  | external (res : Response)
  | internal
  | stutter
  deriving Repr, BEq

def Event.isExternal : Event → Bool
  | .external _ => true
  | _           => false

def Event.isInternal : Event → Bool
  | .internal _ => true
  | _           => false

deriving instance BEq for Protocol.TaskObject

deriving instance BEq for Protocol.PromiseObject
deriving instance BEq for Protocol.Object
deriving instance BEq for Abstract.State

def handleExternal (req : Request) (now : Nat) : Abstract.H Response :=
  match req with
  | .promiseGet              req => Response.promiseGet <$> Abstract.promiseGet req now
  | .promiseCreate           req => Response.promiseCreate <$> Abstract.promiseCreate req now
  | .promiseSettle           req => Response.promiseSettle <$> Abstract.promiseSettle req now
  | .promiseRegisterCallback req => Response.promiseRegisterCallback <$> Abstract.promiseRegisterCallback req now
  | .promiseRegisterListener req => Response.promiseRegisterListener <$> Abstract.promiseRegisterListener req now
  | .promiseSearch           req => Response.promiseSearch <$> Abstract.promiseSearch req now
  | .scheduleGet             req => Response.scheduleGet <$> Abstract.scheduleGet req now
  | .scheduleCreate          req => Response.scheduleCreate <$> Abstract.scheduleCreate req now
  | .scheduleDelete          req => Response.scheduleDelete <$> Abstract.scheduleDelete req now
  | .scheduleSearch          req => Response.scheduleSearch <$> Abstract.scheduleSearch req now
  | .taskGet                 req => Response.taskGet <$> Abstract.taskGet req now
  | .taskCreate              req => Response.taskCreate <$> Abstract.taskCreate req now
  | .taskAcquire             req => Response.taskAcquire <$> Abstract.taskAcquire req now
  | .taskFence               req => Response.taskFence <$> Abstract.taskFence req now
  | .taskHeartbeat           req => Response.taskHeartbeat <$> Abstract.taskHeartbeat req now
  | .taskSuspend             req => Response.taskSuspend <$> Abstract.taskSuspend req now
  | .taskFulfill             req => Response.taskFulfill <$> Abstract.taskFulfill req now
  | .taskRelease             req => Response.taskRelease <$> Abstract.taskRelease req now
  | .taskHalt                req => Response.taskHalt <$> Abstract.taskHalt req now
  | .taskContinue            req => Response.taskContinue <$> Abstract.taskContinue req now
  | .taskSearch              req => Response.taskSearch <$> Abstract.taskSearch req now

def handleInternal (trg : Trigger) (now : Nat) : Abstract.H Unit :=
  match trg with
  | .promiseTimeout   req => Abstract.Internal.processPromiseTimeout req now
  | .callback         req => Abstract.Internal.processCallback req now
  | .listener         req => Abstract.Internal.processListener req now
  | .taskLeaseTimeout req => Abstract.Internal.processLeaseTimeout req now
  | .taskRetryTimeout req => Abstract.Internal.processRetryTimeout req now
  | .scheduleTimeout  req => Abstract.Internal.processSchedule req now

def handle (ev : Event) (now : Nat) : Abstract.H Reply :=
  match ev with
  | .external req => Reply.external <$> handleExternal req now
  | .internal trg => do handleInternal trg now; return .internal
  | .stutter      => return .stutter

def step (mat : Bool) (ev : Event) (now : Nat) (s : Abstract.State) :
    Reply × Abstract.State :=
  Abstract.run mat (handle ev now) s

def exec (mat : Bool) :
    List (Event × Nat) → Abstract.State →
    List Reply × Abstract.State
  | [],           s => ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step mat ev n s
      let (rs, s'') := exec mat w s'
      (r :: rs, s'')

structure Frame where
  state : Abstract.State
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (mat : Bool) (tr : Trace) : Prop :=
  ∀ t : Nat,
    step mat (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {mat : Bool} {tr : Trace} (hv : Valid mat tr) (t : Nat) :
    (tr t).reply = (step mat (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {mat : Bool} {tr : Trace} (hv : Valid mat tr) (t : Nat) :
    (tr (t + 1)).state = (step mat (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {mat : Bool} {tr : Trace} (hv : Valid mat tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

end Abstract
