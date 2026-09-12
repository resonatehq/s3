import «02-abstract».«internal»

namespace Abstract

open ServerModel

open ServerModel (Ident)

inductive Trigger
  | promiseTimeout   (req : ServerModel.PromiseTimeoutReq)
  | callback         (req : ServerModel.PromiseRegisterCallbackReq)
  | listener         (req : ServerModel.PromiseRegisterListenerReq)
  | taskLeaseTimeout (req : ServerModel.TaskLeaseTimeoutReq)
  | taskRetryTimeout (req : ServerModel.TaskRetryTimeoutReq)
  | scheduleTimeout  (req : ServerModel.ScheduleTimeoutReq)
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

deriving instance BEq for ServerModel.TaskObject

deriving instance BEq for ServerModel.PromiseObject
deriving instance BEq for ServerModel.Object
deriving instance BEq for AbstractModel.ServerState

def handleExternal (req : Request) (now : Nat) : AbstractModel.H Response :=
  match req with
  | .promiseGet              req => Response.promiseGet <$> AbstractModel.promiseGet req now
  | .promiseCreate           req => Response.promiseCreate <$> AbstractModel.promiseCreate req now
  | .promiseSettle           req => Response.promiseSettle <$> AbstractModel.promiseSettle req now
  | .promiseRegisterCallback req => Response.promiseRegisterCallback <$> AbstractModel.promiseRegisterCallback req now
  | .promiseRegisterListener req => Response.promiseRegisterListener <$> AbstractModel.promiseRegisterListener req now
  | .promiseSearch           req => Response.promiseSearch <$> AbstractModel.promiseSearch req now
  | .scheduleGet             req => Response.scheduleGet <$> AbstractModel.scheduleGet req now
  | .scheduleCreate          req => Response.scheduleCreate <$> AbstractModel.scheduleCreate req now
  | .scheduleDelete          req => Response.scheduleDelete <$> AbstractModel.scheduleDelete req now
  | .scheduleSearch          req => Response.scheduleSearch <$> AbstractModel.scheduleSearch req now
  | .taskGet                 req => Response.taskGet <$> AbstractModel.taskGet req now
  | .taskCreate              req => Response.taskCreate <$> AbstractModel.taskCreate req now
  | .taskAcquire             req => Response.taskAcquire <$> AbstractModel.taskAcquire req now
  | .taskFence               req => Response.taskFence <$> AbstractModel.taskFence req now
  | .taskHeartbeat           req => Response.taskHeartbeat <$> AbstractModel.taskHeartbeat req now
  | .taskSuspend             req => Response.taskSuspend <$> AbstractModel.taskSuspend req now
  | .taskFulfill             req => Response.taskFulfill <$> AbstractModel.taskFulfill req now
  | .taskRelease             req => Response.taskRelease <$> AbstractModel.taskRelease req now
  | .taskHalt                req => Response.taskHalt <$> AbstractModel.taskHalt req now
  | .taskContinue            req => Response.taskContinue <$> AbstractModel.taskContinue req now
  | .taskSearch              req => Response.taskSearch <$> AbstractModel.taskSearch req now

def handleInternal (trg : Trigger) (now : Nat) : AbstractModel.H Unit :=
  match trg with
  | .promiseTimeout   req => AbstractModel.Internal.processPromiseTimeout req now
  | .callback         req => AbstractModel.Internal.processCallback req now
  | .listener         req => AbstractModel.Internal.processListener req now
  | .taskLeaseTimeout req => AbstractModel.Internal.processLeaseTimeout req now
  | .taskRetryTimeout req => AbstractModel.Internal.processRetryTimeout req now
  | .scheduleTimeout  req => AbstractModel.Internal.processSchedule req now

def handle (ev : Event) (now : Nat) : AbstractModel.H Reply :=
  match ev with
  | .external req => Reply.external <$> handleExternal req now
  | .internal trg => do handleInternal trg now; return .internal
  | .stutter      => return .stutter

def step (mat : Bool) (ev : Event) (now : Nat) (s : AbstractModel.ServerState) :
    Reply × AbstractModel.ServerState :=
  AbstractModel.run mat (handle ev now) s

def exec (mat : Bool) :
    List (Event × Nat) → AbstractModel.ServerState →
    List Reply × AbstractModel.ServerState
  | [],           s => ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step mat ev n s
      let (rs, s'') := exec mat w s'
      (r :: rs, s'')

structure Frame where
  state : AbstractModel.ServerState
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
