namespace ServerModel

structure Ident where
  origin : String
  suffix : String
  deriving Repr, DecidableEq, Inhabited

instance : BEq Ident := instBEqOfDecidableEq

def Ident.sameOrigin (a b : Ident) : Bool := a.origin == b.origin

abbrev Tags := List (String × String)

structure Value where
  headers : Tags          := []
  data    : Option String := none
  deriving Repr, Inhabited

inductive PromiseState
  | pending
  | resolved
  | rejected
  | rejectedCanceled
  | rejectedTimedout
  deriving Repr, DecidableEq

inductive TaskState
  | pending | acquired | suspended | halted | fulfilled
  deriving Repr, DecidableEq

inductive OType
  | internal
  | deadline
  | external
  | runnable (target : String)
  deriving Repr, DecidableEq

def OType.awaitable : OType → Bool
  | .internal => false
  | _         => true

def OType.isRunnable : OType → Bool
  | .runnable _ => true
  | _           => false

def OType.target? : OType → Option String
  | .runnable t => some t
  | _           => none

structure PromiseRecord where
  id        : Ident
  state     : PromiseState
  param     : Value
  value     : Value       := {}
  type      : OType
  timeoutAt : Nat
  createdAt : Nat
  settledAt : Option Nat  := none
  deriving Repr

structure TaskRecord where
  id      : Ident
  state   : TaskState
  version : Nat
  resumes : Nat
  ttl     : Option Nat    := none
  pid     : Option String := none
  deriving Repr

structure Schedule where
  id             : Ident
  cron           : String
  promiseId      : Ident
  promiseTimeout : Nat
  promiseParam   : Value
  promiseType    : OType
  nextRunAt      : Nat
  lastRunAt      : Option Nat := none
  createdAt      : Nat
  deriving Repr

structure PromiseGetReq where
  id : Ident
  deriving Repr

structure PromiseGetRes where
  status  : Nat
  promise : Option PromiseRecord := none
  deriving Repr

structure PromiseCreateReq where
  id        : Ident
  timeoutAt : Nat
  param     : Value
  type      : OType
  delay     : Option Nat := none
  deriving Repr

structure PromiseCreateRes where
  status  : Nat
  promise : Option PromiseRecord
  deriving Repr

structure PromiseSettleReq where
  id    : Ident
  state : PromiseState
  value : Value
  deriving Repr

structure PromiseSettleRes where
  status  : Nat
  promise : Option PromiseRecord := none
  deriving Repr

structure PromiseRegisterCallbackReq where
  awaited : Ident
  awaiter : Ident
  deriving Repr, DecidableEq

structure PromiseRegisterCallbackRes where
  status  : Nat
  promise : Option PromiseRecord := none
  deriving Repr

structure PromiseRegisterListenerReq where
  awaited : Ident
  address : String
  deriving Repr, DecidableEq

structure PromiseRegisterListenerRes where
  status  : Nat
  promise : Option PromiseRecord := none
  deriving Repr

structure PromiseSearchReq where
  state  : Option PromiseState := none
  limit  : Option Nat := none
  cursor : Option String := none
  deriving Repr

structure PromiseSearchRes where
  status   : Nat
  promises : List PromiseRecord := []
  cursor   : Option String := none
  deriving Repr

structure ScheduleGetReq where
  id : Ident
  deriving Repr

structure ScheduleGetRes where
  status   : Nat
  schedule : Option Schedule := none
  deriving Repr

structure ScheduleCreateReq where
  id             : Ident
  cron           : String
  promiseId      : Ident
  promiseTimeout : Nat
  promiseParam   : Value
  promiseType    : OType
  deriving Repr

structure ScheduleCreateRes where
  status   : Nat
  schedule : Option Schedule := none
  deriving Repr

structure ScheduleDeleteReq where
  id : Ident
  deriving Repr

structure ScheduleDeleteRes where
  status : Nat
  deriving Repr

structure ScheduleSearchReq where
  limit  : Option Nat := none
  cursor : Option String := none
  deriving Repr

structure ScheduleSearchRes where
  status    : Nat
  schedules : List Schedule := []
  cursor    : Option String := none
  deriving Repr

structure TaskGetReq where
  id : Ident
  deriving Repr

structure TaskGetRes where
  status : Nat
  task   : Option TaskRecord := none
  deriving Repr

structure TaskCreateReq where
  pid    : String
  ttl    : Nat
  action : PromiseCreateReq
  deriving Repr

structure TaskCreateRes where
  status  : Nat
  task    : Option TaskRecord := none
  promise : Option PromiseRecord := none
  preload : List PromiseRecord := []
  deriving Repr

structure TaskAcquireReq where
  id      : Ident
  version : Nat
  pid     : String
  ttl     : Nat
  deriving Repr

structure TaskAcquireRes where
  status  : Nat
  task    : Option TaskRecord := none
  promise : Option PromiseRecord := none
  preload : List PromiseRecord := []
  deriving Repr

inductive TaskFenceAction
  | create (req : PromiseCreateReq)
  | settle (req : PromiseSettleReq)
  deriving Repr

inductive TaskFenceInnerRes
  | create (res : PromiseCreateRes)
  | settle (res : PromiseSettleRes)
  deriving Repr

structure TaskFenceReq where
  id      : Ident
  version : Nat
  action  : TaskFenceAction
  deriving Repr

structure TaskFenceRes where
  status  : Nat
  action  : Option TaskFenceInnerRes := none
  preload : List PromiseRecord := []
  deriving Repr

structure TaskRef where
  id      : Ident
  version : Nat
  deriving Repr

structure TaskHeartbeatReq where
  pid   : String
  tasks : List TaskRef
  deriving Repr

structure TaskHeartbeatRes where
  status : Nat
  deriving Repr

structure TaskSuspendReq where
  id      : Ident
  version : Nat
  actions : List PromiseRegisterCallbackReq
  deriving Repr

structure TaskSuspendRes where
  status  : Nat
  preload : List PromiseRecord := []
  deriving Repr

structure TaskFulfillReq where
  id      : Ident
  version : Nat
  action  : PromiseSettleReq
  deriving Repr

structure TaskFulfillRes where
  status  : Nat
  promise : Option PromiseRecord := none
  deriving Repr

structure TaskReleaseReq where
  id      : Ident
  version : Nat
  deriving Repr

structure TaskReleaseRes where
  status : Nat
  deriving Repr

structure TaskHaltReq where
  id : Ident
  deriving Repr

structure TaskHaltRes where
  status : Nat
  deriving Repr

structure TaskContinueReq where
  id : Ident
  deriving Repr

structure TaskContinueRes where
  status : Nat
  deriving Repr

structure TaskSearchReq where
  state  : Option TaskState := none
  limit  : Option Nat := none
  cursor : Option String := none
  deriving Repr

structure TaskSearchRes where
  status : Nat
  tasks  : List TaskRecord := []
  cursor : Option String := none
  deriving Repr

structure PromiseTimeoutReq where
  id : Ident
  deriving Repr, DecidableEq

structure TaskLeaseTimeoutReq where
  id : Ident
  deriving Repr, DecidableEq

structure TaskRetryTimeoutReq where
  id : Ident
  deriving Repr, DecidableEq

structure ScheduleTimeoutReq where
  schedule : Ident
  deriving Repr, DecidableEq

structure ResumeReq where
  awaited : String
  awaiter : String
  deriving Repr

inductive ResumeOutcome
  | resumed
  | buffered
  | duplicate
  | expired
  | fulfilled
  | absent
  deriving Repr, DecidableEq

structure ResumeRes where
  outcome : ResumeOutcome
  deriving Repr

def PromiseState.settable : PromiseState → Bool
  | .resolved | .rejected | .rejectedCanceled => true
  | _ => false

def TaskFenceAction.targetId : TaskFenceAction → Ident
  | .create r => r.id
  | .settle r => r.id

def parseNat (s : String) : Nat :=
  go s.toList 0
where
  go : List Char → Nat → Nat
    | [], acc => acc
    | c :: cs, acc => go cs (acc * 10 + (c.toNat - '0'.toNat))

inductive Message
  | execute (taskId : Ident) (version : Nat)
  | unblock (promise : PromiseRecord)
  deriving Repr

structure OutboxEntry where
  address : String
  message : Message
  deriving Repr

inductive OutboxKey
  | execute (taskId : Ident)
  | notify  (promise : Ident) (address : String)
  deriving Repr, DecidableEq

instance : BEq OutboxKey := instBEqOfDecidableEq

def OutboxEntry.key : OutboxEntry → OutboxKey
  | { message := .execute taskId _,  .. } => .execute taskId
  | { address, message := .unblock p }    => .notify p.id address

opaque nextCron : (cron : String) → (after : Nat) → Nat

opaque occurrences : (cron : String) → (since now : Nat) → List Nat

opaque expand : (template id : Ident) → (timestamp : Nat) → Ident

deriving instance BEq for Value
deriving instance BEq for PromiseRecord
deriving instance BEq for TaskRecord
deriving instance BEq for Schedule
deriving instance BEq for ResumeReq
deriving instance BEq for Message
deriving instance BEq for OutboxEntry
deriving instance BEq for ResumeRes
deriving instance BEq for PromiseGetRes
deriving instance BEq for PromiseCreateRes
deriving instance BEq for PromiseSettleRes
deriving instance BEq for PromiseRegisterCallbackRes
deriving instance BEq for PromiseRegisterListenerRes
deriving instance BEq for PromiseSearchRes
deriving instance BEq for ScheduleGetRes
deriving instance BEq for ScheduleCreateRes
deriving instance BEq for ScheduleDeleteRes
deriving instance BEq for ScheduleSearchRes
deriving instance BEq for TaskGetRes
deriving instance BEq for TaskCreateRes
deriving instance BEq for TaskAcquireRes
deriving instance BEq for TaskFenceInnerRes
deriving instance BEq for TaskFenceRes
deriving instance BEq for TaskHeartbeatRes
deriving instance BEq for TaskSuspendRes
deriving instance BEq for TaskFulfillRes
deriving instance BEq for TaskReleaseRes
deriving instance BEq for TaskHaltRes
deriving instance BEq for TaskContinueRes
deriving instance BEq for TaskSearchRes

inductive Request
  | promiseGet              (req : PromiseGetReq)
  | promiseCreate           (req : PromiseCreateReq)
  | promiseSettle           (req : PromiseSettleReq)
  | promiseRegisterCallback (req : PromiseRegisterCallbackReq)
  | promiseRegisterListener (req : PromiseRegisterListenerReq)
  | promiseSearch           (req : PromiseSearchReq)
  | scheduleGet             (req : ScheduleGetReq)
  | scheduleCreate          (req : ScheduleCreateReq)
  | scheduleDelete          (req : ScheduleDeleteReq)
  | scheduleSearch          (req : ScheduleSearchReq)
  | taskGet                 (req : TaskGetReq)
  | taskCreate              (req : TaskCreateReq)
  | taskAcquire             (req : TaskAcquireReq)
  | taskFence               (req : TaskFenceReq)
  | taskHeartbeat           (req : TaskHeartbeatReq)
  | taskSuspend             (req : TaskSuspendReq)
  | taskFulfill             (req : TaskFulfillReq)
  | taskRelease             (req : TaskReleaseReq)
  | taskHalt                (req : TaskHaltReq)
  | taskContinue            (req : TaskContinueReq)
  | taskSearch              (req : TaskSearchReq)
  deriving Repr

inductive Response
  | promiseGet              (res : PromiseGetRes)
  | promiseCreate           (res : PromiseCreateRes)
  | promiseSettle           (res : PromiseSettleRes)
  | promiseRegisterCallback (res : PromiseRegisterCallbackRes)
  | promiseRegisterListener (res : PromiseRegisterListenerRes)
  | promiseSearch           (res : PromiseSearchRes)
  | scheduleGet             (res : ScheduleGetRes)
  | scheduleCreate          (res : ScheduleCreateRes)
  | scheduleDelete          (res : ScheduleDeleteRes)
  | scheduleSearch          (res : ScheduleSearchRes)
  | taskGet                 (res : TaskGetRes)
  | taskCreate              (res : TaskCreateRes)
  | taskAcquire             (res : TaskAcquireRes)
  | taskFence               (res : TaskFenceRes)
  | taskHeartbeat           (res : TaskHeartbeatRes)
  | taskSuspend             (res : TaskSuspendRes)
  | taskFulfill             (res : TaskFulfillRes)
  | taskRelease             (res : TaskReleaseRes)
  | taskHalt                (res : TaskHaltRes)
  | taskContinue            (res : TaskContinueRes)
  | taskSearch              (res : TaskSearchRes)
  deriving Repr, BEq

end ServerModel
