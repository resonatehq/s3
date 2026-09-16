module types

-- The protocol layer's object model, as Alloy signatures. One signature per
-- Lean structure of `src/types.lean`, one field per field. Sums become an
-- abstract signature with one subsignature per constructor. `Option α` is a
-- `lone` field, `Nat` an `Int` restricted to be non-negative, `String` an
-- atom of `Str`.
--
-- Lean structures are values: two are equal when their fields are. Every
-- signature below is given the same value semantics by a fact that
-- identifies atoms with equal fields.
--
-- Lists. The catalogue proves the object model's lists duplicate free
-- (`callbacks`, `listeners`, `resumes`), and their order is unobservable, so
-- they are sets here. A header list is a relation from key to value. A
-- list in a request is a `seq`: the handlers walk it in order.

-- Strings

sig Str {}

one sig EmptyStr extends Str {}

-- Ident

sig Ident {
  origin : one Str,
  suffix : one Str
}

fact IdentValue { no disj a, b : Ident | a.origin = b.origin and a.suffix = b.suffix }

pred sameOrigin [a, b : Ident] { a.origin = b.origin }

-- Value

sig Value {
  headers : Str -> Str,
  data    : lone Str
}

fact ValueValue { no disj a, b : Value | a.headers = b.headers and a.data = b.data }

pred emptyValue [v : Value] { no v.headers and no v.data }

-- PromiseState, TaskState

enum PromiseState { Pending, Resolved, Rejected, RejectedCanceled, RejectedTimedout }

enum TaskState { TaskPending, Acquired, Suspended, Halted, Fulfilled }

fun settable : set PromiseState { Resolved + Rejected + RejectedCanceled }

-- OType

abstract sig OType {}

one sig Internal, Deadline, External extends OType {}

sig Runnable extends OType {
  target : one Str
}

fact RunnableValue { no disj a, b : Runnable | a.target = b.target }

fun awaitable : set OType { OType - Internal }

fun isRunnable : set OType { Runnable }

-- `OType.target?`: the target of a runnable type, none otherwise.
fun targetOf [t : OType] : lone Str { t.target }

-- PromiseObject

sig PromiseObject {
  state     : one PromiseState,
  param     : one Value,
  value     : one Value,
  type      : one OType,
  timeoutAt : one Int,
  createdAt : one Int,
  settledAt : lone Int,
  callbacks : set Ident,
  listeners : set Str
} {
  timeoutAt >= 0 and createdAt >= 0 and all x : settledAt | x >= 0
}

fact PromiseObjectValue {
  no disj a, b : PromiseObject |
    a.state = b.state and a.param = b.param and a.value = b.value and
    a.type = b.type and a.timeoutAt = b.timeoutAt and a.createdAt = b.createdAt and
    a.settledAt = b.settledAt and a.callbacks = b.callbacks and a.listeners = b.listeners
}

-- `p2` is `p` with `awaiterId` appended to its callbacks, or `p` itself
-- when already present.
pred addCallback [p : PromiseObject, awaiterId : Ident, p2 : PromiseObject] {
  awaiterId in p.callbacks
    implies p2 = p
    else sameBirth[p, p2] and sameSettlement[p, p2] and
         p2.listeners = p.listeners and p2.callbacks = p.callbacks + awaiterId
}

pred addListener [p : PromiseObject, address : Str, p2 : PromiseObject] {
  address in p.listeners
    implies p2 = p
    else sameBirth[p, p2] and sameSettlement[p, p2] and
         p2.callbacks = p.callbacks and p2.listeners = p.listeners + address
}

-- The state `p` shows at instant `now`: a pending promise past its timeout
-- is resolved when its type is `deadline`, timed out otherwise.
fun projectedState [p : PromiseObject, now : Int] : one PromiseState {
  (p.state = Pending and p.timeoutAt <= now)
    implies (p.type = Deadline implies Resolved else RejectedTimedout)
    else p.state
}

-- `p2` is `p` projected to instant `now`.
pred projectPromise [p : PromiseObject, now : Int, p2 : PromiseObject] {
  (p.state = Pending and p.timeoutAt <= now)
    implies (sameBirth[p, p2] and sameObligations[p, p2] and p2.value = p.value and
             p2.state = projectedState[p, now] and p2.settledAt = p.timeoutAt)
    else p2 = p
}

-- The field groups of a promise: what it was born with, how it settled,
-- what it owes.
pred sameBirth [p, p2 : PromiseObject] {
  p2.param = p.param and p2.type = p.type and
  p2.timeoutAt = p.timeoutAt and p2.createdAt = p.createdAt
}

pred sameSettlement [p, p2 : PromiseObject] {
  p2.state = p.state and p2.value = p.value and p2.settledAt = p.settledAt
}

pred sameObligations [p, p2 : PromiseObject] {
  p2.callbacks = p.callbacks and p2.listeners = p.listeners
}

-- TaskObject

sig TaskObject {
  state          : one TaskState,
  version        : one Int,
  ttl            : lone Int,
  pid            : lone Str,
  leaseTimeoutAt : lone Int,
  retryTimeoutAt : lone Int,
  resumes        : set Ident
} {
  version >= 0 and
  all x : ttl + leaseTimeoutAt + retryTimeoutAt | x >= 0
}

fact TaskObjectValue {
  no disj a, b : TaskObject |
    a.state = b.state and a.version = b.version and a.ttl = b.ttl and a.pid = b.pid and
    a.leaseTimeoutAt = b.leaseTimeoutAt and a.retryTimeoutAt = b.retryTimeoutAt and
    a.resumes = b.resumes
}

-- `t2` is `t` fulfilled: the state set, the lease, the timers and the
-- resumes cleared, the version kept.
pred fulfillTask [t, t2 : TaskObject] {
  t2.state = Fulfilled and t2.version = t.version and
  no t2.pid and no t2.ttl and no t2.leaseTimeoutAt and no t2.retryTimeoutAt and
  no t2.resumes
}

-- `t2` is how `t` shows next to promise `p`: fulfilled once the promise is
-- settled, itself otherwise.
pred viewTask [t : TaskObject, p : PromiseObject, t2 : TaskObject] {
  (p.state != Pending and t.state != Fulfilled)
    implies fulfillTask[t, t2]
    else t2 = t
}

-- Object

sig Object {
  id      : one Ident,
  promise : one PromiseObject,
  task    : lone TaskObject
}

fact ObjectValue {
  no disj a, b : Object | a.id = b.id and a.promise = b.promise and a.task = b.task
}

-- `o2` is `o` projected to instant `now`: its promise projected, its task
-- viewed next to the projected promise.
pred projectObject [o : Object, now : Int, o2 : Object] {
  o2.id = o.id
  projectPromise[o.promise, now, o2.promise]
  no o.task implies no o2.task else viewTask[o.task, o2.promise, o2.task]
}

-- Records: what an object shows the protocol.

sig PromiseRecord {
  id        : one Ident,
  state     : one PromiseState,
  param     : one Value,
  value     : one Value,
  type      : one OType,
  timeoutAt : one Int,
  createdAt : one Int,
  settledAt : lone Int
} {
  timeoutAt >= 0 and createdAt >= 0 and all x : settledAt | x >= 0
}

fact PromiseRecordValue {
  no disj a, b : PromiseRecord |
    a.id = b.id and a.state = b.state and a.param = b.param and a.value = b.value and
    a.type = b.type and a.timeoutAt = b.timeoutAt and a.createdAt = b.createdAt and
    a.settledAt = b.settledAt
}

-- `r` is the record of promise `p` under `id`: the promise without its
-- callbacks and listeners.
pred promiseToRecord [p : PromiseObject, i : Ident, r : PromiseRecord] {
  r.id = i and r.state = p.state and r.param = p.param and r.value = p.value and
  r.type = p.type and r.timeoutAt = p.timeoutAt and r.createdAt = p.createdAt and
  r.settledAt = p.settledAt
}

sig TaskRecord {
  id      : one Ident,
  state   : one TaskState,
  version : one Int,
  resumes : one Int,
  ttl     : lone Int,
  pid     : lone Str
} {
  version >= 0 and resumes >= 0 and all x : ttl | x >= 0
}

fact TaskRecordValue {
  no disj a, b : TaskRecord |
    a.id = b.id and a.state = b.state and a.version = b.version and
    a.resumes = b.resumes and a.ttl = b.ttl and a.pid = b.pid
}

-- `r` is the record of task `t` under `id`: the task without its timers,
-- its resumes counted.
pred taskToRecord [t : TaskObject, i : Ident, r : TaskRecord] {
  r.id = i and r.state = t.state and r.version = t.version and
  r.resumes = #t.resumes and r.ttl = t.ttl and r.pid = t.pid
}

-- Messages and the outbox

abstract sig Message {}

sig Execute extends Message {
  taskId  : one Ident,
  version : one Int
} { version >= 0 }

sig Unblock extends Message {
  promise : one PromiseRecord
}

fact MessageValue {
  no disj a, b : Execute | a.taskId = b.taskId and a.version = b.version
  no disj a, b : Unblock | a.promise = b.promise
}

sig OutboxEntry {
  address : one Str,
  message : one Message
}

fact OutboxEntryValue {
  no disj a, b : OutboxEntry | a.address = b.address and a.message = b.message
}

-- `OutboxKey`: an execute is keyed by its task, an unblock by its promise
-- and the address. The key is a projection of the entry, so it is a
-- predicate on entries rather than a signature of its own.
pred sameKey [a, b : OutboxEntry] {
  (a.message in Execute and b.message in Execute and
     a.message.taskId = b.message.taskId)
  or
  (a.message in Unblock and b.message in Unblock and
     a.message.promise.id = b.message.promise.id and a.address = b.address)
}

-- Requests and responses. `Request` and `Response` are the sums; each
-- constructor's payload is the subsignature. A status is one of the codes
-- the handlers answer. The schedule requests are left out with the
-- schedules. The trigger requests, `PromiseTimeoutReq`, `TaskLeaseTimeoutReq`
-- and `TaskRetryTimeoutReq`, come last; the callback and listener triggers
-- carry the register requests.

enum Status { s200, s300, s400, s404, s409, s422, s501 }

abstract sig Request {}

abstract sig Response {
  status : one Status
}

sig PromiseGetReq extends Request {
  id : one Ident
}

sig PromiseGetRes extends Response {
  promise : lone PromiseRecord
}

sig PromiseCreateReq extends Request {
  id        : one Ident,
  timeoutAt : one Int,
  param     : one Value,
  type      : one OType,
  delay     : lone Int
} { timeoutAt >= 0 and all x : delay | x >= 0 }

sig PromiseCreateRes extends Response {
  promise : lone PromiseRecord
}

sig PromiseSettleReq extends Request {
  id    : one Ident,
  state : one PromiseState,
  value : one Value
}

sig PromiseSettleRes extends Response {
  promise : lone PromiseRecord
}

sig PromiseRegisterCallbackReq extends Request {
  awaited : one Ident,
  awaiter : one Ident
}

sig PromiseRegisterCallbackRes extends Response {
  promise : lone PromiseRecord
}

sig PromiseRegisterListenerReq extends Request {
  awaited : one Ident,
  address : one Str
}

sig PromiseRegisterListenerRes extends Response {
  promise : lone PromiseRecord
}

sig PromiseSearchReq extends Request {
  state  : lone PromiseState,
  limit  : lone Int,
  cursor : lone Str
} { all x : limit | x >= 0 }

sig PromiseSearchRes extends Response {
  promises : set PromiseRecord,
  cursor   : lone Str
}

sig TaskGetReq extends Request {
  id : one Ident
}

sig TaskGetRes extends Response {
  task : lone TaskRecord
}

sig TaskCreateReq extends Request {
  pid    : one Str,
  ttl    : one Int,
  action : one PromiseCreateReq
} { ttl >= 0 }

sig TaskCreateRes extends Response {
  task    : lone TaskRecord,
  promise : lone PromiseRecord,
  preload : set PromiseRecord
}

sig TaskAcquireReq extends Request {
  id      : one Ident,
  version : one Int,
  pid     : one Str,
  ttl     : one Int
} { version >= 0 and ttl >= 0 }

sig TaskAcquireRes extends Response {
  task    : lone TaskRecord,
  promise : lone PromiseRecord,
  preload : set PromiseRecord
}

abstract sig TaskFenceAction {}

sig FenceCreate extends TaskFenceAction {
  create : one PromiseCreateReq
}

sig FenceSettle extends TaskFenceAction {
  settle : one PromiseSettleReq
}

-- `TaskFenceAction.targetId`
fun targetId [a : TaskFenceAction] : one Ident { a.create.id + a.settle.id }

abstract sig TaskFenceInnerRes {}

sig FenceCreateRes extends TaskFenceInnerRes {
  create : one PromiseCreateRes
}

sig FenceSettleRes extends TaskFenceInnerRes {
  settle : one PromiseSettleRes
}

sig TaskFenceReq extends Request {
  id      : one Ident,
  version : one Int,
  action  : one TaskFenceAction
} { version >= 0 }

sig TaskFenceRes extends Response {
  action  : lone TaskFenceInnerRes,
  preload : set PromiseRecord
}

sig TaskRef {
  id      : one Ident,
  version : one Int
} { version >= 0 }

sig TaskHeartbeatReq extends Request {
  pid   : one Str,
  tasks : seq TaskRef
}

sig TaskHeartbeatRes extends Response {}

sig TaskSuspendReq extends Request {
  id      : one Ident,
  version : one Int,
  actions : seq PromiseRegisterCallbackReq
} { version >= 0 }

sig TaskSuspendRes extends Response {
  preload : set PromiseRecord
}

sig TaskFulfillReq extends Request {
  id      : one Ident,
  version : one Int,
  action  : one PromiseSettleReq
} { version >= 0 }

sig TaskFulfillRes extends Response {
  promise : lone PromiseRecord
}

sig TaskReleaseReq extends Request {
  id      : one Ident,
  version : one Int
} { version >= 0 }

sig TaskReleaseRes extends Response {}

sig TaskHaltReq extends Request {
  id : one Ident
}

sig TaskHaltRes extends Response {}

sig TaskContinueReq extends Request {
  id : one Ident
}

sig TaskContinueRes extends Response {}

sig TaskSearchReq extends Request {
  state  : lone TaskState,
  limit  : lone Int,
  cursor : lone Str
} { all x : limit | x >= 0 }

sig TaskSearchRes extends Response {
  tasks  : set TaskRecord,
  cursor : lone Str
}

fact RequestValue {
  no disj a, b : PromiseGetReq | a.id = b.id
  no disj a, b : PromiseCreateReq |
    a.id = b.id and a.timeoutAt = b.timeoutAt and a.param = b.param and
    a.type = b.type and a.delay = b.delay
  no disj a, b : PromiseSettleReq | a.id = b.id and a.state = b.state and a.value = b.value
  no disj a, b : PromiseRegisterCallbackReq | a.awaited = b.awaited and a.awaiter = b.awaiter
  no disj a, b : PromiseRegisterListenerReq | a.awaited = b.awaited and a.address = b.address
  no disj a, b : PromiseSearchReq | a.state = b.state and a.limit = b.limit and a.cursor = b.cursor
  no disj a, b : TaskGetReq | a.id = b.id
  no disj a, b : TaskCreateReq | a.pid = b.pid and a.ttl = b.ttl and a.action = b.action
  no disj a, b : TaskAcquireReq |
    a.id = b.id and a.version = b.version and a.pid = b.pid and a.ttl = b.ttl
  no disj a, b : FenceCreate | a.create = b.create
  no disj a, b : FenceSettle | a.settle = b.settle
  no disj a, b : TaskFenceReq | a.id = b.id and a.version = b.version and a.action = b.action
  no disj a, b : TaskRef | a.id = b.id and a.version = b.version
  no disj a, b : TaskHeartbeatReq | a.pid = b.pid and a.tasks = b.tasks
  no disj a, b : TaskSuspendReq | a.id = b.id and a.version = b.version and a.actions = b.actions
  no disj a, b : TaskFulfillReq | a.id = b.id and a.version = b.version and a.action = b.action
  no disj a, b : TaskReleaseReq | a.id = b.id and a.version = b.version
  no disj a, b : TaskHaltReq | a.id = b.id
  no disj a, b : TaskContinueReq | a.id = b.id
  no disj a, b : TaskSearchReq | a.state = b.state and a.limit = b.limit and a.cursor = b.cursor
}

fact ResponseValue {
  no disj a, b : PromiseGetRes | a.status = b.status and a.promise = b.promise
  no disj a, b : PromiseCreateRes | a.status = b.status and a.promise = b.promise
  no disj a, b : PromiseSettleRes | a.status = b.status and a.promise = b.promise
  no disj a, b : PromiseRegisterCallbackRes | a.status = b.status and a.promise = b.promise
  no disj a, b : PromiseRegisterListenerRes | a.status = b.status and a.promise = b.promise
  no disj a, b : PromiseSearchRes |
    a.status = b.status and a.promises = b.promises and a.cursor = b.cursor
  no disj a, b : TaskGetRes | a.status = b.status and a.task = b.task
  no disj a, b : TaskCreateRes |
    a.status = b.status and a.task = b.task and a.promise = b.promise and a.preload = b.preload
  no disj a, b : TaskAcquireRes |
    a.status = b.status and a.task = b.task and a.promise = b.promise and a.preload = b.preload
  no disj a, b : FenceCreateRes | a.create = b.create
  no disj a, b : FenceSettleRes | a.settle = b.settle
  no disj a, b : TaskFenceRes | a.status = b.status and a.action = b.action and a.preload = b.preload
  no disj a, b : TaskHeartbeatRes | a.status = b.status
  no disj a, b : TaskSuspendRes | a.status = b.status and a.preload = b.preload
  no disj a, b : TaskFulfillRes | a.status = b.status and a.promise = b.promise
  no disj a, b : TaskReleaseRes | a.status = b.status
  no disj a, b : TaskHaltRes | a.status = b.status
  no disj a, b : TaskContinueRes | a.status = b.status
  no disj a, b : TaskSearchRes | a.status = b.status and a.tasks = b.tasks and a.cursor = b.cursor
}

sig PromiseTimeoutReq {
  id : one Ident
}

sig TaskLeaseTimeoutReq {
  id : one Ident
}

sig TaskRetryTimeoutReq {
  id : one Ident
}

fact TriggerRequestValue {
  no disj a, b : PromiseTimeoutReq | a.id = b.id
  no disj a, b : TaskLeaseTimeoutReq | a.id = b.id
  no disj a, b : TaskRetryTimeoutReq | a.id = b.id
}
