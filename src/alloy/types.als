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
-- they are sets here. A header list is a relation from key to value.

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
    else samePromiseButCallbacks[p, p2] and p2.callbacks = p.callbacks + awaiterId
}

pred addListener [p : PromiseObject, address : Str, p2 : PromiseObject] {
  address in p.listeners
    implies p2 = p
    else samePromiseButListeners[p, p2] and p2.listeners = p.listeners + address
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
    implies (samePromiseButSettlement[p, p2] and
             p2.state = projectedState[p, now] and p2.settledAt = p.timeoutAt)
    else p2 = p
}

pred samePromiseButCallbacks [p, p2 : PromiseObject] {
  p2.state = p.state and p2.param = p.param and p2.value = p.value and
  p2.type = p.type and p2.timeoutAt = p.timeoutAt and p2.createdAt = p.createdAt and
  p2.settledAt = p.settledAt and p2.listeners = p.listeners
}

pred samePromiseButListeners [p, p2 : PromiseObject] {
  p2.state = p.state and p2.param = p.param and p2.value = p.value and
  p2.type = p.type and p2.timeoutAt = p.timeoutAt and p2.createdAt = p.createdAt and
  p2.settledAt = p.settledAt and p2.callbacks = p.callbacks
}

pred samePromiseButSettlement [p, p2 : PromiseObject] {
  p2.param = p.param and p2.value = p.value and p2.type = p.type and
  p2.timeoutAt = p.timeoutAt and p2.createdAt = p.createdAt and
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
