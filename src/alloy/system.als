module system

-- The machine, as in `src/spec/02-abstract/system.lean`. `Machine` is
-- the trace: `mat` fixed for the run, and at every instant `now`, the
-- event and the reply. An event is a request, `Event.external`, a
-- trigger, `Event.internal`, or neither, `Event.stutter`. A reply is the
-- response to a request, `Reply.external`, and none otherwise. `step` is
-- the Lean `step` from one instant to the next, `valid` the Lean `Valid`:
-- the trace starts at `init` and every instant is a step with the clock
-- not going back.

open util/boolean
open types
open state
open external
open internal
open properties

-- `Trigger`: the schedule timeout is left out with the schedules.
abstract sig Trigger {}

sig PromiseTimeout extends Trigger { req : one PromiseTimeoutReq }
sig Callback extends Trigger { req : one PromiseRegisterCallbackReq }
sig Listener extends Trigger { req : one PromiseRegisterListenerReq }
sig TaskLeaseTimeout extends Trigger { req : one TaskLeaseTimeoutReq }
sig TaskRetryTimeout extends Trigger { req : one TaskRetryTimeoutReq }

fact TriggerValue {
  no disj a, b : PromiseTimeout | a.req = b.req
  no disj a, b : Callback | a.req = b.req
  no disj a, b : Listener | a.req = b.req
  no disj a, b : TaskLeaseTimeout | a.req = b.req
  no disj a, b : TaskRetryTimeout | a.req = b.req
}

one sig Machine {
  mat          : one Bool,
  var now      : one Int,
  var request  : lone Request,
  var trigger  : lone Trigger,
  var response : lone Response
}

fact { always (Machine.now >= 0 and (no Machine.request or no Machine.trigger)) }

pred handleExternal [mat : Bool, now : Int, req : Request, res : Response] {
  req in PromiseGetReq implies
    (res in PromiseGetRes and promiseGet[mat, now, req, res])
  req in PromiseCreateReq implies
    (res in PromiseCreateRes and promiseCreate[mat, now, req, res])
  req in PromiseSettleReq implies
    (res in PromiseSettleRes and promiseSettle[mat, now, req, res])
  req in PromiseRegisterCallbackReq implies
    (res in PromiseRegisterCallbackRes and promiseRegisterCallback[mat, now, req, res])
  req in PromiseRegisterListenerReq implies
    (res in PromiseRegisterListenerRes and promiseRegisterListener[mat, now, req, res])
  req in PromiseSearchReq implies
    (res in PromiseSearchRes and promiseSearch[mat, now, req, res])
  req in TaskGetReq implies
    (res in TaskGetRes and taskGet[mat, now, req, res])
  req in TaskCreateReq implies
    (res in TaskCreateRes and taskCreate[mat, now, req, res])
  req in TaskAcquireReq implies
    (res in TaskAcquireRes and taskAcquire[mat, now, req, res])
  req in TaskFenceReq implies
    (res in TaskFenceRes and taskFence[mat, now, req, res])
  req in TaskHeartbeatReq implies
    (res in TaskHeartbeatRes and taskHeartbeat[mat, now, req, res])
  req in TaskSuspendReq implies
    (res in TaskSuspendRes and taskSuspend[mat, now, req, res])
  req in TaskFulfillReq implies
    (res in TaskFulfillRes and taskFulfill[mat, now, req, res])
  req in TaskReleaseReq implies
    (res in TaskReleaseRes and taskRelease[mat, now, req, res])
  req in TaskHaltReq implies
    (res in TaskHaltRes and taskHalt[mat, now, req, res])
  req in TaskContinueReq implies
    (res in TaskContinueRes and taskContinue[mat, now, req, res])
  req in TaskSearchReq implies
    (res in TaskSearchRes and taskSearch[mat, now, req, res])
}

pred handleInternal [now : Int, trg : Trigger] {
  trg in PromiseTimeout implies processPromiseTimeout[now, trg.req]
  trg in Callback implies processCallback[now, trg.req]
  trg in Listener implies processListener[now, trg.req]
  trg in TaskLeaseTimeout implies processLeaseTimeout[now, trg.req]
  trg in TaskRetryTimeout implies processRetryTimeout[now, trg.req]
}

-- `step`: an external event is handled and answered, an internal one is
-- handled, a stutter keeps the state.
pred step {
  some Machine.request implies
    (some Machine.response and
     handleExternal[Machine.mat, Machine.now, Machine.request, Machine.response])
  else some Machine.trigger implies
    (no Machine.response and handleInternal[Machine.now, Machine.trigger])
  else
    (no Machine.response and keep)
}

-- `Valid`
pred valid {
  init
  always (step and Machine.now <= Machine.now')
}

-- A trace that creates a task, acquired, and fulfils it.
run lifecycle {
  valid
  eventually some storedTasks & state.Acquired
  eventually some storedTasks & state.Fulfilled
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable

-- A trace that creates a runnable promise, whose task's retry then
-- dispatches `execute` to its target.
run dispatch {
  valid
  eventually some State.outbox.message & Execute
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable

-- A trace in which a settled promise's listener is told.
run unblock {
  valid
  eventually some State.outbox.message & Unblock
} for 3 but 5 Int, 2 seq, 4 steps, 6 Request, 6 Response, 2 Runnable

-- Every valid trace satisfies the catalogue at every instant.
check catalogueAlongTraces {
  valid implies always stateHolds[Machine.now]
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable
