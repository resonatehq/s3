module theorems

-- What is checked of the model, as the Lean's `03-theorems`: every run
-- and check, over the modules. Runs are witnesses: the states the
-- catalogue admits, and, for every handler and trigger, every answer it
-- can give, at the scope of the checks, so that no check passes for
-- want of an instance. Checks are the catalogue on a step: from any
-- state satisfying the state properties, every handler and trigger leaves
-- a state satisfying them (`_preserves`) and the step satisfies the
-- transition properties (`_transitions`), the triggers the internal ones
-- too; and the catalogue along bounded valid traces.
--
-- Scopes: 5-bit integers, two instants, four atoms per signature.
-- Schedules are scoped out of the commands that do not touch them, as
-- their oracle relations are large. The machine's arithmetic is on
-- naturals and Alloy's integers wrap: a sum that leaves the range wraps
-- to a negative, which no field admits, so at the edge of the range the
-- step does not exist rather than miscomputes. Do not run with
-- `--nooverflow`: it treats an overflowing comparison as satisfied and
-- invents steps.

open util/boolean
open types
open state
open properties
open external
open internal
open system

-- The data model.

run init for 4 but 5 Int, 1 steps, 0 Schedule

run showWellFormed {
  some now : Int | stateHolds[now] and gapsHold[now] and #State.objects >= 3
} for 5 but 5 Int, 1 steps, 0 Schedule

run showAcquired {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some t : storedTasks | t.state = Acquired and some t.resumes
} for 4 but 5 Int, 1 steps, 0 Schedule

run showSuspendedAwaiting {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some o : State.objects | o.task.state = Suspended and o.promise.state = Pending
} for 4 but 5 Int, 1 steps, 0 Schedule

run showOutbox {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some State.outbox.message & Execute and some State.outbox.message & Unblock
} for 5 but 5 Int, 1 steps, 0 Schedule

run showTimedOut {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some o : State.objects | o.promise.state = RejectedTimedout and some o.task
} for 4 but 5 Int, 1 steps, 0 Schedule

run showSchedules {
  some now : Int | stateHolds[now] and gapsHold[now] and #State.schedules = 2
    and some State.schedules.lastRunAt
} for 4 but 5 Int, 1 steps, 2 Schedule

check lookupsAreFunctional {
  all now : Int | stateHolds[now] implies
    all id : Ident | lone object[id] and lone promise[id] and lone task[id] and lone schedule[id]
} for 5 but 5 Int, 1 steps, 2 Schedule

check leaseAndRetryAreExclusive {
  all now : Int | stateHolds[now] implies
    all t : storedTasks | no t.leaseTimeoutAt or no t.retryTimeoutAt
} for 5 but 5 Int, 1 steps, 0 Schedule

check projectionIsIdentityWhenNotDue {
  all p : PromiseObject, now : Int |
    (p.state != Pending or now < p.timeoutAt) implies projectedState[p, now] = p.state
} for 4 but 5 Int, 1 steps, 0 Schedule

check projectionMatchesVerdict {
  all p, p2 : PromiseObject, now : Int |
    (p.state = Pending and no p.settledAt and projectPromise[p, now, p2]) implies
      (p2.settledAt != p2.timeoutAt
        or p2.state = (p2.type = Deadline implies Resolved else RejectedTimedout))
} for 4 but 5 Int, 1 steps, 0 Schedule

check viewFulfils {
  all t, t2 : TaskObject, p : PromiseObject |
    (p.state != Pending and viewTask[t, p, t2]) implies t2.state = Fulfilled
} for 4 but 5 Int, 1 steps, 0 Schedule

run showProjection {
  some o, o2 : Object, now : Int |
    o.promise.state = Pending and o.promise.timeoutAt <= now and some o.task
    and o.task.state = Acquired and projectObject[o, now, o2]
} for 4 but 5 Int, 1 steps, 0 Schedule

run showAddCallback {
  some p, p2 : PromiseObject, a : Ident | a not in p.callbacks and addCallback[p, a, p2]
} for 4 but 5 Int, 1 steps, 0 Schedule

run showRecords {
  some o : Object, r : PromiseRecord, q : TaskRecord |
    some o.task and some o.task.resumes and
    promiseToRecord[o.promise, o.id, r] and taskToRecord[o.task, o.id, q]
} for 4 but 5 Int, 1 steps, 0 Schedule

-- The handlers: a witness per answer, then the catalogue on the step.

run promiseGet_404 {
  some mat : Bool, now : Int, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now] and promiseGet[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseGet_200 {
  some mat : Bool, now : Int, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now] and promiseGet[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseCreate_200_created {
  some mat : Bool, now : Int, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now] and promiseCreate[mat, now, req, res] and res.status = s200 and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseCreate_200_existing {
  some mat : Bool, now : Int, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now] and promiseCreate[mat, now, req, res] and res.status = s200 and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseSettle_400 {
  some mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and promiseSettle[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseSettle_404 {
  some mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and promiseSettle[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseSettle_200_settled {
  some mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and promiseSettle[mat, now, req, res] and res.status = s200 and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseSettle_200_already {
  some mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and promiseSettle[mat, now, req, res] and res.status = s200 and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterCallback_400 {
  some mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterCallback_404 {
  some mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterCallback_422 {
  some mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] and res.status = s422
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterCallback_200_registered {
  some mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] and res.status = s200 and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterCallback_200_unchanged {
  some mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] and res.status = s200 and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterListener_404 {
  some mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and promiseRegisterListener[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterListener_422 {
  some mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and promiseRegisterListener[mat, now, req, res] and res.status = s422
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterListener_200_registered {
  some mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and promiseRegisterListener[mat, now, req, res] and res.status = s200 and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseRegisterListener_200_unchanged {
  some mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and promiseRegisterListener[mat, now, req, res] and res.status = s200 and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run promiseSearch_501 {
  some mat : Bool, now : Int, req : PromiseSearchReq, res : PromiseSearchRes |
    stateHolds[now] and promiseSearch[mat, now, req, res] and res.status = s501
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run scheduleGet_404 {
  some mat : Bool, now : Int, req : ScheduleGetReq, res : ScheduleGetRes |
    stateHolds[now] and scheduleGet[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleGet_200 {
  some mat : Bool, now : Int, req : ScheduleGetReq, res : ScheduleGetRes |
    stateHolds[now] and scheduleGet[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleCreate_200_created {
  some mat : Bool, now : Int, req : ScheduleCreateReq, res : ScheduleCreateRes |
    stateHolds[now] and scheduleCreate[mat, now, req, res] and res.status = s200 and State.schedules' != State.schedules
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleCreate_200_existing {
  some mat : Bool, now : Int, req : ScheduleCreateReq, res : ScheduleCreateRes |
    stateHolds[now] and scheduleCreate[mat, now, req, res] and res.status = s200 and State.schedules' = State.schedules
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleDelete_404 {
  some mat : Bool, now : Int, req : ScheduleDeleteReq, res : ScheduleDeleteRes |
    stateHolds[now] and scheduleDelete[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleDelete_200 {
  some mat : Bool, now : Int, req : ScheduleDeleteReq, res : ScheduleDeleteRes |
    stateHolds[now] and scheduleDelete[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run scheduleSearch_501 {
  some mat : Bool, now : Int, req : ScheduleSearchReq, res : ScheduleSearchRes |
    stateHolds[now] and scheduleSearch[mat, now, req, res] and res.status = s501
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run taskGet_404 {
  some mat : Bool, now : Int, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now] and taskGet[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskGet_200 {
  some mat : Bool, now : Int, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now] and taskGet[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_400 {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_422 {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s422
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_409 {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_200_created {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s200 and no object[req.action.id]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_200_acquired {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s200 and some object[req.action.id] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskCreate_200_fulfilled {
  some mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] and res.status = s200 and some object[req.action.id] and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskAcquire_404 {
  some mat : Bool, now : Int, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now] and taskAcquire[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskAcquire_409 {
  some mat : Bool, now : Int, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now] and taskAcquire[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskAcquire_200 {
  some mat : Bool, now : Int, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now] and taskAcquire[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFence_400 {
  some mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFence_404 {
  some mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFence_409 {
  some mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFence_200_create {
  some mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] and res.status = s200 and res.action in FenceCreateRes and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFence_200_settle {
  some mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] and res.status = s200 and res.action in FenceSettleRes and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskHeartbeat_200_extended {
  some mat : Bool, now : Int, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now] and taskHeartbeat[mat, now, req, res] and res.status = s200 and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskHeartbeat_200_unchanged {
  some mat : Bool, now : Int, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now] and taskHeartbeat[mat, now, req, res] and res.status = s200 and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_400 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_404 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_409 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_422 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s422
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_300 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s300
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSuspend_200 {
  some mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFulfill_400 {
  some mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and taskFulfill[mat, now, req, res] and res.status = s400
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFulfill_404 {
  some mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and taskFulfill[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFulfill_409 {
  some mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and taskFulfill[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskFulfill_200 {
  some mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and taskFulfill[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskRelease_404 {
  some mat : Bool, now : Int, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now] and taskRelease[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskRelease_409 {
  some mat : Bool, now : Int, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now] and taskRelease[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskRelease_200 {
  some mat : Bool, now : Int, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now] and taskRelease[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskHalt_404 {
  some mat : Bool, now : Int, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now] and taskHalt[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskHalt_409 {
  some mat : Bool, now : Int, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now] and taskHalt[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskHalt_200 {
  some mat : Bool, now : Int, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now] and taskHalt[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskContinue_404 {
  some mat : Bool, now : Int, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now] and taskContinue[mat, now, req, res] and res.status = s404
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskContinue_409 {
  some mat : Bool, now : Int, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now] and taskContinue[mat, now, req, res] and res.status = s409
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskContinue_200 {
  some mat : Bool, now : Int, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now] and taskContinue[mat, now, req, res] and res.status = s200
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run taskSearch_501 {
  some mat : Bool, now : Int, req : TaskSearchReq, res : TaskSearchRes |
    stateHolds[now] and taskSearch[mat, now, req, res] and res.status = s501
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseGet_preserves {
  all mat : Bool, now : Int, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now] and promiseGet[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseGet_transitions {
  all mat : Bool, now : Int, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseGet[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseCreate_preserves {
  all mat : Bool, now : Int, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now] and promiseCreate[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseCreate_transitions {
  all mat : Bool, now : Int, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseCreate[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseSettle_preserves {
  all mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and promiseSettle[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseSettle_transitions {
  all mat : Bool, now : Int, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseSettle[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseRegisterCallback_preserves {
  all mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and promiseRegisterCallback[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseRegisterCallback_transitions {
  all mat : Bool, now : Int, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseRegisterCallback[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseRegisterListener_preserves {
  all mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and promiseRegisterListener[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseRegisterListener_transitions {
  all mat : Bool, now : Int, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseRegisterListener[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseSearch_preserves {
  all mat : Bool, now : Int, req : PromiseSearchReq, res : PromiseSearchRes |
    stateHolds[now] and promiseSearch[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check promiseSearch_transitions {
  all mat : Bool, now : Int, req : PromiseSearchReq, res : PromiseSearchRes |
    stateHolds[now] and well_formed_config_retry_positive and promiseSearch[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check scheduleGet_preserves {
  all mat : Bool, now : Int, req : ScheduleGetReq, res : ScheduleGetRes |
    stateHolds[now] and scheduleGet[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleGet_transitions {
  all mat : Bool, now : Int, req : ScheduleGetReq, res : ScheduleGetRes |
    stateHolds[now] and well_formed_config_retry_positive and scheduleGet[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleCreate_preserves {
  all mat : Bool, now : Int, req : ScheduleCreateReq, res : ScheduleCreateRes |
    stateHolds[now] and scheduleCreate[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleCreate_transitions {
  all mat : Bool, now : Int, req : ScheduleCreateReq, res : ScheduleCreateRes |
    stateHolds[now] and well_formed_config_retry_positive and scheduleCreate[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleDelete_preserves {
  all mat : Bool, now : Int, req : ScheduleDeleteReq, res : ScheduleDeleteRes |
    stateHolds[now] and scheduleDelete[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleDelete_transitions {
  all mat : Bool, now : Int, req : ScheduleDeleteReq, res : ScheduleDeleteRes |
    stateHolds[now] and well_formed_config_retry_positive and scheduleDelete[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleSearch_preserves {
  all mat : Bool, now : Int, req : ScheduleSearchReq, res : ScheduleSearchRes |
    stateHolds[now] and scheduleSearch[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check scheduleSearch_transitions {
  all mat : Bool, now : Int, req : ScheduleSearchReq, res : ScheduleSearchRes |
    stateHolds[now] and well_formed_config_retry_positive and scheduleSearch[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check taskGet_preserves {
  all mat : Bool, now : Int, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now] and taskGet[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskGet_transitions {
  all mat : Bool, now : Int, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now] and well_formed_config_retry_positive and taskGet[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskCreate_preserves {
  all mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and taskCreate[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskCreate_transitions {
  all mat : Bool, now : Int, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now] and well_formed_config_retry_positive and taskCreate[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskAcquire_preserves {
  all mat : Bool, now : Int, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now] and taskAcquire[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskAcquire_transitions {
  all mat : Bool, now : Int, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now] and well_formed_config_retry_positive and taskAcquire[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskFence_preserves {
  all mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and taskFence[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskFence_transitions {
  all mat : Bool, now : Int, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now] and well_formed_config_retry_positive and taskFence[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskHeartbeat_preserves {
  all mat : Bool, now : Int, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now] and taskHeartbeat[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskHeartbeat_transitions {
  all mat : Bool, now : Int, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now] and well_formed_config_retry_positive and taskHeartbeat[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskSuspend_preserves {
  all mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and taskSuspend[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskSuspend_transitions {
  all mat : Bool, now : Int, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now] and well_formed_config_retry_positive and taskSuspend[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskFulfill_preserves {
  all mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and taskFulfill[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskFulfill_transitions {
  all mat : Bool, now : Int, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now] and well_formed_config_retry_positive and taskFulfill[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskRelease_preserves {
  all mat : Bool, now : Int, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now] and taskRelease[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskRelease_transitions {
  all mat : Bool, now : Int, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now] and well_formed_config_retry_positive and taskRelease[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskHalt_preserves {
  all mat : Bool, now : Int, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now] and taskHalt[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskHalt_transitions {
  all mat : Bool, now : Int, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now] and well_formed_config_retry_positive and taskHalt[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskContinue_preserves {
  all mat : Bool, now : Int, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now] and taskContinue[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskContinue_transitions {
  all mat : Bool, now : Int, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now] and well_formed_config_retry_positive and taskContinue[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskSearch_preserves {
  all mat : Bool, now : Int, req : TaskSearchReq, res : TaskSearchRes |
    stateHolds[now] and taskSearch[mat, now, req, res] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check taskSearch_transitions {
  all mat : Bool, now : Int, req : TaskSearchReq, res : TaskSearchRes |
    stateHolds[now] and well_formed_config_retry_positive and taskSearch[mat, now, req, res]
      implies transHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

-- The triggers: a witness per outcome, then the catalogue on the step,
-- the internal edges included.

run processPromiseTimeout_settled {
  some now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and processPromiseTimeout[now, req] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processPromiseTimeout_skipped {
  some now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and processPromiseTimeout[now, req] and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processCallback_resumed {
  some now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] and some storedTasks & state.Suspended and after no storedTasks & state.Suspended
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processCallback_told {
  some now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] and State.objects' != State.objects and no storedTasks & state.Suspended
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processCallback_skipped {
  some now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processListener_told {
  some now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and processListener[now, req] and State.outbox' != State.outbox
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processListener_skipped {
  some now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and processListener[now, req] and State.objects' = State.objects and State.outbox' = State.outbox
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processLeaseTimeout_released {
  some now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and processLeaseTimeout[now, req] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processLeaseTimeout_skipped {
  some now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and processLeaseTimeout[now, req] and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processRetryTimeout_dispatched {
  some now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and processRetryTimeout[now, req] and State.outbox' != State.outbox
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processRetryTimeout_skipped {
  some now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and processRetryTimeout[now, req] and State.objects' = State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

run processSchedule_fired {
  some mat : Bool, now : Int, req : ScheduleTimeoutReq |
    stateHolds[now] and processSchedule[mat, now, req] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

run processSchedule_skipped {
  some mat : Bool, now : Int, req : ScheduleTimeoutReq |
    stateHolds[now] and processSchedule[mat, now, req] and State.objects' = State.objects and State.schedules' = State.schedules
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check processPromiseTimeout_preserves {
  all now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and processPromiseTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processPromiseTimeout_transitions {
  all now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and well_formed_config_retry_positive and processPromiseTimeout[now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processCallback_preserves {
  all now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processCallback_transitions {
  all now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and well_formed_config_retry_positive and processCallback[now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processListener_preserves {
  all now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and processListener[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processListener_transitions {
  all now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and well_formed_config_retry_positive and processListener[now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processLeaseTimeout_preserves {
  all now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and processLeaseTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processLeaseTimeout_transitions {
  all now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and well_formed_config_retry_positive and processLeaseTimeout[now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processRetryTimeout_preserves {
  all now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and processRetryTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processRetryTimeout_transitions {
  all now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and well_formed_config_retry_positive and processRetryTimeout[now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 0 Schedule

check processSchedule_preserves {
  all mat : Bool, now : Int, req : ScheduleTimeoutReq |
    stateHolds[now] and processSchedule[mat, now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

check processSchedule_transitions {
  all mat : Bool, now : Int, req : ScheduleTimeoutReq |
    stateHolds[now] and well_formed_config_retry_positive and processSchedule[mat, now, req]
      implies (transHolds[now] and internalWellFormed[now])
} for 4 but 5 Int, 2 seq, 2 steps, 2 Schedule

-- The machine along traces. Runs are pinned to their scenario: an
-- unconstrained `eventually` at this size does not finish.

run lifecycle {
  valid
  Machine.request in TaskCreateReq
  after Machine.request in TaskFulfillReq
  after after some storedTasks & state.Fulfilled
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable, 0 Schedule

run dispatch {
  valid
  Machine.request in PromiseCreateReq
  after Machine.trigger in TaskRetryTimeout
  after after some State.outbox.message & Execute
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable, 0 Schedule

run unblock {
  valid
  Machine.request in PromiseCreateReq
  after Machine.request in PromiseRegisterListenerReq
  after after Machine.trigger in Listener
  after after after some State.outbox.message & Unblock
} for 4 but 5 Int, 2 seq, 4 steps, 3 Request, 3 Response, 0 Schedule

run scheduled {
  valid
  Machine.request in ScheduleCreateReq
  after Machine.trigger in ScheduleTimeout
  after after some State.objects
} for 3 but 5 Int, 2 seq, 3 steps, 3 Request, 3 Response, 2 Schedule

-- Every valid trace satisfies the catalogue at every instant, and every
-- step of it the transition properties.
check catalogueAlongTraces {
  valid implies always (stateHolds[Machine.now] and transHolds[Machine.now])
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable, 0 Schedule
