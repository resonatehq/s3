module system

-- The machine, as in `src/spec/02-abstract/system.lean`. `Machine` is
-- the trace: `mat` fixed for the run, and at every instant `now`, the
-- event and the reply. An event is a request, `Event.external`, or none,
-- `Event.stutter`; the triggers, `Event.internal`, come with the
-- triggers. A reply is the response to a request and none otherwise.
-- `step` is the Lean `step` from one instant to the next, `valid` the
-- Lean `Valid`: the trace starts at `init` and every instant is a step
-- with the clock not going back.

open util/boolean
open types
open state
open external
open properties

one sig Machine {
  mat          : one Bool,
  var now      : one Int,
  var request  : lone Request,
  var response : lone Response
}

fact { always Machine.now >= 0 }

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

-- `step`: an external event is handled, a stutter keeps the state.
pred step {
  some Machine.request implies
    (some Machine.response and
     handleExternal[Machine.mat, Machine.now, Machine.request, Machine.response])
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

-- Every valid trace satisfies the catalogue at every instant.
check catalogueAlongTraces {
  valid implies always stateHolds[Machine.now]
} for 3 but 5 Int, 2 seq, 3 steps, 6 Request, 6 Response, 2 Runnable
