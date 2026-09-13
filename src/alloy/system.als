module system

-- The machine, as in `src/spec/02-abstract/system.lean`: so far the
-- dispatch of an external request to its handler.

open util/boolean
open types
open state
open external

pred handleExternal [mat : Bool, now : Int, s : State, req : Request, res : Response,
                     s2 : State] {
  req in PromiseGetReq implies
    (res in PromiseGetRes and promiseGet[mat, now, s, req, res, s2])
  req in PromiseCreateReq implies
    (res in PromiseCreateRes and promiseCreate[mat, now, s, req, res, s2])
  req in PromiseSettleReq implies
    (res in PromiseSettleRes and promiseSettle[mat, now, s, req, res, s2])
  req in PromiseRegisterCallbackReq implies
    (res in PromiseRegisterCallbackRes and promiseRegisterCallback[mat, now, s, req, res, s2])
  req in PromiseRegisterListenerReq implies
    (res in PromiseRegisterListenerRes and promiseRegisterListener[mat, now, s, req, res, s2])
  req in PromiseSearchReq implies
    (res in PromiseSearchRes and promiseSearch[mat, now, s, req, res, s2])
  req in TaskGetReq implies
    (res in TaskGetRes and taskGet[mat, now, s, req, res, s2])
  req in TaskCreateReq implies
    (res in TaskCreateRes and taskCreate[mat, now, s, req, res, s2])
  req in TaskAcquireReq implies
    (res in TaskAcquireRes and taskAcquire[mat, now, s, req, res, s2])
  req in TaskFenceReq implies
    (res in TaskFenceRes and taskFence[mat, now, s, req, res, s2])
  req in TaskHeartbeatReq implies
    (res in TaskHeartbeatRes and taskHeartbeat[mat, now, s, req, res, s2])
  req in TaskSuspendReq implies
    (res in TaskSuspendRes and taskSuspend[mat, now, s, req, res, s2])
  req in TaskFulfillReq implies
    (res in TaskFulfillRes and taskFulfill[mat, now, s, req, res, s2])
  req in TaskReleaseReq implies
    (res in TaskReleaseRes and taskRelease[mat, now, s, req, res, s2])
  req in TaskHaltReq implies
    (res in TaskHaltRes and taskHalt[mat, now, s, req, res, s2])
  req in TaskContinueReq implies
    (res in TaskContinueRes and taskContinue[mat, now, s, req, res, s2])
  req in TaskSearchReq implies
    (res in TaskSearchRes and taskSearch[mat, now, s, req, res, s2])
}

run handleExternal for 3 but 5 Int, 2 State, 2 seq
