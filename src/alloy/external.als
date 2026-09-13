module external

-- The external handlers, as in `src/spec/02-abstract/external.lean`, one
-- predicate per handler, `[mat, now, s, req, res, s2]`: run under `mat` at
-- instant `now` on state `s`, the handler answers `req` with `res` and
-- leaves `s2`. The branches are the Lean branches in the Lean order.
-- Every read is of `s`, as in the monad; a branch's writes are given to
-- `apply` once, the reads' materialisation first, the handler's own
-- writes overriding it. The schedule handlers are left out with the
-- schedules.

open util/boolean
open types
open state
open properties

-- `{ p with state, value, settledAt := some now }`
pred settled [p : PromiseObject, st : PromiseState, v : Value, now : Int,
              p2 : PromiseObject] {
  sameBirth[p, p2] and sameObligations[p, p2] and
  p2.state = st and p2.value = v and p2.settledAt = now
}

-- `{ t with state := .acquired, version := t.version + 1, ttl, pid,
--    leaseTimeoutAt := some (now + ttl), retryTimeoutAt := none, resumes := [] }`
pred acquired [t : TaskObject, now : Int, who : Str, lease : Int, t2 : TaskObject] {
  t2.state = Acquired and t2.version = plus[t.version, 1] and
  t2.ttl = lease and t2.pid = who and t2.leaseTimeoutAt = plus[now, lease] and
  no t2.retryTimeoutAt and no t2.resumes
}

-- promises

pred promiseGet [mat : Bool, now : Int, s : State, req : PromiseGetReq,
                 res : PromiseGetRes, s2 : State] {
  no object[s, req.id] implies {
    res.status = s404 and no res.promise
    keep[s, s2]
  } else some o, o2 : Object | {
    readObject[s, req.id, now, o, o2]
    res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
    apply[s, matP[mat, o, o2], matT[mat, o, o2], none, s2]
  }
}

-- `promiseCreate` with writes already made: the fence runs it after
-- reading its task.
pred promiseCreateWith [mat : Bool, now : Int, s : State, req : PromiseCreateReq,
                        res : PromiseCreateRes, ps : Ident -> PromiseObject,
                        ts : Ident -> TaskObject, s2 : State] {
  no object[s, req.id] implies (some o : Object | {
    createPromise[now, req, o]
    res.status = s200 and one res.promise and promiseToRecord[o.promise, o.id, res.promise]
    apply[s, ps ++ (o.id -> o.promise), ts ++ (o.id -> o.task), none, s2]
  }) else some o, o2 : Object | {
    readObject[s, req.id, now, o, o2]
    res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
    apply[s, ps ++ matP[mat, o, o2], ts ++ matT[mat, o, o2], none, s2]
  }
}

pred promiseCreate [mat : Bool, now : Int, s : State, req : PromiseCreateReq,
                    res : PromiseCreateRes, s2 : State] {
  promiseCreateWith[mat, now, s, req, res, none -> none, none -> none, s2]
}

pred promiseSettleWith [mat : Bool, now : Int, s : State, req : PromiseSettleReq,
                        res : PromiseSettleRes, ps : Ident -> PromiseObject,
                        ts : Ident -> TaskObject, s2 : State] {
  req.state not in settable implies {
    res.status = s400 and no res.promise
    apply[s, ps, ts, none, s2]
  } else no object[s, req.id] implies {
    res.status = s404 and no res.promise
    apply[s, ps, ts, none, s2]
  } else some o, o2 : Object | {
    readObject[s, req.id, now, o, o2]
    let ps2 = ps ++ matP[mat, o, o2], ts2 = ts ++ matT[mat, o, o2] |
      o2.promise.state = Pending implies (some p : PromiseObject | {
        settled[o2.promise, req.state, req.value, now, p]
        setSettled[s, ps2, ts2, o2, p, s2]
        res.status = s200 and one res.promise and promiseToRecord[p, o2.id, res.promise]
      }) else {
        res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
        apply[s, ps2, ts2, none, s2]
      }
  }
}

pred promiseSettle [mat : Bool, now : Int, s : State, req : PromiseSettleReq,
                    res : PromiseSettleRes, s2 : State] {
  promiseSettleWith[mat, now, s, req, res, none -> none, none -> none, s2]
}

pred promiseRegisterCallback [mat : Bool, now : Int, s : State,
                              req : PromiseRegisterCallbackReq,
                              res : PromiseRegisterCallbackRes, s2 : State] {
  req.awaited = req.awaiter implies {
    res.status = s400 and no res.promise
    keep[s, s2]
  } else not sameOrigin[req.awaited, req.awaiter] implies {
    res.status = s400 and no res.promise
    keep[s, s2]
  } else no object[s, req.awaited] implies {
    res.status = s404 and no res.promise
    keep[s, s2]
  } else some oa, oa2 : Object | {
    readObject[s, req.awaited, now, oa, oa2]
    no object[s, req.awaiter] implies {
      res.status = s422 and no res.promise
      apply[s, matP[mat, oa, oa2], matT[mat, oa, oa2], none, s2]
    } else some ow, ow2 : Object | {
      readObject[s, req.awaiter, now, ow, ow2]
      let ps = matP[mat, oa, oa2] ++ matP[mat, ow, ow2],
          ts = matT[mat, oa, oa2] ++ matT[mat, ow, ow2] |
        ow2.promise.type not in isRunnable implies {
          res.status = s422 and no res.promise
          apply[s, ps, ts, none, s2]
        } else oa2.promise.type not in awaitable implies {
          res.status = s422 and no res.promise
          apply[s, ps, ts, none, s2]
        } else oa2.promise.state = Pending implies {
          ow2.promise.state = Pending implies (some p : PromiseObject | {
            addCallback[oa2.promise, req.awaiter, p]
            apply[s, ps ++ (oa2.id -> p), ts, none, s2]
          }) else
            apply[s, ps, ts, none, s2]
          res.status = s200 and one res.promise and
            promiseToRecord[oa2.promise, oa2.id, res.promise]
        } else {
          res.status = s200 and one res.promise and
            promiseToRecord[oa2.promise, oa2.id, res.promise]
          apply[s, ps, ts, none, s2]
        }
    }
  }
}

pred promiseRegisterListener [mat : Bool, now : Int, s : State,
                              req : PromiseRegisterListenerReq,
                              res : PromiseRegisterListenerRes, s2 : State] {
  no object[s, req.awaited] implies {
    res.status = s404 and no res.promise
    keep[s, s2]
  } else some oa, oa2 : Object | {
    readObject[s, req.awaited, now, oa, oa2]
    let ps = matP[mat, oa, oa2], ts = matT[mat, oa, oa2] |
      oa2.promise.type not in awaitable implies {
        res.status = s422 and no res.promise
        apply[s, ps, ts, none, s2]
      } else oa2.promise.state = Pending implies (some p : PromiseObject | {
        addListener[oa2.promise, req.address, p]
        apply[s, ps ++ (oa2.id -> p), ts, none, s2]
        res.status = s200 and one res.promise and
          promiseToRecord[oa2.promise, oa2.id, res.promise]
      }) else {
        res.status = s200 and one res.promise and
          promiseToRecord[oa2.promise, oa2.id, res.promise]
        apply[s, ps, ts, none, s2]
      }
  }
}

pred promiseSearch [mat : Bool, now : Int, s : State, req : PromiseSearchReq,
                    res : PromiseSearchRes, s2 : State] {
  res.status = s501 and no res.promises and no res.cursor
  keep[s, s2]
}

-- tasks

pred taskGet [mat : Bool, now : Int, s : State, req : TaskGetReq,
              res : TaskGetRes, s2 : State] {
  no object[s, req.id].task implies {
    res.status = s404 and no res.task
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    res.status = s200 and one res.task and taskToRecord[o2.task, o2.id, res.task]
    apply[s, matP[mat, o, o2], matT[mat, o, o2], none, s2]
  }
}

pred taskCreate [mat : Bool, now : Int, s : State, req : TaskCreateReq,
                 res : TaskCreateRes, s2 : State] {
  no res.preload
  let a = req.action |
    a.type not in isRunnable implies {
      res.status = s400 and no res.task and no res.promise
      keep[s, s2]
    } else no object[s, a.id] implies {
      a.timeoutAt > now implies (some p : PromiseObject, t : TaskObject | {
        p.state = Pending and p.param = a.param and emptyValue[p.value] and p.type = a.type and
        p.timeoutAt = a.timeoutAt and p.createdAt = now and no p.settledAt and
        no p.callbacks and no p.listeners
        t.state = Acquired and t.version = 1 and t.ttl = req.ttl and t.pid = req.pid and
        t.leaseTimeoutAt = plus[now, req.ttl] and no t.retryTimeoutAt and no t.resumes
        res.status = s200 and one res.task and taskToRecord[t, a.id, res.task] and
          one res.promise and promiseToRecord[p, a.id, res.promise]
        apply[s, a.id -> p, a.id -> t, none, s2]
      }) else some p : PromiseObject, t : TaskObject | {
        p.state = RejectedTimedout and p.param = a.param and emptyValue[p.value] and
        p.type = a.type and p.timeoutAt = a.timeoutAt and p.createdAt = a.timeoutAt and
        p.settledAt = a.timeoutAt and no p.callbacks and no p.listeners
        t.state = Fulfilled and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and no t.retryTimeoutAt and no t.resumes
        res.status = s200 and one res.task and taskToRecord[t, a.id, res.task] and
          one res.promise and promiseToRecord[p, a.id, res.promise]
        apply[s, a.id -> p, a.id -> t, none, s2]
      }
    } else some o, o2 : Object | {
      readObject[s, a.id, now, o, o2]
      let ps = matP[mat, o, o2], ts = matT[mat, o, o2] |
        o2.promise.type not in isRunnable implies {
          res.status = s422 and no res.task and no res.promise
          apply[s, ps, ts, none, s2]
        } else no o2.task implies {
          res.status = s409 and no res.task and no res.promise
          apply[s, ps, ts, none, s2]
        } else o2.task.state = Fulfilled implies {
          res.status = s200 and one res.task and taskToRecord[o2.task, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[s, ps, ts, none, s2]
        } else o2.task.state = TaskPending implies (some t : TaskObject | {
          acquired[o2.task, now, req.pid, req.ttl, t]
          res.status = s200 and one res.task and taskToRecord[t, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[s, ps, ts ++ (o2.id -> t), none, s2]
        }) else {
          res.status = s409 and no res.task and no res.promise
          apply[s, ps, ts, none, s2]
        }
    }
}

pred taskAcquire [mat : Bool, now : Int, s : State, req : TaskAcquireReq,
                  res : TaskAcquireRes, s2 : State] {
  no res.preload
  no object[s, req.id].task implies {
    res.status = s404 and no res.task and no res.promise
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != TaskPending or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.task and no res.promise
          apply[s, ps, ts, none, s2]
        } else some t2 : TaskObject | {
          acquired[t, now, req.pid, req.ttl, t2]
          res.status = s200 and one res.task and taskToRecord[t2, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[s, ps, ts ++ (o2.id -> t2), none, s2]
        }
  }
}

pred taskFence [mat : Bool, now : Int, s : State, req : TaskFenceReq,
                res : TaskFenceRes, s2 : State] {
  no res.preload
  (targetId[req.action] = req.id or not sameOrigin[targetId[req.action], req.id]) implies {
    res.status = s400 and no res.action
    keep[s, s2]
  } else no object[s, req.id].task implies {
    res.status = s404 and no res.action
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.action
          apply[s, ps, ts, none, s2]
        } else {
          res.status = s200 and one res.action
          req.action in FenceCreate implies
            (res.action in FenceCreateRes and
             promiseCreateWith[mat, now, s, req.action.create, res.action.create, ps, ts, s2])
          req.action in FenceSettle implies
            (res.action in FenceSettleRes and
             promiseSettleWith[mat, now, s, req.action.settle, res.action.settle, ps, ts, s2])
        }
  }
}

-- `heartbeatOne`: the task under `ref` is written with its lease extended
-- when it is acquired under `pid` at `ref.version` and its promise is
-- pending. `heartbeatAll` walks the list; the writes of the refs are on
-- distinct keys or equal, so they are one map.
pred heartbeatMatch [who : Str, ref : TaskRef, o2 : Object] {
  o2.task.state = Acquired and o2.task.version = ref.version and
  o2.task.pid = who and o2.promise.state = Pending
}

pred heartbeatOne [now : Int, t, t2 : TaskObject] {
  t2.state = t.state and t2.version = t.version and t2.ttl = t.ttl and t2.pid = t.pid and
  t2.leaseTimeoutAt = plus[now, (some t.ttl implies t.ttl else 0)] and
  t2.retryTimeoutAt = t.retryTimeoutAt and t2.resumes = t.resumes
}

pred taskHeartbeat [mat : Bool, now : Int, s : State, req : TaskHeartbeatReq,
                    res : TaskHeartbeatRes, s2 : State] {
  res.status = s200
  let refs = req.tasks.elems |
    all ref : refs | some object[s, ref.id].task implies
      some o, o2 : Object | readTaskObject[s, ref.id, now, o, o2] and
        (heartbeatMatch[req.pid, ref, o2] implies some t2 : TaskObject | heartbeatOne[now, o2.task, t2])
  let refs = req.tasks.elems,
      ps = { i : Ident, p : PromiseObject | some ref : refs, o, o2 : Object |
               readTaskObject[s, ref.id, now, o, o2] and i -> p in matP[mat, o, o2] },
      ts = { i : Ident, t : TaskObject | some ref : refs, o, o2 : Object |
               readTaskObject[s, ref.id, now, o, o2] and
               (i -> t in matT[mat, o, o2] or
                (heartbeatMatch[req.pid, ref, o2] and i = o2.id and heartbeatOne[now, o2.task, t])) } |
    apply[s, ps, ts, none, s2]
}

-- `checkAwaited`: walks the actions in order, reading each awaited; it
-- stops at the first that is absent or not awaitable, and otherwise tells
-- whether any awaited is settled. `firstBad` is where it stops.
pred badAwaited [s : State, now : Int, i : Ident] {
  no object[s, i] or (some o2 : Object | some o : object[s, i] | projectObject[o, now, o2] and o2.promise.type not in awaitable)
}

fun firstBad [s : State, now : Int, actions : seq PromiseRegisterCallbackReq] : lone Int {
  min[{ k : actions.inds | badAwaited[s, now, actions[k].awaited] }]
}

fun readActions [s : State, now : Int, actions : seq PromiseRegisterCallbackReq] : set Int {
  some firstBad[s, now, actions]
    implies { k : actions.inds | k <= firstBad[s, now, actions] }
    else actions.inds
}

pred taskSuspend [mat : Bool, now : Int, s : State, req : TaskSuspendReq,
                  res : TaskSuspendRes, s2 : State] {
  no res.preload
  let actions = req.actions, ids = actions.elems.awaited |
    (actions.isEmpty or req.id in ids or
     (some i : ids | not sameOrigin[i, req.id]) or #ids != #actions) implies {
      res.status = s400
      keep[s, s2]
    } else no object[s, req.id].task implies {
      res.status = s404
      keep[s, s2]
    } else some o, o2 : Object | {
      readTaskObject[s, req.id, now, o, o2]
      let t = o2.task |
        (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
          implies {
            res.status = s409
            apply[s, matP[mat, o, o2], matT[mat, o, o2], none, s2]
          } else {
            all k : readActions[s, now, actions] | some object[s, actions[k].awaited] implies
              some oa, oa2 : Object | readObject[s, actions[k].awaited, now, oa, oa2]
            let read = readActions[s, now, actions],
                ps = matP[mat, o, o2] ++
                     { i : Ident, p : PromiseObject | some k : read, oa, oa2 : Object |
                         readObject[s, actions[k].awaited, now, oa, oa2] and i -> p in matP[mat, oa, oa2] },
                ts = matT[mat, o, o2] ++
                     { i : Ident, u : TaskObject | some k : read, oa, oa2 : Object |
                         readObject[s, actions[k].awaited, now, oa, oa2] and i -> u in matT[mat, oa, oa2] } |
              some firstBad[s, now, actions] implies {
                res.status = s422
                apply[s, ps, ts, none, s2]
              } else (some i : ids, oa, oa2 : Object |
                      readObject[s, i, now, oa, oa2] and oa2.promise.state != Pending) implies
                (some t2 : TaskObject | {
                  t2.state = t.state and t2.version = t.version and t2.ttl = t.ttl and
                  t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
                  t2.retryTimeoutAt = t.retryTimeoutAt and no t2.resumes
                  res.status = s300
                  apply[s, ps, ts ++ (o2.id -> t2), none, s2]
                })
              else some t2 : TaskObject | {
                all i : ids | some oa, oa2 : Object, p : PromiseObject |
                  readObject[s, i, now, oa, oa2] and addCallback[oa2.promise, req.id, p]
                t2.state = Suspended and t2.version = t.version and no t2.ttl and no t2.pid and
                no t2.leaseTimeoutAt and no t2.retryTimeoutAt and no t2.resumes
                res.status = s200
                apply[s, ps ++ { i : Ident, p : PromiseObject | some oa, oa2 : Object |
                                   i in ids and readObject[s, i, now, oa, oa2] and
                                   addCallback[oa2.promise, req.id, p] },
                      ts ++ (o2.id -> t2), none, s2]
              }
          }
    }
}

pred taskFulfill [mat : Bool, now : Int, s : State, req : TaskFulfillReq,
                  res : TaskFulfillRes, s2 : State] {
  req.action.state not in settable implies {
    res.status = s400 and no res.promise
    keep[s, s2]
  } else no object[s, req.id].task implies {
    res.status = s404 and no res.promise
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.promise
          apply[s, ps, ts, none, s2]
        } else some p : PromiseObject | {
          settled[o2.promise, req.action.state, req.action.value, now, p]
          setSettled[s, ps, ts, o2, p, s2]
          res.status = s200 and one res.promise and promiseToRecord[p, o2.id, res.promise]
        }
  }
}

pred taskRelease [mat : Bool, now : Int, s : State, req : TaskReleaseReq,
                  res : TaskReleaseRes, s2 : State] {
  no object[s, req.id].task implies {
    res.status = s404
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409
          apply[s, ps, ts, none, s2]
        } else some t2 : TaskObject | {
          t2.state = TaskPending and t2.version = t.version and no t2.ttl and no t2.pid and
          no t2.leaseTimeoutAt and t2.retryTimeoutAt = now and t2.resumes = t.resumes
          res.status = s200
          apply[s, ps, ts ++ (o2.id -> t2), none, s2]
        }
  }
}

pred taskHalt [mat : Bool, now : Int, s : State, req : TaskHaltReq,
               res : TaskHaltRes, s2 : State] {
  no object[s, req.id].task implies {
    res.status = s404
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      t.state = Fulfilled implies {
        res.status = s409
        apply[s, ps, ts, none, s2]
      } else t.state = Halted implies {
        res.status = s200
        apply[s, ps, ts, none, s2]
      } else some t2 : TaskObject | {
        t2.state = Halted and t2.version = t.version and no t2.ttl and no t2.pid and
        no t2.leaseTimeoutAt and no t2.retryTimeoutAt and t2.resumes = t.resumes
        res.status = s200
        apply[s, ps, ts ++ (o2.id -> t2), none, s2]
      }
  }
}

pred taskContinue [mat : Bool, now : Int, s : State, req : TaskContinueReq,
                   res : TaskContinueRes, s2 : State] {
  no object[s, req.id].task implies {
    res.status = s404
    keep[s, s2]
  } else some o, o2 : Object | {
    readTaskObject[s, req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Halted or o2.promise.state != Pending) implies {
        res.status = s409
        apply[s, ps, ts, none, s2]
      } else some t2 : TaskObject | {
        t2.state = TaskPending and t2.version = t.version and t2.ttl = t.ttl and
        t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
        t2.retryTimeoutAt = now and t2.resumes = t.resumes
        res.status = s200
        apply[s, ps, ts ++ (o2.id -> t2), none, s2]
      }
  }
}

pred taskSearch [mat : Bool, now : Int, s : State, req : TaskSearchReq,
                 res : TaskSearchRes, s2 : State] {
  res.status = s501 and no res.tasks and no res.cursor
  keep[s, s2]
}

-- Commands. Each handler has a run showing it can succeed on a well formed
-- state, and a check that it preserves the catalogue's state properties.
-- Run with `--nooverflow`: the machine's arithmetic is on naturals.

run promiseGet_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now, s] and promiseGet[mat, now, s, req, res, s2] and res.status = s200
} for 4 but 5 Int, 2 State, 2 seq

run promiseCreate_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now, s] and promiseCreate[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run promiseSettle_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now, s] and promiseSettle[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run promiseRegisterCallback_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now, s] and promiseRegisterCallback[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run promiseRegisterListener_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now, s] and promiseRegisterListener[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run promiseSearch_ok {
  some mat : Bool, now : Int, s, s2 : State, req : PromiseSearchReq, res : PromiseSearchRes |
    stateHolds[now, s] and promiseSearch[mat, now, s, req, res, s2] and res.status = s501
} for 4 but 5 Int, 2 State, 2 seq

run taskGet_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now, s] and taskGet[mat, now, s, req, res, s2] and res.status = s200
} for 4 but 5 Int, 2 State, 2 seq

run taskCreate_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now, s] and taskCreate[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskAcquire_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now, s] and taskAcquire[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskFence_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now, s] and taskFence[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskHeartbeat_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now, s] and taskHeartbeat[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskSuspend_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now, s] and taskSuspend[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskFulfill_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now, s] and taskFulfill[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskRelease_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now, s] and taskRelease[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskHalt_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now, s] and taskHalt[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskContinue_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now, s] and taskContinue[mat, now, s, req, res, s2] and res.status = s200 and s2 != s
} for 4 but 5 Int, 2 State, 2 seq

run taskSearch_ok {
  some mat : Bool, now : Int, s, s2 : State, req : TaskSearchReq, res : TaskSearchRes |
    stateHolds[now, s] and taskSearch[mat, now, s, req, res, s2] and res.status = s501
} for 4 but 5 Int, 2 State, 2 seq

check promiseGet_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseGetReq, res : PromiseGetRes |
    stateHolds[now, s] and promiseGet[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check promiseCreate_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseCreateReq, res : PromiseCreateRes |
    stateHolds[now, s] and promiseCreate[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check promiseSettle_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseSettleReq, res : PromiseSettleRes |
    stateHolds[now, s] and promiseSettle[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check promiseRegisterCallback_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseRegisterCallbackReq, res : PromiseRegisterCallbackRes |
    stateHolds[now, s] and promiseRegisterCallback[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check promiseRegisterListener_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseRegisterListenerReq, res : PromiseRegisterListenerRes |
    stateHolds[now, s] and promiseRegisterListener[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check promiseSearch_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : PromiseSearchReq, res : PromiseSearchRes |
    stateHolds[now, s] and promiseSearch[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskGet_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskGetReq, res : TaskGetRes |
    stateHolds[now, s] and taskGet[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskCreate_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskCreateReq, res : TaskCreateRes |
    stateHolds[now, s] and taskCreate[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskAcquire_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskAcquireReq, res : TaskAcquireRes |
    stateHolds[now, s] and taskAcquire[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskFence_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskFenceReq, res : TaskFenceRes |
    stateHolds[now, s] and taskFence[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskHeartbeat_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskHeartbeatReq, res : TaskHeartbeatRes |
    stateHolds[now, s] and taskHeartbeat[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskSuspend_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskSuspendReq, res : TaskSuspendRes |
    stateHolds[now, s] and taskSuspend[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskFulfill_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskFulfillReq, res : TaskFulfillRes |
    stateHolds[now, s] and taskFulfill[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskRelease_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskReleaseReq, res : TaskReleaseRes |
    stateHolds[now, s] and taskRelease[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskHalt_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskHaltReq, res : TaskHaltRes |
    stateHolds[now, s] and taskHalt[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskContinue_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskContinueReq, res : TaskContinueRes |
    stateHolds[now, s] and taskContinue[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq

check taskSearch_preserves {
  all mat : Bool, now : Int, s, s2 : State, req : TaskSearchReq, res : TaskSearchRes |
    stateHolds[now, s] and taskSearch[mat, now, s, req, res, s2] implies stateHolds[now, s2]
} for 4 but 5 Int, 2 State, 2 seq
