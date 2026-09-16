module external

-- The external handlers, as in `src/spec/02-abstract/external.lean`, one
-- predicate per handler, `[mat, now, req, res]`: run under `mat` at
-- instant `now` on the current state, the handler answers `req` with
-- `res` and leaves the next state, `State.objects'` and `State.outbox'`.
-- The branches are the Lean branches in the Lean order. Every read is of
-- the current state, as in the monad; a branch's writes are given to
-- `apply` once, the reads' materialisation first, the handler's own
-- writes overriding it.

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

pred promiseGet [mat : Bool, now : Int, req : PromiseGetReq,
                 res : PromiseGetRes] {
  no object[req.id] implies {
    res.status = s404 and no res.promise
    keep
  } else some o, o2 : Object | {
    readObject[req.id, now, o, o2]
    res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
    apply[matP[mat, o, o2], matT[mat, o, o2], none]
  }
}

-- `promiseCreate` with writes already made: the fence runs it after
-- reading its task.
pred promiseCreateWith [mat : Bool, now : Int, req : PromiseCreateReq,
                        res : PromiseCreateRes, ps : Ident -> PromiseObject,
                        ts : Ident -> TaskObject] {
  no object[req.id] implies (some o : Object | {
    createPromise[now, req.id, req.timeoutAt, req.param, req.type, req.delay, o]
    res.status = s200 and one res.promise and promiseToRecord[o.promise, o.id, res.promise]
    apply[ps ++ (o.id -> o.promise), ts ++ (o.id -> o.task), none]
  }) else some o, o2 : Object | {
    readObject[req.id, now, o, o2]
    res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
    apply[ps ++ matP[mat, o, o2], ts ++ matT[mat, o, o2], none]
  }
}

pred promiseCreate [mat : Bool, now : Int, req : PromiseCreateReq,
                    res : PromiseCreateRes] {
  promiseCreateWith[mat, now, req, res, none -> none, none -> none]
}

pred promiseSettleWith [mat : Bool, now : Int, req : PromiseSettleReq,
                        res : PromiseSettleRes, ps : Ident -> PromiseObject,
                        ts : Ident -> TaskObject] {
  req.state not in settable implies {
    res.status = s400 and no res.promise
    apply[ps, ts, none]
  } else no object[req.id] implies {
    res.status = s404 and no res.promise
    apply[ps, ts, none]
  } else some o, o2 : Object | {
    readObject[req.id, now, o, o2]
    let ps2 = ps ++ matP[mat, o, o2], ts2 = ts ++ matT[mat, o, o2] |
      o2.promise.state = Pending implies (some p : PromiseObject | {
        settled[o2.promise, req.state, req.value, now, p]
        setSettled[ps2, ts2, o2, p]
        res.status = s200 and one res.promise and promiseToRecord[p, o2.id, res.promise]
      }) else {
        res.status = s200 and one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
        apply[ps2, ts2, none]
      }
  }
}

pred promiseSettle [mat : Bool, now : Int, req : PromiseSettleReq,
                    res : PromiseSettleRes] {
  promiseSettleWith[mat, now, req, res, none -> none, none -> none]
}

pred promiseRegisterCallback [mat : Bool, now : Int,
                              req : PromiseRegisterCallbackReq,
                              res : PromiseRegisterCallbackRes] {
  req.awaited = req.awaiter implies {
    res.status = s400 and no res.promise
    keep
  } else not sameOrigin[req.awaited, req.awaiter] implies {
    res.status = s400 and no res.promise
    keep
  } else no object[req.awaited] implies {
    res.status = s404 and no res.promise
    keep
  } else some oa, oa2 : Object | {
    readObject[req.awaited, now, oa, oa2]
    no object[req.awaiter] implies {
      res.status = s422 and no res.promise
      apply[matP[mat, oa, oa2], matT[mat, oa, oa2], none]
    } else some ow, ow2 : Object | {
      readObject[req.awaiter, now, ow, ow2]
      let ps = matP[mat, oa, oa2] ++ matP[mat, ow, ow2],
          ts = matT[mat, oa, oa2] ++ matT[mat, ow, ow2] |
        ow2.promise.type not in isRunnable implies {
          res.status = s422 and no res.promise
          apply[ps, ts, none]
        } else oa2.promise.type not in awaitable implies {
          res.status = s422 and no res.promise
          apply[ps, ts, none]
        } else oa2.promise.state = Pending implies {
          ow2.promise.state = Pending implies (some p : PromiseObject | {
            addCallback[oa2.promise, req.awaiter, p]
            apply[ps ++ (oa2.id -> p), ts, none]
          }) else
            apply[ps, ts, none]
          res.status = s200 and one res.promise and
            promiseToRecord[oa2.promise, oa2.id, res.promise]
        } else {
          res.status = s200 and one res.promise and
            promiseToRecord[oa2.promise, oa2.id, res.promise]
          apply[ps, ts, none]
        }
    }
  }
}

pred promiseRegisterListener [mat : Bool, now : Int,
                              req : PromiseRegisterListenerReq,
                              res : PromiseRegisterListenerRes] {
  no object[req.awaited] implies {
    res.status = s404 and no res.promise
    keep
  } else some oa, oa2 : Object | {
    readObject[req.awaited, now, oa, oa2]
    let ps = matP[mat, oa, oa2], ts = matT[mat, oa, oa2] |
      oa2.promise.type not in awaitable implies {
        res.status = s422 and no res.promise
        apply[ps, ts, none]
      } else oa2.promise.state = Pending implies (some p : PromiseObject | {
        addListener[oa2.promise, req.address, p]
        apply[ps ++ (oa2.id -> p), ts, none]
        res.status = s200 and one res.promise and
          promiseToRecord[oa2.promise, oa2.id, res.promise]
      }) else {
        res.status = s200 and one res.promise and
          promiseToRecord[oa2.promise, oa2.id, res.promise]
        apply[ps, ts, none]
      }
  }
}

pred promiseSearch [mat : Bool, now : Int, req : PromiseSearchReq,
                    res : PromiseSearchRes] {
  res.status = s501 and no res.promises and no res.cursor
  keep
}

-- tasks

pred taskGet [mat : Bool, now : Int, req : TaskGetReq,
              res : TaskGetRes] {
  no object[req.id].task implies {
    res.status = s404 and no res.task
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    res.status = s200 and one res.task and taskToRecord[o2.task, o2.id, res.task]
    apply[matP[mat, o, o2], matT[mat, o, o2], none]
  }
}

pred taskCreate [mat : Bool, now : Int, req : TaskCreateReq,
                 res : TaskCreateRes] {
  no res.preload
  let a = req.action |
    a.type not in isRunnable implies {
      res.status = s400 and no res.task and no res.promise
      keep
    } else no object[a.id] implies {
      a.timeoutAt > now implies (some p : PromiseObject, t : TaskObject | {
        p.state = Pending and p.param = a.param and emptyValue[p.value] and p.type = a.type and
        p.timeoutAt = a.timeoutAt and p.createdAt = now and no p.settledAt and
        no p.callbacks and no p.listeners
        t.state = Acquired and t.version = 1 and t.ttl = req.ttl and t.pid = req.pid and
        t.leaseTimeoutAt = plus[now, req.ttl] and no t.retryTimeoutAt and no t.resumes
        res.status = s200 and one res.task and taskToRecord[t, a.id, res.task] and
          one res.promise and promiseToRecord[p, a.id, res.promise]
        apply[a.id -> p, a.id -> t, none]
      }) else some p : PromiseObject, t : TaskObject | {
        p.state = RejectedTimedout and p.param = a.param and emptyValue[p.value] and
        p.type = a.type and p.timeoutAt = a.timeoutAt and p.createdAt = a.timeoutAt and
        p.settledAt = a.timeoutAt and no p.callbacks and no p.listeners
        t.state = Fulfilled and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and no t.retryTimeoutAt and no t.resumes
        res.status = s200 and one res.task and taskToRecord[t, a.id, res.task] and
          one res.promise and promiseToRecord[p, a.id, res.promise]
        apply[a.id -> p, a.id -> t, none]
      }
    } else some o, o2 : Object | {
      readObject[a.id, now, o, o2]
      let ps = matP[mat, o, o2], ts = matT[mat, o, o2] |
        o2.promise.type not in isRunnable implies {
          res.status = s422 and no res.task and no res.promise
          apply[ps, ts, none]
        } else no o2.task implies {
          res.status = s409 and no res.task and no res.promise
          apply[ps, ts, none]
        } else o2.task.state = Fulfilled implies {
          res.status = s200 and one res.task and taskToRecord[o2.task, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[ps, ts, none]
        } else o2.task.state = TaskPending implies (some t : TaskObject | {
          acquired[o2.task, now, req.pid, req.ttl, t]
          res.status = s200 and one res.task and taskToRecord[t, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[ps, ts ++ (o2.id -> t), none]
        }) else {
          res.status = s409 and no res.task and no res.promise
          apply[ps, ts, none]
        }
    }
}

pred taskAcquire [mat : Bool, now : Int, req : TaskAcquireReq,
                  res : TaskAcquireRes] {
  no res.preload
  no object[req.id].task implies {
    res.status = s404 and no res.task and no res.promise
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != TaskPending or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.task and no res.promise
          apply[ps, ts, none]
        } else some t2 : TaskObject | {
          acquired[t, now, req.pid, req.ttl, t2]
          res.status = s200 and one res.task and taskToRecord[t2, o2.id, res.task] and
            one res.promise and promiseToRecord[o2.promise, o2.id, res.promise]
          apply[ps, ts ++ (o2.id -> t2), none]
        }
  }
}

pred taskFence [mat : Bool, now : Int, req : TaskFenceReq,
                res : TaskFenceRes] {
  no res.preload
  (targetId[req.action] = req.id or not sameOrigin[targetId[req.action], req.id]) implies {
    res.status = s400 and no res.action
    keep
  } else no object[req.id].task implies {
    res.status = s404 and no res.action
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.action
          apply[ps, ts, none]
        } else {
          res.status = s200 and one res.action
          req.action in FenceCreate implies
            (res.action in FenceCreateRes and
             promiseCreateWith[mat, now, req.action.create, res.action.create, ps, ts])
          req.action in FenceSettle implies
            (res.action in FenceSettleRes and
             promiseSettleWith[mat, now, req.action.settle, res.action.settle, ps, ts])
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

pred taskHeartbeat [mat : Bool, now : Int, req : TaskHeartbeatReq,
                    res : TaskHeartbeatRes] {
  res.status = s200
  let refs = req.tasks.elems |
    all ref : refs | some object[ref.id].task implies
      some o, o2 : Object | readTaskObject[ref.id, now, o, o2] and
        (heartbeatMatch[req.pid, ref, o2] implies some t2 : TaskObject | heartbeatOne[now, o2.task, t2])
  let refs = req.tasks.elems,
      ps = { i : Ident, p : PromiseObject | some ref : refs, o, o2 : Object |
               readTaskObject[ref.id, now, o, o2] and i -> p in matP[mat, o, o2] },
      ts = { i : Ident, t : TaskObject | some ref : refs, o, o2 : Object |
               readTaskObject[ref.id, now, o, o2] and
               (i -> t in matT[mat, o, o2] or
                (heartbeatMatch[req.pid, ref, o2] and i = o2.id and heartbeatOne[now, o2.task, t])) } |
    apply[ps, ts, none]
}

-- `checkAwaited`: walks the actions in order, reading each awaited; it
-- stops at the first that is absent or not awaitable, and otherwise tells
-- whether any awaited is settled. `firstBad` is where it stops.
pred badAwaited [now : Int, i : Ident] {
  no object[i] or (some o2 : Object | some o : object[i] | projectObject[o, now, o2] and o2.promise.type not in awaitable)
}

fun firstBad [now : Int, actions : seq PromiseRegisterCallbackReq] : lone Int {
  min[{ k : actions.inds | badAwaited[now, actions[k].awaited] }]
}

fun readActions [now : Int, actions : seq PromiseRegisterCallbackReq] : set Int {
  some firstBad[now, actions]
    implies { k : actions.inds | k <= firstBad[now, actions] }
    else actions.inds
}

pred taskSuspend [mat : Bool, now : Int, req : TaskSuspendReq,
                  res : TaskSuspendRes] {
  no res.preload
  let actions = req.actions, ids = actions.elems.awaited |
    (actions.isEmpty or req.id in ids or
     (some i : ids | not sameOrigin[i, req.id]) or #ids != #actions) implies {
      res.status = s400
      keep
    } else no object[req.id].task implies {
      res.status = s404
      keep
    } else some o, o2 : Object | {
      readTaskObject[req.id, now, o, o2]
      let t = o2.task |
        (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
          implies {
            res.status = s409
            apply[matP[mat, o, o2], matT[mat, o, o2], none]
          } else {
            all k : readActions[now, actions] | some object[actions[k].awaited] implies
              some oa, oa2 : Object | readObject[actions[k].awaited, now, oa, oa2]
            let read = readActions[now, actions],
                ps = matP[mat, o, o2] ++
                     { i : Ident, p : PromiseObject | some k : read, oa, oa2 : Object |
                         readObject[actions[k].awaited, now, oa, oa2] and i -> p in matP[mat, oa, oa2] },
                ts = matT[mat, o, o2] ++
                     { i : Ident, u : TaskObject | some k : read, oa, oa2 : Object |
                         readObject[actions[k].awaited, now, oa, oa2] and i -> u in matT[mat, oa, oa2] } |
              some firstBad[now, actions] implies {
                res.status = s422
                apply[ps, ts, none]
              } else (some i : ids, oa, oa2 : Object |
                      readObject[i, now, oa, oa2] and oa2.promise.state != Pending) implies
                (some t2 : TaskObject | {
                  t2.state = t.state and t2.version = t.version and t2.ttl = t.ttl and
                  t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
                  t2.retryTimeoutAt = t.retryTimeoutAt and no t2.resumes
                  res.status = s300
                  apply[ps, ts ++ (o2.id -> t2), none]
                })
              else some t2 : TaskObject | {
                all i : ids | some oa, oa2 : Object, p : PromiseObject |
                  readObject[i, now, oa, oa2] and addCallback[oa2.promise, req.id, p]
                t2.state = Suspended and t2.version = t.version and no t2.ttl and no t2.pid and
                no t2.leaseTimeoutAt and no t2.retryTimeoutAt and no t2.resumes
                res.status = s200
                apply[ps ++ { i : Ident, p : PromiseObject | some oa, oa2 : Object |
                                   i in ids and readObject[i, now, oa, oa2] and
                                   addCallback[oa2.promise, req.id, p] },
                      ts ++ (o2.id -> t2), none]
              }
          }
    }
}

pred taskFulfill [mat : Bool, now : Int, req : TaskFulfillReq,
                  res : TaskFulfillRes] {
  req.action.state not in settable implies {
    res.status = s400 and no res.promise
    keep
  } else no object[req.id].task implies {
    res.status = s404 and no res.promise
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409 and no res.promise
          apply[ps, ts, none]
        } else some p : PromiseObject | {
          settled[o2.promise, req.action.state, req.action.value, now, p]
          setSettled[ps, ts, o2, p]
          res.status = s200 and one res.promise and promiseToRecord[p, o2.id, res.promise]
        }
  }
}

pred taskRelease [mat : Bool, now : Int, req : TaskReleaseReq,
                  res : TaskReleaseRes] {
  no object[req.id].task implies {
    res.status = s404
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Acquired or o2.promise.state != Pending or t.version != req.version)
        implies {
          res.status = s409
          apply[ps, ts, none]
        } else some t2 : TaskObject | {
          t2.state = TaskPending and t2.version = t.version and no t2.ttl and no t2.pid and
          no t2.leaseTimeoutAt and t2.retryTimeoutAt = now and t2.resumes = t.resumes
          res.status = s200
          apply[ps, ts ++ (o2.id -> t2), none]
        }
  }
}

pred taskHalt [mat : Bool, now : Int, req : TaskHaltReq,
               res : TaskHaltRes] {
  no object[req.id].task implies {
    res.status = s404
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      t.state = Fulfilled implies {
        res.status = s409
        apply[ps, ts, none]
      } else t.state = Halted implies {
        res.status = s200
        apply[ps, ts, none]
      } else some t2 : TaskObject | {
        t2.state = Halted and t2.version = t.version and no t2.ttl and no t2.pid and
        no t2.leaseTimeoutAt and no t2.retryTimeoutAt and t2.resumes = t.resumes
        res.status = s200
        apply[ps, ts ++ (o2.id -> t2), none]
      }
  }
}

pred taskContinue [mat : Bool, now : Int, req : TaskContinueReq,
                   res : TaskContinueRes] {
  no object[req.id].task implies {
    res.status = s404
    keep
  } else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let ps = matP[mat, o, o2], ts = matT[mat, o, o2], t = o2.task |
      (t.state != Halted or o2.promise.state != Pending) implies {
        res.status = s409
        apply[ps, ts, none]
      } else some t2 : TaskObject | {
        t2.state = TaskPending and t2.version = t.version and t2.ttl = t.ttl and
        t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
        t2.retryTimeoutAt = now and t2.resumes = t.resumes
        res.status = s200
        apply[ps, ts ++ (o2.id -> t2), none]
      }
  }
}

pred taskSearch [mat : Bool, now : Int, req : TaskSearchReq,
                 res : TaskSearchRes] {
  res.status = s501 and no res.tasks and no res.cursor
  keep
}

-- schedules

pred scheduleGet [mat : Bool, now : Int, req : ScheduleGetReq, res : ScheduleGetRes] {
  no schedule[req.id] implies {
    res.status = s404 and no res.schedule
  } else {
    res.status = s200 and res.schedule = schedule[req.id]
  }
  keep
}

pred scheduleCreate [mat : Bool, now : Int, req : ScheduleCreateReq,
                     res : ScheduleCreateRes] {
  some schedule[req.id] implies {
    res.status = s200 and res.schedule = schedule[req.id]
    keep
  } else some c : Schedule | {
    c.id = req.id and c.cron = req.cron and c.promiseId = req.promiseId and
    c.promiseTimeout = req.promiseTimeout and c.promiseParam = req.promiseParam and
    c.promiseType = req.promiseType and c.createdAt = now and
    c.nextRunAt = c.nextCron[now] and no c.lastRunAt
    res.status = s200 and res.schedule = c
    applyAll[none -> none, none -> none, c, none, none]
  }
}

pred scheduleDelete [mat : Bool, now : Int, req : ScheduleDeleteReq,
                     res : ScheduleDeleteRes] {
  no schedule[req.id] implies {
    res.status = s404
    keep
  } else {
    res.status = s200
    applyAll[none -> none, none -> none, none, schedule[req.id].id, none]
  }
}

pred scheduleSearch [mat : Bool, now : Int, req : ScheduleSearchReq,
                     res : ScheduleSearchRes] {
  res.status = s501 and no res.schedules and no res.cursor
  keep
}
