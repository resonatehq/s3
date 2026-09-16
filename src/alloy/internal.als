module internal

-- The internal triggers, as in `src/spec/02-abstract/internal.lean`, one
-- predicate per trigger, `[now, req]`: at instant `now` on the current
-- state the trigger leaves the next state. The branches are the Lean
-- branches in the Lean order. The promise timeout, the callback and the
-- listener touch what they read, materialising it whatever the machine's
-- `mat`; the lease and retry timeouts view it, writing nothing they did
-- not decide. The schedule trigger is left out with the schedules.

open util/boolean
open types
open state
open properties

-- `processPromiseTimeout`: touch the promise, so a due one is settled.
pred processPromiseTimeout [now : Int, req : PromiseTimeoutReq] {
  no object[req.id] implies keep
  else some o, o2 : Object | {
    readObject[req.id, now, o, o2]
    apply[matP[True, o, o2], matT[True, o, o2], none]
  }
}

-- `resumeOne awaited awaiter`, with writes already made: the awaiter's
-- task is woken when suspended, told when pending, acquired or halted,
-- left alone when fulfilled.
pred resumeOneWith [awaited, awaiter : Ident, now : Int,
                    ps : Ident -> PromiseObject, ts : Ident -> TaskObject] {
  no object[awaiter].task implies apply[ps, ts, none]
  else some o, o2 : Object | {
    readTaskObject[awaiter, now, o, o2]
    let ps2 = ps ++ matP[True, o, o2], ts2 = ts ++ matT[True, o, o2], t = o2.task |
      t.state = Suspended implies (some t2 : TaskObject | {
        t2.state = TaskPending and t2.version = t.version and t2.ttl = t.ttl and
        t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
        t2.retryTimeoutAt = now and t2.resumes = awaited
        apply[ps2, ts2 ++ (o2.id -> t2), none]
      }) else t.state in TaskPending + Acquired + Halted implies {
        awaited not in t.resumes implies (some t2 : TaskObject | {
          t2.state = t.state and t2.version = t.version and t2.ttl = t.ttl and
          t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
          t2.retryTimeoutAt = t.retryTimeoutAt and t2.resumes = t.resumes + awaited
          apply[ps2, ts2 ++ (o2.id -> t2), none]
        }) else
          apply[ps2, ts2, none]
      } else
        apply[ps2, ts2, none]
  }
}

pred resumeOne [awaited, awaiter : Ident, now : Int] {
  resumeOneWith[awaited, awaiter, now, none -> none, none -> none]
}

-- `processCallback`: once the awaited promise is settled, strike the
-- awaiter's callback and resume it.
pred processCallback [now : Int, req : PromiseRegisterCallbackReq] {
  no object[req.awaited] implies keep
  else some o, o2 : Object | {
    readObject[req.awaited, now, o, o2]
    let ps = matP[True, o, o2], ts = matT[True, o, o2] |
      o2.promise.state = Pending implies
        apply[ps, ts, none]
      else req.awaiter in o2.promise.callbacks implies (some p : PromiseObject | {
        sameBirth[o2.promise, p] and sameSettlement[o2.promise, p] and
        p.listeners = o2.promise.listeners and p.callbacks = o2.promise.callbacks - req.awaiter
        resumeOneWith[o2.id, req.awaiter, now, ps ++ (o2.id -> p), ts]
      }) else
        apply[ps, ts, none]
  }
}

-- `processListener`: once the awaited promise is settled, strike the
-- listener and send it `unblock` with the promise's record.
pred processListener [now : Int, req : PromiseRegisterListenerReq] {
  no object[req.awaited] implies keep
  else some o, o2 : Object | {
    readObject[req.awaited, now, o, o2]
    let ps = matP[True, o, o2], ts = matT[True, o, o2] |
      o2.promise.state = Pending implies
        apply[ps, ts, none]
      else req.address in o2.promise.listeners implies
        (some p : PromiseObject, r : PromiseRecord, e : OutboxEntry | {
          sameBirth[o2.promise, p] and sameSettlement[o2.promise, p] and
          p.callbacks = o2.promise.callbacks and p.listeners = o2.promise.listeners - req.address
          promiseToRecord[o2.promise, o2.id, r]
          e.address = req.address and e.message in Unblock and e.message.promise = r
          apply[ps ++ (o2.id -> p), ts, e]
        })
      else
        apply[ps, ts, none]
  }
}

-- `processLeaseTimeout`: an acquired task whose lease has expired, its
-- promise still pending, is released with an immediate retry.
pred processLeaseTimeout [now : Int, req : TaskLeaseTimeoutReq] {
  no object[req.id].task implies keep
  else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let t = o2.task |
      (some t.leaseTimeoutAt and t.state = Acquired and t.leaseTimeoutAt <= now and
       o2.promise.state = Pending) implies (some t2 : TaskObject | {
        t2.state = TaskPending and t2.version = t.version and no t2.pid and no t2.ttl and
        no t2.leaseTimeoutAt and t2.retryTimeoutAt = now and t2.resumes = t.resumes
        apply[none -> none, o2.id -> t2, none]
      }) else
        keep
  }
}

-- `processRetryTimeout`: a pending task whose retry is due, its promise
-- still pending and runnable, is re-armed and its target sent `execute`.
pred processRetryTimeout [now : Int, req : TaskRetryTimeoutReq] {
  no object[req.id].task implies keep
  else some o, o2 : Object | {
    readTaskObject[req.id, now, o, o2]
    let t = o2.task |
      (some t.retryTimeoutAt and t.state = TaskPending and t.retryTimeoutAt <= now and
       o2.promise.state = Pending and o2.promise.type in isRunnable) implies
        (some t2 : TaskObject, e : OutboxEntry | {
          t2.state = t.state and t2.version = t.version and t2.ttl = t.ttl and
          t2.pid = t.pid and t2.leaseTimeoutAt = t.leaseTimeoutAt and
          t2.retryTimeoutAt = plus[now, ServerConfig.retryTimeout] and t2.resumes = t.resumes
          e.address = targetOf[o2.promise.type] and e.message in Execute and
          e.message.taskId = o2.id and e.message.version = t.version
          apply[none -> none, o2.id -> t2, e]
        })
      else
        keep
  }
}

-- Commands. Each trigger has a run showing it acts on a well formed
-- state, and a check that it preserves the catalogue's state properties.

run processPromiseTimeout_ok {
  some now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and processPromiseTimeout[now, req] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps

run processCallback_ok {
  some now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] and
    some storedTasks & state.Suspended and after no storedTasks & state.Suspended
} for 4 but 5 Int, 2 seq, 2 steps

run processListener_ok {
  some now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and processListener[now, req] and State.outbox' != State.outbox
} for 4 but 5 Int, 2 seq, 2 steps

run processLeaseTimeout_ok {
  some now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and processLeaseTimeout[now, req] and State.objects' != State.objects
} for 4 but 5 Int, 2 seq, 2 steps

run processRetryTimeout_ok {
  some now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and processRetryTimeout[now, req] and State.outbox' != State.outbox
} for 4 but 5 Int, 2 seq, 2 steps

check processPromiseTimeout_preserves {
  all now : Int, req : PromiseTimeoutReq |
    stateHolds[now] and processPromiseTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps

check processCallback_preserves {
  all now : Int, req : PromiseRegisterCallbackReq |
    stateHolds[now] and processCallback[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps

check processListener_preserves {
  all now : Int, req : PromiseRegisterListenerReq |
    stateHolds[now] and processListener[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps

check processLeaseTimeout_preserves {
  all now : Int, req : TaskLeaseTimeoutReq |
    stateHolds[now] and processLeaseTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps

check processRetryTimeout_preserves {
  all now : Int, req : TaskRetryTimeoutReq |
    stateHolds[now] and processRetryTimeout[now, req] implies after stateHolds[now]
} for 4 but 5 Int, 2 seq, 2 steps
