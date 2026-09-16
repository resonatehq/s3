module internal

-- The internal triggers, as in `src/spec/02-abstract/internal.lean`, one
-- predicate per trigger, `[now, req]`: at instant `now` on the current
-- state the trigger leaves the next state. The branches are the Lean
-- branches in the Lean order. The promise timeout, the callback and the
-- listener touch what they read, materialising it whatever the machine's
-- `mat`; the lease and retry timeouts view it, writing nothing they did
-- not decide; the schedule trigger reads under the machine's `mat`.

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

-- `processSchedule`: the schedule's occurrences since its next run that
-- are due are fired in order, `createIfAbsent` at each occurrence's
-- instant: the promise expanded from the schedule's template is created
-- when absent, read (and under `mat` materialised, at that instant) when
-- present; then the schedule records the last occurrence and its next
-- run. Two occurrences expanding to one id write the later one, as the
-- fold's last write.
fun expanded [c : Schedule, t : Int] : one Ident { c.expand[t] }

fun dueOccurrences [c : Schedule, now : Int] : set Int {
  { t : c.occurrences[c.nextRunAt] | t <= now }
}

-- The occurrence whose write lands on `i`: the last that expands to it.
fun lastFor [c : Schedule, now : Int, i : Ident] : lone Int {
  max[{ t : dueOccurrences[c, now] | expanded[c, t] = i }]
}

pred firedAt [mat : Bool, c : Schedule, t : Int, o, o2 : Object] {
  no object[expanded[c, t]] implies
    (createPromise[t, expanded[c, t], plus[t, c.promiseTimeout], c.promiseParam,
                   c.promiseType, none, o] and o2 = o)
  else
    readObject[expanded[c, t], t, o, o2]
}

pred processSchedule [mat : Bool, now : Int, req : ScheduleTimeoutReq] {
  no schedule[req.schedule] implies keep
  else let c = schedule[req.schedule], ts = dueOccurrences[c, now] | {
    all t : ts | some o, o2 : Object | firedAt[mat, c, t, o, o2]
    let ps = { i : Ident, p : PromiseObject | some o, o2 : Object |
                 firedAt[mat, c, lastFor[c, now, i], o, o2] and
                 (no object[i] implies i -> p = o.id -> o.promise else i -> p in matP[mat, o, o2]) },
        ts2 = { i : Ident, u : TaskObject | some o, o2 : Object |
                 firedAt[mat, c, lastFor[c, now, i], o, o2] and
                 (no object[i] implies i -> u = o.id -> o.task else i -> u in matT[mat, o, o2]) } |
      some ts implies (some d : Schedule | {
        d.id = c.id and d.cron = c.cron and d.promiseId = c.promiseId and
        d.promiseTimeout = c.promiseTimeout and d.promiseParam = c.promiseParam and
        d.promiseType = c.promiseType and d.createdAt = c.createdAt and
        d.lastRunAt = max[ts] and d.nextRunAt = c.nextCron[max[ts]]
        applyAll[ps, ts2, d, none, none]
      }) else
        applyAll[ps, ts2, none, none, none]
  }
}
