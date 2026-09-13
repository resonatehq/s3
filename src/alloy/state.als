module state

-- The abstract machine's state, as in `src/spec/02-abstract/state.lean`,
-- without schedules. A `State` is the objects it stores and its outbox;
-- the lookups are the Lean lookups, `find?` on a list becoming a
-- comprehension over a set.

open util/boolean
open types

sig State {
  objects : set Object,
  outbox  : set OutboxEntry
}

fact StateValue { no disj a, b : State | a.objects = b.objects and a.outbox = b.outbox }

-- `State.init`
pred init [s : State] { no s.objects and no s.outbox }

-- `State.promises`
fun promises [s : State] : set PromiseObject { s.objects.promise }

-- `State.tasks`
fun tasks [s : State] : set TaskObject { s.objects.task }

-- `s.objects.find? (·.id == id)`
fun object [s : State, i : Ident] : set Object { { o : s.objects | o.id = i } }

-- `State.promise?`
fun promise [s : State, i : Ident] : set PromiseObject { object[s, i].promise }

-- `State.task?`
fun task [s : State, i : Ident] : set TaskObject { object[s, i].task }

-- `State.hasTask`
pred hasTask [s : State, i : Ident] { some task[s, i] }

-- Effects. A step writes in the monad `H`: it reads the state it started
-- from throughout, and its effects are folded onto that state at the end,
-- `applyAll`. Every effect is keyed, `setPromise` and `setTask` by the
-- object's id, `setMessage` by the outbox key, so the fold is determined
-- by the last effect on each key: a step's writes are three keyed maps,
-- and a later effect on a key overrides an earlier one, `++`.
--
-- `apply` is `applyAll`: `setPromise id p` replaces the promise of the
-- object under `id`, creating the object when absent; `setTask id t`
-- replaces the task of the object under `id`, if there is one, and a
-- step only ever sets the task of an object it read or created;
-- `setMessage a m` replaces the entry with the same key.
pred apply [s : State, ps : Ident -> PromiseObject, ts : Ident -> TaskObject,
            ms : set OutboxEntry, s2 : State] {
  let ids = s.objects.id + ps.PromiseObject | {
    s2.objects = { o : Object |
      o.id in ids and
      o.promise = ((o.id in ps.PromiseObject) implies o.id.ps else promise[s, o.id]) and
      o.task = ((o.id in ts.TaskObject) implies o.id.ts else task[s, o.id]) }
    ids in s2.objects.id
  }
  s2.outbox = ms + { e : s.outbox | no m : ms | sameKey[e, m] }
}

-- No effects.
pred keep [s, s2 : State] { apply[s, none -> none, none -> none, none, s2] }

-- Reads. `readObject id now` is the object stored under `id` projected to
-- `now`: `o` as stored, `o2` as read. Under `mat` the read also writes
-- the projection back where it changed a state, `materialise`; `matP`
-- and `matT` are those writes. `readTaskObject` is the read of an object
-- that has a task, and reads nothing otherwise.
pred readObject [s : State, i : Ident, now : Int, o, o2 : Object] {
  o in object[s, i] and projectObject[o, now, o2]
}

pred readTaskObject [s : State, i : Ident, now : Int, o, o2 : Object] {
  readObject[s, i, now, o, o2] and some o.task
}

fun matP [mat : Bool, o, o2 : Object] : Ident -> PromiseObject {
  (mat = True and o2.promise.state != o.promise.state)
    implies o.id -> o2.promise else none -> none
}

fun matT [mat : Bool, o, o2 : Object] : Ident -> TaskObject {
  (mat = True and some o.task and o2.task.state != o.task.state)
    implies o.id -> o2.task else none -> none
}

-- `createPromise req now`: `o` is the object it creates under `req.id`, a
-- pending promise with a pending task when runnable, or, when the timeout
-- has passed, a settled promise with a fulfilled task.
fun due [req : PromiseCreateReq, now : Int] : one Int {
  some req.delay implies max[req.delay + now] else now
}

pred createPromise [now : Int, req : PromiseCreateReq, o : Object] {
  o.id = req.id
  let p = o.promise, t = o.task | {
    p.param = req.param and emptyValue[p.value] and p.type = req.type and
    p.timeoutAt = req.timeoutAt and no p.callbacks and no p.listeners
    req.timeoutAt > now implies {
      p.state = Pending and p.createdAt = now and no p.settledAt
      req.type in isRunnable implies {
        t.state = TaskPending and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and t.retryTimeoutAt = due[req, now] and no t.resumes
      } else no t
    } else {
      p.state = (req.type = Deadline implies Resolved else RejectedTimedout)
      p.createdAt = req.timeoutAt and p.settledAt = req.timeoutAt
      req.type in isRunnable implies {
        t.state = Fulfilled and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and no t.retryTimeoutAt and no t.resumes
      } else no t
    }
  }
}

-- `setSettled o p`, applied: the writes so far, then the promise `p`
-- under `o.id`, then, when `p` is settled and `o` has a task not yet
-- fulfilled, that task fulfilled.
pred setSettled [s : State, ps : Ident -> PromiseObject, ts : Ident -> TaskObject,
                 o : Object, p : PromiseObject, s2 : State] {
  (p.state != Pending and some o.task and o.task.state != Fulfilled) implies
    (some u : TaskObject | fulfillTask[o.task, u] and
      apply[s, ps ++ (o.id -> p), ts ++ (o.id -> u), none, s2])
  else
    apply[s, ps ++ (o.id -> p), ts, none, s2]
}
