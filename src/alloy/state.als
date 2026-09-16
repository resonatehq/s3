module state

-- The abstract machine's state, as in `src/spec/02-abstract/state.lean`.
-- The `State` is the objects it stores, its schedules and its outbox,
-- all mutable: `State.objects` is the store at the current instant,
-- `State.objects'` at the next. The lookups are the Lean lookups on the
-- current instant, `find?` on a list becoming a comprehension over a set.

open util/boolean
open types

one sig State {
  var objects   : set Object,
  var schedules : set Schedule,
  var outbox    : set OutboxEntry
}

-- `State.init`
pred init { no State.objects and no State.schedules and no State.outbox }

-- `ServerConfig`: the retry timeout of `Env.config`, one for the run.
one sig ServerConfig {
  retryTimeout : one Int
} { retryTimeout >= 0 }

-- `State.promises`
fun storedPromises : set PromiseObject { State.objects.promise }

-- `State.tasks`
fun storedTasks : set TaskObject { State.objects.task }

-- `State.objects.find? (·.id == id)`
fun object [i : Ident] : set Object { { o : State.objects | o.id = i } }

-- `State.promise?`
fun promise [i : Ident] : set PromiseObject { object[i].promise }

-- `State.task?`
fun task [i : Ident] : set TaskObject { object[i].task }

-- `State.hasTask`
pred hasTask [i : Ident] { some task[i] }

-- `getSchedule`
fun schedule [i : Ident] : set Schedule { { c : State.schedules | c.id = i } }

-- Effects. A step writes in the monad `H`: it reads the state it started
-- from throughout, and its effects are folded onto that state at the end,
-- `applyAll`. Every effect is keyed, `setPromise` and `setTask` by the
-- object's id, `setSchedule` and `delSchedule` by the schedule's,
-- `setMessage` by the outbox key, so the fold is determined by the last
-- effect on each key: a step's writes are keyed maps, and a later effect
-- on a key overrides an earlier one, `++`.
--
-- `applyAll`, from the current instant to the next: `setPromise id p`
-- replaces the promise of the object under `id`, creating the object
-- when absent; `setTask id t` replaces the task of the object under
-- `id`, if there is one, and a step only ever sets the task of an object
-- it read or created; `setSchedule c` replaces the schedule under `c.id`
-- and `delSchedule id` removes it, and no step does both to one id;
-- `setMessage a m` replaces the entry with the same key. `apply` is the
-- common case, no schedule writes.
pred applyAll [ps : Ident -> PromiseObject, ts : Ident -> TaskObject,
               ss : set Schedule, ds : set Ident, ms : set OutboxEntry] {
  State.schedules' = ss + { c : State.schedules | c.id not in ss.id + ds }
  applyObjects[ps, ts]
  State.outbox' = ms + { e : State.outbox | no m : ms | sameKey[e, m] }
}

pred apply [ps : Ident -> PromiseObject, ts : Ident -> TaskObject,
            ms : set OutboxEntry] {
  State.schedules' = State.schedules
  applyObjects[ps, ts]
  State.outbox' = ms + { e : State.outbox | no m : ms | sameKey[e, m] }
}

pred applyObjects [ps : Ident -> PromiseObject, ts : Ident -> TaskObject] {
  let ids = State.objects.id + ps.PromiseObject | {
    State.objects' = { o : Object |
      o.id in ids and
      o.promise = ((o.id in ps.PromiseObject) implies o.id.ps else promise[o.id]) and
      o.task = ((o.id in ts.TaskObject) implies o.id.ts else task[o.id]) }
    ids in State.objects'.id
  }
}

-- No effects: `applyAll s [] = s`.
pred keep {
  State.objects' = State.objects and State.schedules' = State.schedules and
  State.outbox' = State.outbox
}

-- Reads. `readObject id now` is the object stored under `id` projected to
-- `now`: `o` as stored, `o2` as read. Under `mat` the read also writes
-- the projection back where it changed a state, `materialise`; `matP`
-- and `matT` are those writes. `readTaskObject` is the read of an object
-- that has a task, and reads nothing otherwise.
pred readObject [i : Ident, now : Int, o, o2 : Object] {
  o in object[i] and projectObject[o, now, o2]
}

pred readTaskObject [i : Ident, now : Int, o, o2 : Object] {
  readObject[i, now, o, o2] and some o.task
}

fun matP [mat : Bool, o, o2 : Object] : Ident -> PromiseObject {
  (mat = True and o2.promise.state != o.promise.state)
    implies o.id -> o2.promise else none -> none
}

fun matT [mat : Bool, o, o2 : Object] : Ident -> TaskObject {
  (mat = True and some o.task and o2.task.state != o.task.state)
    implies o.id -> o2.task else none -> none
}

-- `createPromise req now`, `req` given field by field: `o` is the object
-- it creates under `i`, a pending promise with a pending task when
-- runnable, or, when the timeout has passed, a settled promise with a
-- fulfilled task.
fun due [delay : set Int, now : Int] : one Int {
  some delay implies max[delay + now] else now
}

pred createPromise [now : Int, i : Ident, deadline : Int, prm : Value, kind : OType,
                    delay : set Int, o : Object] {
  o.id = i
  let p = o.promise, t = o.task | {
    p.param = prm and emptyValue[p.value] and p.type = kind and
    p.timeoutAt = deadline and no p.callbacks and no p.listeners
    deadline > now implies {
      p.state = Pending and p.createdAt = now and no p.settledAt
      kind in isRunnable implies {
        t.state = TaskPending and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and t.retryTimeoutAt = due[delay, now] and no t.resumes
      } else no t
    } else {
      p.state = (kind = Deadline implies Resolved else RejectedTimedout)
      p.createdAt = deadline and p.settledAt = deadline
      kind in isRunnable implies {
        t.state = Fulfilled and t.version = 0 and no t.ttl and no t.pid and
        no t.leaseTimeoutAt and no t.retryTimeoutAt and no t.resumes
      } else no t
    }
  }
}

-- `setSettled o p`, applied: the writes so far, then the promise `p`
-- under `o.id`, then, when `p` is settled and `o` has a task not yet
-- fulfilled, that task fulfilled.
pred setSettled [ps : Ident -> PromiseObject, ts : Ident -> TaskObject,
                 o : Object, p : PromiseObject] {
  (p.state != Pending and some o.task and o.task.state != Fulfilled) implies
    (some u : TaskObject | fulfillTask[o.task, u] and
      apply[ps ++ (o.id -> p), ts ++ (o.id -> u), none])
  else
    apply[ps ++ (o.id -> p), ts, none]
}
