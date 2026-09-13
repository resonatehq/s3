module state

-- The abstract machine's state, as in `src/spec/02-abstract/state.lean`,
-- without schedules. A `State` is the objects it stores and its outbox;
-- the lookups are the Lean lookups, `find?` on a list becoming a
-- comprehension over a set.

open types

sig State {
  objects : set Object,
  outbox  : set OutboxEntry
}

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
