import Veil

/-!
# The concrete machine, in Veil

An experiment: the promise half of the concrete machine of `impl/`, written as a
[Veil](https://veil.dev) module, so that Veil's tools apply to it: `#check_invariants`
proves the invariants below inductive by SMT, `#model_check` enumerates every state of a
small instance, and the `sat` and `unsat` traces are bounded model checking.

What is modelled, and how it corresponds to `impl/`:

- The bucket. A document is `Origin.current`, the latest version of every object, so the
  documents are relations and functions indexed by object: `stored` says the object is in
  its origin's document, `state`, `kind` and `timeoutAt` are its promise. Parts, appends,
  compaction, etags and conditional writes are below this model: in `Concrete.step` the
  condition of a write is read in the same step, so a write is never refused, and
  `adds_invisible` says the layout of a document changes nothing observable.
- Timers. A timer is a blob at `Path.timer ⟨deadline, id, .promiseTimeout⟩`, so `timer i d`
  says that blob is in the bucket. Task timers are not modelled, since tasks are not.
- The outbox. `outbox i a` says an `unblock` message for promise `i` is queued for
  address `a`, keyed as `OutboxKey.notify`, so a second send replaces the first.
- Time. `now` is the instant a step runs at. It is an uninterpreted totally ordered type
  rather than `Nat`, which keeps every query first-order; `tick` moves it forward.
- The sweep. `Concrete.handle` sweeps the origin before every external request and on
  every internal event. Of the five passes, the two that concern promises are here, in
  order: `promiseTimeouts` settles pending promises whose timeout has passed and deletes
  their timers; `listeners` sends to and clears the listeners of settled promises.
- The handlers. `promiseCreate`, `promiseSettle`, `promiseGet` and
  `promiseRegisterListener` follow `impl/external.lean` line by line, on the swept view,
  with the reply dropped. Values, parameters, `createdAt`, `settledAt`, callbacks and tasks
  are dropped; `OType.runnable` keeps no target.
- The internal event. `Concrete.step` runs a timer only if its blob is in the bucket and
  its deadline has passed, and then only sweeps: that is `promiseTimeout`.

The relation to `impl/` is by hand. Nothing here is proved about `Concrete.step`.
-/

veil module S3Promises

type ident
type origin
type address
type time
instantiate tord : TotalOrderWithMinimum time

/-- `Ident.origin`: the document an object lives in. -/
immutable function originOf : ident → origin

enum pstate = {pending, resolved, rejected, rejectedCanceled, rejectedTimedout}
enum ptype = {internal, deadline, external, runnable}

/-- The documents: the view of every origin, one object per `ident`. -/
relation stored (i : ident) : Bool
function state : ident → pstate
function kind : ident → ptype
function timeoutAt : ident → time
relation listener (i : ident) (a : address) : Bool

/-- The timer blobs: `timer i d` is `Path.timer ⟨d, i, .promiseTimeout⟩` in the bucket. -/
relation timer (i : ident) (d : time) : Bool

/-- The outbox, keyed by promise and address. -/
relation outbox (i : ident) (a : address) : Bool

/-- The instant of the current step. -/
individual now : time

#gen_state

after_init {
  stored I := false
  state I := pending
  kind I := internal
  timeoutAt I := tord.zero
  listener I A := false
  timer I D := false
  outbox I A := false
  now := tord.zero
}

/-- A stored promise that `PromiseObject.project` would settle: pending, timeout passed. -/
ghost relation timedOut (i : ident) :=
  stored i ∧ state i = pending ∧ tord.le (timeoutAt i) now

/-- `Concrete.sweep`, restricted to promises: the `promiseTimeouts` pass, then the
`listeners` pass on the view it leaves. Each pass reads the state left by the one before,
as `Commands.doc` gives the next pass the objects added so far. -/
procedure sweep (o : origin) {
  -- promiseTimeouts: delete the timers of timed-out promises, then settle them
  timer I D := if originOf I = o ∧ timedOut I then false else timer I D
  state I := if originOf I = o ∧ timedOut I then
               (if kind I = deadline then resolved else rejectedTimedout)
             else state I
  -- listeners: notify and clear the listeners of settled promises
  outbox I A := if originOf I = o ∧ stored I ∧ state I ≠ pending ∧ listener I A then true
                else outbox I A
  listener I A := if originOf I = o ∧ stored I ∧ state I ≠ pending then false
                  else listener I A
}

/-- `Concrete.promiseCreate`. An existing promise is returned as is. A new one is pending
with its timer armed if its timeout is in the future, unless it is internal, which is
never awaited and never armed; otherwise it is created already settled, with no timer. -/
action promiseCreate (i : ident) (k : ptype) (t : time) {
  sweep (originOf i)
  if ¬ stored i then
    stored i := true
    kind i := k
    timeoutAt i := t
    if tord.lt now t then
      state i := pending
      if k ≠ internal then
        timer i t := true
    else
      state i := if k = deadline then resolved else rejectedTimedout
}

/-- `Concrete.promiseSettle`. A settable state settles a pending promise and deletes its
timers; anything else, a 400 or a promise already settled, changes nothing but the sweep. -/
action promiseSettle (i : ident) (s : pstate) {
  sweep (originOf i)
  if (s = resolved ∨ s = rejected ∨ s = rejectedCanceled) ∧ stored i ∧ state i = pending then
    state i := s
    timer i D := false
}

/-- `Concrete.promiseGet`. A read is a request, so it sweeps. -/
action promiseGet (i : ident) {
  sweep (originOf i)
}

/-- `Concrete.promiseRegisterListener`. Only an awaitable, pending promise takes a listener. -/
action promiseRegisterListener (i : ident) (a : address) {
  sweep (originOf i)
  if stored i ∧ kind i ≠ internal ∧ state i = pending then
    listener i a := true
}

/-- `Concrete.step` on `Event.internal`: a timer whose blob is present and whose deadline
has passed sweeps its origin. The sweep, not the timer, settles the promise. -/
action promiseTimeout (i : ident) (d : time) {
  require timer i d
  require tord.le d now
  sweep (originOf i)
}

/-- Time never runs backwards. -/
action tick (t : time) {
  require tord.lt now t
  now := t
}

/-- `armed` from the README: every armed timeout timer belongs to a stored, non-internal
promise. -/
safety [armed] timer I D → stored I ∧ kind I ≠ internal
/-- An armed timer's promise is pending, and the timer's deadline is its timeout. -/
invariant [armed_pending] timer I D → state I = pending ∧ D = timeoutAt I
/-- Every pending, awaitable promise has its timer armed. -/
invariant [pending_armed] stored I ∧ state I = pending ∧ kind I ≠ internal → timer I (timeoutAt I)
/-- Only settled promises are notified. -/
invariant [notified_settled] outbox I A → stored I ∧ state I ≠ pending
/-- Only awaitable promises have listeners. -/
invariant [listener_awaitable] listener I A → stored I ∧ kind I ≠ internal

#gen_spec

/- Every reachable state of a small instance: three objects over two origins, one address
and three instants. -/
#model_check { ident := Fin 3, origin := Fin 2, address := Fin 1, time := Fin 3 }
  { originOf := fun i => ⟨i.val % 2, by omega⟩ }

/- The assumptions are satisfiable. -/
sat trace [initial_state] { }

/- Settlement is lazy: a promise can sit in the bucket pending past its timeout, until a
request or its timer sweeps its origin. -/
sat trace [lazy_timeout] {
  any 2 actions
  assert (∃ i, stored i ∧ state i = pending ∧ tord.le (timeoutAt i) now)
}

/- A read sweeps: `promiseGet` after the timeout is what notifies the listener. -/
sat trace [notified] {
  promiseCreate
  promiseRegisterListener
  tick
  promiseGet
  assert (∃ i a, outbox i a)
}

/- No timer is ever orphaned within two steps, for any instance. -/
unsat trace [no_orphan_timer] {
  any 2 actions
  assert (∃ i d, timer i d ∧ ¬ stored i)
}

/- The invariants above are inductive: they hold initially and every action preserves
them, for all instances. -/
#check_invariants

end S3Promises
