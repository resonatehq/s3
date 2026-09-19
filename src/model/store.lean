import Veil

/-!
# Servers and the store as separate actors

The second experiment. `concrete.lean` folds the store into every action: a request
reads, computes and writes in one step, as `Concrete.step` does, and a write is never
refused. Here the bucket and the servers are separate actors, and a request is three
S3 calls, each its own step, interleaved freely with the other servers':

- `readCreate`, `readSettle`, `readTimer`: GET the origin's document. The server keeps
  a snapshot of the document and the instant of the request. The etag is the hash of the
  blob and the hasher is injective, so "the etag still matches" means "the document's
  content is unchanged", and that is the condition `intact` checks. A document never
  returns to an earlier content, objects are only added and only settle, so content
  equality is version equality.
- `arm`: PUT the timers the handler will arm, computed on the snapshot. This is the
  first group in `Commands.effects`, unconditional and before the document write; only
  `promiseCreate` arms a promise timer.
- `writeCreate`, `writeSettle`, `writeSweep`: the conditional PUT of the document, and
  after it the deletes. If the origin is intact the server runs the sweep and the handler
  on the document, which equals its snapshot, and `Concrete.step` would have produced
  the same commands; otherwise the write is refused and the server drops its snapshot,
  which is what `attempt` returns before `runCached` reads again. Nothing else is undone.

Handlers are `promiseCreate` and `promiseSettle`, the sweep is the `promiseTimeouts`
pass, and `readTimer` is the internal event; listeners and the outbox are left out.

What holds with any number of servers is `pending_armed`: every pending awaitable
promise has its timer, so no timeout is ever missed. What does not hold is `armed` from
the README, or `armed_pending` of `concrete.lean`: a refused attempt leaves its timers
in the bucket, for an object the attempt never wrote. `stray_timer` is that trace. Such
a timer fires, and `Concrete.step` only sweeps on a timer, and the sweep deletes the
timers of the objects it settles; a timer without an object is never deleted and fires
at every instant from its deadline on. The Lean proofs do not see this: `armed` is
stated for the single-writer trace, and `runCached_any` relates the documents and the
outbox of the cached machine to the uncached one, not the timers.
-/

set_option maxRecDepth 100000

veil module S3Store

type ident
type origin
type time
type server
instantiate tord : TotalOrderWithMinimum time

immutable function originOf : ident → origin

enum pstate = {pending, resolved, rejected, rejectedCanceled, rejectedTimedout}
enum ptype = {internal, deadline, external, runnable}
enum sphase = {idle, holding, armed}
enum rkind = {create, settle, sweep}

-- the bucket: the documents
relation stored (i : ident) : Bool
function state : ident → pstate
function kind : ident → ptype
function timeoutAt : ident → time
-- the bucket: the timer blobs
relation timer (i : ident) (d : time) : Bool
-- the clock
individual now : time

-- the servers
function phase : server → sphase
function reqKind : server → rkind
function reqId : server → ident
function reqType : server → ptype
function reqTime : server → time
function reqState : server → pstate
function snapOrigin : server → origin
function snapNow : server → time
relation snapStored (s : server) (i : ident) : Bool
function snapState : server → ident → pstate
function snapKind : server → ident → ptype
function snapTimeoutAt : server → ident → time
relation refused (s : server) : Bool

#gen_state

after_init {
  stored I := false
  state I := pending
  kind I := internal
  timeoutAt I := tord.zero
  timer I D := false
  now := tord.zero
  phase S := idle
  reqKind S := sweep
  reqType S := internal
  reqTime S := tord.zero
  reqState S := pending
  snapNow S := tord.zero
  snapStored S I := false
  snapState S I := pending
  snapKind S I := internal
  snapTimeoutAt S I := tord.zero
  refused S := false
}

ghost relation timedOutAt (i : ident) (t : time) :=
  stored i ∧ state i = pending ∧ tord.le (timeoutAt i) t

ghost relation intact (s : server) :=
  ∀ I, originOf I = snapOrigin s →
    stored I = snapStored s I ∧ state I = snapState s I ∧
    kind I = snapKind s I ∧ timeoutAt I = snapTimeoutAt s I

ghost relation settable (s : server) :=
  reqState s = resolved ∨ reqState s = rejected ∨ reqState s = rejectedCanceled

procedure snapshot (s : server) (o : origin) {
  snapOrigin s := o
  snapNow s := now
  snapStored s I := stored I
  snapState s I := state I
  snapKind s I := kind I
  snapTimeoutAt s I := timeoutAt I
  phase s := holding
  refused s := false
}

action readCreate (s : server) (i : ident) (k : ptype) (t : time) {
  require phase s = idle
  snapshot s (originOf i)
  reqKind s := create
  reqId s := i
  reqType s := k
  reqTime s := t
}

action readSettle (s : server) (i : ident) (ps : pstate) {
  require phase s = idle
  snapshot s (originOf i)
  reqKind s := settle
  reqId s := i
  reqState s := ps
}

action readTimer (s : server) (i : ident) (d : time) {
  require phase s = idle
  require timer i d ∧ tord.le d now
  snapshot s (originOf i)
  reqKind s := sweep
  reqId s := i
}

action arm (s : server) {
  require phase s = holding
  if reqKind s = create ∧ ¬ snapStored s (reqId s) ∧ tord.lt (snapNow s) (reqTime s) ∧ reqType s ≠ internal then
    timer (reqId s) (reqTime s) := true
  phase s := armed
}

procedure sweepDoc (o : origin) (t0 : time) {
  timer I D := if originOf I = o ∧ timedOutAt I t0 ∧ D = timeoutAt I then false else timer I D
  state I := if originOf I = o ∧ timedOutAt I t0 then
               (if kind I = deadline then resolved else rejectedTimedout)
             else state I
}

action writeCreate (s : server) {
  require phase s = armed ∧ reqKind s = create
  phase s := idle
  if intact s then
    sweepDoc (snapOrigin s) (snapNow s)
    let i := reqId s
    if ¬ stored i then
      stored i := true
      kind i := reqType s
      timeoutAt i := reqTime s
      state i := if tord.lt (snapNow s) (reqTime s) then pending
                 else (if reqType s = deadline then resolved else rejectedTimedout)
  else
    refused s := true
}

action writeSettle (s : server) {
  require phase s = armed ∧ reqKind s = settle
  phase s := idle
  if intact s then
    sweepDoc (snapOrigin s) (snapNow s)
    let i := reqId s
    if settable s ∧ stored i ∧ state i = pending then
      state i := reqState s
      timer i (timeoutAt i) := false
  else
    refused s := true
}

action writeSweep (s : server) {
  require phase s = armed ∧ reqKind s = sweep
  phase s := idle
  if intact s then
    sweepDoc (snapOrigin s) (snapNow s)
  else
    refused s := true
}

action tick (t : time) {
  require tord.lt now t
  now := t
}

safety [pending_armed] stored I ∧ state I = pending ∧ kind I ≠ internal → timer I (timeoutAt I)
invariant [snapshot_stored] snapStored S I → stored I
invariant [armed_before_write]
  phase S = armed ∧ reqKind S = create ∧ ¬ stored (reqId S) ∧ tord.lt (snapNow S) (reqTime S) ∧ reqType S ≠ internal
    → timer (reqId S) (reqTime S)

#gen_spec

-- Every reachable state of two servers over one object. Two objects are beyond
-- exhaustive search, each server carrying a snapshot; `#simulate` walks that instance.
#model_check { server := Fin 2, ident := Fin 1, origin := Fin 1, time := Fin 2 }
  { originOf := fun _ => 0 }

#simulate { server := Fin 2, ident := Fin 2, origin := Fin 1, time := Fin 3 }
  { originOf := fun _ => 0 } (numTraces := 3000) (maxSteps := 40) (seed := 7)

sat trace [initial_state] { }

-- Two servers create in the same origin; the second write is refused.
sat trace [refused_write] {
  readCreate
  readCreate
  arm
  writeCreate
  arm
  writeCreate
  assert (∃ s, refused s)
}

-- The refused attempt's timer stays in the bucket, for an object that does not exist.
sat trace [stray_timer] {
  readCreate
  readCreate
  arm
  writeCreate
  arm
  writeCreate
  assert (∃ i d, timer i d ∧ ¬ stored i)
}

#check_invariants

end S3Store
