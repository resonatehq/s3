# Resonate on S3

The Resonate protocol, implemented on a compare-and-swap object store, and
the proof that the implementation does what the specification says.

Three parts under `src/`, and the directory layout says so:

```
src/types.lean    the protocol layer — records, requests, responses, tags, messages
src/spec/         the specification: the abstract machine and its catalogue
src/impl/         the implementation on S3, and its refinement proof
```

`types.lean` sits beside `spec/` and `impl/` because it is the one thing
both halves must agree on. The specification says what a server answers
to each request; the implementation answers it; neither may redefine the
alphabet. It is the protocol's `01`; the specification's directories
continue the numbering.

## The specification (`src/spec/`)

A copy of the protocol's Lean specification: an executable **abstract
machine** — a state, a set of effects, and one transition per request —
together with a catalogue of properties every run of it satisfies.

| | |
|---|---|
| `src/types.lean` | the protocol layer: records, requests, responses, tag semantics, the message vocabulary |
| `src/spec/02-abstract` | the machine: `state`, `external` (the 21 handlers), `internal` (the 6 triggers), `system` (the alphabet `Event`/`Reply`, `step`, `exec`, `Trace`, `Valid`), `properties` (the catalogue) |
| `src/spec/03-theorems` | what is proved about it, and the harnesses that evaluate it |

The machine writes every step in a monad `H`: a reader of the state, a
writer of `Effect`s, folded onto the state at the end — one step is one
transaction. The specification's code is unchanged; its former
`01-protocol` (types and validation) is now `types.lean`, and its
comments were removed along with everyone else's.

## The implementation (`src/impl/`)

Read the files in this order.

| file | what it defines |
|---|---|
| `src/impl/cas.lean` | **The CAS machine.** A versioned key–value store with `get`, `put`, `del`, and a condition on every write: `any`, `absent` (`If-None-Match: *`), or `version v` (`If-Match: etag`). A write whose condition fails is *rejected* and changes nothing. Versions are drawn from a counter that never repeats, so a version seen once is never seen again at a different value (`put_version_fresh`). |
| `src/impl/origin.lean` | **The document.** `Origin` is one document per origin holding every promise and task of that origin. `Tx` is a transaction against it: reads see the snapshot, writes accumulate in a fresh copy, messages queue up. `Tx.commit` turns a finished transaction into a `Commit`: the deadlines to **arm** (present after, absent before), the document to **put**, the deadlines to **del** (present before, absent after), and the messages to **send**. |
| `src/impl/handlers.lean` | **The handlers.** The 21 request handlers and the 6 trigger handlers of the protocol, written as plain functions `Origin → Tx → Response × Tx` — no monad. `Handle.external` and `Handle.trigger` run one against a snapshot and commit it, so every handler is a function from a document to a `Commit`: arm these timers, put this document, delete those timers, send these messages. |
| `src/impl/doc.lean` | **The key space and the world.** `Key.origin o` holds the document, `Key.timer dl o` a deadline; the world is the bucket plus the wire (the messages handed to the transport). |
| `src/impl/monad.lean` | **The monad `C`.** Same shape as the specification's `H`, different vocabulary: it reads one snapshot — the document a transaction fetched, with its version — and it emits `putOrigin` (conditional on that version), `armTimer`, `delTimer`, `send`. Effects are performed in order; a refused `putOrigin` stops the transaction there. |
| `src/impl/kernel.lean` | **The kernel.** `decide` runs the handler for the request, then drains the document in three phases — expired deadlines, obligations of settled promises, tasks due for re-dispatch — each a list of triggers run through `Handle.trigger`. `transact` emits the resulting `Commit` in the shell's order: arm the new timers, put the document, delete the timers the handler dropped, send. |
| `src/impl/system.lean` | **The system.** Transactions `begin` (snapshot) and `commit` (decide, CAS-write) in any interleaving, or `stutter`. A sweep is a transaction that names the timer that fired, and it may `begin` only while that timer key is stored and its deadline has passed: the machine never takes an internal step on its own. `run` collects the observations of a finite run: every answered request, with its answer and instant. |
| `src/impl/equiv.lean` | **Handlers against the specification.** `liftH` maps the specification's `H` computations onto `Tx`, and it is a monad morphism. Every handler and every trigger is shown equal to the specification's under it (`promiseCreate_eq`, …, `retryTimeout_eq`); `external_eq` and `trigger_eq` sum this up as: the impl's `Commit` has the same response, the same document and the same sends as one specification step. |
| `src/impl/frame.lean` | **The frame lemmas.** For every specification handler and trigger: two environments that agree on origin `o` get the same answer and effects (`Cong`), and every effect is a write at an id of origin `o` or a message (`LocAt`). |
| `src/impl/apply.lean` | **Effects through lookups.** The specification's effects restated as lookup transformers; congruence on one origin, frame on every other, and the outbox as a fold of sends. |
| `src/impl/commit.lean` | **The commit, performed.** The closed form of a transaction's effects, and the store invariants: `SInv` (versions are fresh), `TxnInv` (an in-flight snapshot is either the stored document or at a version that has moved), `TimerInv` (every deadline a document mentions has its timer key). |
| `src/impl/refinement.lean` | **The theorem.** |
| `src/impl/trace.lean` | **Concrete traces.** `Concrete.Frame`, `Trace`, `Valid`, mirroring the specification's; the timer properties as statements about every valid trace. |
| `src/impl/demo.lean` | An executable scenario and its linearization; `lake build impl.demo` prints it. |

### The theorem

```lean
theorem refines (w : List (Impl.Step × Nat)) :
    obsOf (linearize w State.init)
        (Abstract.exec true (linearize w State.init) ServerState.init).1 =
      (Impl.run w State.init).1 ∧
    Rel (Impl.run w State.init).2.world
        (Abstract.exec true (linearize w State.init) ServerState.init).2
```

Every observable behaviour of the implementation is an observable
behaviour of the specification. For every finite run of the implementation
— transactions beginning and committing in any interleaving, sweeps firing
whenever, the CAS accepting some commits and refusing others — the
**linearization** is a run of the specification from its initial state
whose answered requests are exactly the implementation's, in order, at the
same instants, and whose final state agrees with the implementation's
final world on every lookup. The witness is constructed, not merely shown
to exist: each accepted commit becomes the specification's external event
followed by the internal events the sweep performed; a refused commit, a
`begin`, a `stutter` become nothing (`linearize_nows_pairwise` says the
instants stay monotone, which is what `Abstract.Valid` asks of a trace).
The implementation materialises a task's promise on every read, so the
specification runs with `mat := true`.

The proof is a forward simulation in four layers:

1. **The impl's handler is the specification's handler**
   (`external_eq`, `trigger_eq`). A `Tx` is what the specification's
   `H` looks like when its reads are taken from a snapshot and its writes
   replayed onto a copy; `liftH` says so, and each handler is checked
   against its specification twin through it.
2. **One step against one document is that step against the whole
   state** (`specStep_sim`). The frame lemmas say the handler cannot tell
   the two apart; the lookup lemmas say the writes land the same way.
3. **An accepted commit decided against the current document**
   (`accepted_snapshot`). Its write was conditioned on the version the
   snapshot was read at; versions never recur; so the version still being
   there means the document still is. A refused commit moved no document
   and sent nothing (`commit_rejected`) — only the timers it armed first
   landed, and no lookup sees them. `commit_accepted_is_atomic` states this
   as an equation: an accepted commit *is* the atomic read-modify-write of
   the current document, whatever ran between its `begin` and `commit`.
4. **The world after an accepted commit** is the old world with one
   document replaced and the sends appended to the wire
   (`commit_accepted`), which is the shape layers 1 and 2 produce.

### Timers

The specification has no scheduler: an internal event may occur at any
instant, or never. The implementation is stricter, because the real one
is woken by an external timer service and cannot act on its own. Two
theorems in `trace.lean` say so, for every valid concrete trace from the
initial state:

```lean
theorem Valid.sweep (hv : Valid tr) (t : Nat)
    (he : (tr t).event = .begin o (.sweep fired))
    (hne : (tr (t + 1)).state ≠ (tr t).state) :
    ((tr t).state.world.store.get (.timer fired o)).isSome = true ∧ fired ≤ (tr t).now

theorem Valid.timers (hv : Valid tr) (h0 : (tr 0).state = State.init) (t : Nat) :
    TimerInv (tr t).state.world
```

The first: a sweep that changes anything was admitted while its timer
was stored and due. Nothing internal happens without a timer. The second:
every deadline any document mentions has its timer key in the bucket, so
nothing that should be woken is left without a timer. It holds because
timers are armed before the document that mentions them is written, and
deleted only after a successful write of a document that no longer
mentions them. The shell never deletes a timer on its own, the fired one
included: a timer goes when the handler's commit drops its deadline, and
otherwise it stays armed and fires again. A refused commit may leave a
timer behind that no document mentions; the sweeps it wakes find nothing
due and change nothing.

Requests still drain: a commit of a request runs every trigger due on its
document. That is a reaction to the request, not a spontaneous step, and
the specification permits it since each drained trigger is due at that
instant.

There is no `sorry` in `src/impl/`. The relation between a world and a
specification state is by lookup, not equality: the specification's object
list is in the order its own writes left it, the bucket's documents in the
order it lists them, and no answer this implementation gives depends on
the order.

### What the implementation is, and is not

It follows the S3 backend of `resonatehq/resonate` (`crates/resonate-server-blob`):
one CAS'd object per origin, timer keys that are written before the
document that arms them, the kernel as a pure decision applied by a shell,
sends strictly after the commit. Where it differs, it says so:

- **Every commit drains.** The Rust `handle` settles only the promises a
  request names and leaves the rest to its tick. Sweeping the whole document
  on every commit is the simpler invariant, and each swept step is one the
  specification could have taken anyway.
- **Sweeps are timer-driven.** A sweep names the timer that fired and is
  admitted only while that key is stored and due, as the backend's timer
  daemon would wake it. The machine has no other source of internal steps.
- **One timer key per deadline.** A deadline is armed when the document
  after a commit mentions it and the one before did not, and deleted in
  the opposite case. Firing does not delete a timer; only a handler that
  drops the deadline does.
- **Out of scope**: schedules (cross-origin, their own objects in the S3
  backend), searches (501 in the specification), and heartbeats spanning
  origins (refused by the backend's validators). `Request.origin?` says
  exactly which requests are served; the others open no transaction.
- **Not modelled**: crashes mid-transaction beyond a refused CAS, the codec,
  retries of `Conflict` responses, and the promptness of the timer daemon —
  a due timer may be picked up late or not at all; that it is eventually
  picked up is a liveness assumption on the daemon, not a theorem here.

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
