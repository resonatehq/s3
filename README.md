# Resonate on S3

The Resonate protocol, implemented on a compare-and-swap object store, and
the proof that the implementation does what the specification says.

Three parts, and the directory layout says so:

```
types.lean        the wire surface — records, requests, responses
spec/             the specification: the abstract machine and its catalogue
impl/             the implementation on S3, and its refinement proof
```

`types.lean` is at the top level because it is the one thing both halves
must agree on. The specification says what a server answers to each
request; the implementation answers it; neither may redefine the alphabet.

## The specification (`spec/`)

A copy of the protocol's Lean specification: an executable **abstract
machine** — a state, a set of effects, and one transition per request —
together with a catalogue of properties every run of it satisfies.

| | |
|---|---|
| `spec/01-protocol` | validation, tags, the message vocabulary (imports `types`) |
| `spec/02-abstract` | the machine: `state`, `external` (the 21 handlers), `internal` (the 6 background steps), `system` (the alphabet, `runFin`, `Valid`), `properties` (the catalogue) |
| `spec/04-theorems` | what is proved about it, and the harnesses that evaluate it |

The machine writes every step in a monad `H`: a reader of the state, a
writer of `Effect`s, folded onto the state at the end — one step is one
transaction. Nothing in `spec/` was changed except the one import that
now points at the top-level `types`.

## The implementation (`impl/`)

Read the files in this order; each opens with a header saying what it is
for and why it is shaped the way it is.

| file | what it defines |
|---|---|
| `impl/cas.lean` | **The CAS machine.** A versioned key–value store with `get`, `put`, `del`, and a condition on every write: `any`, `absent` (`If-None-Match: *`), or `version v` (`If-Match: etag`). A write whose condition fails is *rejected* and changes nothing. Versions are drawn from a counter that never repeats, so a version seen once is never seen again at a different value (`put_version_fresh`). |
| `impl/doc.lean` | **The document, the key space, the world.** One document per origin holding every promise and task of that origin; timer keys carrying a deadline and an origin; the world as the bucket plus the wire (the messages handed to the transport, kept in the specification's own outbox discipline). |
| `impl/monad.lean` | **The monad `C`.** Same shape as the specification's `H`, different vocabulary: it reads one snapshot — the document a transaction fetched, with its version — and it emits `putDoc` (conditional on that version), `armTimer`, `delTimer`, `send`. Effects are performed in order; a refused `putDoc` stops the transaction there. |
| `impl/kernel.lean` | **The kernel.** The specification's own handler, run against one origin's document: lift the document to a state, run `Abstraction.handle`, lower the result. The drain sweeps a document in three phases — expired deadlines, obligations of settled promises, tasks due for re-dispatch — each a list of the specification's internal steps. `transact` decides, then emits in the shell's order: arm the new timer, commit the document, clear the old timer, send. |
| `impl/system.lean` | **The system.** Transactions `begin` (snapshot) and `commit` (decide, CAS-write) in any interleaving; sweeps are transactions too. `run` collects the observations of a finite run: every answered request, with its answer and instant. |
| `impl/frame.lean` | **The frame lemmas.** For every handler and every internal step: two environments that agree on origin `o` get the same answer and effects (`Cong`), and every effect is a write at an id of origin `o` or a message (`LocAt`). The same-origin doors of the protocol are exactly where these proofs pick up the fact they need. |
| `impl/apply.lean` | **Effects through lookups.** The specification's effects restated as lookup transformers; congruence on one origin, frame on every other, and the outbox as a fold of sends. |
| `impl/commit.lean` | **The commit, performed.** The closed form of a transaction's effects, the two store invariants (`SInv`: versions are fresh; `TxnInv`: an in-flight snapshot is either the stored document or at a version that has moved), and the CAS as a theorem (`snapshot_current`). |
| `impl/refinement.lean` | **The theorem.** |

### The theorem

```lean
theorem refines (mat : Bool) (w : List (Impl.Step × Nat)) :
    obsOf (linearize mat w State.init)
        (Abstraction.runFin mat (linearize mat w State.init) ServerState.init).1 =
      (Impl.run mat w State.init).1 ∧
    Rel (Impl.run mat w State.init).2.world
        (Abstraction.runFin mat (linearize mat w State.init) ServerState.init).2
```

Every observable behaviour of the implementation is an observable
behaviour of the specification. For every finite run of the implementation
— transactions beginning and committing in any interleaving, sweeps firing
whenever, the CAS accepting some commits and refusing others — the
**linearization** is a run of the specification from its initial state
whose answered requests are exactly the implementation's, in order, at the
same instants, and whose final state agrees with the implementation's
final world on every lookup. The witness is constructed, not merely shown
to exist: each accepted commit becomes the specification's external step
followed by the internal steps the sweep performed; a refused commit, a
`begin`, an `idle` become nothing (`linearize_nows_pairwise` says the
instants stay monotone, which is what `Abstraction.Valid` asks of a trace).

The proof is a forward simulation in three layers:

1. **One step against one document is that step against the whole
   state** (`stepDoc_sim`). The frame lemmas say the handler cannot tell
   the two apart; the lookup lemmas say the writes land the same way.
2. **An accepted commit decided against the current document**
   (`accepted_snapshot`). Its write was conditioned on the version the
   snapshot was read at; versions never recur; so the version still being
   there means the document still is. A refused commit moved no document
   and sent nothing (`commit_rejected`) — only the timer it armed first
   landed, and no lookup sees it. `commit_accepted_is_atomic` states this
   as an equation: an accepted commit *is* the atomic read-modify-write of
   the current document, whatever ran between its `begin` and `commit`.
3. **The world after an accepted commit** is the old world with one
   document replaced and the sends appended to the wire
   (`commit_accepted`), which is the shape layer 1 produces.

There is no `sorry` in `impl/`. The relation between a world and a
specification state is by lookup, not equality: the specification's object
list is in the order its own writes left it, the bucket's documents in the
order it lists them, and no answer this implementation gives depends on
the order.

### What the implementation is, and is not

It follows the S3 backend of `resonatehq/resonate` (`crates/resonate-server-blob`):
one CAS'd object per origin, timer keys that are written before the
document that arms them, the kernel as a pure decision applied by a shell,
sends strictly after the commit. Where it differs, it says so:

- **The kernel is the specification.** The Rust kernel reimplements the
  protocol against its document shape; the model runs the specification's
  handlers against the document, so the refinement is a theorem about the
  *store*, not a re-verification of 21 handlers.
- **Every commit drains.** The Rust `handle` settles only the promises a
  request names and leaves the rest to its tick. Sweeping the whole document
  on every commit is the simpler invariant, and each swept step is one the
  specification could have taken anyway.
- **Which deadlines are armed.** A pending promise's expiry is armed when
  someone is waiting on it — a task, a callback, a listener. The SQL and
  S3 backends arm only targeted promises; this is a superset.
- **Out of scope**: schedules (cross-origin, their own objects in the S3
  backend), searches (501 in the specification), and heartbeats spanning
  origins (refused by the backend's validators). `Request.origin?` says
  exactly which requests are served; the others open no transaction.
- **Not modelled**: crashes mid-transaction beyond a refused CAS, the codec,
  retries of `Conflict` responses, and the timer daemon's scheduling — a
  sweep may happen at any time, as the specification's internal steps may.

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
