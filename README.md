# Resonate on S3

The Resonate protocol, implemented on a compare-and-swap object store, and
the proof that the implementation does what the specification says.

Three parts under `src/`, and the directory layout says so:

```
src/types.lean    the protocol layer — records, requests, responses, the object kind, messages
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
| `src/types.lean` | the protocol layer: records, requests, responses, the object kind `OType` (internal, deadline, external, runnable with its target), the object model (`PromiseObject`, `TaskObject`, `Object`), the `Request` and `Response` alphabets, the message vocabulary |
| `src/spec/02-abstract` | the machine: `state`, `external` (the 21 handlers), `internal` (the 6 triggers), `system` (the alphabet `Event`/`Reply`, `step`, `exec`, `Trace`, `Valid`), `properties` (the catalogue) |
| `src/spec/03-theorems` | what is proved about it, and the harnesses that evaluate it |

The machine writes every step in a monad `H`: a reader of the state, a
writer of `Effect`s, folded onto the state at the end — one step is one
transaction. The specification's code is unchanged; its former
`01-protocol` (types and validation) is now `types.lean`, and its
comments were removed along with everyone else's.

## The implementation (`src/impl/`)

Being rebuilt to mirror `tlap/Concrete.tla` of the specification, one file at
a time.

| file | what it defines |
|---|---|
| `src/impl/external.lean` | `Origin` (one document per origin), `Timer` (a deadline, an object, a kind: promise, lease, retry), `Commands` (timers to arm, the document to put, timers to delete, messages to send), and the pure transition for every external request: `now → Origin → Request → Response × Commands`. Each handler names the timers it arms and deletes. |
| `src/impl/system.lean` | The machine, in the abstract machine's own shape. `State` is a bucket of `Path × Blob` (one blob per origin, one per armed timer) plus the outbox. The machine is parametric in a `Hasher`: an opaque `Hash` type, a function `Blob → Hash`, and the one assumption that distinct blobs have distinct hashes. A put carries a condition, `any`, `absent`, or `hash h` (the S3 `If-Match`), and is refused when the stored blob does not hash to `h`; `applyAll` folds effects and stops at a refused put, as the spec's `applyAll` folds its effects. `run` reads the origin, runs a handler, turns its commands into effects with the document put conditioned on the hash of the blob read, and applies them, like the spec's `run`; `step` is `run` per event. A timer fires only if its path is stored and its deadline has passed. `applyAll_accepted` proves the atomic step is never refused. `exec`, `Frame`, `Trace`, `Valid` as in the spec. |
| `src/impl/refinement.lean` | The theorem, stated. An `Observation` is a request, its response and the instant; `observed tr n` is what the first `n` frames of a trace show, and `nth tr k o` says `o` is the k-th thing shown. `refines`: every valid concrete trace from the empty bucket has a valid abstract trace from the empty state with the same k-th observation for every k. Proof pending. |

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
