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

Being rebuilt to mirror `tlap/Concrete.tla` of the specification, one file at
a time.

| file | what it defines |
|---|---|
| `src/impl/external.lean` | `Document` (one per origin), `Timer` (a deadline, an object, a kind: promise, lease, retry), `Commands` (timers to arm, the document to put, timers to delete, messages to send), and the pure transition for every external request: `Request → now → Document → Response × Commands`. Each handler names the timers it arms and deletes. |

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
