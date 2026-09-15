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

The concrete machine mirrors `tlap/Concrete.tla` of the specification, and
the refinement proof mirrors the machine: one file per layer.

| file | what it defines |
|---|---|
| `src/impl/external.lean` | `Origin` (one document per origin; `write` replaces an object in place, or appends a new one, so the order of the document is stable), `Timer` (a deadline, an object, a kind: promise, lease, retry), `Commands` (timers to arm, the document to put, timers to delete, messages to send), and the pure transition for every external request: `now → Origin → Request → Response × Commands`. Each handler names the timers it arms and deletes. |
| `src/impl/internal.lean` | The sweep, computed object by object from the snapshot: `sweepObject` takes one object through the five stages of `Concrete.tla` in order, `promiseTimeout` (settle a due promise), `listener` (send `unblock` to the listeners of a settled promise and clear them), `callback` (clear the callbacks of a settled promise, and resume the task of an object some settled promise awaits, reading who awaits it from the snapshot with `awaiting`), `leaseTimeout` (release an expired lease and arm an immediate retry) and `retryTimeout` (re-arm a due retry and send `execute`), and returns the new object with its `unblock` and `execute` messages. `sweep` maps `sweepObject` over the document; the timers to arm and to delete are the difference between the timers the old and the new document imply. No intermediate document is ever materialised. |
| `src/impl/system.lean` | The machine, in the abstract machine's own shape. `State` is a bucket of `Path × Blob` (one blob per origin, one per armed timer) plus the outbox. The machine is parametric in a `Hasher`: an opaque `Hash` type, a function `Blob → Hash`, and the one assumption that distinct blobs have distinct hashes. A put carries a condition, `any`, `absent`, or `hash h` (the S3 `If-Match`), and is refused when the stored blob does not hash to `h`; `applyAll` folds effects and stops at a refused put, as the spec's `applyAll` folds its effects. `run` reads the origin, runs a handler, turns its commands into effects with the document put conditioned on the hash of the blob read, and applies them, like the spec's `run`; `handle` sweeps the origin and then runs the request's handler on the swept document, or only sweeps for a timer; `step` is `run (handle ev now)` per event, with the timer's licence checked first. A timer fires only if its path is stored and its deadline has passed. `applyAll_accepted` proves the atomic step is never refused. `exec`, `Frame`, `Trace`, `Valid` as in the spec. |
| `src/impl/passes.lean` | The linearisation device, `Chain`: the sweep as five chained passes over a working document, each pass one trigger at a time, together with `sweepTriggers`, the abstract triggers those passes fire in the order they fire them. Proof only; the machine does not run it. |
| `src/impl/relation.lean` | The vocabulary of the refinement. An `Observation` is a request, its response and the instant; `observed tr n` is what the first `n` frames of a trace show, and `nth tr k o` says `o` is the k-th thing shown, on both levels. `events` linearises a concrete event into abstract events at the same instant, using `Chain.sweepTriggers` for the sweep. `abstract` maps a bucket to an abstract state, `Equiv` relates abstract states by lookup, `WF` says listener and callback lists are duplicate free and callbacks never name their own object or leave the origin, and `Inv` is the bucket invariant: one blob per path, an origin blob holds only its own objects with unique ids, well formed. |
| `src/impl/lookup.lean` | How the abstract monad and the lookups compute: `bind`, `pure`, `readObject`, `touchObject` applied to an environment; `find` on abstract states and `Origin.find` on documents; `Local o org S` says the document and the abstract state agree on every object of origin `o`; `Fx o` says an effect list only touches origin `o`; how `applyAll` moves the outbox (`sendsFold`), leaves schedules and other origins alone. |
| `src/impl/requests.lean` | `Sim`: a handler run on a document simulates the abstract handler run on a related state, with the same response, effects confined to the origin, the same messages, and the documents still related. One lemma per request handler; the search and schedule requests need none because the concrete machine stutters on them. |
| `src/impl/sweep.lean` | `SwInv`: the running relation between a document being swept and the abstract state executing triggers. Each chained pass is shown to execute its trigger list: promise timeouts and lease and retry timeouts by induction over the objects; listeners and callbacks through a stepwise proof device, one step per trigger reading the working document, which equals the bulk pass under `WF`, the resume of an awaiter matching `resumeOne`. `chain_sweep_sim` chains the five passes. |
| `src/impl/equal.lean` | The per-object sweep equals the chained sweep, document for document and message for message, under `WF`. Each pass of the chain is characterised as a map over the document (`bulk_put`); the callbacks pass, the one pass whose triggers read each other's writes, is characterised through `stage`, the value of an object after the objects before it have been processed, and shown to coincide with `callback` computed from the snapshot. `sweep_sim` transfers `chain_sweep_sim` to the sweep the machine runs. |
| `src/impl/wf.lean` | Every request handler preserves `WF`. |
| `src/impl/simulation.lean` | `step_sim`, the one-step simulation. `find_abstract` reads an object of `abstract s` from the blob of its origin; `run_state` describes the bucket and outbox after the atomic put; `handleExternal_sim` dispatches over the request alphabet. A concrete step is a list of abstract events at the same instant that preserves `Inv` and `Equiv` and shows the same observation. |
| `src/impl/trace.lean` | Flattening a sequence of nonempty frame blocks into a trace, and the frames an abstract state runs through on a list of events. |
| `src/impl/refinement.lean` | `refines`: every valid concrete trace from the empty bucket has a valid abstract trace from the empty state with the same k-th observation for every k. The abstract trace is the concatenation, frame by frame, of the linearisation of each concrete step followed by a stutter. |
| `src/impl/cache.lean` | The machine with a read cache next to the bucket. `Cached H` is a bucket and a list of entries by origin, each the document and the etag the put was acknowledged with. `attempt` reads the origin from the cache when it is there and conditions the put on the stored etag, otherwise reads from the bucket and conditions on the hash of what it read; once the put is accepted it remembers the document with the etag of the blob it wrote, and if the put is refused it drops the entry. `runCached` is one attempt, and a second one if the first was refused, which then reads from the bucket. Handlers and `handle` are untouched. Two kinds of statement. From the empty cache: `Sound` says every entry is the blob stored at its path with its hash, every step preserves it, and under it the cached step is the uncached step; `refinesCached` is `refines` for the cached machine. From any cache whose entries carry their own document's etag (`Tagged`): `attempt_dichotomy` says an attempt either reads an entry whose etag matches the bucket and is the uncached step, or reads a stale one and is refused with no origin blob or message changed and the entry dropped; `runCached_any` and `stepCached_any` say that with the retry the step gives the uncached reply, the same documents and messages as the uncached step, keeps `Tagged`, and leaves the cache and the bucket in agreement on that origin (`Agree`). The one residue of a refused attempt is the timer blobs it armed before the refusal, which `Docs` deliberately does not compare. |

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
