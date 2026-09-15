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
| `src/impl/external.lean` | `Origin` (one document per origin), `Timer` (a deadline, an object, a kind: promise, lease, retry), `Commands` (timers to arm, the document to put, timers to delete, messages to send), and the pure transition for every external request: `now → Origin → Request → Response × Commands`. Each handler names the timers it arms and deletes. |
| `src/impl/internal.lean` | The sweep, in the order of `Concrete.tla`: `promiseTimeouts` settles due promises and drops their timers; `listeners` sends `unblock` to the listeners of settled promises; `callbacks` strikes the callbacks of settled promises and resumes their awaiters, arming a retry for a suspended task; `leaseTimeouts` releases expired leases and arms an immediate retry; `retryTimeouts` re-arms due retries and sends `execute` to the target. `sweep` composes the passes with `Commands.merge`. Each pass names the timers it arms and drops. |
| `src/impl/system.lean` | The machine, in the abstract machine's own shape. `State` is a bucket of `Path × Blob` (one blob per origin, one per armed timer) plus the outbox. The machine is parametric in a `Hasher`: an opaque `Hash` type, a function `Blob → Hash`, and the one assumption that distinct blobs have distinct hashes. A put carries a condition, `any`, `absent`, or `hash h` (the S3 `If-Match`), and is refused when the stored blob does not hash to `h`; `applyAll` folds effects and stops at a refused put, as the spec's `applyAll` folds its effects. `run` reads the origin, runs a handler, turns its commands into effects with the document put conditioned on the hash of the blob read, and applies them, like the spec's `run`; `handle` sweeps the origin and then runs the request's handler on the swept document, or only sweeps for a timer; `step` is `run (handle ev now)` per event, with the timer's licence checked first. A timer fires only if its path is stored and its deadline has passed. `applyAll_accepted` proves the atomic step is never refused. `exec`, `Frame`, `Trace`, `Valid` as in the spec. |
| `src/impl/relation.lean` | The vocabulary of the refinement. An `Observation` is a request, its response and the instant; `observed tr n` is what the first `n` frames of a trace show, and `nth tr k o` says `o` is the k-th thing shown, on both levels. `sweepTriggers` lists the abstract triggers a sweep of a document corresponds to, and `events` linearises a concrete event into abstract events at the same instant. `abstract` maps a bucket to an abstract state, `Equiv` relates abstract states by lookup, `WF` says listener and callback lists are duplicate free and callbacks never name their own object or leave the origin, and `Inv` is the bucket invariant: one blob per path, an origin blob holds only its own objects with unique ids, well formed. |
| `src/impl/lookup.lean` | How the abstract monad and the lookups compute: `bind`, `pure`, `readObject`, `touchObject` applied to an environment; `find` on abstract states and `Origin.find` on documents; `Local o org S` says the document and the abstract state agree on every object of origin `o`; `Fx o` says an effect list only touches origin `o`; how `applyAll` moves the outbox (`sendsFold`), leaves schedules and other origins alone. |
| `src/impl/requests.lean` | `Sim`: a handler run on a document simulates the abstract handler run on a related state, with the same response, effects confined to the origin, the same messages, and the documents still related. One lemma per request handler; the search and schedule requests need none because the concrete machine stutters on them. |
| `src/impl/sweep.lean` | `SwInv`: the running relation between a document being swept and the abstract state executing triggers. Each pass is shown to execute its trigger list: promise timeouts and lease and retry timeouts by induction over the objects; listeners and callbacks through a stepwise proof device, one step per trigger reading the working document, which equals the bulk pass under `WF`, the resume of an awaiter matching `resumeOne`. `sweep_sim` chains the five passes. |
| `src/impl/wf.lean` | Every request handler preserves `WF`. |
| `src/impl/simulation.lean` | `step_sim`, the one-step simulation. `find_abstract` reads an object of `abstract s` from the blob of its origin; `run_state` describes the bucket and outbox after the atomic put; `handleExternal_sim` dispatches over the request alphabet. A concrete step is a list of abstract events at the same instant that preserves `Inv` and `Equiv` and shows the same observation. |
| `src/impl/trace.lean` | Flattening a sequence of nonempty frame blocks into a trace, and the frames an abstract state runs through on a list of events. |
| `src/impl/refinement.lean` | `refines`: every valid concrete trace from the empty bucket has a valid abstract trace from the empty state with the same k-th observation for every k. The abstract trace is the concatenation, frame by frame, of the linearisation of each concrete step followed by a stutter. |

## The Alloy model (`src/alloy/`)

The abstract model once more, as an Alloy 6 specification: the data
model, the external handlers, and the machine that runs them along a
trace; the triggers to follow. One module per Lean layer. The state is
mutable in the Alloy 6 sense: `State` is a singleton whose `objects` and
`outbox` are `var`, the lookups and the catalogue read the current
instant, a handler constrains the next (`State.objects'`), and the
machine's `Valid` is a temporal fact over the trace.

| file | what it defines |
|---|---|
| `src/alloy/types.als` | The protocol layer of `types.lean`, one signature per structure: `Ident`, `Value`, `PromiseState`, `TaskState`, `OType` (with `Runnable` carrying its target), `PromiseObject`, `TaskObject`, `Object`, the records `PromiseRecord` and `TaskRecord`, `Message` (`Execute`, `Unblock`), `OutboxEntry`, and the alphabet: `Request` and `Response` with one subsignature per constructor, `Status` the codes the handlers answer. The object model's functions are predicates relating input to output: `addCallback`, `addListener`, `projectPromise`, `fulfillTask`, `viewTask`, `projectObject`, `promiseToRecord`, `taskToRecord`; `projectedState` computes the state a promise shows at an instant; `sameKey` is `OutboxKey`. |
| `src/alloy/state.als` | `State` (`var objects`, `var outbox`, no schedules yet), `init`, the lookups on the current instant `storedPromises`, `storedTasks`, `object`, `promise`, `task`, `hasTask`; the effects: `apply` is `applyAll` from the current instant to the next on a step's keyed writes, `keep` is no effects, `readObject` and `readTaskObject` the reads with `matP` and `matT` what a read materialises, `createPromise`, `setSettled`. |
| `src/alloy/properties.als` | The catalogue's state properties on the current instant, one predicate per Lean property under the same name, `stateHolds` conjoining them, the `gaps`. Runs show the catalogue admits the states it describes; checks show the lookups are functional under it and the projections agree with its verdicts. |
| `src/alloy/external.als` | The 17 non-schedule handlers, one predicate per Lean handler, `[mat, now, req, res]`, with the Lean branches in the Lean order: `promiseGet`, `promiseCreate`, `promiseSettle`, `promiseRegisterCallback`, `promiseRegisterListener`, `promiseSearch`, `taskGet`, `taskCreate`, `taskAcquire`, `taskFence` (through `promiseCreateWith` and `promiseSettleWith`, the inner handlers run after the fence's own reads), `taskHeartbeat`, `taskSuspend` (with `firstBad` where `checkAwaited` stops), `taskFulfill`, `taskRelease`, `taskHalt`, `taskContinue`, `taskSearch`. For every handler a run shows it can succeed on a well formed state and a check shows it preserves the catalogue from any state to the next instant. |
| `src/alloy/system.als` | `Machine`: `mat` fixed for the run, and at every instant `now`, the request and the response (a request is `Event.external`, none is `Event.stutter`; the triggers come later). `handleExternal` dispatches a `Request` to its handler, `step` is the Lean `step` from one instant to the next, `valid` the Lean `Valid`: `init` first, then always a step with the clock not going back. A run shows a trace creating, acquiring and fulfilling a task; a check shows every valid trace satisfies the catalogue at every instant, to a bounded length. |

The translation: a structure is a signature with value semantics (a fact
identifies atoms with equal fields, so `=` is structural equality as in
Lean); a sum is an abstract signature with one subsignature per
constructor; `Option` is `lone`; `Nat` is a non-negative `Int`; `String`
is an atom of `Str`, with `EmptyStr` the empty string. The lists the
catalogue proves duplicate free (`objects` by id, `outbox` by key,
`callbacks`, `listeners`, `resumes`) are sets, so the three uniqueness
properties hold by construction; a header list is a relation; a list in
a request is a `seq`.

The monad: a step reads the state it started from throughout and its
effects are folded onto it at the end. Every effect is keyed, so the
fold is determined by the last effect on each key: a handler's writes
are keyed maps, a read's materialisation first and the handler's own
writes overriding it (`++`), and `apply` folds them once, from the
current instant to the next.

```
java -jar org.alloytools.alloy.dist.jar exec -s glucose src/alloy/properties.als
java -jar org.alloytools.alloy.dist.jar exec -s glucose src/alloy/external.als
java -jar org.alloytools.alloy.dist.jar exec -s glucose src/alloy/system.als
```

Alloy 6.2, no libraries beyond the distribution jar; trace checks are
bounded in length. The bundled native Glucose is much faster than the
default SAT4J on the handler checks (`taskFence` takes half an hour
against more than one); drop `-s glucose` where the native library does
not load. The machine's arithmetic
is on naturals and Alloy's integers wrap; a sum that leaves the range
wraps to a negative, which no field admits, so at the edge of the range
a step does not exist rather than miscomputes. Do not pass
`--nooverflow`: it treats an overflowing comparison as satisfied and
invents steps.

## Build

```
lake build            # types, spec, impl — the fast loop
lake build theorems   # the specification's decide sweeps (minutes)
```

Lean 4 (`lean-toolchain`), no Mathlib.
