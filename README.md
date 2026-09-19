# Resonate on S3

Resonate, implemented on a compare-and-swap object store, in Lean 4. The proof that it does what the specification says.

## What you need to review

You do not need to review the proofs. You need to review the theorems.

Every theorem in this repository is checked by Lean. When `lake build` succeeds, every statement marked `theorem` holds, with no step taken on trust, from the standard axioms of Lean alone. There is no `sorry` in `impl` or `refinement`; the main theorems below depend on nothing but `propext`, `Classical.choice` and `Quot.sound`.

What remains for a human is to read the statements and the definitions they name, and to judge whether they say what you want said. Is `Concrete.step` the machine you intend to run? Is `Abstract.Valid` the specification you mean? Is "the same k-th observation" the equivalence you care about? Those questions are the whole review. Everything between the statement and the closing `:=` has already been checked, more thoroughly than any reader could.

This is why the theorems below are printed in full and translated word for word. The translation is the review.

## Contents

Resonate is a durable execution system. This repository is a Lean 4 formalisation of Resonate on a compare-and-swap object store such as Amazon S3, with machine-checked proofs that the implementation refines its specification. It contains definitions and theorems only, no runnable service.

Four folders under `src/`:

- `types.lean` is the protocol: identifiers, promises, tasks, schedules, callbacks and listeners, outbox messages, and the request and response alphabets.
- `spec/02-abstract` is the specification: an abstract state machine over objects, schedules and an outbox, driven by external requests and internal triggers such as timeouts. `spec/03-theorems` proves properties of the specification; a few `sorry`s remain there, none used below.
- `impl/` is the implementation, laid out like the specification: `state` (the origin document as an append-only log with its compacted view, the bucket, conditional puts and appends, the configuration), `external` (the request handlers), `internal` (the sweep and the merge of commands), `system` (events, the step, traces), and `cache` (the machine with a read cache). Definitions only, no theorems.
- `refinement/` is the proof that `impl` refines `spec`, and the invariants of `impl` on its own. Nothing in `impl` depends on it.
- `model/` is an experiment: the promise half of the concrete machine written as a [Veil](https://veil.dev) module, checked by Veil's tools rather than by hand-written proofs. See [Veil](#veil) below.

A document is stored as a list of parts, and `Origin.current` folds the parts into the view, the latest version of every object. A request first sweeps the document and then runs its handler on the swept view. The sweep is five passes, one per kind of internal trigger: promise timeouts, listeners, callbacks, lease timeouts, retry timeouts. Each pass, like each handler, reads the view left by the passes before it and returns commands: timers to arm and delete, messages to send, and the objects it adds. Commands are merged in sequence: a timer armed and then deleted cancels, a timer deleted and then armed stays armed, and the added objects are compacted to the latest version of each. The merged `add` list is the document's new part; nothing is ever overwritten. The configuration `Config.adds` says how many parts a document may hold before a request writes it whole: with zero adds every write is a whole put, as on S3; with `n` adds a request appends one part, as on S3 Express One Zone, and the request that would exceed `n` writes the compacted document.

The headline theorems follow.

## `refines`

Every run of the implementation, under any configuration, shows exactly the observations of some run of the specification.

```lean
theorem refines (H : Concrete.Hasher) (cfg : Concrete.Config) (tr : Concrete.Trace)
    (valid : Concrete.Valid H cfg tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o
```

Take any hasher `H`, any function from blobs to etags such that distinct blobs have distinct etags. Take any configuration `cfg`, a number of appends allowed per document. Take any infinite sequence of frames `tr` of the concrete machine, each frame a bucket, an event, a reply and an instant. Suppose `valid`: every frame steps to the next by the concrete machine under `cfg`, and time never runs backwards. Suppose `init`: the first frame holds the empty bucket. Then there is a sequence of frames `tr'` of the abstract machine such that: every frame steps to the next by the abstract machine, with materialisation off; its first frame holds the empty abstract state; and for every position `k` and every observation `o`, a request with its response and instant, `o` is the `k`-th observation of the concrete run if and only if it is the `k`-th observation of the abstract run.

## `runCached_any`

From any cache carrying its own etags, a step behaves as if uncached.

```lean
theorem runCached_any {α : Type} (H : Hasher) (cfg : Config) (name : String) (f : Origin → α × Commands)
    {cs : Cached H} (ht : Tagged cs) :
    (runCached H cfg name f cs).2.2 = true ∧
    (runCached H cfg name f cs).1 = (Concrete.run H cfg name f cs.state).1 ∧
    Docs (Concrete.run H cfg name f cs.state).2.1 (runCached H cfg name f cs).2.1.state ∧
    Tagged (runCached H cfg name f cs).2.1 ∧
    Agree (runCached H cfg name f cs).2.1 name
```

Take any hasher `H`, any configuration `cfg`, any origin `name`, and any handler `f` from a document to a reply and the commands to run. Take any cached machine state `cs`: a bucket together with a cache of entries, each an origin, the parts of its document and an etag. Suppose only `ht`: the etag stored in every entry is the etag of the parts stored beside it. Nothing is assumed about whether the cache agrees with the bucket. Then running the handler through the cache, which reads the cache if it can, writes under the stored etag, and on refusal drops the entry and tries once more from the bucket, has five properties. The write is accepted. The reply is the reply the uncached machine gives from the same bucket. The resulting bucket holds, for every origin, the same blob as the uncached machine's, and the same outbox. Every entry of the resulting cache still carries its own etag. And reading `name` through the resulting cache returns exactly what reading the resulting bucket returns: the cache and the store agree on that origin.

## `refinesCached`

The cached implementation, started with an empty cache, refines the specification as well.

```lean
theorem refinesCached (H : Hasher) (cfg : Config) (tr : Cached.Trace H)
    (valid : Cached.Valid H cfg tr) (init : (tr 0).state = Cached.init H) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Cached.nth tr k o ↔ Abstract.nth tr' k o
```

Take any hasher `H`, any configuration `cfg`, and any infinite sequence of frames `tr` of the cached machine, each frame a bucket with its cache, an event, a reply and an instant. Suppose `valid`: every frame steps to the next by the cached machine under `cfg`, and time never runs backwards. Suppose `init`: the first frame holds the empty bucket and the empty cache. Then there is a run `tr'` of the abstract machine, valid with materialisation off and starting from the empty abstract state, such that for every position `k` and every observation `o`, `o` is the `k`-th observation of the cached run if and only if it is the `k`-th observation of the abstract run.

## `armed`

Every armed timeout timer belongs to an existing, non-internal promise.

```lean
theorem armed (H : Concrete.Hasher) (cfg : Concrete.Config) (tr : Concrete.Trace) (valid : Concrete.Valid H cfg tr)
    (init : (tr 0).state = Concrete.State.init) : ∀ n, Armed (tr n).state
```

with

```lean
def Armed (s : Concrete.State) : Prop :=
  ∀ t : Timer, (s.blob? (.timer t)).isSome = true → t.kind = .promiseTimeout →
    ∃ o ∈ (s.origin t.id.origin).objects, o.id = t.id ∧ o.promise.type ≠ .internal
```

Take any hasher `H`, any configuration `cfg`, and any valid concrete run `tr` under `cfg` from the empty bucket. Then in every frame `n` the bucket is `Armed`: for every timer `t` whose blob is present in the bucket, if it is a promise timeout timer, then the document of the timer's origin contains an object with the timer's id, and that object's promise is not of type `internal`. Internal promises are never awaited, so their timeouts are settled lazily, by the sweep of the next request to their origin, and no timer is ever armed for them. The proof goes handler by handler: every timer a handler or the sweep arms is a timer implied by an object it writes, and no handler changes the type of a promise.

## `adds_invisible`

The number of appends allowed changes nothing that can be observed.

```lean
theorem adds_invisible (H : Hasher) (cfg cfg' : Config) (tr : Concrete.Trace)
    (valid : Concrete.Valid H cfg tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Concrete.Trace,
      Concrete.Valid H cfg' tr' ∧
      (tr' 0).state = Concrete.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Concrete.nth tr' k o
```

Take any hasher `H` and any two configurations `cfg` and `cfg'`, for instance zero appends for S3 and a thousand for S3 Express One Zone. Take any valid concrete run `tr` under `cfg` from the empty bucket. Then there is a run `tr'` of the same machine under `cfg'`, valid and starting from the empty bucket, such that for every position `k` and every observation `o`, `o` is the `k`-th observation of the run under `cfg` if and only if it is the `k`-th observation of the run under `cfg'`. The two runs differ only in how each document is laid out in the bucket, as one part or as many. The proof relates the two runs step by step through the compacted view of every document, the timers and the outbox, which the write rule leaves identical whichever branch it takes.

## Veil

`model/concrete.lean` is the promise half of the concrete machine, `promiseCreate`, `promiseSettle`, `promiseGet` and `promiseRegisterListener`, with the two sweep passes they need and the timer event, written as a [Veil](https://veil.dev) module. Veil is a Lean 4 framework for state transition systems: a module declares its state as relations and functions, its transitions as imperative actions, and its properties as invariants, and Veil discharges the proof obligations by SMT, enumerates the states of a finite instance, or searches for traces of a bounded length.

The model is the concrete machine seen through `Origin.current`: the documents are relations indexed by object, the timers are the blobs at their paths, the outbox is keyed as the store keys it, and time is an uninterpreted total order. Every request sweeps its origin first, as `Concrete.handle` does, and a timer event sweeps and nothing more. The correspondence to `impl/` is by hand and is documented at the top of the file; nothing is proved about `Concrete.step` itself.

`lake build model` runs four checks:

- `#check_invariants` proves by SMT that the five invariants, headed by `armed` from above, are inductive: they hold initially and every action preserves them, for every instance of the module's types.
- `#model_check` enumerates every reachable state of an instance with three objects over two origins, one address and three instants, and checks the invariants in each.
- `sat trace` finds runs: one in which a promise sits pending in the bucket past its timeout until something sweeps its origin, and one in which a `promiseGet` is what notifies a listener.
- `unsat trace` proves that no run of two steps, of any instance, leaves a timer without its object.

What the experiment found. Veil's `#check_invariants` proves the invariants inductive for all six actions in about a minute; the invariants were written from the theorem `armed` and its proof and needed no strengthening. The lazy settlement of timeouts, which the Lean proofs handle through `PromiseObject.project`, is visible as a trace. The bounded checker fails on `any 3 actions` in Veil's current pre-release (a `simp` step limit in the trace encoding), so the unbounded queries stop at two steps; explicit three-step sequences work. The model checker compiles a native binary that links Veil's prebuilt cvc5, which on Linux needs two glibc 2.38 symbols the Lean toolchain's bundled sysroot lacks, `__isoc23_strtol` and `__isoc23_fscanf`; a two-line shim archived into the toolchain's `lib/glibc/libc_nonshared.a` resolves it.

Veil requires Lean v4.32.0, so the toolchain is now v4.32.0; the proofs build unchanged. `lake build` does not build the model: `model` is not a default target, so the proofs need neither Veil's dependencies nor an SMT solver.

## Build

```
lake build
```

builds the proofs. `lake build model` also builds Veil and its dependencies, then runs the Veil checks.
