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
- `impl/` is the implementation, laid out like the specification: `state` (the origin document, the bucket, conditional puts), `external` (the request handlers), `internal` (the sweep), `system` (events, the step, traces), and `cache` (the machine with a read cache). Definitions only, no theorems.
- `refinement/` is the proof that `impl` refines `spec`, and the invariants of `impl` on its own. Nothing in `impl` depends on it.

The headline theorems follow.

## `refines`

Every run of the implementation shows exactly the observations of some run of the specification.

```lean
theorem refines (H : Concrete.Hasher) (tr : Concrete.Trace)
    (valid : Concrete.Valid H tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o
```

Take any hasher `H`, any function from blobs to etags such that distinct blobs have distinct etags. Take any infinite sequence of frames `tr` of the concrete machine, each frame a bucket, an event, a reply and an instant. Suppose `valid`: every frame steps to the next by the concrete machine, and time never runs backwards. Suppose `init`: the first frame holds the empty bucket. Then there is a sequence of frames `tr'` of the abstract machine such that: every frame steps to the next by the abstract machine, with materialisation off; its first frame holds the empty abstract state; and for every position `k` and every observation `o`, a request with its response and instant, `o` is the `k`-th observation of the concrete run if and only if it is the `k`-th observation of the abstract run.

## `runCached_any`

From any cache carrying its own etags, a step behaves as if uncached.

```lean
theorem runCached_any {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (ht : Tagged cs) :
    (runCached H name f cs).2.2 = true ∧
    (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    Docs (Concrete.run H name f cs.state).2.1 (runCached H name f cs).2.1.state ∧
    Tagged (runCached H name f cs).2.1 ∧
    Agree (runCached H name f cs).2.1 name
```

Take any hasher `H`, any origin `name`, and any handler `f` from a document to a reply and the commands to run. Take any cached machine state `cs`: a bucket together with a cache of entries, each an origin, a document and an etag. Suppose only `ht`: the etag stored in every entry is the etag of the document stored beside it. Nothing is assumed about whether the cache agrees with the bucket. Then running the handler through the cache, which reads the cache if it can, puts under the stored etag, and on refusal drops the entry and tries once more from the bucket, has five properties. The put is accepted. The reply is the reply the uncached machine gives from the same bucket. The resulting bucket holds, for every origin, the same document as the uncached machine's, and the same outbox. Every entry of the resulting cache still carries its own etag. And reading `name` through the resulting cache returns exactly what reading the resulting bucket returns: the cache and the store agree on that origin.

## `refinesCached`

The cached implementation, started with an empty cache, refines the specification as well.

```lean
theorem refinesCached (H : Hasher) (tr : Cached.Trace H)
    (valid : Cached.Valid H tr) (init : (tr 0).state = Cached.init H) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Cached.nth tr k o ↔ Abstract.nth tr' k o
```

Take any hasher `H` and any infinite sequence of frames `tr` of the cached machine, each frame a bucket with its cache, an event, a reply and an instant. Suppose `valid`: every frame steps to the next by the cached machine, and time never runs backwards. Suppose `init`: the first frame holds the empty bucket and the empty cache. Then there is a run `tr'` of the abstract machine, valid with materialisation off and starting from the empty abstract state, such that for every position `k` and every observation `o`, `o` is the `k`-th observation of the cached run if and only if it is the `k`-th observation of the abstract run.

## `armed`

Only a pending, non-internal promise ever has a timeout timer armed in the bucket.

```lean
theorem armed (H : Concrete.Hasher) (tr : Concrete.Trace) (valid : Concrete.Valid H tr)
    (init : (tr 0).state = Concrete.State.init) : ∀ n, Armed (tr n).state
```

with

```lean
def Armed (s : Concrete.State) : Prop :=
  ∀ t : Timer, (s.blob? (.timer t)).isSome = true → t.kind = .promiseTimeout →
    ∃ o ∈ (s.origin t.id.origin).objects, o.id = t.id ∧ o.promise.type ≠ .internal
```

Take any hasher `H` and any valid concrete run `tr` from the empty bucket. Then in every frame `n` the bucket is `Armed`: for every timer `t` whose blob is present in the bucket, if it is a promise timeout timer, then the document of the timer's origin contains an object with the timer's id, and that object's promise is not of type `internal`. Internal promises are never awaited, so their timeouts are settled lazily, by the sweep of the next request to their origin, and no timer is ever armed for them. The proof goes handler by handler: every timer a handler or the sweep arms is a timer implied by an object it writes, and no handler changes the type of a promise.

## Build

```
lake build
```
