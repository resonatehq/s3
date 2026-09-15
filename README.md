# Resonate on S3

Resonate, implemented on a compare-and-swap object store, in Lean 4. The proof that it does what the specification says.

## Contents

Resonate is a durable execution system. This repository is a Lean 4 formalisation of Resonate on a compare-and-swap object store such as Amazon S3, with machine-checked proofs that the implementation refines its specification. It contains definitions and theorems only, no runnable service.

Three layers under `src/`:

- `types.lean` is the protocol: identifiers, promises, tasks, schedules, callbacks and listeners, outbox messages, and the request and response alphabets.
- `spec/02-abstract` is the specification: an abstract state machine over objects, schedules and an outbox, driven by external requests and internal triggers such as timeouts. `spec/03-theorems` proves properties of the specification; a few `sorry`s remain there, none used by `impl`.
- `impl/` is the implementation: state as blobs in a bucket keyed by path, written with conditional puts; every request and every timer first sweeps its origin document; a read cache is optional.

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

## Build

```
lake build
```
