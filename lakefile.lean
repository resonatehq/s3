import Lake
open Lake DSL

package «resonate-s3» where
  -- pure Lean core; no external dependencies

/-! The repository has three parts, and the directory layout says so.

`types.lean` at the top level is the wire surface — records, requests,
responses. It is the ONE file both halves import, because it is the
one thing they must agree on: the specification says what a server
answers, the implementation answers it, and neither may redefine the
alphabet.

`spec/` is the specification, copied from the protocol specification
(the abstract machine, the property catalogue, the theorems).

`impl/` is the implementation of that protocol on a compare-and-swap
object store — S3 — together with the proof that every observable
behaviour of the implementation is an observable behaviour of the
specification. -/

/-- The protocol surface: `types.lean`, the shared alphabet. -/
@[default_target]
lean_lib «types» where
  srcDir := "."
  roots  := #[`types]

/-- The specification: the machine. `lake build spec` is the fast loop. -/
@[default_target]
lean_lib «spec» where
  srcDir := "spec"
  roots  := #[]
  globs  := #[.submodules `«01-protocol», .submodules `«02-abstract»]

/-- What is proved about the specification, and the harnesses that
    evaluate it. The sweeps here run under kernel `decide` at build time
    (minutes). -/
lean_lib «theorems» where
  srcDir := "spec"
  roots  := #[]
  globs  := #[.submodules `«04-theorems»]

/-- The implementation on a CAS object store, and its refinement proof. -/
@[default_target]
lean_lib «impl» where
  srcDir := "."
  roots  := #[]
  globs  := #[.submodules `impl]
