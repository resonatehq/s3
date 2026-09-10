import Lake
open Lake DSL

package «resonate-s3» where

@[default_target]
lean_lib «types» where
  srcDir := "src"
  roots  := #[`types]

@[default_target]
lean_lib «spec» where
  srcDir := "src/spec"
  roots  := #[]
  globs  := #[.submodules `«02-abstract»]

lean_lib «theorems» where
  srcDir := "src/spec"
  roots  := #[]
  globs  := #[.submodules `«03-theorems»]

@[default_target]
lean_lib «impl» where
  srcDir := "src"
  roots  := #[]
  globs  := #[.submodules `impl]
