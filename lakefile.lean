import Lake
open Lake DSL

require veil from git "https://github.com/verse-lab/veil.git" @ "c645234790c351fd932b0cde8cd9e0d68ee90bd8"

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

@[default_target]
lean_lib «refinement» where
  srcDir := "src"
  roots  := #[]
  globs  := #[.submodules `refinement]

lean_lib «model» where
  srcDir := "src"
  roots  := #[]
  globs  := #[.submodules `model]
