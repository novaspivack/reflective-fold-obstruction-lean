import Lake
open Lake DSL

package «reflective-fold-obstruction-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-
  Mathlib is a **dependency** of this project. Do **not** compile all of Mathlib from
  source locally: after `lake update`, run **`lake exe cache get`** to download
  pre-built `.olean` bundles into `~/.cache/mathlib/`, then `lake build` only
  compiles this repo’s files. See `../docs/008_LEAN_MATHLIB_CACHE_WORKFLOW.md`.
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

/--
  **SPEC_004** import timeline **step 2** (optional flagship dependency).

  Pinned rev must stay aligned with **RepresentationalIncompleteness** public modules;
  bump only after `lake build RepresentationalIncompleteness` is green upstream.
-/
require «representational-incompleteness» from git
  "https://github.com/novaspivack/representational-incompleteness-lean.git"
  @ "1595fac306defa05c085b75c23de82f149b39476"

@[default_target]
lean_lib ReflectiveFoldObstruction where
  roots := #[`ReflectiveFoldObstruction]
