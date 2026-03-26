# reflective-fold-obstruction

Lean 4 + Mathlib formalization for the **reflective fold obstruction** program (outer workspace: `Reflective-Fold-Obstruction`).

## Build

**Use the Mathlib binary cache** — do not compile all of Mathlib from source:

```bash
lake update              # resolve deps → exact mathlib revision
lake exe cache get       # REQUIRED: download pre-built .olean blobs (GitHub source ≠ binaries)
lake build ReflectiveFoldObstruction   # default library target; only this repo + uncached leaves
```

If `lake build` starts compiling thousands of `Mathlib.*` files, you skipped `cache get`, hit a cache miss for an untagged mathlib rev, or removed `~/.cache/mathlib/`. Fix: run `lake exe cache get` again; keep `lakefile.lean` on a **tagged** mathlib release (as pinned) so the community cache always has artifacts.

Workspace documentation: `../docs/lean_mathlib_cache_workflow.md`, `../docs/optional_mathlib.md`.

## Structure

- `ReflectiveFoldObstruction/Basic.lean` — scaffold (extend as formalization grows)
- `docs/argument-structure.md` — plain-language map (starter)

See also `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`, `ARTIFACT.md`.
