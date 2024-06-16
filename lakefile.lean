import Lake
open Lake DSL

package «lean-sorting» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «lsort» where
  root := `Main
  -- supportInterpreter := true

lean_lib «LeanSorting» where
  -- add any library configuration options here
