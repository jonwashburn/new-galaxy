import Lake
open Lake DSL

package «gravity-ilg» where
  -- Add package configuration here if needed

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib ILG where
  -- Expose the ILG namespace (e.g., ILG/RotationLaw.lean)
  globs := #[`ILG]
