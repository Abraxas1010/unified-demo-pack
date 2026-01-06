import Lake
open Lake DSL

package «UnifiedDemoPack» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib UnifiedPack where
lean_lib HeytingLean where

lean_exe unified_demo where
  root := `HeytingLean.CLI.UnifiedDemo

lean_exe proof_graph_dump where
  root := `HeytingLean.CLI.ProofGraphDump
