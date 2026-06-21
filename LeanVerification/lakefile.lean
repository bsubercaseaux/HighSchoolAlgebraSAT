import Lake
open Lake DSL

package «wilkies» where
  version := v!"0.1.0"

lean_lib Wilkies where

@[default_target]
lean_exe wilkies_cnf where
  root := `Main
