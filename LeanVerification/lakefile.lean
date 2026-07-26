import Lake
open Lake DSL

package «wilkies» where
  version := v!"0.1.0"

require LRATCatcher from git
  "https://github.com/leansolving/lrat-catcher" @ "4ec2168b810636e789da3349ab3e670af338187c"

lean_lib Wilkies where

@[default_target]
lean_exe wilkies_cnf where
  root := `Main
