import Lake
open Lake DSL

package "flowregex-lean" where
  version := v!"0.1.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @"v4.22.0-rc3"

@[default_target]
lean_lib «FlowregexLean» where
  -- add library configuration options here
