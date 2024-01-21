import Lake
open Lake DSL

package empty where
  -- add package configuration options here

lean_lib Vec where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
