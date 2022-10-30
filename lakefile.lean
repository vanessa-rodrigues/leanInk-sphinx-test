import Lake
open Lake DSL

package «leanInk-sphinx-test» {
  -- add package configuration options here
}

lean_lib LeanSource {
  -- add library configuration options here
}

@[default_target]
lean_exe «leanInk-sphinx-test» {
  root := `LeanSource
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
