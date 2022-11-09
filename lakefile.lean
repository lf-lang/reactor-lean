import Lake
open Lake DSL

package reactor_lean

lean_lib Runtime

@[default_target]
lean_exe Executable {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
