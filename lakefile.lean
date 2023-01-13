import Lake
open Lake DSL

package reactor_lean

lean_lib Runtime

@[default_target]
lean_exe Executable {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "5770b609aeae209cb80ac74655ee8c750c12aabd"
