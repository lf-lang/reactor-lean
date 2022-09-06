import Lake
open Lake DSL

package reactor_lean

lean_lib Runtime

@[defaultTarget]
lean_exe Executable {
  root := `Main
}
