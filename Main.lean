import Runtime

reactor Main {
  input  := [i1 : Nat,    i2 : String]
  output := [o1 : Bool,   o2 : Unit]
  action := [a1 : String, a2 : Bool × Nat]
  state  := [s1 : Int,    s2 : Bool]

  reaction first (i1, !i2, @a1) → (o1, o2) { 
    let i ← getInput i1
    let i' := (i.getD 0) + 1
    let b := if i' = 0 then true else false
    setOutput o1 b
    setOutput o1 true
    setState s1 (-1 : Int)
    match ← getState s1 with
    | none => return
    | some v => 
      setState s1 (v * 12)
      setState s2 false
  }

  reaction second (i1, @a1, @a2) → (o1) { 
    let _ := (← getAction a1).map (· ++ "suffix")
    let _ ← getInput i1
    schedule a1 112 (by simp) "First"
    schedule a1 113 (by simp) "Second"
    -- IO.println "Hello"
    let dir := IO.appDir
    -- let dir' ← IO.appDir
  }
}

def main : IO Unit := do
  let initial : Reactor Main.scheme := { Main.instance with 
    inputs := fun
      | .i2 => some "input" 
      | _ => none 
    actions := fun
      | .a2 => (true, 1)
      | _ => none
  }
  let ⟨rtr, events⟩ ← initial.run ⟨0, 0⟩
  let input1  := rtr.inputs .i1
  let input2  := rtr.inputs .i2
  let output1 := rtr.outputs .o1
  let output2 := rtr.outputs .o2
  let action1 := rtr.actions .a1
  let action2 := rtr.actions .a2
  let state1  := rtr.state .s1
  let state2  := rtr.state .s2
  IO.println input1
  IO.println input2
  IO.println output1
  IO.println output2
  IO.println action1
  IO.println action2
  IO.println state1
  IO.println state2
  for event in events.toArray do
    IO.println s!"Event: {event.time}"

-- Printing --------------------------------------------------------------------
instance : Enum Main.Input where   allCases := #[.i1, .i2]
instance : Enum Main.Output where  allCases := #[.o1, .o2]
instance : Enum Main.State where   allCases := #[.s1, .s2]
instance : Enum Main.Action where  allCases := #[.a1, .a2]
instance : Enum Main.Reactions.first.Source where allCases := #[.i1, .i2]
instance : Enum Main.Reactions.first.Effect where allCases := #[.o1]

instance : ∀ a, Repr $ Main.Input.scheme.type a  | .i1 | .i2 => inferInstance
instance : ∀ a, Repr $ Main.Output.scheme.type a | .o1 | .o2 => inferInstance
instance : ∀ a, Repr $ Main.State.scheme.type a  | .s1 | .s2 => inferInstance
instance : ∀ a, Repr $ Main.Action.scheme.type a | .a1 | .a2 => inferInstance
--------------------------------------------------------------------------------

-- instance : Repr (Reaction.outputType Main.Reactions.first.instance 12 × Unit) := inferInstance
-- def result := Main.Reactions.first.instance.run Main.instance.inputs Main.instance.actions Main.instance.state ⟨12, 1⟩
-- #eval result