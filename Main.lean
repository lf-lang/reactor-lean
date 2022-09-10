import Runtime

-- network {

  /- main -/ reactor Main {
    input  := [i1 : Nat,    i2 : String]
    output := [o1 : Bool,   o2 : Unit]
    action := [a1 : String, a2 : Bool × Nat]
    state  := [s1 : Int,    s2 : Bool]
    -- nested := [x : Sub, y : Sub]
    -- connections := [x.o1 → y.i3, o1 → x.i2]

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

  reactor Sub {
    input  := [i1 : Nat, i2 : Bool, i3 : Unit]
    output := [o1 : Unit]
    action := []
    state  := []
    -- nested := [a : Grand, b : Grand]
  }

  reactor Grand {
    input  := []
    output := []
    action := []
    state  := []
  }

-- }

inductive Main.Nested | x | y
inductive Sub.Nested  | a | b

abbrev Grand.idTree : Network.ReactorID.Tree := 
  .node Empty (·.rec)

abbrev Sub.idTree : Network.ReactorID.Tree := 
  .node Sub.Nested fun
    | .a => Grand.idTree
    | .b => Grand.idTree

abbrev Main.idTree : Network.ReactorID.Tree := 
  .node Main.Nested fun
    | .x => Sub.idTree
    | .y => Sub.idTree

abbrev Grand.Nested.schemes : Network.ReactorID.Nested Grand.idTree → Reactor.Scheme
  | .final empty => empty.rec

abbrev Sub.Nested.schemes : Network.ReactorID.Nested Sub.idTree → Reactor.Scheme
  | .final .a   => Grand.scheme
  | .final .b   => Grand.scheme
  | .cons  .a n => Grand.Nested.schemes n
  | .cons  .b n => Grand.Nested.schemes n

abbrev Main.Nested.schemes : Network.ReactorID.Nested Main.idTree → Reactor.Scheme
  | .final .x   => Sub.scheme
  | .final .y   => Sub.scheme
  | .cons  .x n => Sub.Nested.schemes n
  | .cons  .y n => Sub.Nested.schemes n

abbrev Grand.Nested.reactors : (id : Network.ReactorID.Nested Grand.idTree) → (Reactor $ Grand.Nested.schemes id)
  | .final empty => empty.rec

abbrev Sub.Nested.reactors : (id : Network.ReactorID.Nested Sub.idTree) → (Reactor $ Sub.Nested.schemes id)
  | .final .a   => Grand.instance
  | .final .b   => Grand.instance
  | .cons  .a n => Grand.Nested.reactors n
  | .cons  .b n => Grand.Nested.reactors n

abbrev Main.Nested.reactors : (id : Network.ReactorID.Nested Main.idTree) → (Reactor $ Main.Nested.schemes id)
  | .final .x   => Sub.instance
  | .final .y   => Sub.instance
  | .cons  .x n => Sub.Nested.reactors n
  | .cons  .y n => Sub.Nested.reactors n

def network : Network := {
  scheme := {
    tree := Main.idTree,
    «reactor» := fun
      | .main => Main.scheme
      | .nested n => Main.Nested.schemes n
  }
  «reactor» := fun
    | .main => Main.instance
    | .nested n => Main.Nested.reactors n
  connections := #[]
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