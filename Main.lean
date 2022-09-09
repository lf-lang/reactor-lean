import Runtime

reactor Main {
  input  := [i1 : Nat,    i2 : String]
  output := [o1 : Bool,   o2 : Unit]
  action := [a1 : String, a2 : Bool × Nat]
  state  := [s1 : Int,    s2 : Bool]

  reaction Rcn1 (i1, !i2, @a1) → (o1, o2) { 
    let i ← getInput i1
    let i' := (i.getD 0) + 1
    let b := if i' = 0 then true else false
    setOutput o1 b
    setOutput o1 true
    -- setState s1 (-1 : Int)
    match ← getState s1 with
    | none => return
    | some v => setState s1 (v * 12)
    schedule a1 1 (by simp) "First"
    schedule a1 1 (by simp) "Second"
    -- IO.println "Hello"
    let dir := IO.appDir
    -- let dir' ← IO.appDir
  }
}

#print Main.Rcn1.instance

-- Printing --------------------------------------------------------------------
instance : Enum Main.Input where   allCases := #[.i1, .i2]
instance : Enum Main.Output where  allCases := #[.o1, .o2]
instance : Enum Main.State where   allCases := #[.s1, .s2]
instance : Enum Main.Action where  allCases := #[.a1, .a2]
instance : Enum Main.Rcn1.Source where allCases := #[.i1, .i2]
instance : Enum Main.Rcn1.Effect where allCases := #[.o1]

instance : ∀ a, Repr $ Main.Input.scheme.type a  | .i1 | .i2 => inferInstance
instance : ∀ a, Repr $ Main.Output.scheme.type a | .o1 | .o2 => inferInstance
instance : ∀ a, Repr $ Main.State.scheme.type a  | .s1 | .s2 => inferInstance
instance : ∀ a, Repr $ Main.Action.scheme.type a | .a1 | .a2 => inferInstance
--------------------------------------------------------------------------------

def testReactor : Reactor Main.scheme := {
  inputs  := fun _ => none
  outputs := fun _ => none
  actions := fun _ => none
  state   := fun _ => none
}

-- instance : Repr (Reaction.outputType testReaction 12 × Unit) := inferInstance
-- def result := ReactionM.run 12 testReactor testReaction
-- #eval result