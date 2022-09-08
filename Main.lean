import Runtime

reactor Main {
  input  := [i1 : Nat,    i2 : String],
  output := [o1 : Bool,   o2 : Unit],
  action := [a1 : String, a2 : Bool × Nat],
  state  := [s1 : Int,    s2 : Bool]
}

inductive ReactionSource | i1 | i2 deriving DecidableEq, Repr
inductive ReactionEffect | o1      deriving DecidableEq, Repr

@[reducible]
instance : InjectiveCoe ReactionSource Main.Input where
  coe a := match a with | .i1 => .i1      | .i2 => .i2
  inv b := match b with | .i1 => some .i1 | .i2 => some .i2
  invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe ReactionEffect Main.Output where
  coe a := match a with | .o1 => .o1
  inv b := match b with | .o1 => some .o1 | .o2 => none
  invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
  coeInvId := (by cases · <;> rfl)

-- Printing --------------------------------------------------------------------
instance : Enum Main.Input where   allCases := #[.i1, .i2]
instance : Enum Main.Output where  allCases := #[.o1, .o2]
instance : Enum Main.State where   allCases := #[.s1, .s2]
instance : Enum Main.Action where  allCases := #[.a1, .a2]
instance : Enum ReactionSource where allCases := #[.i1, .i2]
instance : Enum ReactionEffect where allCases := #[.o1]

instance : ∀ a, Repr $ Main.Input.scheme.type a  | .i1 | .i2 => inferInstance
instance : ∀ a, Repr $ Main.Output.scheme.type a | .o1 | .o2 => inferInstance
instance : ∀ a, Repr $ Main.State.scheme.type a  | .s1 | .s2 => inferInstance
instance : ∀ a, Repr $ Main.Action.scheme.type a | .a1 | .a2 => inferInstance
--------------------------------------------------------------------------------

def testReaction : Reaction Main.Input.scheme Main.Output.scheme Main.Action.scheme Main.State.scheme := {
  sources := ReactionSource,
  effects := ReactionEffect,
  triggers := #[.source .i1, .action .a2],
  body := open ReactionM ReactionSource ReactionEffect Main.Action Main.State in do
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
    IO.println "Hello"
    let dir := IO.appDir
    let dir' ← IO.appDir
}

def testStructure : Reactor.Scheme := {
  inputs    := Main.Input.scheme
  outputs   := Main.Output.scheme
  actions   := Main.Action.scheme
  state     := Main.State.scheme
  reactions := #[testReaction]
}

def testReactor : Reactor testReactorSchemes := {
  inputs  := fun _ => none
  outputs := fun _ => none
  actions := fun _ => none
  state   := fun _ => none
}

-- instance : Repr (Reaction.outputType testReaction 12 × Unit) := inferInstance
-- def result := ReactionM.run 12 testReactor testReaction
-- #eval result