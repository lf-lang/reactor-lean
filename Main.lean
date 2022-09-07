import Runtime

inductive ReactorInput  | i1 | i2 deriving DecidableEq, Repr
inductive ReactorOutput | o1 | o2 deriving DecidableEq, Repr
inductive ReactorState  | s1 | s2 deriving DecidableEq, Repr
inductive ReactorAction | a1 | a2 deriving DecidableEq, Repr

inductive ReactionSource | i1 | i2 deriving DecidableEq, Repr
inductive ReactionEffect | o1      deriving DecidableEq, Repr

@[reducible]
instance : InjectiveCoe ReactionSource ReactorInput where
  coe a := match a with | .i1 => .i1      | .i2 => .i2
  inv b := match b with | .i1 => some .i1 | .i2 => some .i2
  invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe ReactionEffect ReactorOutput where
  coe a := match a with | .o1 => .o1
  inv b := match b with | .o1 => some .o1 | .o2 => none
  invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
  coeInvId := (by cases · <;> rfl)

abbrev ReactorInput.scheme : Scheme := {
  vars := ReactorInput,
  type := fun x => match x with
    | .i1 => Nat
    | .i2 => String
}

abbrev ReactorOutput.scheme : Scheme := {
  vars := ReactorOutput,
  type := fun x => match x with
    | .o1 => Bool
    | .o2 => Unit
}

abbrev ReactorAction.scheme : Scheme := {
  vars := ReactorAction,
  type := fun x => match x with
    | .a1 => String
    | .a2 => Bool × Nat  
}

abbrev ReactorState.scheme : Scheme := {
  vars := ReactorState,
  type := fun x => match x with
    | .s1 => Int
    | .s2 => Bool  
}

-- Printing --------------------------------------------------------------------
instance : Enum ReactorInput where   allCases := #[.i1, .i2]
instance : Enum ReactorOutput where  allCases := #[.o1, .o2]
instance : Enum ReactorState where   allCases := #[.s1, .s2]
instance : Enum ReactorAction where  allCases := #[.a1, .a2]
instance : Enum ReactionSource where allCases := #[.i1, .i2]
instance : Enum ReactionEffect where allCases := #[.o1]

instance : ∀ a, Repr $ ReactorInput.scheme.type a  | .i1 | .i2 => inferInstance
instance : ∀ a, Repr $ ReactorOutput.scheme.type a | .o1 | .o2 => inferInstance
instance : ∀ a, Repr $ ReactorState.scheme.type a  | .s1 | .s2 => inferInstance
instance : ∀ a, Repr $ ReactorAction.scheme.type a | .a1 | .a2 => inferInstance
--------------------------------------------------------------------------------

def testReaction : Reaction ReactorInput.scheme ReactorOutput.scheme ReactorAction.scheme ReactorState.scheme := {
  sources := ReactionSource,
  effects := ReactionEffect,
  triggers := #[.source .i1, .action .a2],
  body := open ReactionM ReactionSource ReactionEffect ReactorAction ReactorState in do
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

def testReactorSchemes : Reactor.Schemes := {
  inputs  := ReactorInput.scheme,
  outputs := ReactorOutput.scheme,
  actions := ReactorAction.scheme,
  state   := ReactorState.scheme,
  reactions := #[testReaction]
}

def testReactor : Reactor testReactorSchemes := {
  inputs  := fun _ => none,
  outputs := fun _ => none,
  actions := fun _ => none,
  state   := fun _ => none
}

-- instance : Repr (Reaction.outputType testReaction 12 × Unit) := inferInstance
-- def result := ReactionM.run 12 testReactor testReaction
-- #eval result