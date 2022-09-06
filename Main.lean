import Runtime

inductive ReactorInput  | i1 | i2 deriving DecidableEq, Repr
inductive ReactorOutput | o1 | o2 deriving DecidableEq, Repr
inductive ReactorState  | s1 | s2 deriving DecidableEq, Repr
inductive ReactorAction | a1 | a2 deriving DecidableEq, Repr

inductive ReactionSource | i1 | i2 deriving DecidableEq, Repr
inductive ReactionEffect | o1      deriving DecidableEq, Repr
inductive ReactionAction | a1 | a2 deriving DecidableEq, Repr

instance : Enumerable ReactorInput  where allCases := #[.i1, .i2]
instance : Enumerable ReactorOutput where allCases := #[.o1, .o2]
instance : Enumerable ReactorState  where allCases := #[.s1, .s2]
instance : Enumerable ReactorAction where allCases := #[.a1, .a2]

instance : Enumerable ReactionSource where allCases := #[.i1, .i2]
instance : Enumerable ReactionEffect where allCases := #[.o1]
instance : Enumerable ReactionAction where allCases := #[.a1, .a2]

@[reducible]
instance : Typed ReactorInput where 
  type
    | .i1 => Nat
    | .i2 => String  
  typeRepr | .i1 | .i2 => inferInstance

@[reducible]
instance : Typed ReactorOutput where
  type
    | .o1 => Bool
    | .o2 => Unit  
  typeRepr | .o1 | .o2 => inferInstance

@[reducible]
instance : Typed ReactorState where
  type
    | .s1 => Int
    | .s2 => Bool  
  typeRepr | .s1 | .s2 => inferInstance

@[reducible]
instance : Typed ReactorAction where
  type
    | .a1 => String
    | .a2 => Bool × Nat  
  typeRepr | .a1 | .a2 => inferInstance

instance : Coe ReactionSource ReactorInput where
  coe 
    | .i1 => .i1
    | .i2 => .i2

instance : TypedCoe ReactionSource ReactorInput where
  coeEqType _ := rfl

instance : Coe ReactionEffect ReactorOutput where
  coe 
    | .o1 => .o1

instance : TypedCoe ReactionEffect ReactorOutput where
  coeEqType _ := rfl

instance : Coe ReactionAction ReactorAction where
  coe 
    | .a1 => .a1
    | .a2 => .a2

instance : TypedCoe ReactionAction ReactorAction where
  coeEqType _ := rfl

open ReactionM in
def testReaction : Reaction ReactorInput ReactorOutput ReactorAction ReactorState := {
  sources := ReactionSource,
  effects := ReactionEffect,
  actions := ReactionAction,
  triggers := fun s => match s with | .i1 => true | .i2 => false,
  body := do
    let i ← getInput .i1
    let i' := (i.getD 0) + 1
    let b := if i' = 0 then true else false
    setOutput .o1 b
    setOutput .o1 true
    setState .s1 (-1 : Int)
    match ← getState .s1 with
    | none => return
    | some v => setState .s1 (v * 12)
    schedule .a1 1 (by simp) "First"
    schedule .a1 1 (by simp) "Second"
}

def testReactor : Reactor := {
  inputs  := { vars := ReactorInput },
  outputs := { vars := ReactorOutput },
  actions := { vars := ReactorAction },
  state   := { vars := ReactorState },
  reactions := #[testReaction]
}

def result := ReactionM.run 12 testReactor testReaction
#eval result

structure Reactor.Context (Action : Type) [Typed Action] where
  time : Time
  events : Array (ReactionM.Event Action time)

def Reactor.run (rtr : Reactor) (ctx : Reactor.Context rtr.actions.vars) : Reactor × (Array $ ReactionM.Event rtr.actions.vars ctx.time) := Id.run do
  let mut events := ctx.events
  let mut rtr := rtr
  for rcn in rtr.reactions do
    -- TODO: We need to set the actions on the rtr first (according to ctx.events).
    --       And then remove the used events.

    let ⟨result, _⟩ := ReactionM.run ctx.time rtr rcn
    let outputs := rtr.outputs.interface.merge' result.effects
    let state := rtr.state.interface.merge result.state
    let inst : Coe (ReactionM.Event rcn.actions ctx.time) (ReactionM.Event rtr.actions.vars ctx.time) := inferInstance
    let newEvents := result.events.map fun e => inst.coe e
    events := events ++ newEvents
    -- TODO: Problem: we can't change the value of rtr.
    --       Solution: Decouple the structure of a reactor from its values.

  return (rtr, #[]) 

    
