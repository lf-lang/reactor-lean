import Std
open Std

abbrev Time := Nat
abbrev Duration := { d : Nat // d > 0 }

structure Tag where
  time : Time
  microstep : Nat

def Time.after (time : Time) : Type := 
  { t : Time // t > time }

instance : Repr (Time.after t) where
  reprPrec t := reprPrec t.val

def Time.advance (time : Time) (d : Duration) : Time.after time := {
  val := time + d,
  property := by simp_arith [Nat.succ_le_of_lt d.property]
}

class Enumerable (α) where
  allCases : Array α

class Typed (α : Type) extends Enumerable α, Repr α where
  type : α → Type
  typeRepr : ∀ a, Repr (type a)
  [decidableEq : DecidableEq α]

attribute [reducible] Typed.type
attribute [instance] Typed.decidableEq Typed.typeRepr

open Typed

@[reducible]
instance [DecidableEq α] [Enumerable α] [Repr α] [Coe α β] [Typed β] : Typed α where
  type a := type (a : β)
  typeRepr := inferInstance

def Interface (Var : Type) [Typed Var] := (var : Var) → Option (type var)

open Format in
instance [inst : Typed Var] : Repr (Interface Var) where
  reprPrec i p := Id.run do
    let mut result : Format := nil 
    for var in inst.allCases do
      let varF := reprPrec var p
      let valueF := reprPrec (i var) p
      let mapsto := varF ++ " ↦ " ++ valueF
      result := result ++ mapsto ++ line
    return result

def Interface.merge [Typed Var] (i₁ i₂ : Interface Var) : Interface Var :=
  fun n => (i₂ n).orElse (fun _ => i₁ n)

section
variable (Input Output Source Effect Action State : Type) 
variable [Typed Input] [Typed Output] [Typed Source] [Typed Effect] [Typed Action] [Typed State]

structure ReactionM.Event (min : Time) where 
  action : Action
  time   : Time.after min
  value  : type action
  deriving Repr

structure ReactionM.Input where
  sources : Interface Source
  actions : Interface Action
  state   : Interface State
  time    : Time

structure ReactionM.Output (now : Time) where
  effects : Interface Effect := fun _ => none
  state   : Interface State
  events  : Array (Event Action now) := #[]
  deriving Repr

def ReactionM (α : Type) := (input : ReactionM.Input Source Action State) → (ReactionM.Output Effect Action State input.time) × α

end

variable {Input Output Source Effect Action State : Type} 
variable [Typed Input] [Typed Output] [Typed Source] [Typed Effect] [Typed Action] [Typed State]

def ReactionM.Output.merge (o₁ o₂ : ReactionM.Output Effect Action State time) : ReactionM.Output Effect Action State time := {
  effects := o₁.effects.merge o₂.effects,
  state := o₁.state.merge o₂.state,
  events := o₁.events ++ o₂.events
}

def ReactionM.Input.noop (input : ReactionM.Input Source Action State) : ReactionM.Output Effect Action State input.time := 
  { state := input.state }

instance : Monad (ReactionM Source Effect Action State) where
  pure a input := 
    let output := input.noop
    (output, a)
  map f ma input :=
    let (output, a) := ma input
    (output, f a)
  seq mf ma input₁ :=
    let (output₁, a) := ma () input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, f) := mf input₂
    (output₂, f a)
  bind ma f input₁ :=
    let (output₁, a) := ma input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, b) := f a input₂
    let output := output₁.merge output₂
    (output, b)

def ReactionM.getInput (source : Source) : ReactionM Source Effect Action State (Option $ type source) :=
  fun input => (input.noop, input.sources source)

def ReactionM.getState (var : State) : ReactionM Source Effect Action State (Option $ type var) :=
  fun input => (input.noop, input.state var)

def ReactionM.getAction (action : Action) : ReactionM Source Effect Action State (Option $ type action) :=
  fun input => (input.noop, input.actions action)

def ReactionM.logicalTime : ReactionM Source Effect Action State Time := 
  fun input => (input.noop, input.time)

def ReactionM.setOutput (effect : Effect) (v : type effect) : ReactionM Source Effect Action State Unit :=
  fun input =>
    let effects := fun e => if h : e = effect then some (h ▸ v) else none
    let output := { effects := effects, state := input.state }
    (output, ())

def ReactionM.setState (var : State) (v : type var) : ReactionM Source Effect Action State Unit :=
  fun input =>
    let state := fun s => if h : s = var then some (h ▸ v) else input.state s
    let output := { state := state }
    (output, ())

def ReactionM.schedule (action : Action) (delay : Nat) (h : delay > 0 := by simp_arith) (v : type action) : ReactionM Source Effect Action State Unit := 
  fun input => 
    let time := input.time.advance ⟨delay, h⟩
    let event : Event Action input.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event] }
    (output, ())

class TypedCoe (α β) [Typed α] [Typed β] extends Coe α β where
  coeEqType : ∀ a, type (coe a) = type a

attribute [instance] TypedCoe.toCoe

structure Reaction (Input Output Action State : Type) [Typed Input] [Typed Output] [Typed Action] [Typed State] where
  sources : Type
  effects : Type
  actions : Type
  triggers : sources → Bool
  [sourcesTyped : Typed sources]
  [effectsTyped : Typed effects]
  [actionsTyped : Typed actions]
  [sourcesTypedCoe : TypedCoe sources Input]
  [effectsTypedCoe : TypedCoe effects Output]
  [actionsTypedCoe : TypedCoe actions Action]
  body : ReactionM sources effects actions State Unit

attribute [instance] Reaction.sourcesTyped Reaction.effectsTyped Reaction.actionsTyped 
attribute [instance] Reaction.sourcesTypedCoe Reaction.effectsTypedCoe Reaction.actionsTypedCoe

structure Reactor.Interface where
  vars : Type
  [varsTyped : Typed vars]
  interface : Interface vars := fun _ => none

attribute [instance] Reactor.Interface.varsTyped 

structure Reactor where
  state   : Reactor.Interface
  inputs  : Reactor.Interface
  outputs : Reactor.Interface
  actions : Reactor.Interface
  reactions : Array (Reaction inputs.vars outputs.vars actions.vars state.vars)

def Reactor.reactionType (rtr : Reactor) :=
  Reaction rtr.inputs.vars rtr.outputs.vars rtr.actions.vars rtr.state.vars

def Reaction.outputType [Typed State] [DecidableEq State] (rcn : Reaction Source Effect Action State) :=
  ReactionM.Output rcn.effects rcn.actions State 

def ReactionM.run (time : Time) (rtr : Reactor) (rcn : rtr.reactionType) : (rcn.outputType time) × Unit :=
  rcn.body {
    sources := fun s => 
      let inst : TypedCoe rcn.sources rtr.inputs.vars := inferInstance
      (inst.coeEqType s) ▸ (rtr.inputs.interface s),
    actions := fun a =>
      let inst : TypedCoe rcn.actions rtr.actions.vars := inferInstance
      (inst.coeEqType a) ▸ (rtr.actions.interface a),
    state := rtr.state.interface,
    time := time
  }

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