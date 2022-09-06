import Runtime.Time
import Runtime.Interface

open Typed

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

instance [Typed S] [Typed Action] [inst : TypedCoe S Action] : Coe (ReactionM.Event S time) (ReactionM.Event Action time) where
  coe e := {
    action := e.action,
    time := e.time,
    value := (inst.coeEqType e.action) ▸ e.value
  }

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