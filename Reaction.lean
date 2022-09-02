import Std
open Std

/-
class Typable (α) where
  type : α → Type

attribute [reducible] Typable.type

open Typable

structure Context (α : Type) [Typable α] where
  vals : (a : α) → type a 

def ContextM (α : Type) [Typable α] (β : Type) := Context α → (Context α) × β

def ContextM.get (a : α) [Typable α] : ContextM α (type a) :=
  fun ctx => (ctx, ctx.vals a) 

instance [Typable α] : Monad (ContextM α) := sorry

inductive Var
  | a 
  | b

@[reducible]
instance : Typable Var where
  type
    | .a => Nat
    | .b => String

open ContextM in
example : ContextM Var Unit := do
  let a ← get .a
  let x := a + 1
  return
-/

-- Generate a type of input ports of the reactor:
-- inductive Input | a | b | c | d
--
-- Generate a type on sources of a reaction:
-- inductive Source | a | b
--
-- The LF frontend ensures that sources ⊆ input ports, thus generate:
--
-- instance : Coe Source Input where
--   coe
--     | .a => .a
--     | .b => .b
--
-- Same for output ports and actions.

instance [Hashable α] {p : α → Prop} : Hashable { a : α // p a } where
  hash a := hash a.val

instance [BEq α] {p : α → Prop} : BEq { a : α // p a } where
  beq a₁ a₂ := BEq.beq a₁.val a₂.val

abbrev Time := Nat
abbrev Duration := { d : Nat // d > 0 }

structure Tag where
  time : Time
  microstep : Nat

def Time.after (time : Time) : Type := 
  { t : Time // t > time }

def Time.advance (time : Time) (d : Duration) : Time.after time := {
  val := time + d,
  property := by simp_arith [Nat.succ_le_of_lt d.property]
}

class Typed (α : Type) where
  type : α → Type

attribute [reducible] Typed.type

open Typed

instance [Typed α] {p : α → Prop} : Typed { a : α // p a } where
  type a := type a.val

@[reducible]
instance [Coe α β] [Typed β] : Typed α where
  type a := type (a : β)

def Interface (Name : Type) [Typed Name] := (name : Name) → Option (type name)

def Interface.merge [Typed Name] (i₁ i₂ : Interface Name) : Interface Name :=
  fun n => (i₂ n).orElse (fun _ => i₁ n)

structure ReactionM.Event (Name : Type) [Typed Name] (now : Time) where 
  action : Name
  time   : Time.after now
  value  : type action

structure ReactionM.Input (Source Action State : Type) [Typed Source] [Typed Action] [Typed State] where
  sources : Interface Source
  actions : Interface Action
  state   : Interface State
  time    : Time

structure ReactionM.Output (Effect Action State : Type) [Typed Effect] [Typed Action] [Typed State] (now : Time) where
  effects : Interface Effect := fun _ => none
  state   : Interface State
  events  : Array (Event Action now) := #[]

def ReactionM.Output.merge [Typed Effect] [Typed Action] [Typed State] (o₁ o₂ : ReactionM.Output Effect Action State time) : ReactionM.Output Effect Action State time := {
  effects := o₁.effects.merge o₂.effects,
  state := o₁.state.merge o₂.state,
  events := o₁.events ++ o₂.events
}

def ReactionM.Input.noop [Typed Source] [Typed Action] [Typed State] [Typed Effect] (input : ReactionM.Input Source Action State) : ReactionM.Output Effect Action State input.time := 
  { state := input.state }

def ReactionM (Source Effect Action State : Type) [Typed Source] [Typed Effect] [Typed Action] [Typed State] [DecidableEq Effect] [DecidableEq State] (α : Type) := 
  (input : ReactionM.Input Source Action State) → (ReactionM.Output Effect Action State input.time) × α

variable [Typed Source] [Typed Effect] [Typed Action] [Typed State] [DecidableEq Effect] [DecidableEq State]

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

structure Reaction (Input Output Action State : Type) [Typed State] [DecidableEq State] where
  sources : Type
  effects : Type
  actions : Type
  triggers : sources → Bool
  [sourcesTyped : Typed sources]
  [effectsTyped : Typed effects]
  [actionsTyped : Typed actions]
  [effectsDecidableEq : DecidableEq effects]
  [actionsDecidableEq : DecidableEq actions]
  [sourcesCoe : Coe sources Input]
  [effectsCoe : Coe effects Output]
  [actionsCoe : Coe actions Action]
  body : ReactionM sources effects actions State Unit

attribute [instance] Reaction.sourcesTyped Reaction.effectsTyped Reaction.actionsTyped 
attribute [instance] Reaction.effectsDecidableEq Reaction.actionsDecidableEq
attribute [instance] Reaction.sourcesCoe Reaction.effectsCoe Reaction.actionsCoe

structure Reactor.Interface where
  names : Type
  [namesTyped : Typed names]
  interface : Interface names := fun _ => none

attribute [instance] Reactor.Interface.namesTyped 

structure Reactor where
  state   : Reactor.Interface
  inputs  : Reactor.Interface
  outputs : Reactor.Interface
  actions : Reactor.Interface
  [stateDecidableEq : DecidableEq state.names]
  reactions : Array (Reaction inputs.names outputs.names actions.names state.names)

attribute [instance] Reactor.stateDecidableEq

def Reactor.reactionType (rtr : Reactor) :=
  Reaction rtr.inputs.names rtr.outputs.names rtr.actions.names rtr.state.names

def Reaction.outputType [Typed State] [DecidableEq State] (rcn : Reaction Source Effect Action State) :=
  ReactionM.Output rcn.effects rcn.actions State 

def ReactionM.run (time : Time) (rtr : Reactor) (rcn : rtr.reactionType) : (rcn.outputType time) × Unit :=
  rcn.body {
    sources := fun s => rtr.inputs.interface s, -- TODO: Problem: (type s) vs (type $ coe s) 
    actions := sorry,
    state   := rtr.state.interface,
    time    := time
  }

inductive ReactorInput  | i1 | i2 
inductive ReactorOutput | o1 | o2
inductive ReactorState  | s1 | s2 deriving DecidableEq
inductive ReactorAction | a1 | a2

inductive ReactionSource | i1 | i2 deriving DecidableEq
inductive ReactionEffect | o1      deriving DecidableEq
inductive ReactionAction | a1 | a2 deriving DecidableEq

@[reducible]
instance : Typed ReactorInput where 
  type
    | .i1 => Nat
    | .i2 => String  

@[reducible]
instance : Typed ReactorOutput where
  type
    | .o1 => Bool
    | .o2 => Unit  

@[reducible]
instance : Typed ReactorState where
  type
    | .s1 => Prop
    | .s2 => Bool  

@[reducible]
instance : Typed ReactorAction where
  type
    | .a1 => String
    | .a2 => Bool × Nat  

instance : Coe ReactionSource ReactorInput where
  coe 
    | .i1 => .i1
    | .i2 => .i2

instance : Coe ReactionEffect ReactorOutput where
  coe 
    | .o1 => .o1

instance : Coe ReactionAction ReactorAction where
  coe 
    | .a1 => .a1
    | .a2 => .a2

open ReactionM in
def testReaction : Reaction ReactorInput ReactorOutput ReactorAction ReactorState := {
  sources := ReactionSource,
  effects := ReactionEffect,
  actions := ReactionAction,
  triggers := fun s => match s with | .i1 => true | .i2 => false,
  body := do
    let i ← getInput .i1
    let i' := (i.getD 0) + 1
    let b := if i' = 0 then false else true
    setOutput .o1 b
    schedule .a1 1 _ "Test"
}






-- [port p 10,   state s₁ 5,   state s₂ 6,   port p 1]
--
-- [             state s₁ 5,   state s₂ 6,   port p 1]
--
-- [port p 1,    state s₁ 5,   state s₂ 6]
--
-- [action a "hello" 10,   action a "again" 10,   action a "future" 20]
--
-- [action a "hello" 10,   action a "future" 20,   action a "again" 10]
--
--
-- Shown so far:
-- ∀ instantaneous executions e₁ e₂:   (e₁ e₂ are change-list equivalent)  ->  e₁ and e₂ result in the same reactor
-- 
-- To show:
-- e₁ e₂ are change-list equivalent
--
-- Approach:
-- Consider execution as (finite) sequence of reactions: rcn₁, rcn₂, rcn₃, ...
--
-- Each reaction induces an "operation":
-- * Not triggered: "skip"
-- * Triggered:     "execute a certain change list"
--
-- We get a sequence of operations op₁, op₂, op₃, ...
-- 
-- change₁, change₂, change₃,    .....    change₃₅,  change₃₆,                      change₃₇, ....
-- [      op for rcn₁      ],    .....    [   op for rcn₇   ], [  skip for rcn₂  ], [ op for rcn₁₂ ... ]
-- 
-- Remaining gap:
-- Show that e₁ and e₂'s operation sequences are permutations of each other.
-- 
-- Almost Shown:
-- e₁ and e₂'s operation sequences are permutations   ->   e₁ and e₂ are change-list equivalent
    