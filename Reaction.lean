import Std
open Std

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

def Time := Nat
  deriving LT

structure Tag where
  time : Time
  microstep : Nat

def Time.after (g : Tag) : Type := 
  { t : Time // t > g.time }

structure Interface.Scheme where
  names : Type 
  types : names → Type
  [namesDecidableEq : DecidableEq names]
  [namesHashable : Hashable names]

attribute [instance] Interface.Scheme.namesDecidableEq
attribute [instance] Interface.Scheme.namesHashable
-- deriving instance BEq for Interface.Scheme.names

def Interface.Scheme.only (s : Interface.Scheme) (included : HashSet s.names) : Interface.Scheme := {
  names := { n : s.names // included.contains n },
  types := fun n => s.types n
}

def Interface (s : Interface.Scheme) := 
  (n : s.names) → Option (s.types n)

def Interface.only (i : Interface s) (included : HashSet s.names) : Interface (s.only included) :=
  fun n => i n.val

structure Reactor.Scheme where
  state   : Interface.Scheme
  inputs  : Interface.Scheme
  outputs : Interface.Scheme
  actions : Interface.Scheme

structure ReactionM.Event (s : Interface.Scheme) where 
  action : s.names
  time   : Time
  value  : s.types action

structure ReactionM.Context (s : Reactor.Scheme) where
  inputs  : Interface s.inputs
  outputs : Interface s.outputs
  actions : Interface s.actions
  state   : Interface s.state
  events  : Array (Event s.actions)

def ReactionM (s : Reactor.Scheme) (_ : Tag) (α : Type) := ReactionM.Context s → (ReactionM.Context s × α)

instance : Monad (ReactionM s g) where
  pure a ctx := 
    (ctx, a)
  map f a ctx := 
    let (ctx, a) := a ctx
    (ctx, f a)
  seq f a ctx :=
    let (ctx, a) := a () ctx
    let (ctx, f) := f ctx
    (ctx, f a)
  bind a f ctx :=
    let (ctx, a) := a ctx
    let (ctx, b) := f a ctx
    (ctx, b)

def ReactionM.getInput (n : s.inputs.names) : ReactionM s g (Option $ s.inputs.types n) :=
  fun ctx => (ctx, ctx.inputs n)

def ReactionM.getState (n : s.state.names) : ReactionM s g (Option $ s.state.types n) :=
  fun ctx => (ctx, ctx.state n)

def ReactionM.getAction (n : s.actions.names) : ReactionM s g (Option $ s.actions.types n) :=
  fun ctx => (ctx, ctx.actions n)

def ReactionM.setOutput (n : s.outputs.names) (v : s.outputs.types n) : ReactionM s g Unit :=
  fun ctx =>
    let outputs := fun m => if h : m = n then some (h ▸ v) else ctx.outputs m
    ({ ctx with outputs := outputs }, ())

def ReactionM.setState (n : s.state.names) (v : s.state.types n) : ReactionM s g Unit :=
  fun ctx =>
    let state := fun m => if h : m = n then some (h ▸ v) else ctx.state m
    ({ ctx with state := state }, ())

def ReactionM.schedule (n : s.actions.names) (t : Time.after g) (v : s.actions.types n) : ReactionM s g Unit := 
  fun ctx => 
    let event : Event s.actions := { action := n, time := t.val, value := v }
    ({ ctx with events := ctx.events.push event }, ())

def Reactor.Scheme.only (s : Reactor.Scheme) (inputs : HashSet s.inputs.names) (outputs : HashSet s.outputs.names) (actions : HashSet s.actions.names) : Reactor.Scheme := { s with
  inputs  := s.inputs.only  inputs,
  outputs := s.outputs.only outputs,
  actions := s.actions.only actions
}

structure 

structure Reaction (state : Interface.Scheme) where
  sources :  Type
  [sourcesBEq : BEq sources]
  [sourcesHashable : Hashable sources]
  effects :  Type
  actions :  Type
  triggers : HashSet sources
  -- body :     (g : Tag) → ReactionM (s.only sources effects actions) g Unit

def Reactor.Scheme.forReaction (s : Reactor.Scheme) (rcn : Reaction s) : Reactor.Scheme :=
  s.only rcn.sources rcn.effects rcn.actions

structure Reactor where
  scheme  : Reactor.Scheme
  state   : Interface scheme.state   := fun _ => none 
  inputs  : Interface scheme.inputs  := fun _ => none 
  outputs : Interface scheme.outputs := fun _ => none 
  actions : Interface scheme.actions := fun _ => none 
  reactions : Array (Reaction scheme)

def ReactionM.run (g : Tag) (rtr : Reactor) (rcn : Reaction rtr.scheme) (m : ReactionM (rtr.scheme.forReaction rcn) g α)  : (ReactionM.Context $ rtr.scheme.forReaction rcn) × α :=
  m {
    inputs  := rtr.inputs.only  rcn.sources,
    outputs := rtr.outputs.only rcn.effects,
    actions := rtr.actions.only rcn.actions,
    state   := rtr.state,
    events  := #[]
  }

inductive TestInputNames  | i1 | i2 deriving DecidableEq, Hashable
inductive TestOutputNames | o1 | o2 deriving DecidableEq, Hashable
inductive TestStateNames  | s1 | s2 deriving DecidableEq, Hashable
inductive TestActionNames | a1 | a2 deriving DecidableEq, Hashable

abbrev testInputScheme : Interface.Scheme := {
  names := TestInputNames,
  types := fun n => 
    match n with
    | .i1 => Nat
    | .i2 => String  
}

def testOutputScheme : Interface.Scheme := {
  names := TestOutputNames,
  types := fun n => 
    match n with
    | .o1 => Bool
    | .o2 => Unit  
}

def testStateScheme : Interface.Scheme := {
  names := TestStateNames,
  types := fun n => 
    match n with
    | .s1 => Prop
    | .s2 => Bool  
}

def testActionScheme : Interface.Scheme := {
  names := TestActionNames,
  types := fun n => 
    match n with
    | .a1 => String
    | .a2 => Bool × Nat  
}

abbrev testScheme : Reactor.Scheme := {
  state   := testStateScheme,
  inputs  := testInputScheme,
  outputs := testOutputScheme,
  actions := testActionScheme
}

open ReactionM in
def testReaction : Reaction testScheme := {
  sources  := HashSet.empty |>.insert .i1 |>.insert .i2,
  triggers := HashSet.empty |>.insert .i1,
  effects  := HashSet.empty |>.insert .o1,
  actions  := HashSet.empty |>.insert .a1 |>.insert .a2,
  body     := fun g => do
    let p₀ ← getInput .nameOfPort
    return
}

def testReactor : Reactor := {
  scheme := testScheme,
  reactions := #[]
}
