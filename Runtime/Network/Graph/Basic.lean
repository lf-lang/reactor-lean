import Runtime.Reaction
import Runtime.Reactor

structure Network.Graph where
  classes : Type
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Network.Graph.decEqClasses

namespace Network.Graph

def Class (graph : Graph) := graph.classes

namespace Class

instance : DecidableEq (Class graph) :=
  fun cls₁ cls₂ => 
    let c₁ : graph.classes := cls₁
    let c₂ : graph.classes := cls₂
    if h : c₁ = c₂ then isTrue h else isFalse h

private def scheme (cls : Class graph) := graph.schemes cls

abbrev interface (cls : Class graph) := cls.scheme.interface

abbrev timers (cls : Class graph) := cls.scheme.timers

structure Child (cls : Class graph) where
  id : cls.scheme.children
  deriving DecidableEq

def Child.class {cls : Class graph} (child : Child cls) : Class graph := 
  cls.scheme.class child.id

-- TODO: Get this coercion to work at call site.
instance {cls : Class graph} : Coe (Child cls) (Class graph) where
  coe child := child.class

abbrev subinterface (cls : Class graph) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child : Child cls => child.class.interface kind

abbrev reactionInputScheme (cls : Class graph) :=
  let localInputs := cls.interface .inputs
  let nestedOutputs := cls.subinterface .outputs
  localInputs ⊎ nestedOutputs

@[simp]
theorem reactionInputScheme_type_left {cls : Class graph} (localInput) : 
  cls.reactionInputScheme.type (.inl localInput) = (cls.interface .inputs).type localInput := rfl 

@[simp]
theorem reactionInputScheme_type_right {cls : Class graph} (child childOutput) : 
  cls.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = (child.class.interface .outputs).type childOutput := by
  simp [Interface.Scheme.bUnion_type]  

abbrev reactionOutputScheme (cls : Class graph) :=
  let localOutputs := cls.interface .outputs
  let nestedInputs := cls.subinterface .inputs
  localOutputs ⊎ nestedInputs

inductive Reaction.Kind
  | pure
  | impure

abbrev Reaction.Kind.monad : Reaction.Kind → (Type → Type)
  | pure => Id
  | impure => IO

open Interface in
structure Reaction (cls : Class graph) where
  kind : Reaction.Kind
  val : Reaction kind.monad
  [subPS : Subscheme val.portSources cls.reactionInputScheme]
  [subPE : Subscheme val.portEffects cls.reactionOutputScheme]
  [subAS : Subscheme val.actionSources (cls.interface .actions)]
  [subAE : Subscheme val.actionEffects (cls.interface .actions)]
  eqState  : cls.interface .state  = val.state  := by rfl
  eqParams : cls.interface .params = val.params := by rfl
  eqTimers : cls.timers = val.timers            := by rfl

open Reaction in
attribute [instance] subPS subPE subAS subAE

instance {reaction : Reaction cls} : Functor reaction.kind.monad :=
  match reaction.kind with | .pure | .impure => inferInstance

structure Subport (cls : Class graph) (kind : Reactor.PortKind) where
  child : Child cls
  port : (child.class.interface kind).vars

abbrev Subport.type (subport : Subport cls kind) : Type := 
  (subport.child.class.interface kind).type subport.port

-- TODO: The `eqTypeProof` is probably broken.
macro "eqTypeProof" : tactic => `(tactic| try (intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp))
structure Connections (cls : Class graph) where 
  source : (Subport cls .input) → Option (Subport cls .output)
  eqType : (source input = some output) → (input.type = output.type) := by sorry -- eqTypeProof

def Connections.empty : Connections cls where
  source _ := none
  eqType := by simp

end Class

end Network.Graph