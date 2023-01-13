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

open Interface in
structure Reaction (cls : Class graph) where
  val : Reaction
  [subPS : Subscheme val.portSources cls.reactionInputScheme]
  [subPE : Subscheme val.portEffects cls.reactionOutputScheme]
  [subAS : Subscheme val.actionSources (cls.interface .actions)]
  [subAE : Subscheme val.actionEffects (cls.interface .actions)]
  eqState  : cls.interface .state = val.state   := by rfl
  eqParams : cls.interface .params = val.params := by rfl
  eqTimers : cls.timers = val.timers            := by rfl

open Reaction in
attribute [instance] subPS subPE subAS subAE

structure Subport (cls : Class graph) (kind : Reactor.PortKind) where
  child : Child cls
  port  : (child.class.interface kind).vars
  deriving DecidableEq

abbrev Subport.type (subport : Subport cls kind) : Type :=
  (subport.child.class.interface kind).type subport.port

structure Connections.DelayedDestination {cls : Class graph} (src : Subport cls .output) where
  dst    : Subport cls .input
  delay  : Duration
  eqType : src.type = dst.type := by rfl

-- The data layout of this type is motivated by execution-specific use cases:
-- * Non-delayed connections are used in a context where a destination
--   port needs to find its corresponding source port (if it exists).
-- * Delayed connections are used in a context where a given source
--   port needs to enumerate all of its delayed destinations.
--
-- Note: We're not to enforcing uniqueness of connections to input ports,
--       as this is handled by the LF frontend.
open Connections in
structure Connections (cls : Class graph) where
  instantaneous : (Subport cls .input) → Option (Subport cls .output)
  delayed       : (src : Subport cls .output) → Array (DelayedDestination src)
  instEqType    : ∀ {dst src}, (instantaneous dst = some src) → dst.type = src.type

end Class
end Network.Graph
