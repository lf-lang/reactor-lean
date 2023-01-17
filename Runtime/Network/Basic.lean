import Runtime.Network.Graph
open Network Graph

structure Network extends Graph where
  root        : Class toGraph
  reactions   : (cls : Class toGraph) → Array (Class.Reaction cls)
  connections : (cls : Class toGraph) → Class.Connections cls

namespace Network

instance : Coe Network Graph := ⟨toGraph⟩

abbrev Graph.Class.reactions {net : Network} (cls : Class net) := net.reactions cls

abbrev Graph.Class.connections {net : Network} (cls : Class net) := net.connections cls

abbrev ReactorId (net : Network) := Graph.Path net net.root

abbrev ReactorId.Child (reactor : ReactorId net) := { child : ReactorId net // child ≻ reactor }

abbrev ReactorId.Child.class (child : Child reactor) : Graph.Class.Child reactor.class :=
  let child : Graph.Path.Child reactor := child
  child.class

abbrev ReactorId.inputs (reactor : ReactorId net) :=
  reactor.class.interface .inputs

abbrev ReactorId.outputs (reactor : ReactorId net) :=
  reactor.class.interface .outputs

abbrev ReactorId.isRoot (reactor : ReactorId net) :=
  reactor.isNil

structure ActionId (net : Network) where
  reactor : ReactorId net
  action  : (reactor.class.interface .actions).vars
  deriving DecidableEq

structure ReactionId (net : Network) where
  reactor     : ReactorId net
  reactionIdx : Fin reactor.class.reactions.size

abbrev ReactionId.reaction (id : ReactionId net) :=
  id.reactor.class.reactions[id.reactionIdx]

def ReactionId.affects (id : ReactionId net) (port : (id.reactor.outputs).vars) : Bool :=
  id.reaction.subPE.inv (.inl port) |>.isSome

structure TimerId (net : Network) where
  reactor : ReactorId net
  timer   : reactor.class.timers
  deriving DecidableEq

structure PortId (net : Network) (kind : Reactor.PortKind) where
  reactor : ReactorId net
  port    : reactor.class.interface kind |>.vars
  deriving DecidableEq

namespace PortId

abbrev type (port : PortId net kind) : Type :=
  port.reactor.class.interface kind |>.type port.port

def hasDelayedConnection (port : PortId net .output) : Bool :=
  if h : port.reactor.isCons then
    -- TODO: We can't destruct here because then the type cast on `port.port` doesn't work.
    let split := port.reactor.split h
    let parent := split.fst
    let leaf := split.snd
    ¬ (parent.class.connections.delayed ⟨leaf, Path.split_class h ▸ port.port⟩ |>.isEmpty)
  else
    -- In this case the reaction that produced the output lives in the top level reactor,
    -- so there are no connections.
    false

structure DelayedDestination (port : PortId net .output) where
  dst : PortId net .input
  delay : Duration
  eqType : (port.reactor.outputs).type port.port = (dst.reactor.inputs).type dst.port

open Path in
def delayedDestinations (port : PortId net .output) : Array (DelayedDestination port) :=
  if h : port.reactor.isCons then
    -- TODO: We can't destruct here because then the type cast on `port` doesn't work.
    let split := port.reactor.split h
    let parent := split.fst
    let leaf := split.snd
    have h₁ := by rw [split_class h]
    let src := ⟨leaf, port.port |> cast h₁⟩
    parent.class.connections.delayed src |>.map fun { dst, delay, eqType } => {
      delay
      dst :=
        have h₂ := by rw [extend_class]
        ⟨parent.extend dst.child, dst.port |> cast h₂⟩
      eqType := by
        simp [ReactorId.outputs, ReactorId.inputs]
        suffices h : port.reactor.outputs.type port.port = src.type by
          rw [h, eqType, Class.Subport.type]
          congr <;> simp [(cast_heq _ _).symm]
        congr <;> simp [split_class, (cast_heq _ _).symm]
    }
  else
    -- In this case the reaction that produced the output lives in the top level reactor,
    -- so there are no connections and hence no destinations.
    #[]

end PortId
end Network
