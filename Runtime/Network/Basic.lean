import Runtime.Network.Graph
open Network Graph

-- Note: We're not restricting `connections` to enforce uniqueness of
--       connections to input ports, as this is handled by the LF frontend.
structure Network extends Graph where
  root        : Class toGraph
  reactions   : (cls : Class toGraph) → Array (Class.Reaction cls)
  connections : (cls : Class toGraph) → Array (Class.Connection cls)

namespace Network

instance : Coe Network Graph := ⟨toGraph⟩

abbrev Graph.Class.reactions {net : Network} (cls : Class net) := net.reactions cls

abbrev Graph.Class.connections {net : Network} (cls : Class net) := net.connections cls

def Graph.Class.nonDelayedSource {net : Network} (cls : Class net) (dst : Class.Subport cls .input) : Option (Class.Subport cls .output) :=
  cls.connections.findSome? fun con => if con.dst = dst then con.src else none

theorem Graph.Class.nonDelayedSource_eqType {net : Network} {cls : Class net} {dst src} :
  (cls.nonDelayedSource dst = some src) → (dst.type = src.type) := by
  intro h
  have ⟨con, _, hs⟩ := Array.findSome?_some h
  split at hs <;> simp at hs
  case _ hd => rw [←hd, ←hs, con.eqType]

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

def ReactionId.affects (id : ReactionId net) (port : (id.reactor.class.interface .outputs).vars) : Bool :=
  id.reaction.subPE.inv (.inl port) |>.isSome

structure TimerId (net : Network) where
  reactor : ReactorId net
  timer   : reactor.class.timers
  deriving DecidableEq

end Network