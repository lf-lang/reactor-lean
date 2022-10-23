import Runtime.Network.Graph

open Network Graph in
structure Network extends Graph where
  root        : Class toGraph
  reactions   : (cls : Class toGraph) → Array cls.reactionType
  connections : (cls : Class toGraph) → Class.Connections cls

namespace Network

instance : Coe Network Graph := ⟨toGraph⟩

-- TODO: These might not work at call site, as `net` might not be inferred.
def Graph.Class.reactions {net : Network} (cls : Class net) := net.reactions cls
def Graph.Class.connections {net : Network} (cls : Class net) := net.connections cls

abbrev ReactorId (net : Network) := Graph.Path net net.root

structure ActionId (net : Network) where
  reactor : ReactorId net
  action : (reactor.class.interface .actions).vars
  deriving DecidableEq

structure ReactionId (net : Network) where
  reactor : ReactorId net
  reactionIdx : Fin reactor.class.reactions.size

abbrev ReactionId.reaction (id : ReactionId net) :=
  id.reactor.class.reactions[id.reactionIdx]

structure TimerId (net : Network) where
  reactor : ReactorId net
  timer : reactor.class.timers
  deriving DecidableEq

end Network