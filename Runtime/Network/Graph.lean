import Runtime.Reactor
import Runtime.Utilities

namespace Network

abbrev ReactorID := Tree.Path.Rooted

-- A network graph is a tree of reactor ids with a function 
-- that maps each path in that tree to a reactor scheme.
structure Graph where
  tree : Tree
  schemes : (ReactorID tree) → Reactor.Scheme

structure ActionID (graph : Graph) where
  reactor : ReactorID graph.tree
  action : (graph.schemes reactor .actions).vars

structure PortID (kind : Reactor.PortKind) (graph : Graph) where
  reactor : ReactorID graph.tree
  port : (graph.schemes reactor kind).vars

abbrev Connection (graph : Graph) := (PortID .output graph) × (PortID .input graph)

structure Event (graph : Graph) (min : Time) where
  id    : ActionID graph
  time  : Time.From min
  value : (graph.schemes id.reactor .actions).type id.action

abbrev Graph.subschemes (graph : Graph) (reactorID : ReactorID graph.tree) : graph.tree[reactorID].branches → Reactor.Scheme := 
  fun branch => graph.schemes (reactorID.extensions branch)

abbrev Graph.reactionType (graph : Graph) (reactorID : ReactorID graph.tree) :=
  let scheme := graph.schemes reactorID
  let subschemes := graph.subschemes reactorID
  let branches := graph.tree[reactorID].branches
  let nested interface := Interface.Scheme.bUnion branches fun branch => (subschemes branch) interface
  let inputs := scheme .inputs ∪ (nested .outputs)
  let outputs := scheme .outputs ∪ (nested .inputs)
  Reaction inputs outputs (scheme .actions) (scheme .state)

end Network