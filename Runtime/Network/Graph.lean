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

set_option trace.Meta.synthInstance true -- TEMP

abbrev Graph.reactionType (graph : Graph) (reactorID : ReactorID graph.tree) :=
  let scheme := graph.schemes reactorID
  let subschemes := graph.subschemes reactorID
  let branches := graph.tree[reactorID].branches
  let nestedOutputs := Interface.Scheme.bUnion branches sorry -- fun branch => (subschemes branch) .outputs
  let nestedInputs := sorry -- Interface.Scheme.bUnion branches sorry -- fun branch => (subschemes branch) .inputs
  let sources := scheme .inputs ∪ nestedOutputs
  let effects := scheme .outputs ∪ nestedInputs
  Reaction sources effects (scheme .actions) (scheme .state)

end Network