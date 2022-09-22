import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root : classes
  schemes : classes → (Reactor.Scheme classes)

attribute [reducible] Graph.schemes

abbrev Graph.rootScheme (graph : Graph) := graph.schemes graph.root

abbrev Graph.subgraph (graph : Graph) (newRoot : graph.classes) : Graph := 
  { graph with root := newRoot }

inductive Graph.Path : Graph → Type _
  | nil : Path graph
  | cons (child : graph.rootScheme.children) : Path (graph.rootScheme.class child |> graph.subgraph) → Path graph
  deriving DecidableEq

def Graph.class (graph : Graph) : (Path graph) → graph.classes
  | .nil                => graph.root
  | .cons child subpath => graph.rootScheme.class child |> graph.subgraph |>.class subpath

abbrev Graph.scheme (graph : Graph) (path : Path graph) : Reactor.Scheme graph.classes :=
  graph.class path |> graph.schemes

abbrev Graph.Path.extend {graph} (path : Path graph) (extension : graph.scheme path |>.children) : Path graph :=
  match path with
  | .nil                => .cons extension .nil
  | .cons child subpath => .cons child (subpath.extend extension)

abbrev ReactorID (graph : Graph) := Graph.Path graph

abbrev Graph.interface (graph : Graph) («class» : graph.classes) :=
  graph.schemes «class» |>.interface 

abbrev Graph.interface' (graph : Graph) (reactorID : Path graph) :=
  graph.class reactorID |> graph.interface 

abbrev Graph.subinterface (graph : Graph) («class» : graph.classes) (child : graph.schemes «class» |>.children) :=
  graph.schemes «class» |>.class child |> graph.interface

abbrev Graph.subinterface' (graph : Graph) («class» : graph.classes) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child => graph.subinterface «class» child kind

abbrev Graph.reactionInputScheme (graph : Graph) («class» : graph.classes) :=
  let localInputs := graph.schemes «class» |>.interface .inputs
  let nestedOutputs := graph.subinterface' «class» .outputs
  localInputs ⊎ nestedOutputs

abbrev Graph.reactionOutputScheme (graph : Graph) («class» : graph.classes) :=
  let localOutputs := graph.schemes «class» |>.interface .outputs
  let nestedInputs := graph.subinterface' «class» .inputs
  localOutputs ⊎ nestedInputs

abbrev Graph.reactionType (graph : Graph) («class» : graph.classes) :=
  let localScheme := graph.interface «class»
  Reaction (graph.reactionInputScheme «class») (graph.reactionOutputScheme «class») (localScheme .actions) (localScheme .state)

abbrev Graph.reactionInputScheme' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionInputScheme <| graph.class reactorID

abbrev Graph.reactionType' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionType <| graph.class reactorID

-- TODO: Recheck this:
-- Lean can't infer this automatically.
@[reducible]
instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.portSources (graph.reactionInputScheme' reactorID).vars :=
  reaction.portSourcesInjCoe

-- TODO: Recheck this:
-- Lean can't infer this automatically.
@[reducible]
instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.actionSources (graph.interface' reactorID .actions).vars :=
  reaction.actionSourcesInjCoe

structure ActionID (graph : Graph) where
  reactor : ReactorID graph
  action : graph.interface' reactor .actions |>.vars
  deriving DecidableEq

structure Subport (graph : Graph) («class» : graph.classes) (kind : Reactor.PortKind) where
  reactor : graph.schemes «class» |>.children
  port : graph.subinterface «class» reactor kind |>.vars
  deriving DecidableEq -- TODO: Remove this if pattern matching works for connections in Main.lean.

structure Connections (graph : Graph) («class» : graph.classes) where
  outForIn : (Subport graph «class» .input) → Option (Subport graph «class» .output)
  eqType : (outForIn input = some output) → (graph.subinterface «class» output.reactor .outputs).type output.port = (graph.subinterface «class» input.reactor .inputs).type input.port

def Connections.empty {graph : Graph} {«class» : graph.classes} : Connections graph «class» := {
  outForIn := fun _ => none
  eqType := by simp [outForIn]
}

structure _root_.Network extends Graph where
  reactions : («class» : toGraph.classes) → Array (toGraph.reactionType «class»)
  connections : («class» : toGraph.classes) → (Connections toGraph «class»)

instance : Coe Network Graph where
  coe := (·.toGraph)

structure ReactionID (net : Network) where
  reactor : ReactorID net
  reactionIdx : Fin (net.class reactor |> net.reactions).size

abbrev reaction (net : Network) (id : ReactionID net) : net.reactionType' id.reactor :=
  (net.class id.reactor |> net.reactions)[id.reactionIdx]

end Network