import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root : classes
  schemes : classes → (Reactor.Scheme classes)

abbrev Graph.rootScheme (graph : Graph) := graph.schemes graph.root

abbrev Graph.subgraph (graph : Graph) (newRoot : graph.classes) : Graph := 
  { graph with root := newRoot }

abbrev Graph.subinterface (graph : Graph) («class» : graph.classes) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child => graph |>.schemes «class» |>.class child |> graph.schemes |>.interface kind

abbrev Graph.reactionInputScheme (graph : Graph) («class» : graph.classes) :=
  let localInputs := graph.schemes «class» |>.interface .inputs
  let nestedOutputs := graph.subinterface «class» .outputs
  localInputs ⊎ nestedOutputs

abbrev Graph.reactionOutputScheme (graph : Graph) («class» : graph.classes) :=
  let localOutputs := graph.schemes «class» |>.interface .outputs
  let nestedInputs := graph.subinterface «class» .inputs
  localOutputs ⊎ nestedInputs

abbrev Graph.reactionType (graph : Graph) («class» : graph.classes) :=
  let localScheme := graph.schemes «class» |>.interface
  Reaction (graph.reactionInputScheme «class») (graph.reactionOutputScheme «class») (localScheme .actions) (localScheme .state)

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

abbrev Graph.reactionInputScheme' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionInputScheme <| graph.class reactorID

abbrev Graph.reactionType' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionType <| graph.class reactorID

-- Lean can't infer this automatically.
instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.portSources (graph.reactionInputScheme' reactorID).vars :=
  reaction.portSourcesInjCoe

-- Lean can't infer this automatically.
instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.actionSources ((graph.scheme reactorID).interface .actions).vars :=
  reaction.actionSourcesInjCoe

structure ActionID (graph : Graph) where
  reactor : ReactorID graph
  action : graph.scheme reactor |>.interface .actions |>.vars
  deriving DecidableEq

structure PortID (kind : Reactor.PortKind) (graph : Graph) where
  reactor : ReactorID graph
  port : graph.scheme reactor |>.interface kind |>.vars
  deriving DecidableEq

-- TODO: Connections can also be constructed at the class-level instead of the
--       instance level!
-- A map from input ports to output ports with matching type.
-- Since each input port can have at most one output port that connects to it,
-- the return type is an optional output port.
structure Connections (graph : Graph) where
  outForIn : (PortID .input graph) → Option (PortID .output graph)
  eqType : (outForIn input = some output) → (graph.scheme output.reactor |>.interface .outputs).type output.port = (graph.scheme input.reactor |>.interface .inputs).type input.port

instance : CoeFun (Connections graph) (fun _ => PortID .input graph → Option (PortID .output graph)) where
  coe := (·.outForIn)

structure _root_.Network extends Graph where
  reactions : («class» : toGraph.classes) → Array (toGraph.reactionType «class»)
  connections : Connections toGraph

instance : Coe Network Graph where
  coe := (·.toGraph)

structure ReactionID (net : Network) where
  reactor : ReactorID net
  reactionIdx : Fin (net.class reactor |> net.reactions).size

abbrev reaction (net : Network) (id : ReactionID net) : net.reactionType' id.reactor :=
  (net.class id.reactor |> net.reactions)[id.reactionIdx]

end Network