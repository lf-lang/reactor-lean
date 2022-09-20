import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  schemes : classes → (Reactor.Scheme classes)
  root : classes

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
  | last (child : graph.rootScheme.children) : Path graph
  | cons (child : graph.rootScheme.children) : Path (graph.rootScheme.class child |> graph.subgraph) → Path graph
  deriving DecidableEq

def Graph.class (graph : Graph) : (Path graph) → graph.classes
  | .last child         => graph.rootScheme.class child
  | .cons child subpath => graph.rootScheme.class child |> graph.subgraph |>.class subpath

abbrev Graph.scheme (graph : Graph) (path : Path graph) : Reactor.Scheme graph.classes :=
  graph.class path |> graph.schemes

abbrev Graph.Path.extend {graph} (path : Path graph) (extension : graph.scheme path |>.children) : Path graph :=
  match path with
  | .last child         => .cons child (.last extension)
  | .cons child subpath => .cons child (subpath.extend extension)

structure _root_.Network extends Graph where
  reactions : («class» : toGraph.classes) → Array (toGraph.reactionType «class»)

abbrev graph (net : Network) : Graph := net.toGraph

inductive ReactorID (net : Network)
  | main 
  | nested (path : Graph.Path net.graph)
  deriving DecidableEq

abbrev «class» (net : Network) : (ReactorID net) → net.classes
  | .main => net.root
  | .nested path => net.graph.class path

abbrev scheme (net : Network) : (ReactorID net) → (Reactor.Scheme net.classes)
  | .main => net.rootScheme
  | .nested path => net.graph.scheme path

theorem scheme_def : {reactorID : ReactorID net} → net.scheme reactorID = net.schemes (net.class reactorID)
  | .main | .nested _ => rfl

abbrev ReactorID.extend (id : ReactorID net) (extension : net.scheme id |>.children) : ReactorID net :=
  match id with
  | .main => .nested <| .last extension
  | .nested path => .nested <| path.extend extension

abbrev reactionInputScheme (net : Network) (reactorID : ReactorID net) :=
  net.graph.reactionInputScheme <| net.class reactorID

abbrev reactionType (net : Network) (reactorID : ReactorID net) :=
  net.graph.reactionType <| net.class reactorID

-- Lean can't infer this automatically.
instance {net : Network} {reactorID : ReactorID net} {reaction : net.reactionType reactorID} : 
  InjectiveCoe reaction.portSources (net.reactionInputScheme reactorID).vars :=
  reaction.portSourcesInjCoe

-- Lean can't infer this automatically.
instance {net : Network} {reactorID : ReactorID net} {reaction : net.reactionType reactorID} : 
  InjectiveCoe reaction.actionSources ((net.scheme reactorID).interface .actions).vars :=
  scheme_def.symm ▸ reaction.actionSourcesInjCoe

structure ActionID (net : Network) where
  reactor : ReactorID net
  action : net.scheme reactor |>.interface .actions |>.vars
  deriving DecidableEq

structure PortID (kind : Reactor.PortKind) (net : Network) where
  reactor : ReactorID net
  port : net.scheme reactor |>.interface kind |>.vars

-- A map from input ports to output ports with matching type.
-- Since each input port can have at most one output port that connects to it,
-- the return type is an optional output port.
structure Connections (net : Network) where
  map : (PortID .input net) → Option (PortID .output net)
  eqType : (map input = some output) → (net.scheme output.reactor |>.interface .outputs).type output.port = (net.scheme input.reactor |>.interface .inputs).type input.port

instance : CoeFun (Connections net) (fun _ => PortID .input net → Option (PortID .output net)) where
  coe := (·.map)

structure ReactionID (net : Network) where
  reactor : ReactorID net
  reactionIdx : Fin (net.class reactor |> net.reactions).size

abbrev reaction (net : Network) (id : ReactionID net) : net.reactionType id.reactor :=
  (net.class id.reactor |> net.reactions)[id.reactionIdx]

end Network