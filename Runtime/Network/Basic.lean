import Runtime.Reactor

namespace Network

structure Graph (Classes : Type) where 
  schemes : Classes → (Reactor.Scheme Classes)

def Graph.subschemes (graph : Graph Classes) («class» : Classes) : (graph.schemes «class»).children → Reactor.Scheme Classes := 
  fun child => graph.schemes «class» |>.class child |> graph.schemes

def Graph.subscheme (graph : Graph Classes) («class» : Classes) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child => (graph.subschemes «class» child).interface kind

def Graph.reactionInputScheme (graph : Graph Classes) («class» : Classes) :=
  let localInputs := (graph.schemes «class»).interface .inputs
  let nestedOutputs := graph.subscheme «class» .outputs
  localInputs ⊎ nestedOutputs

def Graph.reactionOutputScheme (graph : Graph Classes) («class» : Classes) :=
  let localOutputs := (graph.schemes «class»).interface .outputs
  let nestedInputs := graph.subscheme «class» .inputs
  localOutputs ⊎ nestedInputs

def Graph.reactionType (graph : Graph Classes) («class» : Classes) :=
  let localScheme := graph.schemes «class» |>.interface
  Reaction (graph.reactionInputScheme «class») (graph.reactionOutputScheme «class») (localScheme .actions) (localScheme .state)

structure Network where
  classes : Type
  graph : Graph classes
  main : Class
  reactions : («class» : classes) → graph.reactionType «class»

def Network.schemes (net : Network) : net.classes → (Reactor.Scheme net.classes) :=
  net.graph.schemes







partial def Network.instances (net : Network) : Tree :=
  aux net net.main
where 
  aux (net : Network) («class» : net.classes) : Tree :=
    let scheme := net.schemes «class»
    .node scheme.children fun child => aux net (scheme.class child)

mutual

inductive ReactorID (net : Network)
  | main
  | cons (hd : ReactorID net) (tl : Network.class net hd)

def Network.class (net : Network) : (ReactorID net) → net.classes
  | .main => net.main
  | .cons _ _ => sorry

end 













structure ActionID (net : Network) where
  reactor : ReactorID net
  action : (net.schemes reactor .actions).vars

-- TODO: This is exactly the same as the instance for `DecidableEq (Σ a : Type, a)`.
instance : DecidableEq (ActionID graph) :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => 
    if h : a₁ = a₂ then 
      if h' : (h ▸ b₁) = b₂ then
        .isTrue (by subst h h'; rfl)
      else 
        .isFalse (by 
          subst h
          intro hc
          injection hc
          contradiction
        )
    else
      .isFalse (by
        intro hc
        injection hc
        contradiction
      )

structure PortID (kind : Reactor.PortKind) (graph : Graph) where
  reactor : ReactorID graph.tree
  port : (graph.schemes reactor kind).vars

-- TODO: This isn't needed if constructing a network's connections via pattern matching works.
-- TODO: This is exactly the same as the instance for `DecidableEq (Σ a : Type, a)`.
instance : DecidableEq (PortID kind graph) := 
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => 
    if h : a₁ = a₂ then 
      if h' : (h ▸ b₁) = b₂ then
        .isTrue (by subst h h'; rfl)
      else 
        .isFalse (by 
          subst h
          intro hc
          injection hc
          contradiction
        )
    else
      .isFalse (by
        intro hc
        injection hc
        contradiction
      )

-- Lean can't "see through" this automatically.
theorem Graph.reactionOutputScheme_local_type (graph : Graph) (reactorID output) :
  (graph.reactionOutputScheme reactorID).type (.inl output) = ((graph.schemes reactorID) .outputs).type output := rfl

abbrev Graph.reactionType (graph : Graph) (reactorID : ReactorID graph.tree) :=
  let localScheme := graph.schemes reactorID
  Reaction (graph.reactionInputScheme reactorID) (graph.reactionOutputScheme reactorID) (localScheme .actions) (localScheme .state)

-- Lean can't automatically infer this automatically.
instance {graph : Graph} {reactorID : ReactorID graph.tree} {reaction : graph.reactionType reactorID} : 
  InjectiveCoe reaction.portSources (graph.reactionInputScheme reactorID).vars :=
  reaction.portSourcesInjCoe

-- Lean can't automatically infer this automatically.
instance {graph : Graph} {reactorID : ReactorID graph.tree} {reaction : graph.reactionType reactorID} : 
  InjectiveCoe reaction.portEffects (graph.reactionOutputScheme reactorID).vars :=
  reaction.portEffectsInjCoe

-- A map from input ports to output ports with matching type.
-- Since each input port can have at most one output port that connects to it,
-- the return type is an optional output port.
structure Connections (graph : Graph) where
  map : (PortID .input graph) → Option (PortID .output graph)
  eqType : (map input = some output) → (graph.schemes output.reactor .outputs).type output.port = (graph.schemes input.reactor .inputs).type input.port

instance : CoeFun (Connections graph) (fun _ => PortID .input graph → Option (PortID .output graph)) where
  coe c := c.map

structure _root_.Network extends Graph where
  connections : Connections toGraph
  reactions : (id : ReactorID toGraph.tree) → Array (toGraph.reactionType id) 
  -- TODO: We only want a mapping from each reactor scheme to an array of reactions.
  --       This also means that we could map each 

abbrev graph (net : Network) : Graph := net.toGraph

structure ReactionID (net : Network) where
  reactor : ReactorID net.tree
  reactionIdx : Fin (net.reactions reactor).size

abbrev reaction (net : Network) (id : ReactionID net) : net.reactionType id.reactor :=
  (net.reactions id.reactor)[id.reactionIdx]

end Network