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

theorem Graph.Path.extend_scheme {graph : Graph} {path : Path graph} {child : graph.scheme path |>.children} : 
  (graph.scheme path |>.class child |> graph.schemes) = (path.extend child |> graph.scheme) := by
  induction path <;> simp [extend, scheme, «class»]
  case cons graph hd tl hi =>
    congr
    specialize @hi child
    cases hc : extend tl child
    · sorry
    · sorry

def Graph.Path.isChildOf : Path graph → Path graph → Bool
  | .cons _ .nil, .nil => true 
  | .cons child₁ subpath₁, .cons child₂ subpath₂ => 
    if h : child₁ = child₂ 
    then subpath₁.isChildOf (h ▸ subpath₂) 
    else false
  | _, _ => false

theorem Graph.Path.isChildOf_cons_eq_child : isChildOf (.cons child₁ child) (.cons child₂ parent) → child₁ = child₂ := by
  intro h
  simp [isChildOf] at h
  split at h <;> simp [*]

theorem Graph.Path.isChildOf_cons : isChildOf (.cons child' child) (.cons child' parent) → child.isChildOf parent :=
  fun _ => by simp_all [isChildOf]

def Graph.Path.last (child : Path graph) {parent} (h : child.isChildOf parent) : (graph.scheme parent).children :=
  match child, parent with
  | .cons child₁ .nil, .nil => child₁
  | .cons child₁ subpath₁, .cons child₂ subpath₂ =>
    have hc : child₁ = child₂ := isChildOf_cons_eq_child h
    (hc ▸ subpath₁).last (by subst hc; exact isChildOf_cons h)

def Graph.Path.isSiblingOf : Path graph → Path graph → Bool
  | .cons _ .nil, .cons _ .nil => true -- we allow a child to be its own sibling
  | .cons child₁ subpath₁, .cons child₂ subpath₂ =>
    if h : child₁ = child₂ 
    then subpath₁.isSiblingOf (h ▸ subpath₂) 
    else false
  | _, _ => false

/-
theorem Graph.Path.isSiblingOf_symm {path₁ path₂ : Path graph} : (path₁.isSiblingOf path₂) → (path₂.isSiblingOf path₁) := by
  intro h
  unfold isSiblingOf at h
  split at h <;> simp [isSiblingOf] at *
  split at h <;> simp [isSiblingOf] at *
  rename_i hc
  have h' := isSiblingOf_symm h
  sorry -- sibling -> cons is also sibling
-/

theorem Graph.Path.isSiblingOf_is_cons : isSiblingOf path₁ path₂ → ∃ child parent, path₁ = .cons child parent := by
  intro h
  unfold isSiblingOf at h
  split at h
  · rename_i child _
    exists child, nil
  · rename_i subpath _ _ _
    sorry
  · contradiction

-- Note the prefix of `.nil` is `.nil`.
def Graph.Path.prefix : Path graph → Path graph
  | .nil | .cons _ .nil => .nil
  | .cons head subpath => .cons head subpath.prefix

theorem Graph.Path.cons_isChildOf_prefix : isChildOf (.cons child parent) («prefix» <| .cons child parent) := by
  sorry

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
  Reaction 
    (graph.reactionInputScheme «class») 
    (graph.reactionOutputScheme «class») 
    (localScheme .actions) 
    (localScheme .state) 
    (graph.schemes «class»).timers

abbrev Graph.reactionInputScheme' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionInputScheme <| graph.class reactorID

abbrev Graph.reactionOutputScheme' (graph : Graph) (reactorID : ReactorID graph) :=
  graph.reactionOutputScheme <| graph.class reactorID

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
  InjectiveCoe reaction.portEffects (graph.reactionOutputScheme' reactorID).vars :=
  reaction.portEffectsInjCoe

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

macro "eqTypeProof" : tactic => `(intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp)
structure Connections (graph : Graph) («class» : graph.classes) where
  source : (Subport graph «class» .input) → Option (Subport graph «class» .output)
  eqType : (source input = some output) → (graph.subinterface «class» output.reactor .outputs).type output.port = (graph.subinterface «class» input.reactor .inputs).type input.port := by eqTypeProof

def Connections.empty {graph : Graph} {«class» : graph.classes} : Connections graph «class» where
  source _ := none
  eqType := by simp [source]

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

abbrev connections' (net : Network) (reactorID : ReactorID net) : (Connections net <| net.class reactorID) :=
  net.class reactorID |> net.connections

structure TimerID (net : Network) where
  reactor : ReactorID net
  timer : net.scheme reactor |>.timers
  deriving DecidableEq

end Network