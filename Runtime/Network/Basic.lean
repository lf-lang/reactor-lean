import Runtime.Network.Graph

namespace Network

/-
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

theorem Graph.Path.isSiblingOf_symm {path₁ path₂ : Path graph} : (path₁.isSiblingOf path₂) → (path₂.isSiblingOf path₁) := by
  intro h
  unfold isSiblingOf at h
  split at h <;> simp [isSiblingOf] at *
  split at h <;> simp [isSiblingOf] at *
  rename_i hc
  have h' := isSiblingOf_symm h
  sorry -- sibling -> cons is also sibling

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
  | .cons head subpath  => .cons head subpath.prefix

theorem Graph.Path.cons_isChildOf_prefix : isChildOf (.cons child parent) («prefix» <| .cons child parent) := by
  sorry
-/

-- TODO: Rename this to ReactorId.
--       Should this be rooted already?
--       Perhaps at this point we shouldn't even be using ReactorID yet, but stay at Graph.Path.
abbrev ReactorID (graph : Graph) := Graph.Path graph graph.root

-- TODO: Graph.subinterface seems to be a representative of the following API problem.
--       having something like an element of `graph.classes` contains a bunch of information, which always requires
--       us to go through `graph` though.
--       E.g. if we want to access one of the class's childrens scheme:
--       (graph.schemes «class»).class child |> graph.scheme
-- Solution?:

abbrev Graph.Path.reactionInputScheme (path : Graph.Path graph start) :=
  path.class.reactionInputScheme

abbrev Graph.reactionOutputScheme (path : Graph.Path graph start) :=
  path.class.reactionOutputScheme 

abbrev Graph.reactionType (path : Graph.Path graph start) :=
  path.class.reactionType

instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.portSources (graph.reactionInputScheme' reactorID).vars :=
  reaction.portSourcesInjCoe

instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.portEffects (graph.reactionOutputScheme' reactorID).vars :=
  reaction.portEffectsInjCoe

instance {reactorID : ReactorID graph} {reaction : graph.reactionType' reactorID} : 
  InjectiveCoe reaction.actionSources (reactorID.scheme.interface .actions).vars :=
  reaction.actionSourcesInjCoe

structure ActionID (graph : Graph) where
  reactor : ReactorID graph
  action : reactor.scheme.interface .actions |>.vars
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
  reactionIdx : Fin (net.reactions reactor.class).size

abbrev reaction (net : Network) (id : ReactionID net) : net.reactionType' id.reactor :=
  (net.reactions id.reactor.class)[id.reactionIdx]

abbrev connections' (net : Network) (reactorID : ReactorID net) : (Connections net reactorID.class) :=
  net.connections reactorID.class

structure TimerID (net : Network) where
  reactor : ReactorID net
  timer : reactor.scheme.timers
  deriving DecidableEq

end Network