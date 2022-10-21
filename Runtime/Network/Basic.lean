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

structure Graph.Class.Subport (cls : Class graph) (kind : Reactor.PortKind) where
  reactor : cls.scheme.children
  port : (cls.child reactor).interface kind |>.vars

abbrev Graph.Class.Subport.type (subport : Subport cls kind) : Type := 
  let subclass := cls.child subport.reactor
  let subinterface := subclass.interface kind 
  subinterface.type subport.port

-- TODO: The `eqTypeProof` is probably broken.
macro "eqTypeProof" : tactic => `(intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp)
structure Graph.Class.Connections (cls : Class graph) where 
  source : (Class.Subport cls .input) → Option (Class.Subport cls .output)
  eqType : (source input = some output) → (input.type = output.type) := by eqTypeProof

def Graph.Class.Connections.empty {cls : Graph.Class graph} : Graph.Class.Connections cls where
  source _ := none
  eqType := by simp

open Graph in
structure _root_.Network extends Graph where
  root        : Class toGraph
  reactions   : (cls : Class toGraph) → Array cls.reactionType
  connections : (cls : Class toGraph) → Class.Connections cls

instance : Coe Network Graph where
  coe := (·.toGraph)

abbrev ReactorId (net : Network) := Graph.Path net net.root

def ReactorId.reactions (id : ReactorId net) :=
  net.reactions id.class

def ReactorId.connections (id : ReactorId net) :=
  net.connections id.class

structure ActionId (net : Network) where
  reactor : ReactorId net
  action : (reactor.scheme.interface .actions).vars
  deriving DecidableEq

structure ReactionId (net : Network) where
  reactor : ReactorId net
  reactionIdx : Fin reactor.reactions.size

abbrev ReactionId.reaction (id : ReactionId net) :=
  id.reactor.reactions[id.reactionIdx]

structure TimerId (net : Network) where
  reactor : ReactorId net
  timer : reactor.scheme.timers
  deriving DecidableEq

end Network