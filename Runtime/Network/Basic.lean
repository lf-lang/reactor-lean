import Runtime.Network.Graph

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