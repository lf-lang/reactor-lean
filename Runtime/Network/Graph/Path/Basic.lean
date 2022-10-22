import Runtime.Network.Graph.Basic

namespace Network.Graph

inductive Path (graph : Graph) : Class graph → Type _
  | nil : Path graph _
  | cons {start : Class graph} (child : Class.Child start) : Path graph child.class → Path graph start
  deriving DecidableEq

namespace Path

def isCons : Path graph start → Bool
  | .nil => false
  | .cons .. => true

theorem isCons_of_cons : (Path.cons child subpath).isCons := rfl

theorem isCons_of_eq_cons {path : Path graph start} : (path = .cons child subpath) → path.isCons :=
  (by rw [·, isCons_of_cons])

theorem isCons_def {path : Path graph start} : path.isCons ↔ (∃ child subpath, path = .cons child subpath) := by
  simp [isCons]
  constructor
  case mp => 
    split <;> intro
    · contradiction
    · exists ‹_›, ‹_›
  case mpr =>
    intro ⟨_, _, h⟩
    simp [h]

def «class» : (Path graph start) → Class graph
  | .nil            => start
  | .cons _ subpath => subpath.class

@[simp]
theorem nil_class : (nil : Path graph start).class = start := rfl

@[simp]
theorem cons_class : (Path.cons child subpath).class = subpath.class := rfl

@[simp]
theorem eq_class_iff_cons_eq_class : (path₁.class = path₂.class) ↔ (Path.cons child₁ path₁).class = (Path.cons child₂ path₂).class := ⟨id, id⟩

instance {path : Path graph start} {reaction : path.class.reactionType} : 
  InjectiveCoe reaction.portSources path.class.reactionInputScheme.vars :=
  reaction.portSourcesInjCoe

instance {path : Path graph start} {reaction : path.class.reactionType} : 
  InjectiveCoe reaction.portEffects path.class.reactionOutputScheme.vars :=
  reaction.portEffectsInjCoe

instance {path : Path graph start} {reaction : path.class.reactionType} : 
  InjectiveCoe reaction.actionSources (path.class.interface .actions).vars :=
  reaction.actionSourcesInjCoe

end Path
end Network.Graph