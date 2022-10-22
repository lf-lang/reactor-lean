import Runtime.Network.Graph.Basic

namespace Network.Graph

inductive Path (graph : Graph) : Class graph → Type _
  | nil : Path graph _
  | cons {start : Class graph} (child : Class.Child start) : Path graph child.class → Path graph start
  deriving DecidableEq

namespace Path

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