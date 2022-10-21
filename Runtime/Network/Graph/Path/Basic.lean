import Runtime.Network.Graph.Class

namespace Network.Graph

inductive Path (graph : Graph) : Class graph → Type _
  | nil : Path graph _
  | cons {start : Class graph} (child : start.scheme.children) : Path graph (start.child child) → Path graph start
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

abbrev scheme (path : Path graph start) := path.class.scheme

@[simp]
theorem nil_scheme : (nil : Path graph start).scheme = start.scheme := rfl

@[simp]
theorem cons_scheme : (Path.cons child subpath).scheme = subpath.scheme := rfl

@[simp]
theorem eq_scheme_iff_cons_eq_scheme : (path₁.scheme = path₂.scheme) ↔ (Path.cons child₁ path₁).scheme = (Path.cons child₂ path₂).scheme := ⟨id, id⟩

abbrev reactionInputScheme (path : Graph.Path graph start) :=
  path.class.reactionInputScheme

abbrev reactionOutputScheme (path : Graph.Path graph start) :=
  path.class.reactionOutputScheme 

abbrev reactionType (path : Graph.Path graph start) :=
  path.class.reactionType

instance {path : Path graph start} {reaction : path.reactionType} : 
  InjectiveCoe reaction.portSources path.reactionInputScheme.vars :=
  reaction.portSourcesInjCoe

instance {path : Path graph start} {reaction : path.reactionType} : 
  InjectiveCoe reaction.portEffects path.reactionOutputScheme.vars :=
  reaction.portEffectsInjCoe

instance {path : Path graph start} {reaction : path.reactionType} : 
  InjectiveCoe reaction.actionSources (path.scheme.interface .actions).vars :=
  reaction.actionSourcesInjCoe

end Path
end Network.Graph