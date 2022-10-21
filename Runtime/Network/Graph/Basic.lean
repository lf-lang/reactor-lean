import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root    : classes -- TODO: Is the root still needed now that paths are relative? Or should it be moved to `Network`?
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Graph.decEqClasses

namespace Graph

inductive Path (graph : Graph) : graph.classes → Type _
  | nil : Path graph _
  | cons {start : graph.classes} (child : (graph.schemes start).children) : Path graph (graph.schemes start |>.class child) → Path graph start
  deriving DecidableEq

namespace Path

def «class» : (Path graph start) → graph.classes
  | .nil            => start
  | .cons _ subpath => subpath.class

@[simp]
theorem nil_class : (nil : Path graph start).class = start := rfl

@[simp]
theorem cons_class : (Path.cons child subpath).class = subpath.class := rfl

abbrev scheme (path : Path graph start) : Reactor.Scheme graph.classes :=
  graph.schemes path.class

@[simp]
theorem nil_scheme : (nil : Path graph start).scheme = graph.schemes start := rfl

@[simp]
theorem cons_scheme : (Path.cons child subpath).scheme = subpath.scheme := rfl

end Path
end Graph
end Network