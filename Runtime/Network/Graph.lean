import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root    : classes -- TODO: Is the root still needed now that paths are relative?
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Graph.decEqClasses

inductive Graph.Path (graph : Graph) : graph.classes → Type _
  | nil : Path graph _
  | cons {start : graph.classes} (child : (graph.schemes start).children) : Path graph (graph.schemes start |>.class child) → Path graph start
  deriving DecidableEq

def Graph.Path.class : (Path graph start) → graph.classes
  | .nil            => start
  | .cons _ subpath => subpath.class

@[simp]
theorem Graph.Path.nil_class : (nil : Path graph start).class = start := rfl

@[simp]
theorem Graph.Path.cons_class : (Path.cons child subpath).class = subpath.class := rfl

abbrev Graph.Path.scheme (path : Path graph start) : Reactor.Scheme graph.classes :=
  graph.schemes path.class

abbrev Graph.Path.extend (path : Path graph start) (leaf : path.scheme.children) : Path graph start :=
  match path with
  | .nil                => .cons leaf .nil
  | .cons child subpath => .cons child (subpath.extend leaf)

@[simp]
theorem Graph.Path.nil_scheme : (nil : Path graph start).scheme = graph.schemes start := rfl

@[simp]
theorem Graph.Path.cons_scheme : (Path.cons child subpath).scheme = subpath.scheme := rfl

@[simp]
theorem Graph.Path.extend_scheme {path : Path graph start} {leaf} : (path.extend leaf).scheme = graph.schemes (path.scheme.class leaf) :=
  match path with
  | .nil => rfl
  | .cons _ subpath => subpath.extend_scheme

@[simp]
theorem Graph.Path.extend_class {path : Path graph start} {leaf} : (path.extend leaf).class = path.scheme.class leaf := 
  match path with
  | .nil => rfl
  | .cons _ subpath => subpath.extend_class

end Network