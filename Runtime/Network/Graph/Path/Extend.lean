import Runtime.Network.Graph.Path.Subpaths

namespace Network.Graph.Path

abbrev extend (path : Path graph start) (leaf : Class.Child path.class) : Path graph start :=
  match path with
  | nil                => cons leaf nil
  | cons child subpath => cons child (subpath.extend leaf)

@[simp]
theorem extend_class {path : Path graph start} {leaf} : (path.extend leaf).class = leaf.class := 
  match path with
  | nil => rfl
  | cons _ subpath => subpath.extend_class
    
@[simp]
theorem extend_prefix?_eq_self {path : Path graph start} {leaf} : (path.extend leaf).prefix? = path := by
  induction path 
  case nil => simp [extend, prefix?]
  case cons subpath hi => simp [extend, prefix?_cons_eq_cons_prefix? hi]

end Network.Graph.Path