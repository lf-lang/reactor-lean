import Runtime.Network.Graph.Path.Basic

namespace Network.Graph.Path

-- The prefix of a path is the path without the leaf.
-- If the path is already `.nil` it remains the same.
def prefix? : Path graph start → Option (Path graph start)
  | nil => none
  | cons _ nil => some nil
  | cons child subpath => subpath.prefix? >>= (cons child ·)    

-- TODO: Make this an iff.
theorem isCons_prefix_isSome {path : Path graph start} : path.isCons → path.prefix?.isSome := by
  intro h
  induction path
  case nil =>
    have ⟨_, _, _⟩ := isCons_def.mp h
    contradiction
  case cons child₁ subpath₁ hi => 
    cases subpath₁
    case nil => simp [prefix?, Option.isSome]
    case cons child₂ subpath₂ => 
      specialize hi isCons_of_cons
      have ⟨subpath, hi⟩ := Option.isSome_def.mp hi
      simp [prefix?, hi, Option.isSome_def]
      exists .cons child₁ subpath

def snd (path : Path graph start) (_ : path.isCons) : Class.Child start :=
  match path with
  | nil => by contradiction
  | cons child _ => child

@[simp]
theorem cons_snd_eq_child : (cons child path).snd h = child := rfl

-- Note: We can't define this property with an optional return type,
--       as we can't even state the return type for an invalid input path.
def suffix (path : Path graph start) (h) : Path graph (path.snd h) := 
  match path with
  | nil => by contradiction
  | cons _ subpath => subpath

end Network.Graph.Path
