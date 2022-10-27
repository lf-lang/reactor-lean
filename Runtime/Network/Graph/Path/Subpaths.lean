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




-- Note: We can't define this property with an optional return type,
--       as we can't even state the return type for an invalid input path.
def suffix (path : Path graph start) (_ : path.snd? = some snd) : Path graph snd := 
  match path with
  | nil => by contradiction
  | cons child subpath => (by simp_all [cons_snd?_eq_child] : child = snd) ▸ subpath

end Network.Graph.Path
