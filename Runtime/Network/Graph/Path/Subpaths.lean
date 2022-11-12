import Runtime.Network.Graph.Path.Basic

namespace Network.Graph.Path

-- The prefix of a path is the path without the leaf.
-- If the path is already `.nil` it remains the same.
def prefix? : Path graph start → Option (Path graph start)
  | nil => none
  | cons _ nil => some nil
  | cons child subpath => subpath.prefix? >>= (cons child ·)      

theorem prefix?_iff_cons_prefix? {graph} {start : Class graph} {child : Class.Child start} {path₁ path₂ : Path graph child.class} :
  (path₁.prefix? = some path₂) ↔ (cons child path₁).prefix? = some (cons child path₂) := by
  constructor
  all_goals 
    intro h
    cases path₁
    case nil => simp [prefix?] at h
  case mp.cons => simp [prefix?, h]; rfl
  case mpr.cons => sorry

theorem prefix?_cons_eq_cons_prefix? {graph} {start : Class graph} {child : Class.Child start} {subpath subprefix : Path graph child.class} : 
  (subpath.prefix? = some subprefix) → (cons child subpath).prefix? = cons child subprefix := by
  intro h
  cases subpath
  case nil => simp [prefix?] at h
  case cons child' subpath => simp [prefix?, h]; rfl

theorem prefix?_isSome_iff_isCons {path : Path graph start} : path.prefix?.isSome ↔ path.isCons := by
  constructor
  case mp => sorry
  case mpr =>
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
        have ⟨subpath, hi⟩ := Option.isSome_iff_exists.mp hi
        simp [prefix?, hi, Option.isSome_iff_exists]
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

@[simp]
theorem suffix_class {path : Path graph start} {h} : (path.suffix h).class = path.class := by
  rw [suffix]
  split
  case _ h => simp [isCons] at h
  · simp

def split (path : Path graph start) (_ : path.isCons) : Σ «prefix» : Path graph start, Class.Child prefix.class :=
  match path with
  | nil => by contradiction
  | cons child nil => ⟨nil, child⟩
  | cons child subpath@(cons _ _) => 
    let ⟨sub, cls⟩ := subpath.split (by simp_all [isCons_of_cons])
    ⟨cons child sub, cls⟩

theorem split_class {path : Path graph start} {h : path.isCons} : (path.split h).snd.class = path.class := by
  induction path
  case nil => contradiction
  case cons child subpath hi =>
    cases subpath
    case nil => rfl
    case cons child' subpath => rw [split]; exact hi

end Network.Graph.Path
