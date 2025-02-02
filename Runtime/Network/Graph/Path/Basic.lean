import Runtime.Network.Graph.Basic

namespace Network.Graph

inductive Path (graph : Graph) : Class graph → Type _
  | nil : Path graph _
  | cons {start : Class graph} (child : Class.Child start) : Path graph child.class → Path graph start
  deriving DecidableEq

namespace Path

def isNil : Path graph start → Bool
  | nil => true
  | cons .. => false

theorem isNil_of_nil : (nil : Path graph start).isNil := rfl

@[simp]
theorem isNil_def {path : Path graph start} : path.isNil ↔ path = nil := by
  cases path <;> simp [isNil]

def isCons : Path graph start → Bool
  | nil => false
  | cons .. => true

theorem isCons_of_cons : (Path.cons child subpath).isCons := rfl

theorem isCons_of_eq_cons {path : Path graph start} : (path = cons child subpath) → path.isCons :=
  (by rw [·, isCons_of_cons])

theorem isCons_def {path : Path graph start} : path.isCons ↔ (∃ child subpath, path = cons child subpath) := by
  cases path <;> simp [isCons]

theorem isCons_iff_not_isNil {path : Path graph start} : path.isCons ↔ ¬path.isNil := by
  cases path <;> simp [isCons, isNil]

theorem isNil_iff_not_isCons {path : Path graph start} : path.isNil ↔ ¬path.isCons := by
  cases path <;> simp [isCons, isNil]

def «class» : (Path graph start) → Class graph
  | nil            => start
  | cons _ subpath => subpath.class

@[simp]
theorem nil_class : (nil : Path graph start).class = start := rfl

@[simp]
theorem cons_class : (Path.cons child subpath).class = subpath.class := rfl

@[simp]
theorem eq_class_iff_cons_eq_class : (path₁.class = path₂.class) ↔ (Path.cons child₁ path₁).class = (Path.cons child₂ path₂).class := ⟨id, id⟩

end Path
end Network.Graph
