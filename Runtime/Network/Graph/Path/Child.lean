import Runtime.Network.Graph.Path.Succ

namespace Network.Graph.Path

def Child (path : Path graph start) := { child // child ≻ path }

namespace Child

theorem parent_eq_nil_class {path : Path graph start} {child : Child path} : (child.val = cons c nil) → start = path.class := by
  intro h
  have h' := child.property
  simp [Succ, h, prefix?] at h'
  simp [←h']

-- TODO: This could also be expressed in `Subpaths.lean` using `prefix?`.
theorem split_fst_eq_parent (child : Child path) :
  (child.val.split child.property.isCons).fst = path := by
  sorry

def «class» (child : Child path) : Class.Child path.class :=
  split_fst_eq_parent child ▸ (child.val.split child.property.isCons).snd

@[simp]
theorem class_eq_class {child : Child path} : child.class.class = child.val.class := by
  sorry

end Child
end Network.Graph.Path
