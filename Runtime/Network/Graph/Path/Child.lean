import Runtime.Network.Graph.Path.Succ

namespace Network.Graph.Path

def Child (path : Path graph start) := { child // child ≻ path }

theorem Child.parent_eq_nil_class {path : Path graph start} {child : Child path} : (child.val = cons c nil) → start = path.class := by
  intro h
  have h' := child.property
  simp [Succ, h, prefix?] at h'
  simp [←h']

-- An extended path's class is a child class of its parent's class.
def Child.class : (child : Child path) → Class.Child path.class := fun child =>
  match h : child.val with 
  | nil => by have := h ▸ child.property.isCons; contradiction
  | cons c nil => (parent_eq_nil_class h) ▸ c
  | cons c subpath@(cons _ _) =>
    have path_isCons := (h ▸ child.property).isCons'
    have h₁ : c.class = path.snd path_isCons := sorry -- TODO: look at the picture in your folder
    let pathSuffix := path.suffix path_isCons
    let subpath := h₁ ▸ subpath
    have h₂ : subpath ≻ pathSuffix := sorry
    suffix_class ▸ «class» ⟨subpath, h₂⟩
termination_by «class» child => sizeOf child.val -- TODO: Perhaps use an explictly define path length property instead.
decreasing_by sorry

@[simp]
theorem Child.class_eq_class {child : Child path} : child.class.class = child.val.class := by
  sorry

end Network.Graph.Path
