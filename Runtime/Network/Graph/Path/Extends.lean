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

@[simp]
theorem reactionInputScheme_right_type_eq_extend_child_type {path : Path graph start} {child childOutput} : 
  path.class.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = 
  ((path.extend child).class.interface .outputs).type (extend_class ▸ childOutput) := by
  simp
  sorry -- by extend_class

-- TODO: Rename this to `Succ`?
def Extends (path₁ path₂ : Path graph start) :=
  path₁.prefix? = path₂

infix:35 " ≻ " => Extends

theorem Extends.isCons : (path₁ ≻ path₂) → path₁.isCons :=
  fun h => prefix?_isSome_iff_isCons.mp (Option.isSome_def.mpr ⟨_, h⟩)

theorem Extends.isCons' : (cons c₁ (cons c₂ path₁) ≻ path₂) → path₂.isCons := by
  intro h
  have ⟨subpath, hp⟩ := prefix?_isSome_iff_isCons.mpr (@isCons_of_cons _ _ c₂ path₁) |> Option.isSome_def.mp
  simp [Extends, prefix?, hp] at h
  simp [isCons_def]
  exists c₁, subpath
  injection h with h
  exact h.symm

theorem Extends.iff_cons_Extends {path₁ path₂} : 
  (path₁ ≻ path₂) ↔ (cons child path₁) ≻ (cons child path₂) :=
  prefix?_iff_cons_prefix?

theorem Extends.nil : (cons child nil) ≻ nil := rfl

instance : Decidable (path₁ ≻ path₂) :=
  if h : path₁.prefix? = path₂ then isTrue h else isFalse h

theorem Extends.cons (path₁) : ∃ path₂, (cons child path₁) ≻ path₂ := by
  cases h : (Path.cons child path₁).prefix?
  case none =>
    have h : ¬(Path.cons child path₁).prefix?.isSome := by simp [Option.isSome_def]; intro ⟨_, _⟩; simp_all
    have := mt prefix?_isSome_iff_isCons.mpr h
    contradiction
  case some pre => exists pre

def Child (path : Path graph start) := { child // child ≻ path }

theorem Child.parent_eq_nil_class {path : Path graph start} {child : Child path} : (child.val = cons c nil) → start = path.class := by
  intro h
  have h' := child.property
  simp [Extends, h, prefix?] at h'
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
