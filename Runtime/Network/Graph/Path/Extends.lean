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
theorem reactionInputScheme_right_type_eq_extend_child_type {path : Path graph start} {child childOutput} : 
  path.class.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = 
  ((path.extend child).class.interface .outputs).type (extend_class ▸ childOutput) := by
  simp
  sorry -- by extend_class

-- TODO: Rename this to `Succ`?
def Extends (path₁ path₂ : Path graph start) :=
  ∃ leaf, path₁ = path₂.extend leaf

infix:35 " ≻ " => Extends

theorem Extends.isCons : (path₁ ≻ path₂) → path₁.isCons := by
  intro ⟨_, h⟩
  rw [isCons_def]
  cases path₁
  case cons child subpath => exists child, subpath
  case nil => cases path₂ <;> simp [extend] at h

theorem Extends.isCons' : (cons c₁ (cons c₂ path₁) ≻ path₂) → path₂.isCons := by
  intro ⟨_, h⟩
  rw [isCons_def]
  cases path₂
  case nil => 
    rw [extend] at h
    injection h with _ h _
    subst h
    contradiction
  case cons => 
    exists ‹_›, ‹_›

theorem Extends.iff_cons_Extends {path₁ path₂} : 
  (path₁ ≻ path₂) ↔ (cons child path₁) ≻ (cons child path₂) := by
  constructor
  case mp =>
    intro ⟨child, h⟩
    exists child
    rw [h]
  case mpr =>
    intro ⟨child, h⟩
    cases path₁
    case nil => cases path₂ <;> simp [extend] at h  
    case cons => simp at h; exact ⟨_, h⟩
  
theorem Extends.cons_child : (cons child₁ path₁) ≻ (cons child₂ path₂) → child₁ = child₂ := by
  intro ⟨child, h⟩
  simp [extend] at h
  exact h.left

def «extends» : Path graph start → Path graph start → Bool
  | cons _ nil,           nil                  => true 
  | cons child₁ subpath₁, cons child₂ subpath₂ => if h : child₁ = child₂ then subpath₁.extends (h ▸ subpath₂) else false
  | _,                     _                    => false

theorem extend_extends {path : Path graph start} {child} : (path.extend child).extends path :=
  match path with
  | nil => rfl
  | cons _ _ => by simp [«extends», extend_extends]

theorem Extends.of_extends : path₁.extends path₂ → (path₁ ≻ path₂) := by
  intro h
  induction path₁
  case nil => simp [«extends»] at h
  case cons child subpath hi => 
    cases path₂ <;> cases subpath
    case nil.nil => exists child
    case nil.cons => simp [«extends»] at h
    case cons.nil => 
      simp [«extends»] at h
      split at h <;> contradiction
    case cons.cons =>
      simp [«extends»] at h
      split at h
      case inl hc => 
        subst hc
        exact Extends.iff_cons_Extends.mp (hi h)
      case inr hc => 
        contradiction

theorem Extends.to_extends : (path₁ ≻ path₂) → path₁.extends path₂ := by
  intro ⟨child, h⟩
  induction path₁
  case nil => cases path₂ <;> contradiction
  case cons subpath hi =>
    cases path₂
    case nil =>
      cases subpath
      case nil => simp [«extends»]
      case cons =>
        simp [«extends»] at h
        have ⟨hc, h⟩ := h
        subst hc
        contradiction
    case cons =>
      simp [«extends»] at h
      have ⟨hc, h⟩ := h
      subst hc
      simp [«extends», eq_of_heq h, extend_extends]       

theorem Extends.iff_extends : (path₁ ≻ path₂) ↔ (path₁.extends path₂) := ⟨to_extends, of_extends⟩

instance : Decidable (path₁ ≻ path₂) :=
  if h : path₁.extends path₂
  then isTrue (Extends.of_extends h)
  else isFalse (mt Extends.to_extends h)

-- TODO: Once we prove this, we don't need `extends` to show decidability of `Extends` anymore.
theorem Extends.iff_prefix? : (path₁ ≻ path₂) ↔ path₁.prefix? = path₂ := by
  constructor
  sorry
  sorry

theorem Extends.cons (path₁) : ∃ path₂, (Path.cons child path₁) ≻ path₂ := by
  cases h : (Path.cons child path₁).prefix?
  case none =>
    have h : ¬(Path.cons child path₁).prefix?.isSome := by simp [Option.isSome_def]; intro ⟨_, _⟩; simp_all
    have := mt isCons_prefix_isSome h
    contradiction
  case some pre => 
    exists pre
    exact Extends.iff_prefix?.mpr h






def Child (path : Path graph start) := { child // child ≻ path }

@[simp]
theorem suffix_class {path : Path graph start} {h} : (path.suffix h).class = path.class := by
  rw [suffix]
  split
  case _ h => simp [isCons] at h
  · simp

theorem Child.parent_eq_nil_class {path : Path graph start} {child : Child path} : (child.val = cons c nil) → start = path.class := by
  intro h
  have h' := Extends.iff_prefix?.mp child.property
  simp [h, prefix?] at h'
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
