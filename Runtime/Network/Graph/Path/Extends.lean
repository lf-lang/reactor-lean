import Runtime.Network.Graph.Path.Basic

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

def Extends (path₁ path₂ : Path graph start) :=
  ∃ leaf, path₁ = path₂.extend leaf

infix:35 " ≻ " => Extends

theorem Extends.isCons : (path₁ ≻ path₂) → path₁.isCons := by
  intro ⟨_, h⟩
  rw [isCons_def]
  cases path₁
  case cons child subpath => exists child, subpath
  case nil => cases path₂ <;> simp [extend] at h

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

-- The prefix of a path is the path without the leaf.
-- If the path is already `.nil` it remains the same.
def «prefix» : Path graph start → Option (Path graph start)
  | nil => none
  | cons _ nil => some nil
  | cons child subpath => subpath.prefix >>= (cons child ·)    

theorem isCons_prefix_isSome {path : Path graph start} : path.isCons → path.prefix.isSome := by
  intro h
  induction path
  case nil =>
    have ⟨_, _, _⟩ := isCons_def.mp h
    contradiction
  case cons child₁ subpath₁ hi => 
    cases subpath₁
    case nil => simp [«prefix», Option.isSome]
    case cons child₂ subpath₂ => 
      specialize hi isCons_of_cons
      have ⟨subpath, hi⟩ := Option.isSome_def.mp hi
      simp [«prefix», hi, Option.isSome_def]
      exists .cons child₁ subpath

-- TODO: Once we prove this, we don't need `extends` to show decidability of `Extends` anymore.
theorem Extends.iff_prefix : (path₁ ≻ path₂) ↔ path₁.prefix = path₂ := by
  constructor
  sorry
  sorry

theorem Extends.cons (path₁) : ∃ path₂, (Path.cons child path₁) ≻ path₂ := by
  cases h : (Path.cons child path₁).prefix
  case none =>
    have h : ¬(Path.cons child path₁).prefix.isSome := by simp [Option.isSome_def]; intro ⟨_, _⟩; simp_all
    have := mt isCons_prefix_isSome h
    contradiction
  case some pre => 
    exists pre
    exact Extends.iff_prefix.mpr h

-- TODO:
-- def suffix (path : Path graph start) : Option (Path graph (Class.Child start)) := sorry

def Child (path : Path graph start) := { child // child ≻ path }

-- An extended path's class is a child class of its parent's class.
def Child.class' {start} {path : Path graph start} : (child : Child path) → Class.Child path.class := fun child => 
  match h : child.val with 
  | cons c nil => 
    have ht : start = path.class := by
      have h' := Extends.iff_prefix.mp child.property
      simp [h, «prefix»] at h'; simp [←h']
    ht ▸ c
  | cons c subpath@(cons _ _) =>
    /-
    have : subpath ≻ path.suffix /- we need a notion of a suffix, which is kind of the opposite of prefix. But first finish apply.child-/ := by
      have ⟨_, H⟩  := Extends.cons subpath
      rename_i h₁ _
      rw [h₁] at H
    -/
    sorry
  | nil => 
    by have := h ▸ child.property.isCons; contradiction

@[simp]
theorem Child.class'_eq_class {child : Child path} : child.class'.class = child.val.class := 
  sorry

end Network.Graph.Path
