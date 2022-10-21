import Runtime.Network.Graph.Path.Basic

namespace Network.Graph.Path

abbrev extend (path : Path graph start) (leaf : path.scheme.children) : Path graph start :=
  match path with
  | .nil                => .cons leaf .nil
  | .cons child subpath => .cons child (subpath.extend leaf)

@[simp]
theorem extend_scheme {path : Path graph start} {leaf} : (path.extend leaf).scheme = (path.class.child leaf).scheme :=
  match path with
  | .nil => rfl
  | .cons _ subpath => subpath.extend_scheme

@[simp]
theorem extend_class {path : Path graph start} {leaf} : (path.extend leaf).class = path.class.child leaf := 
  match path with
  | .nil => rfl
  | .cons _ subpath => subpath.extend_class

def Extends (path₁ path₂ : Path graph start) :=
  ∃ leaf, path₁ = path₂.extend leaf

infix:35 " ≻ " => Extends

theorem Extends.is_cons : (path₁ ≻ path₂) → (∃ child subpath, path₁ = .cons child subpath) := by
  intro ⟨_, h⟩
  cases path₁
  case cons child subpath => exists child, subpath
  case nil => cases path₂ <;> simp [extend] at h

theorem Extends.not_nil : (path₁ ≻ path₂) → (path₁ ≠ .nil) := by
  intro h
  have ⟨_, _, h⟩ := h.is_cons
  simp [h]

theorem Extends.iff_cons_Extends {path₁ path₂} : 
  (path₁ ≻ path₂) ↔ (.cons child path₁) ≻ (.cons child path₂) := by
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
  
theorem Extends.cons_child : (.cons child₁ path₁) ≻ (.cons child₂ path₂) → child₁ = child₂ := by
  intro ⟨child, h⟩
  simp [extend] at h
  exact h.left

def «extends» : Path graph start → Path graph start → Bool
  | .cons _ .nil,          .nil                  => true 
  | .cons child₁ subpath₁, .cons child₂ subpath₂ => if h : child₁ = child₂ then subpath₁.extends (h ▸ subpath₂) else false
  | _,                      _                    => false

theorem extend_extends {path : Path graph start} {child} : (path.extend child).extends path :=
  match path with
  | .nil => rfl
  | .cons _ _ => by simp [«extends», extend_extends]

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
  then .isTrue (Extends.of_extends h)
  else .isFalse (mt Extends.to_extends h)

end Network.Graph.Path
