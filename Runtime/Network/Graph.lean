import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root    : classes -- TODO: Is the root still needed now that paths are relative? Or should it be moved to `Network`?
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Graph.decEqClasses

namespace Graph

inductive Path (graph : Graph) : graph.classes → Type _
  | nil : Path graph _
  | cons {start : graph.classes} (child : (graph.schemes start).children) : Path graph (graph.schemes start |>.class child) → Path graph start
  deriving DecidableEq

namespace Path

def «class» : (Path graph start) → graph.classes
  | .nil            => start
  | .cons _ subpath => subpath.class

@[simp]
theorem nil_class : (nil : Path graph start).class = start := rfl

@[simp]
theorem cons_class : (Path.cons child subpath).class = subpath.class := rfl

abbrev scheme (path : Path graph start) : Reactor.Scheme graph.classes :=
  graph.schemes path.class

abbrev extend (path : Path graph start) (leaf : path.scheme.children) : Path graph start :=
  match path with
  | .nil                => .cons leaf .nil
  | .cons child subpath => .cons child (subpath.extend leaf)

@[simp]
theorem nil_scheme : (nil : Path graph start).scheme = graph.schemes start := rfl

@[simp]
theorem cons_scheme : (Path.cons child subpath).scheme = subpath.scheme := rfl

@[simp]
theorem extend_scheme {path : Path graph start} {leaf} : (path.extend leaf).scheme = graph.schemes (path.scheme.class leaf) :=
  match path with
  | .nil => rfl
  | .cons _ subpath => subpath.extend_scheme

@[simp]
theorem extend_class {path : Path graph start} {leaf} : (path.extend leaf).class = path.scheme.class leaf := 
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

end Path
end Graph
end Network