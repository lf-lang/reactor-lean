import Runtime.Network.Graph.Path.Extends

namespace Network.Graph.Path

-- Note: Every node except for the start can be its own sibling.
def Sibling (path₁ path₂ : Path graph start) :=
  ∃ parent, (path₁ ≻ parent) ∧ (path₂ ≻ parent)

infix:35 " ≂ " => Sibling

theorem Sibling.symm : (path₁ ≂ path₂) → (path₂ ≂ path₁) := 
  fun ⟨parent, h₁, h₂⟩ => ⟨parent, h₂, h₁⟩

theorem Sibling.isCons₁ : (path₁ ≂ path₂) → path₁.isCons :=
  fun ⟨_, h, _⟩ => h.isCons

theorem Sibling.isCons₂ : (path₁ ≂ path₂) → path₂.isCons := 
  fun ⟨_, _, h⟩ => h.isCons

theorem Sibling.to_eq_prefix : (path₁ ≂ path₂) → (path₁.prefix = path₂.prefix) := by
  intro ⟨_, _, _⟩
  simp_all [Extends.iff_prefix]

theorem Sibling.of_eq_prefix : (path₁.prefix = some parent) → (path₂.prefix = some parent) → (path₁ ≂ path₂) := by
  intro h₁ h₂
  simp [←Extends.iff_prefix] at h₁ h₂
  exact ⟨_, h₁, h₂⟩

instance : Decidable (path₁ ≂ path₂) :=
  match h₁ : path₁.prefix, h₂ : path₂.prefix with
  | none, _ => .isFalse (by have := isCons_prefix_isSome ·.isCons₁; simp_all [Option.isSome])
  | _, none => .isFalse (by have := isCons_prefix_isSome ·.isCons₂; simp_all [Option.isSome])
  | some pre₁, some pre₂ =>
    if h : pre₁ = pre₂ 
    then .isTrue (Sibling.of_eq_prefix h₁ (h ▸ h₂))
    else .isFalse (by simp_all [mt Sibling.to_eq_prefix])

end Network.Graph.Path