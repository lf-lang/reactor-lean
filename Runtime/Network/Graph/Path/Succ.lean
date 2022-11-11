import Runtime.Network.Graph.Path.Subpaths

namespace Network.Graph.Path

def Succ (path₁ path₂ : Path graph start) :=
  path₁.prefix? = path₂

infix:35 " ≻ " => Succ

theorem Succ.isCons : (path₁ ≻ path₂) → path₁.isCons :=
  fun h => prefix?_isSome_iff_isCons.mp (Option.isSome_def.mpr ⟨_, h⟩)

theorem Succ.isCons' : (cons c₁ (cons c₂ path₁) ≻ path₂) → path₂.isCons := by
  intro h
  have ⟨subpath, hp⟩ := prefix?_isSome_iff_isCons.mpr (@isCons_of_cons _ _ c₂ path₁) |> Option.isSome_def.mp
  simp [Succ, prefix?, hp] at h
  simp [isCons_def]
  exists c₁, subpath
  injection h with h
  exact h.symm

theorem Succ.iff_cons_Succ {path₁ path₂} : 
  (path₁ ≻ path₂) ↔ (cons child path₁) ≻ (cons child path₂) :=
  prefix?_iff_cons_prefix?

theorem Succ.nil : (cons child nil) ≻ nil := rfl

instance : Decidable (path₁ ≻ path₂) := 
  if h : path₁.prefix? = path₂ then isTrue h else isFalse h

theorem Succ.cons (path₁) : ∃ path₂, (cons child path₁) ≻ path₂ := by
  cases h : (Path.cons child path₁).prefix?
  case none =>
    have h : ¬(Path.cons child path₁).prefix?.isSome := by simp_all [Option.isSome_def]
    have := mt prefix?_isSome_iff_isCons.mpr h
    contradiction
  case some pre => exists pre

end Network.Graph.Path