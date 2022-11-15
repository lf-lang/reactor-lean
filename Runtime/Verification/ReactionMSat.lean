import Runtime.Reaction

instance : LawfulMonad IO := sorry

namespace ReactionM

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/SatisfiesM.2Eand
theorem SatisfiesM.and [Functor m] [LawfulFunctor m] {x : m α} :
  (SatisfiesM p x) → (SatisfiesM q x) → SatisfiesM (fun a => p a ∧ q a) x := by
  sorry

protected def Sat
  (input : Input σPortSource σActionSource σState σParam)
  (comp : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam α) 
  (prop : (Output σPortEffect σActionEffect σState input.time × α) → Prop) :=
  SatisfiesM (α := (Output σPortEffect σActionEffect σState input.time) × _) prop (comp input)

set_option hygiene false -- TODO: `in`
local macro input:term " -[" comp:term "]→ " prop:term : term => `(
  ReactionM.Sat  
    (σPortSource := σPortSource) 
    (σPortEffect := σPortEffect) 
    (σActionSource := σActionSource) 
    (σActionEffect := σActionEffect) 
    (σState := σState) 
    (σParam := σParam)
    $input $comp $prop
)

theorem Sat.bind {comp₂ : α → ReactionM (α := β) ..} {prop₂ : (Output .. × β) → Prop} {propₘ  : (Output .. × β) → Prop} : 
  (input -[comp₁]→ prop₁) →  
  (∀ {out₁ val₁}, prop₁ (out₁, val₁) → { input with state := out₁.state } -[comp₂ val₁]→ prop₂) →
  (∀ {out₁ val₁ out₂ val₂}, prop₁ (out₁, val₁) → prop₂ (out₂, val₂) → propₘ (out₁.merge out₂, val₂)) →
  input -[comp₁ >>= comp₂]→ propₘ := by
  intro h₁ h₂ hₘ
  apply SatisfiesM.bind h₁
  intro _ ho₁
  apply SatisfiesM.bind (h₂ ho₁)
  intro _ ho₂
  apply SatisfiesM.pure
  exact hₘ ho₁ ho₂

theorem Sat.and : 
  (input -[comp]→ prop₁) → 
  (input -[comp]→ prop₂) → 
  input -[comp]→ (fun out => prop₁ out ∧ prop₂ out) :=
  SatisfiesM.and

end ReactionM