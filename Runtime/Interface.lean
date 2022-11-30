import Runtime.Utilities

namespace Interface

structure Scheme where
  vars : Type
  type : vars → Type
  [varsDecidableEq : DecidableEq vars]

attribute [reducible] Scheme.type
attribute [instance] Scheme.varsDecidableEq

abbrev Scheme.union (σ₁ σ₂ : Scheme) : Scheme where
  vars := Sum σ₁.vars σ₂.vars
  type
    | .inl var => σ₁.type var
    | .inr var => σ₂.type var

infix:65 " ⊎ " => Scheme.union

@[simp]
theorem Scheme.union_type_left (σ₁ σ₂ : Scheme) (var : σ₁.vars) :
  (σ₁ ⊎ σ₂).type (.inl var) = σ₁.type var := rfl

@[simp]
theorem Scheme.union_type_right (σ₁ σ₂ : Scheme) (var : σ₂.vars) :
  (σ₁ ⊎ σ₂).type (.inr var) = σ₂.type var := rfl

-- σs is an I-indexed family of schemes.
def Scheme.bUnion (σs : I → Scheme) [DecidableEq I] : Scheme where
  vars := (i : I) × (σs i).vars
  type := fun ⟨i, var⟩ => (σs i).type var

prefix:100 " ⨄ " => Scheme.bUnion

@[simp]
theorem Scheme.bUnion_vars (σs : I → Scheme) [DecidableEq I] :
  (⨄ σs).vars = ((i : I) × (σs i).vars) := rfl

@[simp]
theorem Scheme.bUnion_type (σs : I → Scheme) [DecidableEq I] (var : (σs i).vars) :
  (⨄ σs).type ⟨i, var⟩ = (σs i).type var := rfl

class Subscheme (σ₁ σ₂ : Scheme) where
  coe       : σ₁.vars → σ₂.vars
  inv       : σ₂.vars → Option σ₁.vars
  invInj    : ∀ {a b₁ b₂}, (inv b₁ = some a) → (inv b₂ = some a) → (b₁ = b₂)
  coeInvId  : ∀ a, inv (coe a) = a
  coeEqType : ∀ {v}, σ₂.type (coe v) = σ₁.type v

theorem Subscheme.invEqType [inst : Subscheme σ₁ σ₂] : ∀ {b}, (inst.inv b = some a) → (σ₁.type a = σ₂.type b) :=
  fun h => by rw [←inst.coeEqType (v := a), inst.invInj h (inst.coeInvId a)]

end Interface

def Interface (σ : Interface.Scheme) := (var : σ.vars) → (σ.type var)

def Interface? (σ : Interface.Scheme) := (var : σ.vars) → Option (σ.type var)

def Interface?.empty : Interface? σ := fun _ => none

@[simp]
theorem Interface?.empty_none : Interface?.empty var = none := rfl

def Interface?.isEmpty (i : Interface? σ) := i = Interface?.empty

@[simp]
theorem Interface?.isEmpty_def (i : Interface? σ) : i.isEmpty ↔ i = Interface?.empty := by
  simp [isEmpty]

def Interface?.isPresent (i : Interface? σ) (var : σ.vars) : Bool :=
  i var |>.isSome

@[simp]
theorem Interface?.isPresent_def (i : Interface? σ) : i.isPresent var ↔ ∃ v, i var = some v := by
  simp [isPresent, Option.isSome_iff_exists]

-- Merge i₂ into i₁.
def Interface?.merge (i₁ i₂ : Interface? σ) : Interface? σ :=
  fun var => i₂ var |>.orElse fun _ => i₁ var

theorem Interface?.merge_val₁ (i₁ i₂ : Interface? σ) : (i₂ var = none) → (i₁.merge i₂) var = i₁ var := by
  simp_all [merge, Option.orElse]

theorem Interface?.merge_val₂ (i₁ i₂ : Interface? σ) : (i₂ var = some v) → (i₁.merge i₂) var = some v := by
  simp_all [merge, Option.orElse]

theorem Interface?.merge_idem : Interface?.merge i i = i := by
  funext var
  simp [merge, Option.orElse]
  split
  · exact Eq.symm ‹_›
  · simp

def Interface?.restrict [inst : Interface.Subscheme σ₁ σ₂] (i : Interface? σ₂) : Interface? σ₁ :=
  fun var => inst.coeEqType ▸ i (inst.coe var)
