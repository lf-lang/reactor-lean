class Enumerable (α) where
  allCases : Array α

class Typed (α : Type) extends Enumerable α, Repr α where
  type : α → Type
  typeRepr : ∀ a, Repr (type a)
  [decidableEq : DecidableEq α]

attribute [reducible] Typed.type
attribute [instance] Typed.decidableEq Typed.typeRepr

open Typed

@[reducible]
instance [DecidableEq α] [Enumerable α] [Repr α] [Coe α β] [Typed β] : Typed α where
  type a := type (a : β)
  typeRepr := inferInstance

def Interface (Var : Type) [Typed Var] := (var : Var) → Option (type var)

open Std in
instance [inst : Typed Var] : Repr (Interface Var) where
  reprPrec i p := Id.run do
    let mut result := .nil 
    for var in inst.allCases do
      let varF := reprPrec var p
      let valueF := reprPrec (i var) p
      let mapsto := varF ++ " ↦ " ++ valueF
      result := result ++ mapsto ++ .line
    return result

-- Merge i₂ into i₁.
def Interface.merge [Typed Var] (i₁ i₂ : Interface Var) : Interface Var :=
  fun n => (i₂ n).orElse (fun _ => i₁ n)

class TypedCoe (α β) [Typed α] [Typed β] extends Coe α β where
  coeEqType : ∀ a, type (coe a) = type a

attribute [instance] TypedCoe.toCoe

-- Merge i₂ into i₁.
def Interface.merge' [Typed Var] [Typed S] [TypedCoe S Var] (i₁ : Interface Var) (i₂ : Interface S) : Interface Var :=
  fun n => sorry