inductive List.Sorted [LE α] : List α → Prop
  | nil : Sorted []
  | singleton : Sorted [a]
  | cons : (fst ≤ snd) → Sorted (snd :: tl) → Sorted (hd :: snd :: tl)

structure SortedArray (α) [LE α] extends Array α where 
  isSorted : List.Sorted toArray.data

namespace SortedArray

variable [LE α]

def nil : SortedArray α := {
  isSorted := List.Sorted.nil
}

notation "#[]" => SortedArray.nil

def singleton (a : α) : SortedArray α := {
  isSorted := List.Sorted.singleton (a := a)
}

notation "#[" a "]" => SortedArray.singleton a

def merge (s₁ s₂ : SortedArray α) : SortedArray α :=
  go 0 0 s₁ s₂ #[]
where 
  go (i₁ i₂ : Nat) (s₁ s₂ acc : SortedArray α) (h₁ : i₁ ≤ s₁.size := by simp) (h₂ : i₂ ≤ s₂.size := by simp) : SortedArray α :=
  sorry

  