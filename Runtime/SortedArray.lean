import Runtime.Utilities

inductive List.Sorted [LE α] : List α → Prop
  | nil : Sorted []
  | singleton : Sorted [a]
  | cons : (fst ≤ snd) → Sorted (snd :: tl) → Sorted (hd :: snd :: tl)

structure SortedArray (α) [Ord α] extends Array α where 
  isSorted : List.Sorted toArray.data
  deriving Repr

namespace SortedArray

variable [Ord α]

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
  -- TODO: temporary
  let sorted := (s₁.toArray ++ s₂.toArray).insertionSort (Ord.compare · · |>.isLE)
  { toArray := sorted, isSorted := sorry }

  