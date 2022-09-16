import Runtime.Utilities.Extensions

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

notation "#[]#" => SortedArray.nil

def singleton (a : α) : SortedArray α := {
  isSorted := List.Sorted.singleton (a := a)
}

notation "#[" a "]#" => SortedArray.singleton a

-- Note: For the purposes of reactor execution, it is important that this merge is stable.
-- That is, it should be the same as would be produced by a stable sorting algorithm on
-- input `s₁ ++ s₂`.
def merge (s₁ s₂ : SortedArray α) : SortedArray α :=
  -- TODO: temporary
  let sorted := (s₁.toArray ++ s₂.toArray).insertionSort (Ord.compare · · |>.isLE)
  { toArray := sorted, isSorted := sorry }