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

def coe [Ord β] [Coe α β] (s : SortedArray α) (h : ∀ a₁ a₂, compare a₁ a₂ = compare (a₁ : β) (a₂ : β)) : SortedArray β := {
  toArray := s.toArray.map Coe.coe
  isSorted := sorry
}

def nil : SortedArray α := {
  isSorted := List.Sorted.nil
}

notation "#[]#" => SortedArray.nil

def singleton (a : α) : SortedArray α := {
  isSorted := List.Sorted.singleton (a := a)
}

notation "#[" a "]#" => SortedArray.singleton a

-- Note: For the purposes of reactor execution, it is important that this merge is stable
--       in the sense that for elements of equal ordering, those from s₁ are sorted earlier 
--       than those from s₂. Also the order present within a given array (s₁ or s₂) is not 
--       disturbed.
def merge (s₁ s₂ : SortedArray α) : SortedArray α :=
  -- TODO: temporary
  let sorted := (s₁.toArray ++ s₂.toArray).insertionSort (Ord.compare · · |>.isLE)
  { toArray := sorted, isSorted := sorry }