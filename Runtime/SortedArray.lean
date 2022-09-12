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

def coe [Ord β] [Coe α β] (s : SortedArray α) (h : ∀ a₁ a₂, compare a₁ a₂ = compare (a₁ : β) (a₂ : β)) : SortedArray β := {
  toArray := s.toArray.map Coe.coe
  isSorted := sorry
}

instance [Ord β] [ordCoe : OrdCoe α β] : Coe (SortedArray α) (SortedArray β) where
  coe s := s.coe ordCoe.coeOrd

def nil : SortedArray α := {
  isSorted := List.Sorted.nil
}

notation "#[]#" => SortedArray.nil

def singleton (a : α) : SortedArray α := {
  isSorted := List.Sorted.singleton (a := a)
}

notation (priority := default - 1) "#[" a "]#" => SortedArray.singleton a

instance : LE (SortedArray α) where
  le s₁ s₂ := 
    match s₁.toArray[s₁.size - 1]?, s₂.toArray[0]? with
    | _, none | none, _ => True
    | some last₁, some first₂ => last₁ ≤ first₂

def append (s₁ s₂ : SortedArray α) (h : s₁ ≤ s₂) : SortedArray α :=
  ⟨s₁.toArray ++ s₂.toArray, sorry⟩ 

-- Note: For the purposes of reactor execution, it is important that this merge is stable
--       in the sense that for elements of equal ordering, those from s₁ are sorted earlier 
--       than those from s₂. Also the order present within a given array (s₁ or s₂) is not 
--       disturbed.
def merge (s₁ s₂ : SortedArray α) : SortedArray α :=
  -- TODO: temporary
  let sorted := (s₁.toArray ++ s₂.toArray).insertionSort (Ord.compare · · |>.isLE)
  { toArray := sorted, isSorted := sorry }
  
-- Note: For the purposes of reactor execution, it is important that this split is stable.
def split (s : SortedArray α) (p : α → Bool) : (SortedArray α) × (SortedArray α) :=
  -- TODO: temporary - This can be done more efficiently (note: Array.split is stable)
  let ⟨fst, snd⟩ := s.toArray.split p
  (⟨fst, sorry⟩, ⟨snd, sorry⟩)

def unique (s : SortedArray α) (f : α → β) [DecidableEq β] : (SortedArray α) × (SortedArray α) := Id.run do
  let mut included : Array α := #[] 
  let mut excluded : Array α := #[]
  for a in s.toArray do
    if included.any (f a = f ·) 
    then excluded := excluded.push a
    else included := included.push a
  return (⟨included, sorry⟩, ⟨excluded, sorry⟩)
  