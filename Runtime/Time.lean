abbrev Time := Nat
abbrev Duration := Nat
abbrev Time.From (time : Time) := { t : Time // t ≥ time }

instance : Ord (Time.From time) where
  compare t₁ t₂ := compare t₁.val t₂.val

structure Tag where
  time : Time
  microstep : Nat

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d
  property := by simp_arith
}

def Tag.advance (tag : Tag) (time : Time) : Tag := 
  match Ord.compare tag.time time with
  | .lt => { time := time, microstep := 0 }
  | .eq => { tag with microstep := tag.microstep + 1 }
  | .gt => tag -- TODO: This can only happen if there is an error in the implementation of reactor execution.

