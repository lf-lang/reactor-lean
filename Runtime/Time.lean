abbrev Time := Nat
abbrev Duration := Nat
abbrev Time.From (time : Time) := { t : Time // t ≥ time }

instance : Ord (Time.From time) where
  compare t₁ t₂ := compare t₁.val t₂.val

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d
  property := by simp_arith
}

structure Tag where
  time : Time
  microstep : Nat
  deriving DecidableEq

def Tag.advance (tag : Tag) (time : Time) : Tag := 
  match compare tag.time time with
  | .lt => { time := time, microstep := 0 }
  | .eq => { tag with microstep := tag.microstep + 1 }
  | .gt => tag -- TODO: This can only happen if there is an error in the implementation of reactor execution.

