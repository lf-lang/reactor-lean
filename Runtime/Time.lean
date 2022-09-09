abbrev Time := Nat
abbrev Time.After (time : Time) := { t : Time // t > time }
abbrev Duration := { d : Nat // d > 0 }

instance : Ord (Time.After time) where
  compare t₁ t₂ := compare t₁.val t₂.val

structure Tag where
  time : Time
  microstep : Nat

def Time.advance (time : Time) (d : Duration) : Time.After time := {
  val := time + d
  property := by simp_arith [Nat.succ_le_of_lt d.property]
}