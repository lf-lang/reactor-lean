abbrev Time := Nat
abbrev Duration := { d : Nat // d > 0 }

structure Tag where
  time : Time
  microstep : Nat

def Time.after (time : Time) : Type := 
  { t : Time // t > time }

instance : Repr (Time.after t) where
  reprPrec t := reprPrec t.val

def Time.advance (time : Time) (d : Duration) : Time.after time := {
  val := time + d,
  property := by simp_arith [Nat.succ_le_of_lt d.property]
}