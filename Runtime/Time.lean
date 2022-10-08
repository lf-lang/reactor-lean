abbrev Time := Nat -- Time is measured in nanoseconds.
abbrev Time.From (time : Time) := { t : Time // t ≥ time }

inductive Duration
  | ns : Nat → Duration
  | μs : Nat → Duration 
  | ms : Nat → Duration
  | s  : Nat → Duration

def Duration.asNs : Duration → Nat
  | ns d => d
  | μs d => 1000 * d 
  | ms d => 1000000 * d 
  | s d  => 1000000000 * d 

def Duration.asMs : Duration → Nat
  | ns d => d / 1000000
  | μs d => d / 1000
  | ms d => d 
  | s d  => 1000 * d 

instance : Ord (Time.From time) where
  compare t₁ t₂ := compare t₁.val t₂.val

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d.asNs
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

