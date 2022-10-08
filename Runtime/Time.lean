abbrev Time := Nat -- Time is measured in nanoseconds.
abbrev Time.From (time : Time) := { t : Time // t ≥ time }

inductive Duration
  | ns : Nat → Duration
  | micros : Nat → Duration -- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Mu.20symbol
  | ms : Nat → Duration
  | s : Nat → Duration

def Duration.asNs : Duration → Nat
  | ns d     => d
  | micros d => 1000 * d 
  | ms d     => 1000000 * d 
  | s d      => 1000000000 * d 

def Duration.asMicros : Duration → Nat
  | ns d     => d / 1000
  | micros d => d 
  | ms d     => 1000 * d 
  | s d      => 1000000 * d 

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

