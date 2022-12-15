import Runtime.Utilities.Lean
import Lean

/--
Time `Unit`s are used for converting between different units of time when getting and setting
instances of `Time`.
-/
protected inductive Time.Unit
  | ns | μs | ms | s | mins | hours | days | weeks

/--
The multiplication factor required to convert a given number of time units of a given unit to the
equivalent number of nanoseconds. For example, to convert five minutes to the equivalent number of
nanoseconds we write `5 * Unit.mins.nsRatio`.
-/
def Time.Unit.nsRatio : Time.Unit → Nat
  | ns    => 1
  | μs    => 1000
  | ms    => 1000 * 1000
  | s     => 1000 * 1000 * 1000
  | mins  => 1000 * 1000 * 1000 * 60
  | hours => 1000 * 1000 * 1000 * 60 * 60
  | days  => 1000 * 1000 * 1000 * 60 * 60 * 24
  | weeks => 1000 * 1000 * 1000 * 60 * 60 * 24 * 7

/-- A list of all members of `Time.Unit`. -/
def Time.Unit.allCases : Array Time.Unit :=
  #[ns, μs, ms, s, mins, hours, days, weeks]

instance : ToString Time.Unit where
  toString
    | .ns    => "ns"
    | .μs    => "μs"
    | .ms    => "ms"
    | .s     => "s"
    | .mins  => "mins"
    | .hours => "hours"
    | .days  => "days"
    | .weeks => "weeks"

/--
A `Time` describes a point in time as a nonnegative number of nanoseconds.
To access the underlying value of a given instance of `Time`, use `Time.to`.
To construct an instance of `Time`, use `Time.of` or the conveniences
`Nat.{ns, μs, ms, s, mins, hours, days, weeks}`.
-/
structure Time where
  private mk ::
  private ns : Nat
  deriving DecidableEq

instance : ToString Time where
  toString t := s!"{t.ns} ns"

/-- The `<` relation of `Time` is determined by the underlying value. -/
instance : LT Time where
  lt t₁ t₂ := t₁.ns < t₂.ns

/-- The `≤` relation of `Time` is determined by the underlying value. -/
instance : LE Time where
  le t₁ t₂ := t₁.ns ≤ t₂.ns

instance : Decidable ((t₁ : Time) < t₂) := by
  simp [LT.lt]; infer_instance

instance : Decidable ((t₁ : Time) ≤ t₂) := by
  simp [LE.le]; infer_instance

theorem Time.ext {time₁ time₂ : Time} : time₁.ns = time₂.ns → time₁ = time₂ :=
  fun _ => by cases time₁; simp_all

theorem Time.le_antisymm {time₁ : Time} : (time₁ ≤ time₂) → (time₂ ≤ time₁) → time₁ = time₂ :=
  (Time.ext <| Nat.le_antisymm · ·)

@[simp]
theorem Time.le_refl {time : Time} : time ≤ time := Nat.le_refl _

/--
A `Duration` describes a span of time described by a nonnegative number of nanoseconds. It is thus
simply a different way of interpreting instances of `Time`.
-/
abbrev Duration := Time

/--
Creates an instance of time whose underlying number of nanoseconds matches the given number of time
units of a given unit. For example, `Time.of 5 .mins` constructs an instance of `Time` whose
underlying value represents five minutes.
-/
def Time.of (value : Nat) (unit : Time.Unit) : Time :=
  { ns := value * unit.nsRatio }

/--
Returns the number of time units of a given unit, which represent the given time. The resulting
value is rounded down to the nearest natural number. For example, if `t` is a `Time` with an
underlying value of 4200 nanoseconds, then `t.to .μs = 4` and `t.to .ms = 0`.
-/
def Time.to (time : Time) (unit : Time.Unit) : Nat :=
  time.ns / unit.nsRatio

-- For each time unit `x`, this creates a definition `Nat.x` which constructs a `Time` from the
-- number and unit.
--
-- TODO: Use `run_cmd` for this if it is moved from Mathlib to Std.
open Lean in macro "mk_nat_to_time_ctors" : command =>
  return ⟨mkNullNode (← Time.Unit.allCases.mapM fun unit =>
    let withUnit := (mkIdent <| · ++ (toString unit))
    `(/-- A convenience for constructing a `Time` with the given unit. -/
      protected abbrev $(withUnit `Nat) : Nat → Time := (Time.of · $(withUnit `Time.Unit)))
  )⟩
mk_nat_to_time_ctors

theorem Time.of_to : (Time.of value unit).to unit = value := by
  simp [of, to, Unit.nsRatio]
  cases unit <;> simp only [Nat.mul_div_cancel]

/-- The current time according to `IO.monoNanosNow`. -/
def Time.now : IO Time :=
  return { ns := ← IO.monoNanosNow }

/--
A convenience for constructing instances of `Time` with a value of 0, as this doesn't require a
unit.
-/
instance : OfNat Time 0 where
  ofNat := { ns := 0 }

theorem Time.zero_eq_zero : (0 : Time) = Time.of 0 unit := by simp [of]

@[simp]
theorem Time.zero_le {time : Time} : 0 ≤ time := by apply Nat.zero_le

/-- Adding a `Duration` to a `Time` adds the underlying values. -/
instance : HAdd Time Duration Time where
  hAdd t d := { ns := t.ns + d.ns }

/--
Subtracting a `Duration` from a `Time` subtracts the underlying values. Note that for duration `d`
and time `t` with `d ≥ t`, `t - d = 0`.
-/
instance : HSub Time Duration Time where
  hSub t d := { ns := t.ns - d.ns }

/--
Subtracting a `Time` from a `Time` produces their difference as a `Duration`. Note that for times
`t₁` and `t₂` with `t₂ ≥ t₁`, `t₁ - t₂ = 0`.
-/
instance : HSub Time Time Duration where
   hSub t₁ t₂ := { ns := t₁.ns - t₂.ns }

/-- A `Time.From t` is a time which is at least "as late" as `t`. -/
abbrev Time.From (min : Time) := { time : Time // min ≤ time }

/-- Any given time `t` can be lifted to a `Time.From t`, as it is at least "as late" as itself. -/
instance : CoeDep Time t (Time.From t) where
  coe := ⟨t, by simp_arith [LE.le]⟩

/-- The `≤` relation of `Time.From` is determined by the `Time` value. -/
instance : LE (Time.From t) where
  le t₁ t₂ := t₁.val ≤ t₂.val

@[simp]
theorem Time.From.le_refl {time : Time.From t} : time ≤ time := Nat.le_refl _

/-- A `Tag` describes a logical time tag as in the Reactor model. -/
structure Tag where
  time : Time
  microstep : Nat
  deriving DecidableEq

instance : ToString Tag where
  toString tag := s!"⟨{tag.time}, {tag.microstep}⟩"

/-- The `<` relation of `Tag` is determined lexicographically by its components. -/
instance : LT Tag where
  lt tag₁ tag₂ :=
    if tag₁.time = tag₂.time
    then tag₁.microstep < tag₂.microstep
    else tag₁.time < tag₂.time

/-- "Incrementing" a tag means advancing it to the next microstep. -/
def Tag.increment (tag : Tag) : Tag := { tag with
  microstep := tag.microstep + 1
}

/--
Advances the given tag `g` *to* (not *by*) a given time `t`.
We can't move backwards as `t < g.time` is excluded by the type of `t`.
-/
def Tag.advance (tag : Tag) (time : Time.From tag.time) : Tag :=
  if tag.time < time
  then { time := time, microstep := 0 }
  else tag.increment

@[simp]
theorem Tag.advance_time {tag : Tag} {time} : (tag.advance time).time = time := by
  simp [advance]
  split <;> simp
  case _ h => simp_arith [LT.lt] at h; exact Time.le_antisymm time.property h

theorem Tag.lt_advance : (tag : Tag) < tag.advance t := by
  simp [advance]
  split
  case inr => simp_arith [LT.lt, increment]
  case inl => simp [LT.lt] at *; split <;> simp_all
