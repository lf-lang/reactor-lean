import Runtime.Execution.ReactionInputs

namespace Network.Graph.Class.Reaction

inductive Trigger (net : Network)
  | port {kind} (id : PortId net kind)
  | action (id : ActionId net)
  | timer (id : TimerId net)
  | startup
  | shutdown

def Trigger.lift {reactor : ReactorId net} {reaction : Reaction reactor.class} :
  reaction.val.triggerType → Trigger net
  | .action a => .action ⟨reactor, reaction.subAS.coe a⟩
  | .timer t  => .timer ⟨reactor, reaction.eqTimers ▸ t⟩
  | .startup  => .startup
  | .shutdown => .shutdown
  | .port p =>
    match reaction.subPS.coe p with
    | .inl input =>
      (.port (kind := .input) ⟨reactor, input⟩)
    | .inr ⟨c, output⟩ =>
      (.port (kind := .output) ⟨reactor.extend c, cast (by rw [Path.extend_class]) output⟩)

inductive Trigger.Equiv {reactor : ReactorId net} {reaction : Reaction reactor.class} :
  (Trigger net) → reaction.val.triggerType → Prop
  | action :   Equiv (.action ⟨reactor, reaction.subAS.coe a⟩) (.action a)
  | timer :    Equiv (.timer ⟨reactor, reaction.eqTimers ▸ t⟩) (.timer t)
  | startup :  Equiv .startup .startup
  | shutdown : Equiv .shutdown .shutdown
  | input :
    (reaction.subPS.coe p = .inl input) →
    Equiv (.port (kind := .input) ⟨reactor, input⟩) (.port p)
  | output {h} :
    (reaction.subPS.coe p = .inr ⟨c, output⟩) →
    Equiv (.port (kind := .output) ⟨reactor.extend c, cast h output⟩) (.port p)

infix:50 " ≡ " => Trigger.Equiv

theorem Trigger.Equiv.lift
  {reactor : ReactorId net} {reaction : Reaction reactor.class} (t : reaction.val.triggerType) :
  Trigger.lift t ≡ t := by
  cases t
  all_goals
    simp [Trigger.lift]
    first
    | constructor
    | split <;> (constructor; assumption)

end Network.Graph.Class.Reaction

namespace Execution.Executable
open Network Graph Class

/--
A predicate indicating whether a given executable triggers a given reaction by means of a given
trigger. The main use case for this predicate is its closure: `Triggers`.
-/
inductive Activates (exec : Executable net) : (Class.Reaction.Trigger net) → Prop
  | port     : (exec.portIsPresent p)       → Activates _ (.port p)
  | action   : (exec.actionIsPresent a)     → Activates _ (.action a)
  | timer    : (exec.timer t |>.isFiring)   → Activates _ (.timer t)
  | startup  : (exec.isStartingUp)          → Activates _ .startup
  | shutdown : (exec.state = .shuttingDown) → Activates _ .shutdown

/-- A predicate indicating whether a given executable triggers a given reaction. -/
inductive Triggers (exec) {reactor : ReactorId net} (reaction : Reaction reactor.class) : Prop
  | witness (equiv : t ≡ t') (mem : t' ∈ reaction.val.triggers.data) (active : Activates exec t)

/-- A decision procedure for `Triggers`. -/
private def triggers (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class) :=
  reaction.val.triggers.any (activated ·)
where
  activated : reaction.val.triggerType → Bool
  | .port   port   => exec.reactionInputs reactor |>.isPresent (reaction.subPS.coe port)
  | .action action => exec.interface reactor .actions |>.isPresent (reaction.subAS.coe action)
  | .timer  timer  => exec.reactors reactor |>.timer (reaction.eqTimers ▸ timer) |>.isFiring
  | .startup       => exec.isStartingUp
  | .shutdown      => exec.state = .shuttingDown

theorem Activates.iff_equiv_trigger_activated {t'} :
  (t ≡ t') → (Activates exec t ↔ triggers.activated exec reaction t') := by
  intro equiv
  unfold triggers.activated
  constructor
  case mp =>
    intro activates
    cases equiv <;> cases activates
    all_goals
      simp_all [actionIsPresent, portIsPresent, reactionInputs]
      try assumption
    case output.port a' _ c o a h =>
      have ⟨v, h⟩ := h
      exists cast sorry v
      sorry
  case mpr =>
    intro h
    cases equiv
    all_goals
      simp at h
      constructor
      simp [actionIsPresent, portIsPresent]
      try assumption
    all_goals
      have ⟨v, h⟩ := h
      simp [reactionInputs] at h
    · sorry
    · sorry

theorem Triggers.iff_triggers_eq_true : (Triggers exec reaction) ↔ (exec.triggers reaction) := by
  unfold triggers
  constructor
  case mp =>
    intro ⟨equiv, mem, active⟩
    rw [Array.any_iff_mem_where]
    refine ⟨_, mem, ?_⟩
    exact Activates.iff_equiv_trigger_activated equiv |>.mp active
  case mpr =>
    intro h
    have ⟨t', mem, active⟩ := Array.any_iff_mem_where.mp h
    have ⟨_, equiv⟩ : ∃ t, t ≡ t' := ⟨_, Reaction.Trigger.Equiv.lift t'⟩
    refine .witness equiv mem ?_
    exact Activates.iff_equiv_trigger_activated equiv |>.mpr active

instance : Decidable (Triggers exec reaction) :=
  decidable_of_iff' _ Triggers.iff_triggers_eq_true

end Execution.Executable
