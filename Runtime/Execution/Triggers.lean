import Runtime.Execution.ReactionInputs

namespace Execution.Executable
open Network Graph Class

-- TODO: Replace the `port` constructor's condition with something more akin to:
--       "∃ portSource ∈ reaction.portSources: exec[portsSource].isPresent"

/--
A predicate indicating whether a given executable triggers a given reaction by means of a given
trigger. The main use case for this predicate is its closure `Triggers`.
-/
private inductive TriggersWith
  (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class)
  : reaction.val.triggerType → Prop
  | port     : (exec.reactionInputs reactor |>.isPresent (reaction.subPS.coe port))       → TriggersWith _ _ (.port port)
  | action   : (exec.interface reactor .actions |>.isPresent (reaction.subAS.coe action)) → TriggersWith _ _ (.action action)
  | timer    : (exec.reactors reactor |>.timer (reaction.eqTimers ▸ timer) |>.isFiring)   → TriggersWith _ _ (.timer timer)
  | startup  : (exec.isStartingUp)                                                        → TriggersWith _ _ .startup
  | shutdown : (exec.state = .shuttingDown)                                               → TriggersWith _ _ .shutdown

/-- A decision procedure for `TriggersWith` which is used in its `Decidable` instance. -/
private def triggersWith
  (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class)
  : reaction.val.triggerType → Bool
  | .port   port   => exec.reactionInputs reactor     |>.isPresent (reaction.subPS.coe port)
  | .action action => exec.interface reactor .actions |>.isPresent (reaction.subAS.coe action)
  | .timer  timer  => exec.reactors reactor           |>.timer (reaction.eqTimers ▸ timer) |>.isFiring
  | .startup       => exec.isStartingUp
  | .shutdown      => exec.state = .shuttingDown

instance : Decidable (TriggersWith exec reaction trigger) :=
  if h : triggersWith exec reaction trigger then
    .isTrue <| by
      cases trigger
      all_goals simp only [triggersWith, decide_eq_true_iff] at h
      case port     => exact .port h
      case action   => exact .action h
      case timer    => exact .timer h
      case startup  => exact .startup h
      case shutdown => exact .shutdown h
  else
    .isFalse <| by
      intro hc
      cases hc
      all_goals
        simp only [triggersWith, decide_eq_true_iff] at h
        contradiction

/-- A predicate indicating whether a given executable triggers a given reaction. -/
inductive Triggers
  (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class) : Prop :=
  | witness (mem : trigger ∈ reaction.val.triggers.data) (trig : TriggersWith exec reaction trigger)

instance : Decidable (Triggers exec reaction) :=
  if h : reaction.val.triggers.any (TriggersWith exec reaction ·) then
    .isTrue <| by
      have ⟨_, ⟨mem, trig⟩⟩ := Array.any_iff_mem_where.mp h
      refine .witness mem ?_
      exact decide_eq_true_iff _ |>.mp trig
  else
    .isFalse <| by
      intro ⟨mem, _⟩
      have h := (mt Array.any_iff_mem_where.mpr h) |> not_exists.mp
      have h := not_and.mp (h _) mem
      simp [decide_eq_true_iff] at h
      contradiction

end Execution.Executable
