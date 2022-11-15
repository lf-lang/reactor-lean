import Runtime.Verification.ReactionMSat

namespace ReactionM

set_option hygiene false -- TODO: `in`
local macro input:term " -[" comp:term "]→ " prop:term : term => `(
  ReactionM.Sat  
    (σPortSource := σPortSource) 
    (σPortEffect := σPortEffect) 
    (σActionSource := σActionSource) 
    (σActionEffect := σActionEffect) 
    (σState := σState) 
    (σParam := σParam)
    $input $comp $prop
)

open Lean 

local macro "rcn_val_rfl" : tactic => `(tactic| exists return ⟨(Input.noop ‹_›, _), by first | rfl | simp⟩)
local macro "rcn_out_rfl" comp:ident param:optional(term) : tactic => 
  match param with
  | some p => `(tactic| exists return ⟨(Input.noop ‹_›, Prod.snd (← $comp $p ‹_› (σPortEffect := σPortEffect) (σActionEffect := σActionEffect))), by first | rfl | simp⟩)
  | none => `(tactic| exists return ⟨(Input.noop ‹_›, Prod.snd (← $comp ‹_› (σPortEffect := σPortEffect) (σActionEffect := σActionEffect))), by first | rfl | simp⟩)

theorem getInput_value       : input -[getInput port]→ (·.snd = input.ports port)             := by rcn_val_rfl
theorem getInput_state       : input -[getInput port]→ (·.fst.state var = input.state var)    := by rcn_out_rfl getInput _
theorem getInput_ports       : input -[getInput port]→ (·.fst.ports.isEmpty)                  := by rcn_out_rfl getInput _

theorem getState_value       : input -[getState stv]→ (·.snd = input.state stv)               := by rcn_val_rfl
theorem getState_state       : input -[getState stv]→ (·.fst.state var = input.state var)     := by rcn_out_rfl getState _
theorem getState_ports       : input -[getState stv]→ (·.fst.ports.isEmpty)                   := by rcn_out_rfl getState _

theorem getAction_def        : input -[getAction action]→ (·.snd = input.actions action)      := by rcn_val_rfl
theorem getAction_state      : input -[getAction action]→ (·.fst.state var = input.state var) := by rcn_out_rfl getAction _
theorem getAction_ports      : input -[getAction action]→ (·.fst.ports.isEmpty)               := by rcn_out_rfl getAction _

theorem getParam_def         : input -[getParam param]→ (·.snd = input.params param)          := by rcn_val_rfl
theorem getParam_state       : input -[getParam param]→ (·.fst.state var = input.state var)   := by rcn_out_rfl getParam _
theorem getParam_ports       : input -[getParam param]→ (·.fst.ports.isEmpty)                 := by rcn_out_rfl getParam _

theorem getTag_def           : input -[getTag]→ (·.snd = input.tag)                           := by rcn_val_rfl
theorem getTag_state         : input -[getTag]→ (·.fst.state var = input.state var)           := by rcn_out_rfl getTag
theorem getTag_ports         : input -[getTag]→ (·.fst.ports.isEmpty)                         := by rcn_out_rfl getTag

theorem getLogicalTime_def   : input -[getLogicalTime]→ (·.snd = input.time)                  := by rcn_val_rfl
theorem getLogicalTime_state : input -[getLogicalTime]→ (·.fst.state var = input.state var)   := by rcn_out_rfl getLogicalTime
theorem getLogicalTime_ports : input -[getLogicalTime]→ (·.fst.ports.isEmpty)                 := by rcn_out_rfl getLogicalTime

-- TODO:
theorem getLogicalTime_def' : 
  (input -[getTag]→         (·.snd = tag)) → 
  (input -[getLogicalTime]→ (·.snd = tag.time)) := by
  intro h
  simp [ReactionM.Sat, getLogicalTime]
  apply SatisfiesM.bind_pre
  simp
  refine SatisfiesM.imp ?_ (p := fun out => input.tag = tag) (by
    intro a h
    simp [h]
    sorry
  )
  sorry  

theorem setOutput_def : input -[setOutput port v]→ (·.fst.ports port = some v) := by
  exists do
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    return ⟨({ ports, state := input.state }, ()), by simp⟩

theorem setState_eq_new_val : input -[setState stv v]→ (·.fst.state stv = some v) := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp⟩

theorem setState_eq_old_val : input -[setState stv v]→ (fun out => ∀ stv', (stv' ≠ stv) → out.fst.state stv' = input.state stv') := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp_all⟩

theorem schedule_def : input -[schedule action delay v]→ (·.fst.events = #[⟨action, v, input.time.advance delay⟩]#) := by
  exists do
    let time := input.time.advance delay
    return ⟨({ state := input.state, events := #[{ action, time, value := v }]# }, ()), by simp⟩

end ReactionM