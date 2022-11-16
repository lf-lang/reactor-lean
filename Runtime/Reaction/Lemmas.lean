import Runtime.Reaction.Monad

namespace ReactionT

open Lean in
scoped macro "mk_value_lemma " op:ident field:ident : command => `(
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_value")  {σPS σPE σAS σAE σS σP input var} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) var input).snd = input.$field var  := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_state")  {σPS σPE σAS σAE σS σP input var} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) var input).fst.state = input.state := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_ports")  {σPS σPE σAS σAE σS σP input var} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) var input).fst.ports.isEmpty       := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_events") {σPS σPE σAS σAE σS σP input var} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) var input).fst.events = #[]#       := rfl
)

open Lean in
scoped macro "mk_value_lemma' " op:ident field:ident : command => `(
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_value")  {σPS σPE σAS σAE σS σP input} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) input).snd = input.$field      := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_state")  {σPS σPE σAS σAE σS σP input} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) input).fst.state = input.state := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_ports")  {σPS σPE σAS σAE σS σP input} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) input).fst.ports.isEmpty       := rfl
  @[simp] theorem $(mkIdentFrom op s!"{op.getId}_events") {σPS σPE σAS σAE σS σP input} : ($op (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) input).fst.events = #[]#       := rfl
)

mk_value_lemma  getInput       ports  
mk_value_lemma  getState       state  
mk_value_lemma  getAction      actions
mk_value_lemma  getParam       params 
mk_value_lemma' getTag         tag
mk_value_lemma' getLogicalTime time

/-
theorem setOutput_def : input -[setOutput port v]→ (·.fst.ports port = v) := by
  exists do
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    return ⟨({ ports, state := input.state }, ()), by simp⟩

theorem setState_eq_new_val : input -[setState stv v]→ (·.fst.state stv = v) := by
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

theorem schedule_state : input -[schedule action delay v]→ (·.fst.state var = input.state var) := sorry

-/

end ReactionT