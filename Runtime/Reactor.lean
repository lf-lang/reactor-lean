import Runtime.Reaction

variable {Input Output Source Effect Action State : Type} 
variable [Typed Input] [Typed Output] [Typed Source] [Typed Effect] [Typed Action] [Typed State]

structure Reactor.Interface where
  vars : Type
  [varsTyped : Typed vars]
  interface : Interface vars := fun _ => none

attribute [instance] Reactor.Interface.varsTyped 

structure Reactor where
  state   : Reactor.Interface
  inputs  : Reactor.Interface
  outputs : Reactor.Interface
  actions : Reactor.Interface
  reactions : Array (Reaction inputs.vars outputs.vars actions.vars state.vars)

def Reactor.reactionType (rtr : Reactor) :=
  Reaction rtr.inputs.vars rtr.outputs.vars rtr.actions.vars rtr.state.vars

def Reaction.outputType [Typed State] [DecidableEq State] (rcn : Reaction Source Effect Action State) :=
  ReactionM.Output rcn.effects rcn.actions State 

def ReactionM.run (time : Time) (rtr : Reactor) (rcn : rtr.reactionType) : (rcn.outputType time) × Unit :=
  rcn.body {
    sources := fun s => 
      let inst : TypedCoe rcn.sources rtr.inputs.vars := inferInstance
      (inst.coeEqType s) ▸ (rtr.inputs.interface s),
    actions := fun a =>
      let inst : TypedCoe rcn.actions rtr.actions.vars := inferInstance
      (inst.coeEqType a) ▸ (rtr.actions.interface a),
    state := rtr.state.interface,
    time := time
  }