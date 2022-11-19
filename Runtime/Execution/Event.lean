import Runtime.Network.Basic

namespace Execution
open Network

inductive Event (net : Network)
  | action      (time : Time) (id : ActionId net) (value : (id.reactor.class.interface .actions).type id.action)
  | timer       (time : Time) (id : TimerId net)
  | propagation (time : Time) (id : PortId net .input) (value : id.reactor.inputs.type id.port)

namespace Event

def time : Event net → Time
  | action time .. | timer time .. | propagation time .. => time

instance : LE (Event net) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event net) ≤ e₂) := by
  simp [LE.le]; infer_instance

inductive Id (net : Network)
  | action      : ActionId net      → Id net
  | timer       : TimerId net       → Id net
  | propagation : PortId net .input → Id net
  deriving DecidableEq

def id : Event net → Event.Id net
  | action      _ id _ => .action id
  | timer       _ id   => .timer id
  | propagation _ id _ => .propagation id

def timer? : Event net → Option (TimerId net)
  | timer _ id => id
  | _          => none

def actionValue (event : Event net) {id} (_ : event.id = .action id) : id.reactor.class.interface .actions |>.type id.action :=
  match event with | action _ id' value => (by simp_all [Event.id] : id = id') ▸ value

def propagationValue (event : Event net) {id} (_ : event.id = .propagation id) : id.reactor.inputs.type id.port :=
  match event with | propagation _ id' value => (by simp_all [Event.id] : id = id') ▸ value

end Event
end Execution
