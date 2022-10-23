import Runtime.Network.Basic

namespace Network

inductive Event (net : Network)
  | action (time : Time) (id : ActionId net) (value : id.reactor.class.interface .actions |>.type id.action)
  | timer (time : Time) (id : TimerId net)

namespace Event
  
def time : Event net → Time
  | .action time .. | .timer time .. => time

instance : LE (Event net) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event net) ≤ e₂) := by
  simp [LE.le]; infer_instance

inductive Id (net : Network)
  | action : ActionId net → Id net
  | timer  : TimerId net → Id net
  deriving DecidableEq

def id : Event net → Event.Id net
  | .action _ id _ => .action id
  | .timer _ id => .timer id

def actionValue (event : Event net) {id} (h : event.id = .action id) : id.reactor.class.interface .actions |>.type id.action :=
  match event with
  | .timer .. => by simp [Network.Event.id] at h 
  | .action _ id' value => (by simp_all [Network.Event.id] : id = id') ▸ value
  
end Event
end Network