/--
A reaction `Trigger` identifies an event which should cause a reaction to fire. Reactions explictly
declare their triggers and thus the events which should cause them to fire. The different kinds of
triggers are active under the following conditions (according to `Execution.Executable.triggers`):

* `startup`: at tag (0, 0)
* `shutdown`: at the last tag at which a given reactor system executes
* `port p`: when the port with name `p` is present
* `action a`: when the action with name `a` is present
* `timer t`: when the timer with name `t` fires
-/
inductive Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

def Trigger.valued : (Trigger Port Action Timer) → Bool
  | port _ | action _ => true
  | _ => false
