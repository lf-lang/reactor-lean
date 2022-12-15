import Runtime.Interface
import Runtime.Timer

namespace Reactor

/-- A classifier for whether a given port is an input or an output port. -/
inductive PortKind
  | input
  | output

/--
A classifier for the different kinds of interfaces (mappings from identifiers to values) present in
reactors.
-/
inductive InterfaceKind
  | inputs
  | outputs
  | actions
  | state
  | params

/--
This function indicates which interface-kind requires which flavor of interface. We define two
flavors of interfaces: `Interface`, which is a total map and `Interface?` which is a partial map.
Ports and actions must be able to represent absent values and hence use `Interface?`. State
variables and reactor parameters can have default values and thus use total `Interface`s.
-/
abbrev InterfaceKind.interfaceType : InterfaceKind → (Interface.Scheme → Type)
  | inputs | outputs | actions => Interface?
  | state  | params            => Interface

/-- A list of all members of `Reactor.InterfaceKind`. -/
def InterfaceKind.allCases : Array Reactor.InterfaceKind :=
  #[.inputs, .outputs, .actions, .state, .params]

instance : Coe PortKind InterfaceKind where
  coe
    | .input => .inputs
    | .output => .outputs

/--
A `Reactor.Scheme` describes the *structure* of a reactor without any concrete data. That is, it
describes what a reactor *class* looks like, not an *instance*.

The type is parameterized over a type of `classes` which is an enumeration of the names of all of
the different reactor classes appearing in a given LF program. This is required to specify which
class each child reactor belongs to.

Note that the values of parameters and timers are not part of a reactor scheme, as they are
instance-dependent.
-/
structure Scheme (classes : Type) where
  interface : InterfaceKind → Interface.Scheme
  /-- An enumeration of the names of the timers appearing in the reactor. -/
  timers : Type
  /-- An enumeration of the names of the child (nested) instances of the reactor. -/
  children : Type
  «class» : children → classes
  [decEqTimers : DecidableEq timers]
  [decEqChildren : DecidableEq children]

attribute [instance] Scheme.decEqTimers Scheme.decEqChildren

end Reactor
