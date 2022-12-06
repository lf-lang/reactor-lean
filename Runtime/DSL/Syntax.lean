import Runtime.DSL.Model
import Lean
open Lean Macro

declare_syntax_cat interface_var
syntax ident " : " term (":=" term)? : interface_var

declare_syntax_cat interface_decl
syntax "[" interface_var,* "]" : interface_decl

declare_syntax_cat ident_list
syntax "[" ident,* "]" : ident_list

declare_syntax_cat trigger_decl
syntax "triggers" "{"
  "ports"   ident_list
  "actions" ident_list
  "timers"  ident_list
  "meta"    ident_list
  "}" : trigger_decl

declare_syntax_cat reaction_decl
syntax "{"
  &"kind"          ident
  "portSources"   ident_list
  "portEffects"   ident_list
  "actionSources" ident_list
  "actionEffects" ident_list
  trigger_decl
  "body" "{" doSeq "}"
  "}" : reaction_decl

declare_syntax_cat timer_decl
syntax "{"
  &"name"   ident
  "offset" term
  "period" term
  "}" : timer_decl

declare_syntax_cat instance_decl
syntax ident " : " ident " := " interface_decl : instance_decl

declare_syntax_cat nested_decl
syntax "[" instance_decl,* "]" : nested_decl

declare_syntax_cat reactor_decl
syntax "reactor" ident
  "parameters"  interface_decl
  "inputs"      interface_decl
  "outputs"     interface_decl
  "actions"     interface_decl
  "state"       interface_decl
  "timers"      "[" timer_decl,* "]"
  "nested"      nested_decl
  "connections" interface_decl
  "reactions" "[" reaction_decl,* "]"
  : reactor_decl

declare_syntax_cat network_decl
syntax reactor_decl+ : network_decl

declare_syntax_cat lf_decl
syntax "lf" "{" network_decl &"schedule" ident_list "}" : lf_decl

def InterfaceVar.fromSyntax : TSyntax `interface_var → MacroM InterfaceVar
  | `(interface_var| $id:ident : $value)             => return { id := id, value := value, default := none }
  | `(interface_var| $id:ident : $value := $default) => return { id := id, value := value, default := default }
  | _                                                => throwUnsupported

def InterfaceDecl.fromSyntax : TSyntax `interface_decl → MacroM InterfaceDecl
  | `(interface_decl| [$vars:interface_var,*]) => vars.getElems.mapM InterfaceVar.fromSyntax
  | _ => throwUnsupported

def InstanceDecl.fromSyntax : TSyntax `instance_decl → MacroM InstanceDecl
  | `(instance_decl| $name:ident : $«class»:ident := $params:interface_decl) => return {
      id := name
      «class» := «class»
      params := ← InterfaceDecl.fromSyntax params
    }
  | _ => throwUnsupported

def NestedDecl.fromSyntax : TSyntax `nested_decl → MacroM NestedDecl
  | `(nested_decl| [$children:instance_decl,*]) => children.getElems.mapM InstanceDecl.fromSyntax
  | _ => throwUnsupported

def TriggerDecl.fromSyntax : TSyntax `trigger_decl → MacroM TriggerDecl
  | `(trigger_decl| triggers { ports [$p:ident,*] actions [$a:ident,*] timers [$t:ident,*] meta [$m:ident,*] }) =>
    return { «ports» := p, «actions» := a, «timers» := t, «meta» := m }
  | _ => throwUnsupported

def ReactionDecl.fromSyntax : TSyntax `reaction_decl → MacroM ReactionDecl
  | `(reaction_decl| {
      kind $k portSources [$ps:ident,*] portEffects [$pe:ident,*] actionSources [$as:ident,*]
      actionEffects [$ae:ident,*] $ts:trigger_decl body { $b:doSeq }
    }) => return {
      «kind» := k
      dependencies := fun | .portSource => ps | .portEffect => pe | .actionSource => as | .actionEffect => ae
      «triggers» := ← TriggerDecl.fromSyntax ts
      «body» := b
    }
  | _ => throwUnsupported

def TimerDecl.fromSyntax : TSyntax `timer_decl → MacroM TimerDecl
  | `(timer_decl| { name $n:ident offset $o period $p }) =>
    return { «name» := n, «offset» := o, «period» := p }
  | _ => throwUnsupported

def ReactorDecl.fromSyntax : TSyntax `reactor_decl → MacroM ReactorDecl
  | `(reactor_decl| reactor $name:ident parameters $p inputs $i outputs $o actions $a state $s timers [ $t,* ] nested $n connections $c reactions [$r:reaction_decl,*]) => do
    let i ← InterfaceDecl.fromSyntax i
    let o ← InterfaceDecl.fromSyntax o
    let a ← InterfaceDecl.fromSyntax a
    let s ← InterfaceDecl.fromSyntax s
    let n ← NestedDecl.fromSyntax n
    let c ← InterfaceDecl.fromSyntax c
    let p ← InterfaceDecl.fromSyntax p
    let r ← r.getElems.mapM ReactionDecl.fromSyntax
    return {
      name := name
      interfaces := fun | .inputs => i | .outputs => o | .actions => a | .state => s | .params => p
      «timers» := ← t.getElems.mapM TimerDecl.fromSyntax
      «nested» := n
      «connections» := c
      «reactions» := r
    }
  | _ => throwUnsupported

def NetworkDecl.fromSyntax : TSyntax `network_decl → MacroM NetworkDecl
  | `(network_decl| $reactors:reactor_decl*) => return {
      reactors := (← reactors.mapM ReactorDecl.fromSyntax)
    }
  | _ => throwUnsupported

def LFDecl.fromSyntax : TSyntax `lf_decl → MacroM LFDecl
  | `(lf_decl| lf { $network:network_decl schedule [$sched:ident,*] }) => return {
      network := ← NetworkDecl.fromSyntax network
      «schedule» := sched
    }
  | _ => throwUnsupported
