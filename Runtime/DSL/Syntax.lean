import Runtime.DSL.Model
import Lean
open Lean Macro

declare_syntax_cat interface_var
syntax ident " : " term : interface_var

declare_syntax_cat interface_decl
syntax "[" interface_var,* "]" : interface_decl

declare_syntax_cat ident_list
syntax "[" ident,* "]" : ident_list

declare_syntax_cat trigger_decl
syntax "triggers" "{"
  "ports" ident_list
  "actions" ident_list
  "meta" ident_list
  "}" : trigger_decl

declare_syntax_cat reaction_decl
syntax "{"  
  "portSources"   ident_list
  "portEffects"   ident_list
  "actionSources" ident_list
  "actionEffects" ident_list
  trigger_decl
  "body" ":=" doSeq
  "}" : reaction_decl

declare_syntax_cat reactor_decl
syntax "reactor" ident 
  "inputs"  interface_decl 
  "outputs" interface_decl 
  "actions" interface_decl 
  "state"   interface_decl 
  "nested"  interface_decl
  "reactions" "[" reaction_decl* "]"
  : reactor_decl

declare_syntax_cat graph_decl
syntax ident "where" reactor_decl+ : graph_decl

def InterfaceVar.fromSyntax : TSyntax `interface_var → MacroM InterfaceVar
  | `(interface_var| $id:ident : $value) => return { id := id, value := value }
  | _ => throwUnsupported

def InterfaceDecl.fromSyntax : TSyntax `interface_decl → MacroM InterfaceDecl
  | `(interface_decl| [$vars:interface_var,*]) => vars.getElems.mapM InterfaceVar.fromSyntax
  | _ => throwUnsupported

def TriggerDecl.fromSyntax : TSyntax `trigger_decl → MacroM TriggerDecl
  | `(trigger_decl| triggers { ports [$p:ident,*] actions [$a:ident,*] meta [$m:ident,*] }) =>
    return { «ports» := p, «actions» := a, «meta» := m }
  | _ => throwUnsupported

def ReactionDecl.fromSyntax : TSyntax `reaction_decl → MacroM ReactionDecl 
  | `(reaction_decl| { 
      portSources [$ps:ident,*] portEffects [$pe:ident,*] actionSources [$as:ident,*] 
      actionEffects [$ae:ident,*] $ts:trigger_decl body := $b:doSeq
    }) => return { 
      dependencies := fun | .portSource => ps | .portEffect => pe | .actionSource => as | .actionEffect => ae
      «triggers» := ← TriggerDecl.fromSyntax ts
      «body» := b
    }
  | _ => throwUnsupported

def ReactorDecl.fromSyntax : TSyntax `reactor_decl → MacroM ReactorDecl
  | `(reactor_decl| reactor $name:ident inputs $i outputs $o actions $a state $s nested $n reactions [$r:reaction_decl*]) => do
    let i ← InterfaceDecl.fromSyntax i
    let o ← InterfaceDecl.fromSyntax o
    let a ← InterfaceDecl.fromSyntax a
    let s ← InterfaceDecl.fromSyntax s
    let n ← InterfaceDecl.fromSyntax n
    let r ← r.mapM ReactionDecl.fromSyntax
    return {
      name := name
      interfaces := fun | .inputs => i | .outputs => o | .actions => a | .state => s
      «nested» := n
      «reactions» := r  
    }
  | _ => throwUnsupported

def GraphDecl.fromSyntax : TSyntax `graph_decl → MacroM GraphDecl
  | `(graph_decl| $name:ident where $reactors:reactor_decl*) => return {
      name := name
      reactors := (← reactors.mapM ReactorDecl.fromSyntax)
    }
  | _ => throwUnsupported