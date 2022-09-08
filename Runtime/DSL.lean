import Runtime.Network
import Lean
open Lean Macro

declare_syntax_cat interface_var
syntax ident " : " term : interface_var

def getInterfaceVarComponents : (TSyntax `interface_var) → MacroM (Ident × Term)
  | `(interface_var| $i:ident : $t) => return (i, t)
  | _ => throwUnsupported

declare_syntax_cat interface_scheme
syntax "[" interface_var,* "]" : interface_scheme

def getInterfaceSchemeVars : (TSyntax `interface_scheme) → MacroM (Array $ TSyntax `interface_var)
  | `(interface_scheme| [ $vars,* ]) => return vars
  | _ => throwUnsupported

macro "interface" name:ident scheme:interface_scheme : command => do
  let vars ← getInterfaceSchemeVars scheme
  let components ← vars.mapM getInterfaceVarComponents
  let ⟨ids, types⟩ := components.unzip
  let schemeName := mkIdentFrom name (name.getId ++ "scheme")
  `(
    inductive $name $[| $ids:ident]* deriving DecidableEq
    abbrev $schemeName : Interface.Scheme := {
      vars := $name
      type := fun x => match x with $[| $ids => $types]*
    }
  )

declare_syntax_cat reactor_scheme_field
syntax ident " := " interface_scheme : reactor_scheme_field

def getReactorSchemeFieldComponents : (TSyntax `reactor_scheme_field) → MacroM (Ident × TSyntax `interface_scheme)
  | `(reactor_scheme_field| $i:ident := $s) => return (i, s)
  | _ => throwUnsupported

declare_syntax_cat reactor_scheme
syntax "{" reactor_scheme_field,* "}" : reactor_scheme

inductive ReactorSchemeField
  | input
  | output
  | action
  | state
  deriving BEq

def ReactorSchemeField.all : Array ReactorSchemeField := 
  #[.input, .output, .action, .state]

instance : ToString ReactorSchemeField where
  toString
    | .input => "input"
    | .output => "output"
    | .action => "action"
    | .state => "state"

def ReactorSchemeField.fromIdent (i : Ident) : MacroM ReactorSchemeField :=
  match i.getId.toString with
  | "input"  => return .input
  | "output" => return .output
  | "action" => return .action
  | "state"   => return .state
  | invalid   => Macro.throwErrorAt i s!"invalid reactor field '{invalid}'"

def getReactorSchemeInterfaces : (TSyntax `reactor_scheme) → MacroM (ReactorSchemeField → (MacroM $ TSyntax `interface_scheme))
  | `(reactor_scheme| { $syns:reactor_scheme_field,* }) => do
    let components ← syns.getElems.mapM getReactorSchemeFieldComponents
    let fields ← components.mapM fun ⟨id, scheme⟩ => return (← ReactorSchemeField.fromIdent id, scheme)
    return fun field => 
      match fields.find? (·.fst == field) with 
      | none          => Macro.throwError s!"missing field '{field}'"
      | some ⟨_, syn⟩ => return syn
  | _ => throwUnsupported

def makeReactorSchemeInterfaceCommands (container : Ident) (scheme : TSyntax `reactor_scheme) : MacroM (Array Command) := do
  let interfaces ← getReactorSchemeInterfaces scheme
  ReactorSchemeField.all.mapM fun field => do
    let fieldIdent := mkIdentFrom container (container.getId ++ (toString field).capitalize)
    let «interface» ← interfaces field
    `(interface $fieldIdent:ident $«interface»)

macro "reactor" name:ident scheme:reactor_scheme : command => do
  let interfaceCommands := mkNullNode (← makeReactorSchemeInterfaceCommands name scheme)
  return interfaceCommands