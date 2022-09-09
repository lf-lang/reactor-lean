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
  let schemeName := mkIdentFrom name (name.getId ++ `scheme)
  `(
    inductive $name $[| $ids:ident]* deriving DecidableEq
    abbrev $schemeName : $(mkIdent `Interface.Scheme) := {
      vars := $name
      type := fun x => match x with $[| $ids => $types]*
    }
  )