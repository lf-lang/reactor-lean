import Lean
import Runtime.Utilities.Extensions

open Lean Macro

def emptyInjectiveCoeCommand (sub total : Term) : MacroM Command := `(
  @[reducible] instance : InjectiveCoe $sub $total where
    coe := (·.casesOn)
    inv _ := none
)

def partialInjectiveCoeCommand (sub total : Term) (cases : Array Ident) (terms : Array Term) : MacroM Command := `(
  @[reducible] instance : InjectiveCoe $sub $total where
    coe $[| $cases => $terms]*
    inv $[| $terms => some $cases]* | _ => none
)  

def totalInjectiveCoeCommand (sub total : Term) (cases : Array Ident) (terms : Array Term) : MacroM Command := `(
  @[reducible] instance : InjectiveCoe $sub $total where
    coe $[| $cases => $terms]*
    inv $[| $terms => some $cases]*
)  

def injectiveCoeTerms (cases : Array Ident) : MacroM (Array Term) := 
  cases.mapM fun case => do
    match case.getId with
    | .str .anonymous l            => `(.inl $(mkIdent <| .mkStr1 l))
    | .str (.str .anonymous l) rtr => `(.inr ⟨$(mkIdent <| .mkSimple rtr), $(mkIdent <| .mkSimple l)⟩)
    | _                            => throwUnsupported 

declare_syntax_cat injective_coe_gen
syntax "gen_injective_coe" term term "[" ident,* "]" "!"? : injective_coe_gen

/- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Parser.20category.20for.20instance.20parameters
macro_rules
  | `(injective_coe_gen| gen_injective_coe $sub $total []) => do emptyInjectiveCoe sub total
  | `(injective_coe_gen| gen_injective_coe $sub $total [ $cases,* ]) => do partialInjectiveCoe sub total cases (← injectiveCoeTerms cases)
  | `(injective_coe_gen| gen_injective_coe $sub $total [ $cases,* ]!) => do emptyInjectiveCoe sub total cases (← injectiveCoeTerms cases)
-/