import Runtime.Time
import Runtime.Interface
import Runtime.Reaction

open Std

class Enum (α) where
  allCases : Array α

def Enum.allCasesOf : (α : Type) → [Enum α] → Array α := 
  fun _ => allCases

instance : Repr (Time.After t) where
  reprPrec t := reprPrec t.val

instance {σ : Interface.Scheme} [Repr σ.vars] [Enum σ.vars] [∀ a, Repr $ σ.type a] : Repr (Interface σ) where
  reprPrec i p := 
    let list := Enum.allCasesOf σ.vars |>.foldl (init := .nil) fun result var =>
      result ++ (reprPrec var p) ++ " ↦ " ++ (reprPrec (i var) p) ++ ", "
    "[" ++ list ++ "]"

instance {σAction : Interface.Scheme} [Repr σAction.vars] [∀ a, Repr $ σAction.type a] : Repr (Event σAction time) where
  reprPrec e p := "(" ++ (reprPrec e.action p) ++ " ↦ " ++ (reprPrec e.value p) ++ ", " ++ (reprPrec e.time p) ++ ")"

instance {σEffect σAction σState : Interface.Scheme} [Repr σEffect.vars] [Enum σEffect.vars] [∀ a, Repr $ σEffect.type a] [Repr σAction.vars] [∀ a, Repr $ σAction.type a] [Repr σState.vars] [Enum σState.vars] [∀ a, Repr $ σState.type a] : Repr (ReactionM.Output σEffect σAction σState time) where
  reprPrec o p := "{" ++ "eff: " ++ (reprPrec o.effects p) ++ ", " ++ (reprPrec o.state p) ++ ", " ++ (reprPrec o.events p) ++ "}"
