import Batteries.Data.Array.Basic
import Batteries.Tactic.Lint.Frontend
import Cli.Basic
import Lean.Util.SearchPath
import equational_theories.Closure
import Mathlib.Lean.CoreM
import Mathlib.Control.Random

open Lean Cli

def randomVarName (vars : String) : RandT IO Name := 
  match h : vars.toList.length with
  | 0 => do throw <| .userError "Empty string"
  | n+1 => do
    let f : Fin (n+1) ← Random.randFin
    return vars.toList[f].toString.toName

partial
def randomFreeMagmaTerm' (vars : String) (length : Nat) : RandT IO (FreeMagma Name) := 
  match length with
  | 0 => do throw <| .userError "Can't generate a word of length zero"
  | 1 => .Leaf <$> randomVarName vars 
  | n+2 => do
    let ⟨a, _, _⟩ ← Random.randBound Nat 1 (n+1) (Nat.le_add_left _ _)
    let b := (n+2) - a
    let a ← randomFreeMagmaTerm' vars a
    let b ← randomFreeMagmaTerm' vars b
    return .Fork a b

def randomFreeMagmaTerm (vars : String) (minLen maxLen : Nat) : 
    RandT IO (FreeMagma Name) := do
  if minLen = 0 then throw <| .userError "Minimum length must be at least 1"
  let ⟨a, _, _⟩ ← Random.randBound Nat (min minLen maxLen) (max minLen maxLen) (by omega)
  randomFreeMagmaTerm' vars a

def randomFreeMagmaTermWithLenDist (vars : String) (lenDist : RandT IO Nat) : 
    RandT IO (FreeMagma Name) := do
  let len ← lenDist
  randomFreeMagmaTerm' vars (max len 1)

partial
def getEquationAsLaw (eqn : String) : CoreM (Law.MagmaLaw Name) := Meta.MetaM.run' do
  let env ← getEnv
  let some c := env.find? eqn.toName | throwError "Failed to find {eqn}"
  let some val := c.value? | throwError "Failed to find {eqn} value"
  Meta.lambdaTelescope val fun _ body => Meta.forallTelescope body fun _ body => do
    match_expr body with 
    | Eq _ lhs rhs => return ⟨← mkFreeMagma lhs, ← mkFreeMagma rhs⟩
    | _ => throwError "Failed to find {eqn} equation components"
where mkFreeMagma expr := do
  match_expr expr with 
  | Magma.op _ _ lhs rhs => 
    return .Fork (← mkFreeMagma lhs) (← mkFreeMagma rhs)
  | _ => 
    match expr with 
    | .fvar id => return .Leaf (← id.getUserName)
    | _ => throwError "Failed to find {eqn} equation components"

def FreeMagma.tokenize {α : Type} [ToString α] : FreeMagma α → Array String
  | .Leaf x => #[s!"{x}"]
  | .Fork x y => #["mul"] ++ x.tokenize ++ y.tokenize

def runTokenizeEquations (_inp : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules #[`equational_theories] do 
  for i in [:5000] do
    let eqNm := s!"Equation{i}"
    let law ← try getEquationAsLaw eqNm catch _ => continue
    println! Json.compress <| 
      .mkObj [
        ("name", eqNm), 
        ("lhs", toJson law.lhs.tokenize), 
        ("rhs", toJson law.rhs.tokenize)
      ]
  return 0

def tokenizedData : Cmd := `[Cli|
  tokenized_data VIA runTokenizeEquations;
  "Print tokenized equations."
]

def main (args : List String) : IO UInt32 := do
  tokenizedData.validate args
