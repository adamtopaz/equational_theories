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

def randomMagmaLaw' (vars : String) (lhsLen rhsLen : Nat) : RandT IO (Law.MagmaLaw Name) := do
  let lhs ← randomFreeMagmaTerm' vars lhsLen
  let rhs ← randomFreeMagmaTerm' vars rhsLen
  return ⟨lhs, rhs⟩

def randomMagmaLaw (vars : String) (minLen maxLen : Nat) : RandT IO (Law.MagmaLaw Name) := do
  let a := min minLen maxLen
  let b := max minLen maxLen
  have h : a <= b := by omega
  let ⟨lhsLen, _, _⟩ ← Random.randBound Nat a b h
  let ⟨rhsLen, _, _⟩ ← Random.randBound Nat a b h
  randomMagmaLaw' vars lhsLen rhsLen

def randomMagmaLawWithLenDist (vars : String) (lenDist : RandT IO Nat) : 
    RandT IO (Law.MagmaLaw Name) := do
  let lhsLen ← lenDist
  let rhsLen ← lenDist
  randomMagmaLaw' vars lhsLen rhsLen

def randomMagmaLawWithLenDists (vars : String) (lhsDist rhsDist : RandT IO Nat) : 
    RandT IO (Law.MagmaLaw Name) := do
  let lhsLen ← lhsDist
  let rhsLen ← rhsDist
  randomMagmaLaw' vars lhsLen rhsLen

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

def Law.MagmaLaw.tokenize {α : Type} [ToString α] (law : Law.MagmaLaw α) : Json := 
  .mkObj [
    ("lhs", toJson law.lhs.tokenize), 
    ("rhs", toJson law.rhs.tokenize)
  ] 

def Law.MagmaLaw.tokenizeWithName {α : Type} [ToString α] (law : Law.MagmaLaw α) (name : String) : 
    Json := 
  .mkObj [
    ("name", name),
    ("lhs", toJson law.lhs.tokenize), 
    ("rhs", toJson law.rhs.tokenize)
  ] 

def runTokenizeEquations (_inp : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules #[`equational_theories] do 
  for i in [:5000] do
    let eqNm := s!"Equation{i}"
    let law ← try getEquationAsLaw eqNm catch _ => continue
    println! Json.compress <| law.tokenizeWithName eqNm
  return 0

def tokenizeEquations : Cmd := `[Cli|
  equations VIA runTokenizeEquations;
  "Print tokenized equations."
]

def runGenerateEquations (inp : Cli.Parsed) : IO UInt32 := do
  let vars := inp.positionalArg! "vars" |>.as! String
  let num := inp.positionalArg! "num" |>.as! Nat
  let minLen := inp.positionalArg! "minLen" |>.as! Nat
  let maxLen := inp.positionalArg! "maxLen" |>.as! Nat
  for _ in [:num] do
    let law ← IO.runRand <| randomMagmaLaw vars minLen maxLen
    println! Json.compress <| law.tokenize
  return 0

def generateEquations : Cmd := `[Cli|
  generate VIA runGenerateEquations;
  "Generate random equations and tokenize them"
  ARGS:
  vars : String; "Variables to use in equations"
  num : Nat; "Number of equations to generate"
  minLen : Nat; "Minimum length of terms in equations"
  maxLen : Nat; "Maximum length of terms in equations"
]

def entrypoint : Cmd := `[Cli|
  tokenized_data NOOP;
  "Entry point for tokenized data"

  SUBCOMMANDS:
  tokenizeEquations; generateEquations
] 

def main (args : List String) : IO UInt32 := do
  entrypoint.validate args
