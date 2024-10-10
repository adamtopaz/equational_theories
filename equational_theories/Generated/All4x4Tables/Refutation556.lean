
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,2,1],[2,4,0,4,1],[2,0,0,4,3],[2,4,3,2,1],[1,0,3,4,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,3,2,1],[2,4,0,4,1],[2,0,0,4,3],[2,4,3,2,1],[1,0,3,4,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,0,3,2,1],[2,4,0,4,1],[2,0,0,4,3],[2,4,3,2,1],[1,0,3,4,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,3,2,1],[2,4,0,4,1],[2,0,0,4,3],[2,4,3,2,1],[1,0,3,4,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2093] [3952] :=
    ⟨Fin 5, «FinitePoly [[1,0,3,2,1],[2,4,0,4,1],[2,0,0,4,3],[2,4,3,2,1],[1,0,3,4,3]]», by decideFin!⟩
