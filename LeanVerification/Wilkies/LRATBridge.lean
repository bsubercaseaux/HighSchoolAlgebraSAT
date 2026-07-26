import Std.Tactic.BVDecide.LRAT
import Wilkies.Correctness

/-!
# Bridge from the Wilkies CNF to Lean's LRAT checker

This is the small, proof-producing adapter needed by the size-11 native LRAT
certificate.
-/

namespace Wilkies

open Std.Sat

attribute [local instance] Classical.propDecidable

/-- Translate a DIMACS-style integer literal to Lean core's zero-based literal. -/
def toStdLit (lit : Lit) : Literal Nat :=
  if 0 < lit then (lit.toNat - 1, true)
  else if lit < 0 then ((-lit).toNat - 1, false)
  else (0, false)

def toStdClause (clause : Clause) : Std.Sat.CNF.Clause Nat :=
  clause.map toStdLit

/-- The CNF consumed by Lean's LRAT checker; clause order is preserved exactly. -/
def toStdCNF (cnf : CNF) : Std.Sat.CNF Nat :=
  { clauses := (cnf.map toStdClause).toArray }

/-- Convert a propositional assignment to the zero-based Boolean convention. -/
noncomputable def toStdAssignment (tau : Assignment) : Nat → Bool :=
  fun v => if tau (v + 1) then true else false

theorem toStdLit_eval_eq_true
    (tau : Assignment) {lit : Lit} (h : evalLit tau lit) :
    (toStdAssignment tau (toStdLit lit).1 == (toStdLit lit).2) = true := by
  unfold evalLit at h
  by_cases hpos : 0 < lit
  · simp [hpos] at h
    have hnat : 0 < lit.toNat := Int.pos_iff_toNat_pos.mp hpos
    have hidx : lit.toNat - 1 + 1 = lit.toNat := by omega
    simp [toStdLit, hpos, toStdAssignment, hidx, h]
  · by_cases hneg : lit < 0
    · simp [hpos, hneg] at h
      have hnegpos : 0 < -lit := Int.neg_pos.mpr hneg
      have hnat : 0 < (-lit).toNat := Int.pos_iff_toNat_pos.mp hnegpos
      have hidx : (-lit).toNat - 1 + 1 = (-lit).toNat := by omega
      simp [toStdLit, hpos, hneg, toStdAssignment, hidx, h]
    · simp [hpos, hneg] at h

theorem toStdClause_eval_eq_true
    (tau : Assignment) {clause : Clause} (h : evalClause tau clause) :
    Std.Sat.CNF.Clause.eval (toStdAssignment tau) (toStdClause clause) = true := by
  induction clause with
  | nil => simp [evalClause] at h
  | cons lit rest ih =>
      rcases h with hLit | hRest
      · apply Bool.or_eq_true_iff.mpr
        exact Or.inl (toStdLit_eval_eq_true tau hLit)
      · apply Bool.or_eq_true_iff.mpr
        exact Or.inr (ih hRest)

theorem toStdCNF_eval_eq_true
    (tau : Assignment) {cnf : CNF} (h : evalCNF tau cnf) :
    Std.Sat.CNF.eval (toStdAssignment tau) (toStdCNF cnf) = true := by
  induction cnf with
  | nil => simp [toStdCNF, Std.Sat.CNF.eval]
  | cons clause rest ih =>
      have hRest :
          ∀ clause, clause ∈ rest →
            Std.Sat.CNF.Clause.eval (toStdAssignment tau) (toStdClause clause) = true := by
        simpa [toStdCNF, Std.Sat.CNF.eval] using ih h.2
      simpa [toStdCNF, Std.Sat.CNF.eval] using
        And.intro (toStdClause_eval_eq_true tau h.1) hRest

/-- Soundness bridge from Lean core's CNF semantics to this development's semantics. -/
theorem unsatisfiable_of_toStdCNF_unsat {cnf : CNF}
    (h : (toStdCNF cnf).Unsat) : Unsatisfiable cnf := by
  rintro ⟨tau, hTau⟩
  have hTrue := toStdCNF_eval_eq_true tau hTau
  have hFalse := h (toStdAssignment tau)
  rw [hTrue] at hFalse
  contradiction

end Wilkies
