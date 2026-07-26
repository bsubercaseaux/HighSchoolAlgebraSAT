import LRATCatcher.Reflect
import Wilkies.LRATBridge

/-!
# LRAT-Catcher certificate for the size-11 main theorem

The certificate is generated from a `kissat --no-factor` DRAT proof of an
UNSAT core, trimmed with `drat-trim`, then rebased to the full source formula.
LRAT-Catcher imports and replays the textual LRAT proof against
`toStdCNF (encode 11)` itself, so it cannot drift from the Lean encoder.
-/

namespace Wilkies

lrat_reflect_cnf native_std_unsatisfiable_encode_11
  (toStdCNF (encode 11)) "certificates/wilkies_11.lrat"

theorem kissat_unsatisfiable_encode_11 : Unsatisfiable (encode 11) :=
  unsatisfiable_of_toStdCNF_unsat native_std_unsatisfiable_encode_11

/-- There is no eleven-element HSI algebra in which Wilkie's identity fails. -/
theorem no_order11_generalCountermodel :
    ¬ ∃ A, GeneralCountermodel 11 A := by
  intro h
  have h5 : InDomain 11 5 := by
    rw [InDomain_iff]
    omega
  exact kissat_unsatisfiable_encode_11
    ((simpEnc_encoder_correctness_general h5).2 h)

theorem every_order11_hsi_satisfies_wilkie
    (A : Algebra) (C : Closed 11 A) (H : HSI 11 A) :
    ∀ x y, InDomain 11 x → InDomain 11 y →
      wilkieP A x y x = wilkieP A y x x := by
  intro x y hx hy
  by_cases hEq : wilkieP A x y x = wilkieP A y x x
  · exact hEq
  · exact False.elim (no_order11_generalCountermodel
      ⟨A, {
        closed := C
        hsi := H
        violates_wilkie := ⟨x, y, hx, hy, hEq⟩
      }⟩)

#print axioms native_std_unsatisfiable_encode_11
#print axioms no_order11_generalCountermodel

end Wilkies
