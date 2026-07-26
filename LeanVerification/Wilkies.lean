import Wilkies.LRAT11
import Wilkies.Monotonicity

namespace Wilkies

/-- There is no HSI countermodel of Wilkie's identity of order at most eleven. -/
theorem no_generalCountermodel_of_order_le_eleven {n : Nat} (hn : n ≤ 11) :
    ¬ ∃ A, GeneralCountermodel n A :=
  no_generalCountermodels_below_of_no_generalCountermodels hn
    no_order11_generalCountermodel

end Wilkies
