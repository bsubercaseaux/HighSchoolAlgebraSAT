import Wilkies.Correctness

/-!
# Extending finite HSI countermodels by zero

An HSI algebra on `{1, ..., n}` can be extended by a fresh element `n + 1`
that acts as a zero.  It is additive-neutral, multiplicatively absorbing, and
uses the standard totalized exponentiation convention `x^0 = 1` (including
`0^0 = 1`).  This will make countermodel existence upward closed.
-/

namespace Wilkies

/-- Adjoin the fresh element `n + 1` as a zero to an algebra on `{1, ..., n}`. -/
def adjoinZero (n : Nat) (A : Algebra) : Algebra where
  add x y := if x = n + 1 then y else if y = n + 1 then x else A.add x y
  mul x y := if x = n + 1 then n + 1 else if y = n + 1 then n + 1 else A.mul x y
  exp x y := if y = n + 1 then 1 else if x = n + 1 then n + 1 else A.exp x y

private theorem inDomain_succ_top (n : Nat) : InDomain (n + 1) (n + 1) := by
  rw [InDomain_iff]
  omega

private theorem inDomain_succ_one (n : Nat) : InDomain (n + 1) 1 := by
  rw [InDomain_iff]
  omega

private theorem inDomain_succ_of_old {n x : Nat}
    (hx : InDomain n x) : InDomain (n + 1) x := by
  rw [InDomain_iff] at hx ⊢
  omega

private theorem inDomain_old_of_succ_ne_top {n x : Nat}
    (hx : InDomain (n + 1) x) (hxtop : x ≠ n + 1) : InDomain n x := by
  rw [InDomain_iff] at hx ⊢
  omega

private theorem old_ne_top {n x : Nat} (hx : InDomain n x) : x ≠ n + 1 := by
  rw [InDomain_iff] at hx
  omega

@[simp] private theorem adjoinZero_add_top_left (n : Nat) (A : Algebra) (x : Nat) :
    (adjoinZero n A).add (n + 1) x = x := by
  simp [adjoinZero]

@[simp] private theorem adjoinZero_add_top_right (n : Nat) (A : Algebra) (x : Nat) :
    (adjoinZero n A).add x (n + 1) = x := by
  by_cases h : x = n + 1 <;> simp [adjoinZero, h]

@[simp] private theorem adjoinZero_mul_top_left (n : Nat) (A : Algebra) (x : Nat) :
    (adjoinZero n A).mul (n + 1) x = n + 1 := by
  simp [adjoinZero]

@[simp] private theorem adjoinZero_mul_top_right (n : Nat) (A : Algebra) (x : Nat) :
    (adjoinZero n A).mul x (n + 1) = n + 1 := by
  simp [adjoinZero]

@[simp] private theorem adjoinZero_exp_top_right (n : Nat) (A : Algebra) (x : Nat) :
    (adjoinZero n A).exp x (n + 1) = 1 := by
  simp [adjoinZero]

private theorem adjoinZero_add_old {n : Nat} {A : Algebra} {x y : Nat}
    (hx : InDomain n x) (hy : InDomain n y) :
    (adjoinZero n A).add x y = A.add x y := by
  simp [adjoinZero, old_ne_top hx, old_ne_top hy]

private theorem adjoinZero_mul_old {n : Nat} {A : Algebra} {x y : Nat}
    (hx : InDomain n x) (hy : InDomain n y) :
    (adjoinZero n A).mul x y = A.mul x y := by
  simp [adjoinZero, old_ne_top hx, old_ne_top hy]

private theorem adjoinZero_exp_old {n : Nat} {A : Algebra} {x y : Nat}
    (hx : InDomain n x) (hy : InDomain n y) :
    (adjoinZero n A).exp x y = A.exp x y := by
  simp [adjoinZero, old_ne_top hx, old_ne_top hy]

private theorem inDomain_one_of_pos {n : Nat} (hn : 1 ≤ n) : InDomain n 1 := by
  rw [InDomain_iff]
  omega

private theorem adjoinZero_exp_top_left_old {n : Nat} {A : Algebra} {y : Nat}
    (hy : InDomain n y) :
    (adjoinZero n A).exp (n + 1) y = n + 1 := by
  simp [adjoinZero, old_ne_top hy]

private theorem adjoinZero_mul_one {n : Nat} {A : Algebra}
    (hn : 1 ≤ n) (H : HSI n A) {x : Nat} (hx : InDomain (n + 1) x) :
    (adjoinZero n A).mul x 1 = x := by
  by_cases hxtop : x = n + 1
  · subst x
    simp [adjoinZero]
  · have hxOld := inDomain_old_of_succ_ne_top hx hxtop
    have h1 := inDomain_one_of_pos hn
    rw [adjoinZero_mul_old hxOld h1]
    exact H.mul_one hxOld

private theorem adjoinZero_one_mul {n : Nat} {A : Algebra}
    (hn : 1 ≤ n) (H : HSI n A) {x : Nat} (hx : InDomain (n + 1) x) :
    (adjoinZero n A).mul 1 x = x := by
  by_cases hxtop : x = n + 1
  · subst x
    simp [adjoinZero]
  · have hxOld := inDomain_old_of_succ_ne_top hx hxtop
    have h1 := inDomain_one_of_pos hn
    rw [adjoinZero_mul_old h1 hxOld]
    calc
      A.mul 1 x = A.mul x 1 := H.mul_comm h1 hxOld
      _ = x := H.mul_one hxOld

theorem adjoinZero_closed {n : Nat} {A : Algebra} (C : Closed n A) :
    Closed (n + 1) (adjoinZero n A) where
  add_mem := by
    intro i j hi hj
    by_cases hitop : i = n + 1
    · subst i
      simpa using hj
    by_cases hjtop : j = n + 1
    · subst j
      simpa using hi
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    rw [adjoinZero_add_old hiOld hjOld]
    exact inDomain_succ_of_old (C.add_mem hiOld hjOld)
  mul_mem := by
    intro i j hi hj
    by_cases hitop : i = n + 1
    · subst i
      simpa [adjoinZero] using inDomain_succ_top n
    by_cases hjtop : j = n + 1
    · subst j
      simpa [adjoinZero, hitop] using inDomain_succ_top n
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    rw [adjoinZero_mul_old hiOld hjOld]
    exact inDomain_succ_of_old (C.mul_mem hiOld hjOld)
  exp_mem := by
    intro i j hi hj
    by_cases hjtop : j = n + 1
    · subst j
      simpa [adjoinZero] using inDomain_succ_one n
    by_cases hitop : i = n + 1
    · subst i
      simpa [adjoinZero, hjtop] using inDomain_succ_top n
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    rw [adjoinZero_exp_old hiOld hjOld]
    exact inDomain_succ_of_old (C.exp_mem hiOld hjOld)

theorem adjoinZero_hsi {n : Nat} {A : Algebra}
    (hn : 1 ≤ n) (C : Closed n A) (H : HSI n A) :
    HSI (n + 1) (adjoinZero n A) where
  add_comm := by
    intro i j hi hj
    by_cases hitop : i = n + 1
    · subst i
      simp
    by_cases hjtop : j = n + 1
    · subst j
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    rw [adjoinZero_add_old hiOld hjOld, adjoinZero_add_old hjOld hiOld]
    exact H.add_comm hiOld hjOld
  add_assoc := by
    intro i j k hi hj hk
    by_cases hitop : i = n + 1
    · subst i
      simp
    by_cases hjtop : j = n + 1
    · subst j
      simp
    by_cases hktop : k = n + 1
    · subst k
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    have hkOld := inDomain_old_of_succ_ne_top hk hktop
    have hijOld := C.add_mem hiOld hjOld
    have hjkOld := C.add_mem hjOld hkOld
    rw [adjoinZero_add_old hjOld hkOld, adjoinZero_add_old hiOld hjkOld,
      adjoinZero_add_old hiOld hjOld, adjoinZero_add_old hijOld hkOld]
    exact H.add_assoc hiOld hjOld hkOld
  mul_one := by
    intro i hi
    exact adjoinZero_mul_one hn H hi
  mul_comm := by
    intro i j hi hj
    by_cases hitop : i = n + 1
    · subst i
      simp
    by_cases hjtop : j = n + 1
    · subst j
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    rw [adjoinZero_mul_old hiOld hjOld, adjoinZero_mul_old hjOld hiOld]
    exact H.mul_comm hiOld hjOld
  mul_assoc := by
    intro i j k hi hj hk
    by_cases hitop : i = n + 1
    · subst i
      simp
    by_cases hjtop : j = n + 1
    · subst j
      simp
    by_cases hktop : k = n + 1
    · subst k
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    have hkOld := inDomain_old_of_succ_ne_top hk hktop
    have hijOld := C.mul_mem hiOld hjOld
    have hjkOld := C.mul_mem hjOld hkOld
    rw [adjoinZero_mul_old hjOld hkOld, adjoinZero_mul_old hiOld hjkOld,
      adjoinZero_mul_old hiOld hjOld, adjoinZero_mul_old hijOld hkOld]
    exact H.mul_assoc hiOld hjOld hkOld
  distrib := by
    intro i j k hi hj hk
    by_cases hitop : i = n + 1
    · subst i
      simp
    by_cases hjtop : j = n + 1
    · subst j
      simp
    by_cases hktop : k = n + 1
    · subst k
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    have hkOld := inDomain_old_of_succ_ne_top hk hktop
    have hjkOld := C.add_mem hjOld hkOld
    have hijOld := C.mul_mem hiOld hjOld
    have hikOld := C.mul_mem hiOld hkOld
    rw [adjoinZero_add_old hjOld hkOld, adjoinZero_mul_old hiOld hjkOld,
      adjoinZero_mul_old hiOld hjOld, adjoinZero_mul_old hiOld hkOld,
      adjoinZero_add_old hijOld hikOld]
    exact H.distrib hiOld hjOld hkOld
  one_exp := by
    intro i hi
    by_cases hitop : i = n + 1
    · subst i
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have h1 := inDomain_one_of_pos hn
    rw [adjoinZero_exp_old h1 hiOld]
    exact H.one_exp hiOld
  exp_one := by
    intro i hi
    by_cases hitop : i = n + 1
    · subst i
      simp [adjoinZero]
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have h1 := inDomain_one_of_pos hn
    rw [adjoinZero_exp_old hiOld h1]
    exact H.exp_one hiOld
  exp_add := by
    intro i j k hi hj hk
    have D := adjoinZero_closed C
    by_cases hitop : i = n + 1
    · subst i
      by_cases hjtop : j = n + 1
      · subst j
        by_cases hktop : k = n + 1
        · subst k
          rw [adjoinZero_add_top_left, adjoinZero_exp_top_right]
          exact (adjoinZero_one_mul hn H (inDomain_succ_one n)).symm
        · have hkOld := inDomain_old_of_succ_ne_top hk hktop
          rw [adjoinZero_add_top_left, adjoinZero_exp_top_right]
          exact (adjoinZero_one_mul hn H (D.exp_mem (inDomain_succ_top n) hk)).symm
      · have hjOld := inDomain_old_of_succ_ne_top hj hjtop
        by_cases hktop : k = n + 1
        · subst k
          rw [adjoinZero_add_top_right, adjoinZero_exp_top_right]
          exact (adjoinZero_mul_one hn H (D.exp_mem (inDomain_succ_top n) hj)).symm
        · have hkOld := inDomain_old_of_succ_ne_top hk hktop
          have hjkOld := C.add_mem hjOld hkOld
          rw [adjoinZero_add_old hjOld hkOld,
            adjoinZero_exp_top_left_old hjkOld,
            adjoinZero_exp_top_left_old hjOld,
            adjoinZero_exp_top_left_old hkOld]
          simp
    · have hiOld := inDomain_old_of_succ_ne_top hi hitop
      by_cases hjtop : j = n + 1
      · subst j
        by_cases hktop : k = n + 1
        · subst k
          rw [adjoinZero_add_top_left, adjoinZero_exp_top_right]
          exact (adjoinZero_one_mul hn H (inDomain_succ_one n)).symm
        · rw [adjoinZero_add_top_left, adjoinZero_exp_top_right]
          exact (adjoinZero_one_mul hn H (D.exp_mem hi hk)).symm
      · have hjOld := inDomain_old_of_succ_ne_top hj hjtop
        by_cases hktop : k = n + 1
        · subst k
          rw [adjoinZero_add_top_right, adjoinZero_exp_top_right]
          exact (adjoinZero_mul_one hn H (D.exp_mem hi hj)).symm
        · have hkOld := inDomain_old_of_succ_ne_top hk hktop
          have hjkOld := C.add_mem hjOld hkOld
          have hijOld := C.exp_mem hiOld hjOld
          have hikOld := C.exp_mem hiOld hkOld
          rw [adjoinZero_add_old hjOld hkOld, adjoinZero_exp_old hiOld hjkOld,
            adjoinZero_exp_old hiOld hjOld, adjoinZero_exp_old hiOld hkOld,
            adjoinZero_mul_old hijOld hikOld]
          exact H.exp_add hiOld hjOld hkOld
  exp_mul := by
    intro i j k hi hj hk
    have D := adjoinZero_closed C
    by_cases hktop : k = n + 1
    · subst k
      rw [adjoinZero_exp_top_right, adjoinZero_exp_top_right,
        adjoinZero_exp_top_right]
      exact (adjoinZero_one_mul hn H (inDomain_succ_one n)).symm
    have hkOld := inDomain_old_of_succ_ne_top hk hktop
    by_cases hitop : i = n + 1
    · subst i
      rw [adjoinZero_mul_top_left, adjoinZero_exp_top_left_old hkOld]
      simp
    by_cases hjtop : j = n + 1
    · subst j
      rw [adjoinZero_mul_top_right, adjoinZero_exp_top_left_old hkOld]
      simp
    have hiOld := inDomain_old_of_succ_ne_top hi hitop
    have hjOld := inDomain_old_of_succ_ne_top hj hjtop
    have hijOld := C.mul_mem hiOld hjOld
    have hikOld := C.exp_mem hiOld hkOld
    have hjkOld := C.exp_mem hjOld hkOld
    rw [adjoinZero_mul_old hiOld hjOld, adjoinZero_exp_old hijOld hkOld,
      adjoinZero_exp_old hiOld hkOld, adjoinZero_exp_old hjOld hkOld,
      adjoinZero_mul_old hikOld hjkOld]
    exact H.exp_mul hiOld hjOld hkOld
  exp_assoc := by
    intro i j k hi hj hk
    have D := adjoinZero_closed C
    by_cases hktop : k = n + 1
    · subst k
      rw [adjoinZero_exp_top_right, adjoinZero_mul_top_right,
        adjoinZero_exp_top_right]
    have hkOld := inDomain_old_of_succ_ne_top hk hktop
    by_cases hitop : i = n + 1
    · subst i
      by_cases hjtop : j = n + 1
      · subst j
        have h1 := inDomain_one_of_pos hn
        rw [adjoinZero_exp_top_right, adjoinZero_exp_old h1 hkOld,
          adjoinZero_mul_top_left, adjoinZero_exp_top_right]
        exact H.one_exp hkOld
      · have hjOld := inDomain_old_of_succ_ne_top hj hjtop
        have hjkOld := C.mul_mem hjOld hkOld
        rw [adjoinZero_exp_top_left_old hjOld,
          adjoinZero_exp_top_left_old hkOld,
          adjoinZero_mul_old hjOld hkOld,
          adjoinZero_exp_top_left_old hjkOld]
    · have hiOld := inDomain_old_of_succ_ne_top hi hitop
      by_cases hjtop : j = n + 1
      · subst j
        have h1 := inDomain_one_of_pos hn
        rw [adjoinZero_exp_top_right, adjoinZero_exp_old h1 hkOld,
          adjoinZero_mul_top_left, adjoinZero_exp_top_right]
        exact H.one_exp hkOld
      · have hjOld := inDomain_old_of_succ_ne_top hj hjtop
        have hijOld := C.exp_mem hiOld hjOld
        have hjkOld := C.mul_mem hjOld hkOld
        rw [adjoinZero_exp_old hiOld hjOld, adjoinZero_exp_old hijOld hkOld,
          adjoinZero_mul_old hjOld hkOld, adjoinZero_exp_old hiOld hjkOld]
        exact H.exp_assoc hiOld hjOld hkOld

private theorem adjoinZero_x2_old {n : Nat} {A : Algebra}
    {x : Nat} (hx : InDomain n x) :
    x2 (adjoinZero n A) x = x2 A x := by
  unfold x2
  exact adjoinZero_mul_old hx hx

private theorem adjoinZero_x3_old {n : Nat} {A : Algebra} (C : Closed n A)
    {x : Nat} (hx : InDomain n x) :
    x3 (adjoinZero n A) x = x3 A x := by
  have hx2 := C.mul_mem hx hx
  unfold x3
  rw [adjoinZero_x2_old hx]
  exact adjoinZero_mul_old hx2 hx

private theorem adjoinZero_x4_old {n : Nat} {A : Algebra} (C : Closed n A)
    {x : Nat} (hx : InDomain n x) :
    x4 (adjoinZero n A) x = x4 A x := by
  have hx2 := C.mul_mem hx hx
  have hx3 := C.mul_mem hx2 hx
  unfold x4
  rw [adjoinZero_x3_old C hx]
  exact adjoinZero_mul_old hx3 hx

private theorem adjoinZero_Pterm_old {n : Nat} {A : Algebra}
    (hn : 1 ≤ n) {x : Nat} (hx : InDomain n x) :
    Pterm (adjoinZero n A) x = Pterm A x := by
  unfold Pterm
  exact adjoinZero_add_old (inDomain_one_of_pos hn) hx

private theorem adjoinZero_Qterm_old {n : Nat} {A : Algebra} (C : Closed n A)
    (hn : 1 ≤ n) {x : Nat} (hx : InDomain n x) :
    Qterm (adjoinZero n A) x = Qterm A x := by
  have hP := C.add_mem (inDomain_one_of_pos hn) hx
  have hx2 := C.mul_mem hx hx
  unfold Qterm
  rw [adjoinZero_Pterm_old hn hx, adjoinZero_x2_old hx]
  exact adjoinZero_add_old hP hx2

private theorem adjoinZero_Rterm_old {n : Nat} {A : Algebra} (C : Closed n A)
    (hn : 1 ≤ n) {x : Nat} (hx : InDomain n x) :
    Rterm (adjoinZero n A) x = Rterm A x := by
  have hx2 := C.mul_mem hx hx
  have hx3 := C.mul_mem hx2 hx
  unfold Rterm
  rw [adjoinZero_x3_old C hx]
  exact adjoinZero_add_old (inDomain_one_of_pos hn) hx3

private theorem adjoinZero_Sterm_old {n : Nat} {A : Algebra} (C : Closed n A)
    (hn : 1 ≤ n) {x : Nat} (hx : InDomain n x) :
    Sterm (adjoinZero n A) x = Sterm A x := by
  have hx2 := C.mul_mem hx hx
  have hx3 := C.mul_mem hx2 hx
  have hx4 := C.mul_mem hx3 hx
  have hx2' : InDomain n (x2 A x) := by simpa [x2] using hx2
  have hx4' : InDomain n (x4 A x) := by simpa [x4] using hx4
  have honeX2 := C.add_mem (inDomain_one_of_pos hn) hx2
  unfold Sterm
  rw [adjoinZero_x2_old hx, adjoinZero_x4_old C hx]
  rw [adjoinZero_add_old (A := A) (inDomain_one_of_pos hn) hx2']
  exact adjoinZero_add_old (A := A) honeX2 hx4'

private theorem adjoinZero_wilkieCore_old {n : Nat} {A : Algebra} (C : Closed n A)
    {p q r s x y : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x) (hy : InDomain n y) :
    wilkieCore (adjoinZero n A) p q r s x y = wilkieCore A p q r s x y := by
  have hpy := C.exp_mem hp hy
  have hqy := C.exp_mem hq hy
  have hrx := C.exp_mem hr hx
  have hsx := C.exp_mem hs hx
  have hsumPQ := C.add_mem hpy hqy
  have hsumRS := C.add_mem hrx hsx
  have hleft := C.exp_mem hsumPQ hx
  have hright := C.exp_mem hsumRS hy
  unfold wilkieCore
  rw [adjoinZero_exp_old hp hy, adjoinZero_exp_old hq hy,
    adjoinZero_add_old hpy hqy, adjoinZero_exp_old hsumPQ hx,
    adjoinZero_exp_old hr hx, adjoinZero_exp_old hs hx,
    adjoinZero_add_old hrx hsx, adjoinZero_exp_old hsumRS hy,
    adjoinZero_mul_old hleft hright]

private theorem wilkieP_eq_core (A : Algebra) (x y z : Nat) :
    wilkieP A x y z = wilkieCore A (Pterm A z) (Qterm A z) (Rterm A z) (Sterm A z) x y := by
  rfl

private theorem adjoinZero_wilkieP_old {n : Nat} {A : Algebra}
    (hn : 1 ≤ n) (C : Closed n A) {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    wilkieP (adjoinZero n A) x y z = wilkieP A x y z := by
  rw [wilkieP_eq_core, wilkieP_eq_core,
    adjoinZero_Pterm_old hn hz, adjoinZero_Qterm_old C hn hz,
    adjoinZero_Rterm_old C hn hz, adjoinZero_Sterm_old C hn hz]
  rcases pqrs_terms_mem_of_closed C (inDomain_one_of_pos hn) hz with ⟨hP, hQ, hR, hS⟩
  exact adjoinZero_wilkieCore_old C hP hQ hR hS hx hy

/-- A countermodel remains a countermodel after adjoining one fresh zero. -/
theorem extendCountermodelByZero {n : Nat} {A : Algebra}
    (M : GeneralCountermodel n A) :
    ∃ B, GeneralCountermodel (n + 1) B := by
  rcases M.violates_wilkie with ⟨x, y, hx, hy, hFails⟩
  have hn : 1 ≤ n := by
    rw [InDomain_iff] at hx
    omega
  refine ⟨adjoinZero n A, ?_⟩
  refine {
    closed := adjoinZero_closed M.closed
    hsi := adjoinZero_hsi hn M.closed M.hsi
    violates_wilkie := ⟨x, y, inDomain_succ_of_old hx, inDomain_succ_of_old hy, ?_⟩
  }
  unfold WilkieFailsAt at hFails ⊢
  rw [adjoinZero_wilkieP_old hn M.closed hx hy hx,
    adjoinZero_wilkieP_old hn M.closed hy hx hx]
  exact hFails

/-- Extend a finite countermodel by any prescribed number of fresh zeros. -/
theorem GeneralCountermodel.extendBy {m : Nat} {A : Algebra}
    (M : GeneralCountermodel m A) :
    ∀ k : Nat, ∃ B, GeneralCountermodel (m + k) B
  | 0 => ⟨A, by simpa using M⟩
  | k + 1 => by
      obtain ⟨B, hB⟩ := M.extendBy k
      obtain ⟨D, hD⟩ := extendCountermodelByZero hB
      exact ⟨D, by simpa [Nat.add_assoc] using hD⟩

/-- If no countermodel exists at `n`, none exists at any smaller size. -/
theorem no_generalCountermodels_below_of_no_generalCountermodels
    {m n : Nat} (hmn : m ≤ n) (hN : ¬ ∃ A, GeneralCountermodel n A) :
    ¬ ∃ A, GeneralCountermodel m A := by
  rintro ⟨A, M⟩
  obtain ⟨B, hB⟩ := M.extendBy (n - m)
  apply hN
  refine ⟨B, ?_⟩
  simpa [Nat.add_sub_of_le hmn] using hB

end Wilkies
