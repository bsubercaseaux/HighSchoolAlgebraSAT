import Wilkies.EncoderSimplified
import Lean.Elab.Tactic.Omega

namespace Wilkies

abbrev Assignment := Nat → Prop

def evalLit (τ : Assignment) (lit : Lit) : Prop :=
  if 0 < lit then τ lit.toNat
  else if lit < 0 then ¬τ (-lit).toNat
  else False

def evalClause (τ : Assignment) : Clause → Prop
  | [] => False
  | lit :: rest => evalLit τ lit ∨ evalClause τ rest

def evalCNF (τ : Assignment) : CNF → Prop
  | [] => True
  | clause :: rest => evalClause τ clause ∧ evalCNF τ rest

def Satisfiable (cnf : CNF) : Prop :=
  ∃ τ, evalCNF τ cnf

def Unsatisfiable (cnf : CNF) : Prop :=
  ¬ Satisfiable cnf

def CNFBelow (cnf : CNF) (bound : Nat) : Prop :=
  ∀ clause, clause ∈ cnf → ∀ lit, lit ∈ clause → litVar lit < bound

theorem litVar_pos (v : Nat) : litVar (pos v) = v := by
  have hnot : ¬(((v : Nat) : Int) < 0) := by omega
  simp [litVar, pos, hnot]

theorem litVar_neg (v : Nat) : litVar (neg v) = v := by
  cases v with
  | zero => simp [litVar, neg]
  | succ v => simp [litVar, neg]

theorem litVar_pos_lt_of {v bound : Nat} (h : v < bound) :
    litVar (pos v) < bound := by
  simpa [litVar_pos] using h

theorem litVar_neg_lt_of {v bound : Nat} (h : v < bound) :
    litVar (neg v) < bound := by
  simpa [litVar_neg] using h

theorem evalLit_congr_of_litVar
    {τ σ : Assignment} {lit : Lit}
    (h : τ (litVar lit) ↔ σ (litVar lit)) :
    evalLit τ lit ↔ evalLit σ lit := by
  by_cases hpos : 0 < lit
  · have hnotneg : ¬ (lit < 0) := by
      intro hlt
      have hbad : (0 : Int) < 0 := by
        calc
          (0 : Int) < lit := hpos
          _ < 0 := hlt
      omega
    have hvar : litVar lit = lit.toNat := by
      simp [litVar, hnotneg]
    have h' : τ lit.toNat ↔ σ lit.toNat := by
      simpa [hvar] using h
    simpa [evalLit, hpos] using h'
  · by_cases hneg : lit < 0
    · have hvar : litVar lit = (-lit).toNat := by
        simp [litVar, hneg]
      have h' : τ (-lit).toNat ↔ σ (-lit).toNat := by
        simpa [hvar] using h
      have hnot : (¬τ (-lit).toNat ↔ ¬σ (-lit).toNat) :=
        ⟨(fun hn hs => hn (h'.mpr hs)),
          (fun hn hs => hn (h'.mp hs))⟩
      simpa [evalLit, hpos, hneg] using hnot
    · simp [evalLit, hpos, hneg]

theorem evalClause_congr_of_below
    {τ σ : Assignment} {bound : Nat} :
    ∀ {clause : Clause},
      (∀ lit, lit ∈ clause → litVar lit < bound) →
      (∀ v, v < bound → (τ v ↔ σ v)) →
        (evalClause τ clause ↔ evalClause σ clause)
  | [], _, _ => by simp [evalClause]
  | lit :: rest, hbelow, hagree => by
      have hlit : litVar lit < bound := hbelow lit (by simp)
      have hrest : ∀ l, l ∈ rest → litVar l < bound := by
        intro l hl
        exact hbelow l (by simp [hl])
      have ih := evalClause_congr_of_below hrest hagree
      simp [evalClause, evalLit_congr_of_litVar (hagree (litVar lit) hlit), ih]

theorem evalCNF_congr_of_below
    {τ σ : Assignment} {bound : Nat} :
    ∀ {cnf : CNF},
      CNFBelow cnf bound →
      (∀ v, v < bound → (τ v ↔ σ v)) →
        (evalCNF τ cnf ↔ evalCNF σ cnf)
  | [], _, _ => by simp [evalCNF]
  | clause :: rest, hbelow, hagree => by
      have hclause : ∀ lit, lit ∈ clause → litVar lit < bound := by
        intro lit hlit
        exact hbelow clause (by simp) lit hlit
      have hrest : CNFBelow rest bound := by
        intro c hc lit hlit
        exact hbelow c (by simp [hc]) lit hlit
      have ih := evalCNF_congr_of_below hrest hagree
      simp [evalCNF, evalClause_congr_of_below hclause hagree, ih]

theorem evalClause_congr
    {τ σ : Assignment} (h : ∀ v, τ v ↔ σ v) :
    ∀ clause : Clause, evalClause τ clause ↔ evalClause σ clause
  | [] => by simp [evalClause]
  | lit :: rest => by
      have hlit : evalLit τ lit ↔ evalLit σ lit :=
        evalLit_congr_of_litVar (h (litVar lit))
      have hrest : evalClause τ rest ↔ evalClause σ rest :=
        evalClause_congr h rest
      simp [evalClause, hlit, hrest]

theorem evalCNF_congr
    {τ σ : Assignment} (h : ∀ v, τ v ↔ σ v) :
    ∀ cnf : CNF, evalCNF τ cnf ↔ evalCNF σ cnf
  | [] => by simp [evalCNF]
  | clause :: rest => by
      have hclause : evalClause τ clause ↔ evalClause σ clause :=
        evalClause_congr h clause
      have hrest : evalCNF τ rest ↔ evalCNF σ rest :=
        evalCNF_congr h rest
      simp [evalCNF, hclause, hrest]

theorem evalCNF_append (τ : Assignment) (left right : CNF) :
    evalCNF τ (left ++ right) ↔ evalCNF τ left ∧ evalCNF τ right := by
  induction left with
  | nil =>
      simp [evalCNF]
  | cons clause rest ih =>
      simp [evalCNF, ih, and_assoc]

theorem evalCNF_flatMap
    {α : Type} (τ : Assignment) (xs : List α) (f : α → CNF) :
    evalCNF τ (flatMap xs f) ↔ ∀ x, x ∈ xs → evalCNF τ (f x) := by
  induction xs with
  | nil =>
      simp [flatMap, evalCNF]
  | cons x xs ih =>
      simp [flatMap, evalCNF_append, ih]

def AtLeastOneVars (τ : Assignment) (vars : List Nat) : Prop :=
  ∃ v, v ∈ vars ∧ τ v

def AtMostOneVars (τ : Assignment) : List Nat → Prop
  | [] => True
  | v :: vars => (∀ w, w ∈ vars → ¬(τ v ∧ τ w)) ∧ AtMostOneVars τ vars

def ExactlyOneVars (τ : Assignment) (vars : List Nat) : Prop :=
  AtLeastOneVars τ vars ∧ AtMostOneVars τ vars

theorem evalLit_pos_of_pos (τ : Assignment) {v : Nat} (hv : 0 < v) :
    evalLit τ (pos v) ↔ τ v := by
  cases v with
  | zero => cases hv
  | succ v =>
      have hgt : (0 : Int) < ((v + 1 : Nat) : Int) := by omega
      simp [pos, evalLit]

theorem evalLit_neg_of_pos (τ : Assignment) {v : Nat} (hv : 0 < v) :
    evalLit τ (neg v) ↔ ¬τ v := by
  cases v with
  | zero => cases hv
  | succ v =>
      have hnotpos : ¬(((v : Int) + 1) < 0) := by omega
      simp [neg, evalLit, hnotpos]

theorem evalClause_two_neg_iff
    (τ : Assignment) {x y : Nat} (hx : 0 < x) (hy : 0 < y) :
    evalClause τ [neg x, neg y] ↔ ¬(τ x ∧ τ y) := by
  simp [evalClause, evalLit_neg_of_pos τ hx, evalLit_neg_of_pos τ hy]
  constructor
  · intro h hxtrue
    cases h with
    | inl hxfalse => exact False.elim (hxfalse hxtrue)
    | inr hyfalse => exact hyfalse
  · intro h
    by_cases hxtrue : τ x
    · right
      exact h hxtrue
    · left
      exact hxtrue

theorem evalCNF_negPairClauses_iff
    (τ : Assignment) {x : Nat} (hx : 0 < x)
    (vars : List Nat) (hpos : ∀ y, y ∈ vars → 0 < y) :
    evalCNF τ (vars.map (fun y => [neg x, neg y])) ↔
      ∀ y, y ∈ vars → ¬(τ x ∧ τ y) := by
  induction vars with
  | nil =>
      simp [evalCNF]
  | cons y ys ih =>
      have hy : 0 < y := hpos y (by simp)
      have hys : ∀ z, z ∈ ys → 0 < z := by
        intro z hz
        exact hpos z (by simp [hz])
      have ih' := ih hys
      constructor
      · intro h z hz
        simp [evalCNF, evalClause_two_neg_iff τ hx hy, ih'] at h
        cases hz with
        | head =>
            intro hxy
            exact h.1 hxy.1 hxy.2
        | tail _ hzTail =>
            intro hxy
            exact h.2 z hzTail hxy.1 hxy.2
      · intro h
        constructor
        · exact (evalClause_two_neg_iff τ hx hy).2 (h y (by simp))
        · exact ih'.2 (by
            intro z hz
            exact h z (by simp [hz]))

theorem evalCNF_atMostOnePairwise_iff
    (τ : Assignment) (vars : List Nat)
    (hpos : ∀ v, v ∈ vars → 0 < v) :
    evalCNF τ (atMostOnePairwise vars) ↔ AtMostOneVars τ vars := by
  induction vars with
  | nil =>
      simp [atMostOnePairwise, AtMostOneVars, evalCNF]
  | cons v vars ih =>
      have hv : 0 < v := hpos v (by simp)
      have hvars : ∀ w, w ∈ vars → 0 < w := by
        intro w hw
        exact hpos w (by simp [hw])
      rw [atMostOnePairwise, evalCNF_append]
      rw [evalCNF_negPairClauses_iff τ hv vars hvars]
      rw [ih hvars]
      simp [AtMostOneVars]

theorem evalClause_posList_iff
    (τ : Assignment) (vars : List Nat)
    (hpos : ∀ v, v ∈ vars → 0 < v) :
    evalClause τ (vars.map pos) ↔ AtLeastOneVars τ vars := by
  induction vars with
  | nil =>
      simp [evalClause, AtLeastOneVars]
  | cons v vars ih =>
      have hv : 0 < v := hpos v (by simp)
      have hvars : ∀ w, w ∈ vars → 0 < w := by
        intro w hw
        exact hpos w (by simp [hw])
      have ih' := ih hvars
      simp [evalClause, evalLit_pos_of_pos τ hv, ih', AtLeastOneVars]

theorem evalCNF_exactlyOnePairwise_iff
    (τ : Assignment) (vars : List Nat)
    (hpos : ∀ v, v ∈ vars → 0 < v) :
    evalCNF τ (exactlyOnePairwise vars) ↔ ExactlyOneVars τ vars := by
  rw [exactlyOnePairwise, evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ vars hpos]
  simp [evalCNF]
  rw [evalClause_posList_iff τ vars hpos]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

theorem AtMostOneVars.unique
    {τ : Assignment} {vars : List Nat} (h : AtMostOneVars τ vars)
    {x y : Nat} (hx : x ∈ vars) (hy : y ∈ vars) (hτx : τ x) (hτy : τ y) :
    x = y := by
  induction vars generalizing x y with
  | nil =>
      cases hx
  | cons head tail ih =>
      simp [AtMostOneVars] at h
      cases hx with
      | head =>
          cases hy with
          | head => rfl
          | tail _ hyTail =>
              exact False.elim (h.1 y hyTail hτx hτy)
      | tail _ hxTail =>
          cases hy with
          | head =>
              exact False.elim (h.1 x hxTail hτy hτx)
          | tail _ hyTail =>
              exact ih h.2 hxTail hyTail hτx hτy

theorem ExactlyOneVars.exists_true
    {τ : Assignment} {vars : List Nat} (h : ExactlyOneVars τ vars) :
    ∃ v, v ∈ vars ∧ τ v :=
  h.1

theorem ExactlyOneVars.unique
    {τ : Assignment} {vars : List Nat} (h : ExactlyOneVars τ vars)
    {x y : Nat} (hx : x ∈ vars) (hy : y ∈ vars) (hτx : τ x) (hτy : τ y) :
    x = y :=
  h.2.unique hx hy hτx hτy

theorem AtMostOneVars.map_of_unique
    {τ : Assignment} {xs : List Nat} {f : Nat → Nat} {r : Nat}
    (nodup : xs.Nodup)
    (huniq : ∀ x, x ∈ xs → τ (f x) → x = r)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    AtMostOneVars τ (xs.map f) := by
  induction xs with
  | nil =>
      simp [AtMostOneVars]
  | cons x xs ih =>
      rw [List.nodup_cons] at nodup
      change (∀ w, w ∈ xs.map f → ¬(τ (f x) ∧ τ w)) ∧
        AtMostOneVars τ (xs.map f)
      constructor
      · intro w hw hboth
        rcases List.mem_map.mp hw with ⟨y, hy, rfl⟩
        have hxmem : x ∈ x :: xs := by simp
        have hymem : y ∈ x :: xs := by simp [hy]
        have hxr : x = r := huniq x hxmem hboth.1
        have hyr : y = r := huniq y hymem hboth.2
        have hxy : x = y := hxr.trans hyr.symm
        exact nodup.1 (by simpa [hxy] using hy)
      · apply ih
        · exact nodup.2
        · intro y hy hτ
          exact huniq y (by simp [hy]) hτ
        · intro y hy z hz hEq
          exact hinj y (by simp [hy]) z (by simp [hz]) hEq

theorem ExactlyOneVars.map_of_unique
    {τ : Assignment} {xs : List Nat} {f : Nat → Nat} {r : Nat}
    (nodup : xs.Nodup) (hr : r ∈ xs) (htrue : τ (f r))
    (huniq : ∀ x, x ∈ xs → τ (f x) → x = r)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    ExactlyOneVars τ (xs.map f) := by
  constructor
  · exact ⟨f r, List.mem_map.mpr ⟨r, hr, rfl⟩, htrue⟩
  · exact AtMostOneVars.map_of_unique nodup huniq hinj

theorem addVar_pos (n i j k : Nat) : 0 < addVar n i j k := by
  simp [addVar]

theorem mulVar_pos (n i j k : Nat) : 0 < mulVar n i j k := by
  simp [mulVar]

theorem expVar_pos (n i j k : Nat) : 0 < expVar n i j k := by
  simp [expVar]

theorem add2Var_pos (n i j k l : Nat) : 0 < add2Var n i j k l := by
  simp [add2Var]

theorem mul2Var_pos (n i j k l : Nat) : 0 < mul2Var n i j k l := by
  simp [mul2Var]

theorem distVar_pos (n x y z l : Nat) : 0 < distVar n x y z l := by
  simp [distVar]

theorem expAddVar_pos (n x y z l : Nat) : 0 < expAddVar n x y z l := by
  simp [expAddVar]

theorem expMulVar_pos (n x y z l : Nat) : 0 < expMulVar n x y z l := by
  simp [expMulVar]

theorem exp2Var_pos (n x y z l : Nat) : 0 < exp2Var n x y z l := by
  simp [exp2Var]

theorem termVar_pos (n termIndex value : Nat) : 0 < termVar n termIndex value := by
  simp [termVar]

theorem opVar_pos (n : Nat) (op : Op) (i j k : Nat) :
    0 < opVar n op i j k := by
  cases op <;> simp [opVar, addVar_pos, mulVar_pos, expVar_pos]

theorem symIndex_comm (n i j : Nat) :
    symIndex n i j = symIndex n j i := by
  simp [symIndex, Nat.min_comm, Nat.max_comm]

theorem addVar_comm (n i j k : Nat) :
    addVar n i j k = addVar n j i k := by
  simp [addVar, symIndex_comm]

theorem mulVar_comm (n i j k : Nat) :
    mulVar n i j k = mulVar n j i k := by
  simp [mulVar, symIndex_comm]

theorem addVar_canon (n i j k : Nat) :
    addVar n (min i j) (max i j) k = addVar n i j k := by
  by_cases hij : i ≤ j
  · simp [Nat.min_eq_left hij, Nat.max_eq_right hij]
  · have hji : j ≤ i := Nat.le_of_not_ge hij
    simp [Nat.min_eq_right hji, Nat.max_eq_left hji, addVar_comm]

theorem mulVar_canon (n i j k : Nat) :
    mulVar n (min i j) (max i j) k = mulVar n i j k := by
  by_cases hij : i ≤ j
  · simp [Nat.min_eq_left hij, Nat.max_eq_right hij]
  · have hji : j ≤ i := Nat.le_of_not_ge hij
    simp [Nat.min_eq_right hji, Nat.max_eq_left hji, mulVar_comm]

theorem mapped_values_pos
    {n : Nat} {f : Nat → Nat} (hf : ∀ k, 0 < f k) :
    ∀ v, v ∈ (values n).map f → 0 < v := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨k, _hk, rfl⟩
  exact hf k

theorem mem_flatMap_iff {α β : Type} {x : β} :
    ∀ (xs : List α) (f : α → List β),
      x ∈ flatMap xs f ↔ ∃ a, a ∈ xs ∧ x ∈ f a
  | [], _ => by
      simp [flatMap]
  | a :: xs, f => by
      rw [flatMap]
      rw [List.mem_append]
      rw [mem_flatMap_iff xs f]
      constructor
      · intro h
        cases h with
        | inl hfa => exact ⟨a, by simp, hfa⟩
        | inr hrest =>
            rcases hrest with ⟨b, hbxs, hfb⟩
            exact ⟨b, by simp [hbxs], hfb⟩
      · intro h
        rcases h with ⟨b, hb, hfb⟩
        cases hb with
        | head => exact Or.inl hfb
        | tail _ hbxs => exact Or.inr ⟨b, hbxs, hfb⟩

theorem mem_values_iff {n x : Nat} :
    x ∈ values n ↔ 1 ≤ x ∧ x ≤ n := by
  unfold values
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    have hi_lt : i < n := List.mem_range.mp hi
    omega
  · intro h
    rcases h with ⟨hlo, hhi⟩
    apply List.mem_map.mpr
    refine ⟨x - 1, ?_, ?_⟩
    · apply List.mem_range.mpr
      omega
    · omega

theorem values_nodup (n : Nat) : (values n).Nodup := by
  unfold values
  exact List.Pairwise.map (R := fun a b : Nat => a ≠ b) (S := fun a b : Nat => a ≠ b)
    (fun i => i + 1)
    (by
      intro a b hne heq
      exact hne (Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using heq)))
    List.nodup_range

theorem indexOf_lt_length_of_mem
    {α : Type} [DecidableEq α] {needle : α} :
    ∀ {xs : List α}, needle ∈ xs → indexOf needle xs < xs.length
  | [], h => by cases h
  | x :: xs, h => by
      by_cases hneedle : needle = x
      · simp [indexOf, hneedle]
      · have htail : needle ∈ xs := by
          cases h with
          | head => exact False.elim (hneedle rfl)
          | tail _ hmem => exact hmem
        have ih := indexOf_lt_length_of_mem (needle := needle) htail
        simpa [indexOf, hneedle] using ih

theorem indexOf_eq_of_mem
    {α : Type} [DecidableEq α] {needle x : α} :
    ∀ {xs : List α}, needle ∈ xs → x ∈ xs →
      indexOf needle xs = indexOf x xs → needle = x
  | [], hneedle, _, _ => by cases hneedle
  | y :: ys, hneedle, hx, hidx => by
      by_cases hny : needle = y
      · by_cases hxy : x = y
        · exact hny.trans hxy.symm
        · have hxTail : x ∈ ys := by
            cases hx with
            | head => exact False.elim (hxy rfl)
            | tail _ hmem => exact hmem
          simp [indexOf, hny, hxy] at hidx
      · have hneedleTail : needle ∈ ys := by
          cases hneedle with
          | head => exact False.elim (hny rfl)
          | tail _ hmem => exact hmem
        by_cases hxy : x = y
        · simp [indexOf, hny, hxy] at hidx
        · have hxTail : x ∈ ys := by
            cases hx with
            | head => exact False.elim (hxy rfl)
            | tail _ hmem => exact hmem
          have htailIdx : indexOf needle ys = indexOf x ys := by
            have hsucc : indexOf needle ys + 1 = indexOf x ys + 1 := by
              simpa [indexOf, hny, hxy] using hidx
            omega
          exact indexOf_eq_of_mem hneedleTail hxTail htailIdx

theorem valuePred_lt {n k : Nat} (hk : k ∈ values n) :
    k - 1 < n := by
  rw [mem_values_iff] at hk
  omega

theorem linearIndex_lt_mul
    {a A n k : Nat} (ha : a < A) (hk : k ∈ values n) :
    a * n + (k - 1) < A * n := by
  have hklt : k - 1 < n := valuePred_lt hk
  have hstep : a * n + (k - 1) < a * n + n :=
    Nat.add_lt_add_left hklt (a * n)
  have hstep' : a * n + (k - 1) < (a + 1) * n := by
    simpa [Nat.add_mul, Nat.one_mul] using hstep
  have ha' : a + 1 ≤ A := Nat.succ_le_of_lt ha
  exact Nat.lt_of_lt_of_le hstep' (Nat.mul_le_mul_right n ha')

theorem linearIndex_succ_le_mul
    {a A n k : Nat} (ha : a < A) (hk : k ∈ values n) :
    a * n + (k - 1) + 1 ≤ A * n := by
  exact Nat.succ_le_of_lt (linearIndex_lt_mul ha hk)

theorem linearIndex2_lt_mul_mul
    {a A n k l : Nat} (ha : a < A) (hk : k ∈ values n) (hl : l ∈ values n) :
    (a * n + (k - 1)) * n + (l - 1) < A * n * n := by
  have hfirst : a * n + (k - 1) < A * n := linearIndex_lt_mul ha hk
  have h := linearIndex_lt_mul (a := a * n + (k - 1)) (A := A * n) hfirst hl
  simpa [Nat.mul_assoc] using h

theorem linearIndex2_succ_le_mul_mul
    {a A n k l : Nat} (ha : a < A) (hk : k ∈ values n) (hl : l ∈ values n) :
    (a * n + (k - 1)) * n + (l - 1) + 1 ≤ A * n * n := by
  exact Nat.succ_le_of_lt (linearIndex2_lt_mul_mul ha hk hl)

theorem linearIndex_succ_inj
    {a b n k l : Nat} (hk : k ∈ values n) (hl : l ∈ values n)
    (h : a * n + (k - 1) + 1 = b * n + (l - 1) + 1) :
    a = b ∧ k = l := by
  have h0 : a * n + (k - 1) = b * n + (l - 1) := by
    omega
  by_cases hab : a = b
  · subst b
    have hDigit : k - 1 = l - 1 := Nat.add_left_cancel h0
    rw [mem_values_iff] at hk hl
    exact ⟨rfl, by omega⟩
  · cases Nat.lt_or_gt_of_ne hab with
    | inl halt =>
        have hklt : k - 1 < n := valuePred_lt hk
        have hleft : a * n + (k - 1) < (a + 1) * n := by
          simpa [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left hklt (a * n)
        have hsucc : a + 1 ≤ b := Nat.succ_le_of_lt halt
        have hmul : (a + 1) * n ≤ b * n := Nat.mul_le_mul_right n hsucc
        have hright : b * n ≤ b * n + (l - 1) := Nat.le_add_right _ _
        have hlt : a * n + (k - 1) < b * n + (l - 1) :=
          Nat.lt_of_lt_of_le hleft (Nat.le_trans hmul hright)
        rw [h0] at hlt
        exact False.elim (Nat.lt_irrefl _ hlt)
    | inr hbgt =>
        have hllt : l - 1 < n := valuePred_lt hl
        have hright : b * n + (l - 1) < (b + 1) * n := by
          simpa [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left hllt (b * n)
        have hsucc : b + 1 ≤ a := Nat.succ_le_of_lt hbgt
        have hmul : (b + 1) * n ≤ a * n := Nat.mul_le_mul_right n hsucc
        have hleft : a * n ≤ a * n + (k - 1) := Nat.le_add_right _ _
        have hlt : b * n + (l - 1) < a * n + (k - 1) :=
          Nat.lt_of_lt_of_le hright (Nat.le_trans hmul hleft)
        rw [← h0] at hlt
        exact False.elim (Nat.lt_irrefl _ hlt)

theorem linearIndex_inj
    {a b n k l : Nat} (hk : k ∈ values n) (hl : l ∈ values n)
    (h : a * n + (k - 1) = b * n + (l - 1)) :
    a = b ∧ k = l := by
  exact linearIndex_succ_inj hk hl (by omega)

theorem succ_mem_values_of_lt {n d : Nat} (hd : d < n) :
    d + 1 ∈ values n := by
  rw [mem_values_iff]
  omega

theorem linearIndex0_lt_mul
    {a A base d : Nat} (ha : a < A) (hd : d < base) :
    a * base + d < A * base := by
  have h := linearIndex_lt_mul (n := base) ha (succ_mem_values_of_lt hd)
  simpa using h

theorem linearIndex0_inj
    {a b base d e : Nat} (hd : d < base) (he : e < base)
    (h : a * base + d = b * base + e) :
    a = b ∧ d = e := by
  have hdv : d + 1 ∈ values base := succ_mem_values_of_lt hd
  have hev : e + 1 ∈ values base := succ_mem_values_of_lt he
  have hlin : a * base + ((d + 1) - 1) = b * base + ((e + 1) - 1) := by
    simpa using h
  have hsplit := linearIndex_inj hdv hev hlin
  exact ⟨hsplit.1, by omega⟩

theorem addVar_inj_value {n i j k l : Nat}
    (hk : k ∈ values n) (hl : l ∈ values n)
    (h : addVar n i j k = addVar n i j l) :
    k = l := by
  rw [mem_values_iff] at hk hl
  unfold addVar at h
  omega

theorem mulVar_inj_value {n i j k l : Nat}
    (hk : k ∈ values n) (hl : l ∈ values n)
    (h : mulVar n i j k = mulVar n i j l) :
    k = l := by
  rw [mem_values_iff] at hk hl
  unfold mulVar at h
  omega

theorem expVar_inj_value {n i j k l : Nat}
    (hk : k ∈ values n) (hl : l ∈ values n)
    (h : expVar n i j k = expVar n i j l) :
    k = l := by
  rw [mem_values_iff] at hk hl
  unfold expVar at h
  omega

theorem add2Var_inj_value {n i j k l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : add2Var n i j k l = add2Var n i j k r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold add2Var at h
  omega

theorem mul2Var_inj_value {n i j k l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : mul2Var n i j k l = mul2Var n i j k r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold mul2Var at h
  omega

theorem distVar_inj_value {n x y z l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : distVar n x y z l = distVar n x y z r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold distVar at h
  omega

theorem expAddVar_inj_value {n x y z l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : expAddVar n x y z l = expAddVar n x y z r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold expAddVar at h
  omega

theorem expMulVar_inj_value {n x y z l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : expMulVar n x y z l = expMulVar n x y z r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold expMulVar at h
  omega

theorem exp2Var_inj_value {n x y z l r : Nat}
    (hl : l ∈ values n) (hr : r ∈ values n)
    (h : exp2Var n x y z l = exp2Var n x y z r) :
    l = r := by
  rw [mem_values_iff] at hl hr
  unfold exp2Var at h
  omega

theorem termVar_inj_value {n termIndex k l : Nat}
    (hk : k ∈ values n) (hl : l ∈ values n)
    (h : termVar n termIndex k = termVar n termIndex l) :
    k = l := by
  rw [mem_values_iff] at hk hl
  unfold termVar at h
  omega

theorem exists_value_of_exact_mapped
    {n : Nat} {τ : Assignment} {f : Nat → Nat}
    (h : ExactlyOneVars τ ((values n).map f)) :
    ∃ k, k ∈ values n ∧ τ (f k) := by
  rcases h.exists_true with ⟨v, hv, hτv⟩
  rcases List.mem_map.mp hv with ⟨k, hk, rfl⟩
  exact ⟨k, hk, hτv⟩

noncomputable def selectValue (n : Nat) (τ : Assignment) (f : Nat → Nat) : Nat := by
  classical
  exact if h : ∃ k, k ∈ values n ∧ τ (f k) then Classical.choose h else 1

theorem selectValue_spec
    {n : Nat} {τ : Assignment} {f : Nat → Nat}
    (h : ∃ k, k ∈ values n ∧ τ (f k)) :
    selectValue n τ f ∈ values n ∧ τ (f (selectValue n τ f)) := by
  classical
  unfold selectValue
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem selectValue_eq_iff
    {n : Nat} {τ : Assignment} {f : Nat → Nat}
    (hexact : ExactlyOneVars τ ((values n).map f))
    (hinj : ∀ {a b}, a ∈ values n → b ∈ values n → f a = f b → a = b)
    {k : Nat} (hk : k ∈ values n) :
    selectValue n τ f = k ↔ τ (f k) := by
  let hExists := exists_value_of_exact_mapped hexact
  have hspec := selectValue_spec (n := n) (τ := τ) (f := f) hExists
  constructor
  · intro hsel
    simpa [hsel] using hspec.2
  · intro hτk
    have hVarEq : f (selectValue n τ f) = f k := by
      exact hexact.unique
        (List.mem_map.mpr ⟨selectValue n τ f, hspec.1, rfl⟩)
        (List.mem_map.mpr ⟨k, hk, rfl⟩)
        hspec.2 hτk
    exact hinj hspec.1 hk hVarEq

theorem mem_rangeFromTo_iff {lo hi x : Nat} (hlohi : lo ≤ hi) :
    x ∈ rangeFromTo lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  unfold rangeFromTo
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
    have hd_lt : d < hi + 1 - lo := List.mem_range.mp hd
    omega
  · intro h
    rcases h with ⟨hlox, hxhi⟩
    apply List.mem_map.mpr
    refine ⟨x - lo, ?_, ?_⟩
    · apply List.mem_range.mpr
      omega
    · omega

theorem mem_product2_iff {xs ys : List Nat} {p : Nat × Nat} :
    p ∈ product2 xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  unfold product2
  rw [mem_flatMap_iff]
  constructor
  · intro h
    rcases h with ⟨x, hx, hp⟩
    rcases List.mem_map.mp hp with ⟨y, hy, rfl⟩
    exact ⟨hx, hy⟩
  · intro h
    rcases p with ⟨x, y⟩
    exact ⟨x, h.1, List.mem_map.mpr ⟨y, h.2, rfl⟩⟩

theorem mem_product3_iff {xs ys zs : List Nat} {p : Nat × Nat × Nat} :
    p ∈ product3 xs ys zs ↔ p.1 ∈ xs ∧ p.2.1 ∈ ys ∧ p.2.2 ∈ zs := by
  unfold product3
  rw [mem_flatMap_iff]
  constructor
  · intro h
    rcases h with ⟨x, hx, hrest⟩
    rw [mem_flatMap_iff] at hrest
    rcases hrest with ⟨y, hy, hp⟩
    rcases List.mem_map.mp hp with ⟨z, hz, rfl⟩
    exact ⟨hx, hy, hz⟩
  · intro h
    rcases p with ⟨x, y, z⟩
    refine ⟨x, h.1, ?_⟩
    rw [mem_flatMap_iff]
    exact ⟨y, h.2.1, List.mem_map.mpr ⟨z, h.2.2, rfl⟩⟩

theorem mem_product4_iff {xs ys zs ws : List Nat} {p : Nat × Nat × Nat × Nat} :
    p ∈ product4 xs ys zs ws ↔
      p.1 ∈ xs ∧ p.2.1 ∈ ys ∧ p.2.2.1 ∈ zs ∧ p.2.2.2 ∈ ws := by
  unfold product4
  rw [mem_flatMap_iff]
  constructor
  · intro h
    rcases h with ⟨x, hx, hrest1⟩
    rw [mem_flatMap_iff] at hrest1
    rcases hrest1 with ⟨y, hy, hrest2⟩
    rw [mem_flatMap_iff] at hrest2
    rcases hrest2 with ⟨z, hz, hp⟩
    rcases List.mem_map.mp hp with ⟨w, hw, hpair⟩
    cases hpair
    exact ⟨hx, hy, hz, hw⟩
  · intro h
    rcases p with ⟨x, y, z, w⟩
    refine ⟨x, h.1, ?_⟩
    rw [mem_flatMap_iff]
    refine ⟨y, h.2.1, ?_⟩
    rw [mem_flatMap_iff]
    exact ⟨z, h.2.2.1, List.mem_map.mpr ⟨w, h.2.2.2, rfl⟩⟩

def OperationTotalitySemantics (n : Nat) (τ : Assignment) : Prop :=
  (∀ p, p ∈ symPairs n →
    ExactlyOneVars τ ((values n).map (fun k => addVar n p.1 p.2 k))) ∧
  (∀ p, p ∈ symPairs n →
    ExactlyOneVars τ ((values n).map (fun k => mulVar n p.1 p.2 k))) ∧
  (∀ p, p ∈ product2 (values n) (values n) →
    ExactlyOneVars τ ((values n).map (fun k => expVar n p.1 p.2 k)))

theorem totalityClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (totalityClauses n) ↔ OperationTotalitySemantics n τ := by
  unfold totalityClauses OperationTotalitySemantics
  rw [evalCNF_append]
  rw [evalCNF_append]
  rw [evalCNF_flatMap]
  rw [evalCNF_flatMap]
  rw [evalCNF_flatMap]
  constructor
  · intro h
    constructor
    · intro p hp
      exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (addVar_pos n p.1 p.2))).1
        (h.1.1 p hp)
    · constructor
      · intro p hp
        exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (mulVar_pos n p.1 p.2))).1
          (h.1.2 p hp)
      · intro p hp
        exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (expVar_pos n p.1 p.2))).1
          (h.2 p hp)
  · intro h
    constructor
    · constructor
      · intro p hp
        exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (addVar_pos n p.1 p.2))).2
          (h.1 p hp)
      · intro p hp
        exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (mulVar_pos n p.1 p.2))).2
          (h.2.1 p hp)
    · intro p hp
      exact (evalCNF_exactlyOnePairwise_iff τ _ (mapped_values_pos (expVar_pos n p.1 p.2))).2
        (h.2.2 p hp)

theorem evalCNF_posUnitClauses_iff
    {α : Type} (τ : Assignment) (xs : List α) (f : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < f x) :
    evalCNF τ (xs.map (fun x => [pos (f x)])) ↔ ∀ x, x ∈ xs → τ (f x) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos : 0 < f x := hpos x (by simp)
      have hxs : ∀ y, y ∈ xs → 0 < f y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF, evalClause, evalLit_pos_of_pos τ hxpos, ih hxs]

theorem evalCNF_negUnitClauses_iff
    {α : Type} (τ : Assignment) (xs : List α) (f : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < f x) :
    evalCNF τ (xs.map (fun x => [neg (f x)])) ↔ ∀ x, x ∈ xs → ¬τ (f x) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos : 0 < f x := hpos x (by simp)
      have hxs : ∀ y, y ∈ xs → 0 < f y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF, evalClause, evalLit_neg_of_pos τ hxpos, ih hxs]

theorem evalClause_imp2_iff
    (τ : Assignment) {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    evalClause τ [neg a, neg b, pos c] ↔ (τ a → τ b → τ c) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_neg_of_pos τ hb,
    evalLit_pos_of_pos τ hc]
  constructor
  · intro h hτa hτb
    cases h with
    | inl hna => exact False.elim (hna hτa)
    | inr hbc =>
        cases hbc with
        | inl hnb => exact False.elim (hnb hτb)
        | inr hτc => exact hτc
  · intro h
    by_cases hτa : τ a
    · by_cases hτb : τ b
      · right
        right
        exact h hτa hτb
      · right
        left
        exact hτb
    · left
      exact hτa

theorem evalClause_imp1_iff
    (τ : Assignment) {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) :
    evalClause τ [neg a, pos b] ↔ (τ a → τ b) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_pos_of_pos τ hb]
  constructor
  · intro h hτa
    cases h with
    | inl hna => exact False.elim (hna hτa)
    | inr hτb => exact hτb
  · intro h
    by_cases hτa : τ a
    · right
      exact h hτa
    · left
      exact hτa

theorem evalClause_imp3_iff
    (τ : Assignment) {a b c d : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    evalClause τ [neg a, neg b, neg c, pos d] ↔ (τ a → τ b → τ c → τ d) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_neg_of_pos τ hb,
    evalLit_neg_of_pos τ hc, evalLit_pos_of_pos τ hd]
  constructor
  · intro h hτa hτb hτc
    cases h with
    | inl hna => exact False.elim (hna hτa)
    | inr hbcd =>
        cases hbcd with
        | inl hnb => exact False.elim (hnb hτb)
        | inr hcd =>
            cases hcd with
            | inl hnc => exact False.elim (hnc hτc)
            | inr hτd => exact hτd
  · intro h
    by_cases hτa : τ a
    · by_cases hτb : τ b
      · by_cases hτc : τ c
        · right
          right
          right
          exact h hτa hτb hτc
        · right
          right
          left
          exact hτc
      · right
        left
        exact hτb
    · left
      exact hτa

theorem evalClause_neg_pos_pos_iff
    (τ : Assignment) {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    evalClause τ [neg a, pos b, pos c] ↔ (τ a → ¬τ b → τ c) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_pos_of_pos τ hb,
    evalLit_pos_of_pos τ hc]
  constructor
  · intro h hτa hnτb
    cases h with
    | inl hna => exact False.elim (hna hτa)
    | inr hbc =>
        cases hbc with
        | inl hτb => exact False.elim (hnτb hτb)
        | inr hτc => exact hτc
  · intro h
    by_cases hτa : τ a
    · by_cases hτb : τ b
      · right
        left
        exact hτb
      · right
        right
        exact h hτa hτb
    · left
      exact hτa

def AssignmentLexLE (τ : Assignment) : List (Nat × Nat) → Prop
  | [] => True
  | (a, b) :: rest =>
      (¬τ a ∧ τ b) ∨ ((τ a ↔ τ b) ∧ AssignmentLexLE τ rest)

theorem AssignmentLexLE_congr
    {τ σ : Assignment} :
    ∀ {pairs : List (Nat × Nat)},
      (∀ p, p ∈ pairs → (τ p.1 ↔ σ p.1) ∧ (τ p.2 ↔ σ p.2)) →
        (AssignmentLexLE τ pairs ↔ AssignmentLexLE σ pairs)
  | [], _ => by simp [AssignmentLexLE]
  | p :: ps, h => by
      have hp := h p (by simp)
      have hps : ∀ q, q ∈ ps → (τ q.1 ↔ σ q.1) ∧ (τ q.2 ↔ σ q.2) := by
        intro q hq
        exact h q (by simp [hq])
      have ih := AssignmentLexLE_congr (pairs := ps) hps
      cases p with
      | mk a b =>
          simp [AssignmentLexLE, hp.1, hp.2, ih]

theorem lexStepClauses_correct
    (τ : Assignment) {aux a b next : Nat}
    (haux : 0 < aux) (ha : 0 < a) (hb : 0 < b) (hnext : 0 < next) :
    evalCNF τ (lexStepClauses aux a b next) ↔
      (τ aux → τ a → τ b) ∧
      (τ aux → τ a → τ next) ∧
      (τ aux → ¬τ b → τ next) := by
  unfold lexStepClauses
  simp [evalCNF,
    evalClause_imp2_iff τ haux ha hb,
    evalClause_imp2_iff τ haux ha hnext,
    evalClause_neg_pos_pos_iff τ haux hb hnext]

theorem lexSmallerEqAuxCount_pos (pairs : List (Nat × Nat)) :
    0 < lexSmallerEqAuxCount pairs := by
  unfold lexSmallerEqAuxCount
  omega

def PairVarsPositive (pairs : List (Nat × Nat)) : Prop :=
  ∀ p, p ∈ pairs → 0 < p.1 ∧ 0 < p.2

def PairVarsBelow (pairs : List (Nat × Nat)) (bound : Nat) : Prop :=
  ∀ p, p ∈ pairs → p.1 < bound ∧ p.2 < bound

theorem pairVarsPositive_tail
    {p : Nat × Nat} {ps : List (Nat × Nat)}
    (h : PairVarsPositive (p :: ps)) :
    PairVarsPositive ps := by
  intro q hq
  exact h q (by simp [hq])

theorem pairVarsBelow_tail
    {p : Nat × Nat} {ps : List (Nat × Nat)} {bound : Nat}
    (h : PairVarsBelow (p :: ps) bound) :
    PairVarsBelow ps bound := by
  intro q hq
  exact h q (by simp [hq])

theorem pairVarsBelow_mono
    {ps : List (Nat × Nat)} {a b : Nat}
    (h : PairVarsBelow ps a) (hle : a ≤ b) :
    PairVarsBelow ps b := by
  intro q hq
  have hq' := h q hq
  exact ⟨Nat.lt_of_lt_of_le hq'.1 hle, Nat.lt_of_lt_of_le hq'.2 hle⟩

theorem CNFBelow_append {left right : CNF} {bound : Nat} :
    CNFBelow (left ++ right) bound ↔ CNFBelow left bound ∧ CNFBelow right bound := by
  unfold CNFBelow
  constructor
  · intro h
    constructor
    · intro clause hc lit hlit
      exact h clause (by simp [hc]) lit hlit
    · intro clause hc lit hlit
      exact h clause (by simp [hc]) lit hlit
  · intro h clause hc lit hlit
    rw [List.mem_append] at hc
    cases hc with
    | inl hleft => exact h.1 clause hleft lit hlit
    | inr hright => exact h.2 clause hright lit hlit

theorem CNFBelow_map
    {α : Type} {xs : List α} {f : α → Clause} {bound : Nat}
    (h : ∀ x, x ∈ xs → ∀ lit, lit ∈ f x → litVar lit < bound) :
    CNFBelow (xs.map f) bound := by
  intro clause hclause lit hlit
  rcases List.mem_map.mp hclause with ⟨x, hx, rfl⟩
  exact h x hx lit hlit

theorem CNFBelow_flatMap
    {α : Type} {xs : List α} {f : α → CNF} {bound : Nat}
    (h : ∀ x, x ∈ xs → CNFBelow (f x) bound) :
    CNFBelow (flatMap xs f) bound := by
  intro clause hclause lit hlit
  rw [mem_flatMap_iff] at hclause
  rcases hclause with ⟨x, hx, hclause⟩
  exact h x hx clause hclause lit hlit

theorem CNFBelow_atMostOnePairwise
    {vars : List Nat} {bound : Nat}
    (hvars : ∀ v, v ∈ vars → v < bound) :
    CNFBelow (atMostOnePairwise vars) bound := by
  induction vars with
  | nil =>
      simp [atMostOnePairwise, CNFBelow]
  | cons v vars ih =>
      rw [atMostOnePairwise, CNFBelow_append]
      constructor
      · apply CNFBelow_map
        intro w hw lit hlit
        simp at hlit
        rcases hlit with rfl | rfl
        · exact litVar_neg_lt_of (hvars v (by simp))
        · exact litVar_neg_lt_of (hvars w (by simp [hw]))
      · apply ih
        intro w hw
        exact hvars w (by simp [hw])

theorem CNFBelow_exactlyOnePairwise
    {vars : List Nat} {bound : Nat}
    (hvars : ∀ v, v ∈ vars → v < bound) :
    CNFBelow (exactlyOnePairwise vars) bound := by
  rw [exactlyOnePairwise, CNFBelow_append]
  constructor
  · exact CNFBelow_atMostOnePairwise hvars
  · intro clause hclause lit hlit
    simp at hclause
    subst clause
    rcases List.mem_map.mp hlit with ⟨v, hv, rfl⟩
    exact litVar_pos_lt_of (hvars v hv)

theorem lexStepClauses_below
    {aux a b next bound : Nat}
    (haux : aux < bound) (ha : a < bound) (hb : b < bound)
    (hnext : next < bound) :
    CNFBelow (lexStepClauses aux a b next) bound := by
  intro clause hclause lit hlit
  simp [lexStepClauses] at hclause
  rcases hclause with rfl | rfl | rfl
  · simp at hlit
    rcases hlit with rfl | rfl | rfl
    · simpa [litVar_neg] using haux
    · simpa [litVar_neg] using ha
    · simpa [litVar_pos] using hb
  · simp at hlit
    rcases hlit with rfl | rfl | rfl
    · simpa [litVar_neg] using haux
    · simpa [litVar_neg] using ha
    · simpa [litVar_pos] using hnext
  · simp at hlit
    rcases hlit with rfl | rfl | rfl
    · simpa [litVar_neg] using haux
    · simpa [litVar_pos] using hb
    · simpa [litVar_pos] using hnext

theorem lexCompareClausesFrom_below
    {aux : Nat} :
    ∀ {pairs : List (Nat × Nat)},
      PairVarsBelow pairs aux →
        CNFBelow (lexCompareClausesFrom aux pairs)
          (aux + lexSmallerEqAuxCount pairs)
  | [], _ => by
      intro clause hclause
      cases hclause
  | (a, b) :: rest, hbelow => by
      by_cases hab : a = b
      · have htail := lexCompareClausesFrom_below
          (aux := aux) (pairs := rest) (pairVarsBelow_tail hbelow)
        simpa [lexCompareClausesFrom, lexSmallerEqAuxCount,
          lexCompareAuxCount, hab] using htail
      · have hp := hbelow (a, b) (by simp)
        have hrestBelow : PairVarsBelow rest (aux + 1) :=
          pairVarsBelow_mono (pairVarsBelow_tail hbelow) (by omega)
        have htail := lexCompareClausesFrom_below
          (aux := aux + 1) (pairs := rest) hrestBelow
        have hstep :
            CNFBelow (lexStepClauses aux a b (aux + 1))
              (aux + lexSmallerEqAuxCount ((a, b) :: rest)) := by
          apply lexStepClauses_below
          · unfold lexSmallerEqAuxCount lexCompareAuxCount
            simp [hab]
          · unfold lexSmallerEqAuxCount lexCompareAuxCount
            simp [hab]
            omega
          · unfold lexSmallerEqAuxCount lexCompareAuxCount
            simp [hab]
            omega
          · unfold lexSmallerEqAuxCount lexCompareAuxCount
            simp [hab]
        rw [lexCompareClausesFrom, if_neg hab, CNFBelow_append]
        constructor
        · exact hstep
        · simpa [lexSmallerEqAuxCount, lexCompareAuxCount, hab,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htail

theorem lexSmallerEqClausesFrom_below
    {aux : Nat} {pairs : List (Nat × Nat)}
    (hbelow : PairVarsBelow pairs aux) :
    CNFBelow (lexSmallerEqClausesFrom aux pairs)
      (aux + lexSmallerEqAuxCount pairs) := by
  unfold lexSmallerEqClausesFrom
  rw [CNFBelow_append]
  constructor
  · intro clause hclause lit hlit
    simp at hclause
    subst clause
    simp at hlit
    subst lit
    simp [litVar_pos]
    exact lexSmallerEqAuxCount_pos pairs
  · exact lexCompareClausesFrom_below hbelow

theorem lexCompareClauses_eval_of_auxes_false
    {τ : Assignment} :
    ∀ {aux : Nat} {pairs : List (Nat × Nat)},
      0 < aux →
      (∀ k, aux ≤ k → ¬τ k) →
        evalCNF τ (lexCompareClausesFrom aux pairs)
  | aux, [], _, _ => by
      exact trivial
  | aux, (a, b) :: rest, hauxPos, hfalse => by
      by_cases hab : a = b
      · simpa [lexCompareClausesFrom, hab] using
          lexCompareClauses_eval_of_auxes_false
            (aux := aux) (pairs := rest) hauxPos hfalse
      · have hauxFalse : ¬τ aux := hfalse aux (by omega)
        have hstep : evalCNF τ (lexStepClauses aux a b (aux + 1)) := by
          unfold lexStepClauses
          have hneg : evalLit τ (neg aux) :=
            (evalLit_neg_of_pos τ hauxPos).2 hauxFalse
          simp [evalCNF, evalClause, hneg]
        have htail : evalCNF τ (lexCompareClausesFrom (aux + 1) rest) :=
          lexCompareClauses_eval_of_auxes_false
            (aux := aux + 1) (pairs := rest) (by omega)
            (by
              intro k hk
              exact hfalse k (by omega))
        simp [lexCompareClausesFrom, hab, evalCNF_append, hstep, htail]

theorem lexCompareClauses_eval_implies_assignmentLexLE
    {τ : Assignment} :
    ∀ {aux : Nat} {pairs : List (Nat × Nat)},
      0 < aux → PairVarsPositive pairs →
      τ aux → evalCNF τ (lexCompareClausesFrom aux pairs) →
        AssignmentLexLE τ pairs
  | _, [], _, _, _, _ => by simp [AssignmentLexLE]
  | aux, (a, b) :: rest, hauxPos, hpos, hprev, hcnf => by
      by_cases hab : a = b
      · have htailCnf : evalCNF τ (lexCompareClausesFrom aux rest) := by
          simpa [lexCompareClausesFrom, hab] using hcnf
        have htailLex :=
          lexCompareClauses_eval_implies_assignmentLexLE
            (aux := aux) (pairs := rest) hauxPos
            (pairVarsPositive_tail hpos) hprev htailCnf
        subst b
        simp [AssignmentLexLE, htailLex]
      · have hp := hpos (a, b) (by simp)
        have hsplit : evalCNF τ (lexStepClauses aux a b (aux + 1)) ∧
            evalCNF τ (lexCompareClausesFrom (aux + 1) rest) := by
          simpa [lexCompareClausesFrom, hab, evalCNF_append] using hcnf
        have hstep := (lexStepClauses_correct τ hauxPos hp.1 hp.2 (by omega)).1 hsplit.1
        by_cases haTrue : τ a
        · by_cases hbTrue : τ b
          · have hnext : τ (aux + 1) := hstep.2.1 hprev haTrue
            have htailLex :=
              lexCompareClauses_eval_implies_assignmentLexLE
                (aux := aux + 1) (pairs := rest) (by omega)
                (pairVarsPositive_tail hpos) hnext hsplit.2
            exact Or.inr ⟨by constructor <;> intro _ <;> assumption, htailLex⟩
          · exact False.elim (hbTrue (hstep.1 hprev haTrue))
        · by_cases hbTrue : τ b
          · exact Or.inl ⟨haTrue, hbTrue⟩
          · have hnext : τ (aux + 1) := hstep.2.2 hprev hbTrue
            have htailLex :=
              lexCompareClauses_eval_implies_assignmentLexLE
                (aux := aux + 1) (pairs := rest) (by omega)
                (pairVarsPositive_tail hpos) hnext hsplit.2
            exact Or.inr ⟨by constructor <;> intro h <;> contradiction, htailLex⟩

theorem lexCompareClauses_satisfiable_of_assignmentLexLE
    {τ : Assignment} :
    ∀ {aux : Nat} {pairs : List (Nat × Nat)},
      0 < aux → PairVarsPositive pairs → PairVarsBelow pairs aux →
      AssignmentLexLE τ pairs →
        ∃ τ' : Assignment,
          (∀ v, v < aux → (τ' v ↔ τ v)) ∧
          τ' aux ∧ evalCNF τ' (lexCompareClausesFrom aux pairs)
  | aux, [], _, _, _, _ => by
      let τ' : Assignment := fun v => v = aux ∨ τ v
      refine ⟨τ', ?_, ?_, ?_⟩
      · intro v hv
        simp [τ']
        omega
      · simp [τ']
      · exact trivial
  | aux, (a, b) :: rest, hauxPos, hpos, hbelow, hlex => by
      by_cases hab : a = b
      · subst b
        have htailLex : AssignmentLexLE τ rest := by
          simpa [AssignmentLexLE] using hlex
        rcases lexCompareClauses_satisfiable_of_assignmentLexLE
            (aux := aux) (pairs := rest) hauxPos
            (pairVarsPositive_tail hpos) (pairVarsBelow_tail hbelow) htailLex with
          ⟨τ', hpreserve, haux, hcnf⟩
        exact ⟨τ', hpreserve, haux, by simpa [lexCompareClausesFrom] using hcnf⟩
      · rcases hlex with hstrict | heq
        · let τ' : Assignment := fun v =>
            if v = aux then True else if aux + 1 ≤ v then False else τ v
          have hpBelow := hbelow (a, b) (by simp)
          have haPreserve : τ' a ↔ τ a := by
            have hane : a ≠ aux := by omega
            simp [τ', hane]
            omega
          have hbPreserve : τ' b ↔ τ b := by
            have hbne : b ≠ aux := by omega
            simp [τ', hbne]
            omega
          have hstep : evalCNF τ' (lexStepClauses aux a b (aux + 1)) := by
            apply (lexStepClauses_correct τ' hauxPos
              (hpos (a, b) (by simp)).1 (hpos (a, b) (by simp)).2 (by omega)).2
            constructor
            · intro _ _
              exact hbPreserve.2 hstrict.2
            · constructor
              · intro _ ha
                exact False.elim (hstrict.1 (haPreserve.1 ha))
              · intro _ hb
                exact False.elim (hb (hbPreserve.2 hstrict.2))
          have htail : evalCNF τ' (lexCompareClausesFrom (aux + 1) rest) :=
            lexCompareClauses_eval_of_auxes_false
              (aux := aux + 1) (pairs := rest) (by omega)
              (by
                intro k hk
                have hkne : k ≠ aux := by omega
                simp [τ', hkne]
                intro hlt
                omega)
          refine ⟨τ', ?_, ?_, ?_⟩
          · intro v hv
            have hvne : v ≠ aux := by omega
            simp [τ', hvne]
            omega
          · simp [τ']
          · simp [lexCompareClausesFrom, hab, evalCNF_append, hstep, htail]
        · let τ0 : Assignment := fun v => if v = aux then True else τ v
          have htailBelow : PairVarsBelow rest (aux + 1) :=
            pairVarsBelow_mono (pairVarsBelow_tail hbelow) (by omega)
          have htailLex0 : AssignmentLexLE τ0 rest := by
            have hcongr : ∀ p, p ∈ rest → (τ p.1 ↔ τ0 p.1) ∧ (τ p.2 ↔ τ0 p.2) := by
              intro p hp
              have hpBelow := (pairVarsBelow_tail hbelow) p hp
              constructor
              · have hpne : p.1 ≠ aux := by omega
                simp [τ0, hpne]
              · have hpne : p.2 ≠ aux := by omega
                simp [τ0, hpne]
            exact (AssignmentLexLE_congr (τ := τ) (σ := τ0)
              (pairs := rest) hcongr).1 heq.2
          rcases lexCompareClauses_satisfiable_of_assignmentLexLE
              (aux := aux + 1) (pairs := rest) (by omega)
              (pairVarsPositive_tail hpos) htailBelow htailLex0 with
            ⟨τ', hpreserve, hnext, htail⟩
          have hpBelow := hbelow (a, b) (by simp)
          have haPreserve : τ' a ↔ τ a := by
            have hpa := hpreserve a (by omega)
            have hane : a ≠ aux := by omega
            simpa [τ0, hane] using hpa
          have hbPreserve : τ' b ↔ τ b := by
            have hpb := hpreserve b (by omega)
            have hbne : b ≠ aux := by omega
            simpa [τ0, hbne] using hpb
          have haux' : τ' aux := by
            have hpaux := hpreserve aux (by omega)
            exact hpaux.2 (by simp [τ0])
          have hstep : evalCNF τ' (lexStepClauses aux a b (aux + 1)) := by
            apply (lexStepClauses_correct τ' hauxPos
              (hpos (a, b) (by simp)).1 (hpos (a, b) (by simp)).2 (by omega)).2
            constructor
            · intro _ ha
              exact hbPreserve.2 ((heq.1).1 (haPreserve.1 ha))
            · constructor
              · intro _ _
                exact hnext
              · intro _ _
                exact hnext
          refine ⟨τ', ?_, haux', ?_⟩
          · intro v hv
            have hpv := hpreserve v (by omega)
            have hvne : v ≠ aux := by omega
            simpa [τ0, hvne] using hpv
          · simp [lexCompareClausesFrom, hab, evalCNF_append, hstep, htail]

theorem lexSmallerEqClausesFrom_implies_assignmentLexLE
    {τ : Assignment} {aux : Nat} {pairs : List (Nat × Nat)}
    (hauxPos : 0 < aux) (hpos : PairVarsPositive pairs)
    (h : evalCNF τ (lexSmallerEqClausesFrom aux pairs)) :
    AssignmentLexLE τ pairs := by
  unfold lexSmallerEqClausesFrom at h
  rw [evalCNF_append] at h
  have haux : τ aux := by
    simpa [evalCNF, evalClause, evalLit_pos_of_pos τ hauxPos] using h.1
  exact lexCompareClauses_eval_implies_assignmentLexLE
    (aux := aux) (pairs := pairs) hauxPos hpos haux h.2

theorem lexSmallerEqClausesFrom_satisfiable_iff_assignmentLexLE
    {τ : Assignment} {aux : Nat} {pairs : List (Nat × Nat)}
    (hauxPos : 0 < aux) (hpos : PairVarsPositive pairs)
    (hbelow : PairVarsBelow pairs aux) :
    (∃ τ' : Assignment,
      (∀ v, v < aux → (τ' v ↔ τ v)) ∧
      evalCNF τ' (lexSmallerEqClausesFrom aux pairs)) ↔
      AssignmentLexLE τ pairs := by
  constructor
  · intro h
    rcases h with ⟨τ', hpreserve, hcnf⟩
    have hlex' :=
      lexSmallerEqClausesFrom_implies_assignmentLexLE
        (τ := τ') hauxPos hpos hcnf
    have hcongr : ∀ p, p ∈ pairs → (τ' p.1 ↔ τ p.1) ∧ (τ' p.2 ↔ τ p.2) := by
      intro p hp
      have hpBelow := hbelow p hp
      exact ⟨hpreserve p.1 hpBelow.1, hpreserve p.2 hpBelow.2⟩
    exact (AssignmentLexLE_congr (τ := τ') (σ := τ)
      (pairs := pairs) hcongr).1 hlex'
  · intro hlex
    rcases lexCompareClauses_satisfiable_of_assignmentLexLE
        (aux := aux) (pairs := pairs) hauxPos hpos hbelow hlex with
      ⟨τ', hpreserve, haux, hcompare⟩
    refine ⟨τ', hpreserve, ?_⟩
    unfold lexSmallerEqClausesFrom
    rw [evalCNF_append]
    constructor
    · simpa [evalCNF, evalClause, evalLit_pos_of_pos τ' hauxPos] using haux
    · exact hcompare

theorem evalCNF_imp2Clauses_iff
    {α : Type} (τ : Assignment) (xs : List α)
    (a b c : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < a x ∧ 0 < b x ∧ 0 < c x) :
    evalCNF τ (xs.map (fun x => [neg (a x), neg (b x), pos (c x)])) ↔
      ∀ x, x ∈ xs → τ (a x) → τ (b x) → τ (c x) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos := hpos x (by simp)
      have hxspos : ∀ y, y ∈ xs → 0 < a y ∧ 0 < b y ∧ 0 < c y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF, evalClause_imp2_iff τ hxpos.1 hxpos.2.1 hxpos.2.2, ih hxspos]

theorem evalCNF_imp1Clauses_iff
    {α : Type} (τ : Assignment) (xs : List α)
    (a b : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < a x ∧ 0 < b x) :
    evalCNF τ (xs.map (fun x => [neg (a x), pos (b x)])) ↔
      ∀ x, x ∈ xs → τ (a x) → τ (b x) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos := hpos x (by simp)
      have hxspos : ∀ y, y ∈ xs → 0 < a y ∧ 0 < b y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF, evalClause_imp1_iff τ hxpos.1 hxpos.2, ih hxspos]

theorem evalCNF_imp3Clauses_iff
    {α : Type} (τ : Assignment) (xs : List α)
    (a b c d : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < a x ∧ 0 < b x ∧ 0 < c x ∧ 0 < d x) :
    evalCNF τ (xs.map (fun x => [neg (a x), neg (b x), neg (c x), pos (d x)])) ↔
      ∀ x, x ∈ xs → τ (a x) → τ (b x) → τ (c x) → τ (d x) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos := hpos x (by simp)
      have hxspos : ∀ y, y ∈ xs → 0 < a y ∧ 0 < b y ∧ 0 < c y ∧ 0 < d y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF,
        evalClause_imp3_iff τ hxpos.1 hxpos.2.1 hxpos.2.2.1 hxpos.2.2.2,
        ih hxspos]

theorem evalCNF_twoNegClauses_iff
    {α : Type} (τ : Assignment) (xs : List α)
    (a b : α → Nat)
    (hpos : ∀ x, x ∈ xs → 0 < a x ∧ 0 < b x) :
    evalCNF τ (xs.map (fun x => [neg (a x), neg (b x)])) ↔
      ∀ x, x ∈ xs → ¬(τ (a x) ∧ τ (b x)) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos := hpos x (by simp)
      have hxspos : ∀ y, y ∈ xs → 0 < a y ∧ 0 < b y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF, evalClause_two_neg_iff τ hxpos.1 hxpos.2, ih hxspos]

theorem evalClause_three_neg_iff
    (τ : Assignment) {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    evalClause τ [neg a, neg b, neg c] ↔ ¬(τ a ∧ τ b ∧ τ c) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_neg_of_pos τ hb,
    evalLit_neg_of_pos τ hc]
  constructor
  · intro h hτa hτb hτc
    cases h with
    | inl hna => exact hna hτa
    | inr hbc =>
        cases hbc with
        | inl hnb => exact hnb hτb
        | inr hnc => exact hnc hτc
  · intro h
    by_cases hτa : τ a
    · by_cases hτb : τ b
      · by_cases hτc : τ c
        · exact False.elim (h hτa hτb hτc)
        · right
          right
          exact hτc
      · right
        left
        exact hτb
    · left
      exact hτa

theorem evalClause_five_neg_iff
    (τ : Assignment) {a b c d e : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    evalClause τ [neg a, neg b, neg c, neg d, neg e] ↔
      ¬(τ a ∧ τ b ∧ τ c ∧ τ d ∧ τ e) := by
  simp [evalClause, evalLit_neg_of_pos τ ha, evalLit_neg_of_pos τ hb,
    evalLit_neg_of_pos τ hc, evalLit_neg_of_pos τ hd,
    evalLit_neg_of_pos τ he]
  constructor
  · intro h hτa hτb hτc hτd hτe
    cases h with
    | inl hna => exact hna hτa
    | inr hbcde =>
        cases hbcde with
        | inl hnb => exact hnb hτb
        | inr hcde =>
            cases hcde with
            | inl hnc => exact hnc hτc
            | inr hde =>
                cases hde with
                | inl hnd => exact hnd hτd
                | inr hne => exact hne hτe
  · intro h
    by_cases hτa : τ a
    · by_cases hτb : τ b
      · by_cases hτc : τ c
        · by_cases hτd : τ d
          · by_cases hτe : τ e
            · exact False.elim (h hτa hτb hτc hτd hτe)
            · right
              right
              right
              right
              exact hτe
          · right
            right
            right
            left
            exact hτd
        · right
          right
          left
          exact hτc
      · right
        left
        exact hτb
    · left
      exact hτa

theorem evalCNF_fiveNegClauses_iff
    {α : Type} (τ : Assignment) (xs : List α)
    (a b c d e : α → Nat)
    (hpos : ∀ x, x ∈ xs →
      0 < a x ∧ 0 < b x ∧ 0 < c x ∧ 0 < d x ∧ 0 < e x) :
    evalCNF τ (xs.map (fun x =>
      [neg (a x), neg (b x), neg (c x), neg (d x), neg (e x)])) ↔
      ∀ x, x ∈ xs →
        ¬(τ (a x) ∧ τ (b x) ∧ τ (c x) ∧ τ (d x) ∧ τ (e x)) := by
  induction xs with
  | nil =>
      simp [evalCNF]
  | cons x xs ih =>
      have hxpos := hpos x (by simp)
      have hxspos : ∀ y, y ∈ xs →
          0 < a y ∧ 0 < b y ∧ 0 < c y ∧ 0 < d y ∧ 0 < e y := by
        intro y hy
        exact hpos y (by simp [hy])
      simp [evalCNF,
        evalClause_five_neg_iff τ hxpos.1 hxpos.2.1 hxpos.2.2.1
          hxpos.2.2.2.1 hxpos.2.2.2.2,
        ih hxspos]

def UnitIdentitySemantics (n : Nat) (τ : Assignment) : Prop :=
  (∀ x, x ∈ values n → τ (mulVar n x 1 x)) ∧
  (∀ x, x ∈ values n → τ (expVar n 1 x 1)) ∧
  (∀ x, x ∈ values n → τ (expVar n x 1 x))

theorem unitIdentityClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (unitIdentityClauses n) ↔ UnitIdentitySemantics n τ := by
  unfold unitIdentityClauses UnitIdentitySemantics
  rw [evalCNF_append]
  rw [evalCNF_append]
  rw [evalCNF_posUnitClauses_iff τ (values n) (fun x => mulVar n x 1 x)
    (by intro x _; exact mulVar_pos n x 1 x)]
  rw [evalCNF_posUnitClauses_iff τ (values n) (fun x => expVar n 1 x 1)
    (by intro x _; exact expVar_pos n 1 x 1)]
  rw [evalCNF_posUnitClauses_iff τ (values n) (fun x => expVar n x 1 x)
    (by intro x _; exact expVar_pos n x 1 x)]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

def AddAssocInnerSemantics (n : Nat) (τ : Assignment) (i j k : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => add2Var n i j k l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    (τ (addVar n j k q.2) → τ (addVar n i q.2 q.1) → τ (add2Var n i j k q.1)) ∧
    (τ (addVar n i j q.2) → τ (addVar n q.2 k q.1) → τ (add2Var n i j k q.1)))

theorem addAssocInner_correct (n : Nat) (τ : Assignment) (i j k : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => add2Var n i j k l)) ++
        flatMap (product2 (values n) (values n)) (fun (l, m) => [
          [neg (addVar n j k m), neg (addVar n i m l), pos (add2Var n i j k l)],
          [neg (addVar n i j m), neg (addVar n m k l), pos (add2Var n i j k l)]
        ])) ↔
      AddAssocInnerSemantics n τ i j k := by
  unfold AddAssocInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (add2Var_pos n i j k))]
  rw [evalCNF_flatMap]
  constructor
  · intro h
    constructor
    · exact h.1
    · intro q hq
      have hqeval := h.2 q hq
      cases q with
      | mk l m =>
          simp [evalCNF,
            evalClause_imp2_iff τ (addVar_pos n j k m) (addVar_pos n i m l)
              (add2Var_pos n i j k l),
            evalClause_imp2_iff τ (addVar_pos n i j m) (addVar_pos n m k l)
              (add2Var_pos n i j k l)] at hqeval
          exact hqeval
  · intro h
    constructor
    · exact h.1
    · intro q hq
      cases q with
      | mk l m =>
          have hqsem := h.2 (l, m) hq
          simp [evalCNF,
            evalClause_imp2_iff τ (addVar_pos n j k m) (addVar_pos n i m l)
              (add2Var_pos n i j k l),
            evalClause_imp2_iff τ (addVar_pos n i j m) (addVar_pos n m k l)
              (add2Var_pos n i j k l)]
          exact hqsem

def AddAssocSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ p, p ∈ symPairs n →
    ∀ j, j ∈ values n → AddAssocInnerSemantics n τ p.1 j p.2

theorem addAssocClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (addAssocClauses n) ↔ AddAssocSemantics n τ := by
  unfold addAssocClauses AddAssocSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h p hp j hj
    have hp_eval := h p hp
    cases p with
    | mk i k =>
        rw [evalCNF_flatMap] at hp_eval
        exact (addAssocInner_correct n τ i j k).1 (hp_eval j hj)
  · intro h p hp
    cases p with
    | mk i k =>
        rw [evalCNF_flatMap]
        intro j hj
        exact (addAssocInner_correct n τ i j k).2 (h (i, k) hp j hj)

def MulAssocInnerSemantics (n : Nat) (τ : Assignment) (i j k : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => mul2Var n i j k l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    (τ (mulVar n j k q.2) → τ (mulVar n i q.2 q.1) → τ (mul2Var n i j k q.1)) ∧
    (τ (mulVar n i j q.2) → τ (mulVar n q.2 k q.1) → τ (mul2Var n i j k q.1)))

theorem mulAssocInner_correct (n : Nat) (τ : Assignment) (i j k : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => mul2Var n i j k l)) ++
        flatMap (product2 (values n) (values n)) (fun (l, m) => [
          [neg (mulVar n j k m), neg (mulVar n i m l), pos (mul2Var n i j k l)],
          [neg (mulVar n i j m), neg (mulVar n m k l), pos (mul2Var n i j k l)]
        ])) ↔
      MulAssocInnerSemantics n τ i j k := by
  unfold MulAssocInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (mul2Var_pos n i j k))]
  rw [evalCNF_flatMap]
  constructor
  · intro h
    constructor
    · exact h.1
    · intro q hq
      have hqeval := h.2 q hq
      cases q with
      | mk l m =>
          simp [evalCNF,
            evalClause_imp2_iff τ (mulVar_pos n j k m) (mulVar_pos n i m l)
              (mul2Var_pos n i j k l),
            evalClause_imp2_iff τ (mulVar_pos n i j m) (mulVar_pos n m k l)
              (mul2Var_pos n i j k l)] at hqeval
          exact hqeval
  · intro h
    constructor
    · exact h.1
    · intro q hq
      cases q with
      | mk l m =>
          have hqsem := h.2 (l, m) hq
          simp [evalCNF,
            evalClause_imp2_iff τ (mulVar_pos n j k m) (mulVar_pos n i m l)
              (mul2Var_pos n i j k l),
            evalClause_imp2_iff τ (mulVar_pos n i j m) (mulVar_pos n m k l)
              (mul2Var_pos n i j k l)]
          exact hqsem

def MulAssocSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ p, p ∈ symPairs n →
    ∀ j, j ∈ values n → MulAssocInnerSemantics n τ p.1 j p.2

theorem mulAssocClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (mulAssocClauses n) ↔ MulAssocSemantics n τ := by
  unfold mulAssocClauses MulAssocSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h p hp j hj
    have hp_eval := h p hp
    cases p with
    | mk i k =>
        rw [evalCNF_flatMap] at hp_eval
        exact (mulAssocInner_correct n τ i j k).1 (hp_eval j hj)
  · intro h p hp
    cases p with
    | mk i k =>
        rw [evalCNF_flatMap]
        intro j hj
        exact (mulAssocInner_correct n τ i j k).2 (h (i, k) hp j hj)

def DistInnerSemantics (n : Nat) (τ : Assignment) (x y z : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => distVar n x y z l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    τ (addVar n y z q.2) → τ (mulVar n x q.2 q.1) → τ (distVar n x y z q.1)) ∧
  (∀ q, q ∈ product3 (values n) (values n) (values n) →
    τ (mulVar n x y q.2.1) → τ (mulVar n x z q.2.2) →
      τ (addVar n q.2.1 q.2.2 q.1) → τ (distVar n x y z q.1))

theorem distInner_correct (n : Nat) (τ : Assignment) (x y z : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => distVar n x y z l)) ++
        (product2 (values n) (values n)).map (fun (l, m) =>
          [neg (addVar n y z m), neg (mulVar n x m l), pos (distVar n x y z l)]) ++
        (product3 (values n) (values n) (values n)).map (fun (l, m1, m2) =>
          [neg (mulVar n x y m1), neg (mulVar n x z m2), neg (addVar n m1 m2 l),
            pos (distVar n x y z l)])) ↔
      DistInnerSemantics n τ x y z := by
  unfold DistInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (distVar_pos n x y z))]
  rw [evalCNF_imp2Clauses_iff τ (product2 (values n) (values n))
    (fun q => addVar n y z q.2)
    (fun q => mulVar n x q.2 q.1)
    (fun q => distVar n x y z q.1)
    (by
      intro q _
      exact ⟨addVar_pos n y z q.2, mulVar_pos n x q.2 q.1, distVar_pos n x y z q.1⟩)]
  rw [evalCNF_imp3Clauses_iff τ (product3 (values n) (values n) (values n))
    (fun q => mulVar n x y q.2.1)
    (fun q => mulVar n x z q.2.2)
    (fun q => addVar n q.2.1 q.2.2 q.1)
    (fun q => distVar n x y z q.1)
    (by
      intro q _
      exact ⟨mulVar_pos n x y q.2.1, mulVar_pos n x z q.2.2,
        addVar_pos n q.2.1 q.2.2 q.1, distVar_pos n x y z q.1⟩)]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

def DistSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ x, x ∈ values n →
    ∀ p, p ∈ symPairs n → DistInnerSemantics n τ x p.1 p.2

theorem distClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (distClauses n) ↔ DistSemantics n τ := by
  unfold distClauses DistSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h x hx p hp
    have hx_eval := h x hx
    rw [evalCNF_flatMap] at hx_eval
    cases p with
    | mk y z =>
        exact (distInner_correct n τ x y z).1 (hx_eval (y, z) hp)
  · intro h x hx
    rw [evalCNF_flatMap]
    intro p hp
    cases p with
    | mk y z =>
        exact (distInner_correct n τ x y z).2 (h x hx (y, z) hp)

def ExpAddInnerSemantics (n : Nat) (τ : Assignment) (x y z : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => expAddVar n x y z l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    τ (addVar n y z q.2) → τ (expVar n x q.2 q.1) → τ (expAddVar n x y z q.1)) ∧
  (∀ q, q ∈ product3 (values n) (values n) (values n) →
    τ (expVar n x y q.2.1) → τ (expVar n x z q.2.2) →
      τ (mulVar n q.2.1 q.2.2 q.1) → τ (expAddVar n x y z q.1))

theorem expAddInner_correct (n : Nat) (τ : Assignment) (x y z : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => expAddVar n x y z l)) ++
        (product2 (values n) (values n)).map (fun (l, m) =>
          [neg (addVar n y z m), neg (expVar n x m l), pos (expAddVar n x y z l)]) ++
        (product3 (values n) (values n) (values n)).map (fun (l, m1, m2) =>
          [neg (expVar n x y m1), neg (expVar n x z m2), neg (mulVar n m1 m2 l),
            pos (expAddVar n x y z l)])) ↔
      ExpAddInnerSemantics n τ x y z := by
  unfold ExpAddInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (expAddVar_pos n x y z))]
  rw [evalCNF_imp2Clauses_iff τ (product2 (values n) (values n))
    (fun q => addVar n y z q.2)
    (fun q => expVar n x q.2 q.1)
    (fun q => expAddVar n x y z q.1)
    (by
      intro q _
      exact ⟨addVar_pos n y z q.2, expVar_pos n x q.2 q.1,
        expAddVar_pos n x y z q.1⟩)]
  rw [evalCNF_imp3Clauses_iff τ (product3 (values n) (values n) (values n))
    (fun q => expVar n x y q.2.1)
    (fun q => expVar n x z q.2.2)
    (fun q => mulVar n q.2.1 q.2.2 q.1)
    (fun q => expAddVar n x y z q.1)
    (by
      intro q _
      exact ⟨expVar_pos n x y q.2.1, expVar_pos n x z q.2.2,
        mulVar_pos n q.2.1 q.2.2 q.1, expAddVar_pos n x y z q.1⟩)]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

def ExpAddSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ x, x ∈ values n →
    ∀ p, p ∈ symPairs n → ExpAddInnerSemantics n τ x p.1 p.2

theorem expAddClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (expAddClauses n) ↔ ExpAddSemantics n τ := by
  unfold expAddClauses ExpAddSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h x hx p hp
    have hx_eval := h x hx
    rw [evalCNF_flatMap] at hx_eval
    cases p with
    | mk y z =>
        exact (expAddInner_correct n τ x y z).1 (hx_eval (y, z) hp)
  · intro h x hx
    rw [evalCNF_flatMap]
    intro p hp
    cases p with
    | mk y z =>
        exact (expAddInner_correct n τ x y z).2 (h x hx (y, z) hp)

def ExpMulInnerSemantics (n : Nat) (τ : Assignment) (x y z : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => expMulVar n x y z l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    τ (mulVar n x y q.2) → τ (expVar n q.2 z q.1) → τ (expMulVar n x y z q.1)) ∧
  (∀ q, q ∈ product3 (values n) (values n) (values n) →
    τ (expVar n x z q.2.1) → τ (expVar n y z q.2.2) →
      τ (mulVar n q.2.1 q.2.2 q.1) → τ (expMulVar n x y z q.1))

theorem expMulInner_correct (n : Nat) (τ : Assignment) (x y z : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => expMulVar n x y z l)) ++
        (product2 (values n) (values n)).map (fun (l, m) =>
          [neg (mulVar n x y m), neg (expVar n m z l), pos (expMulVar n x y z l)]) ++
        (product3 (values n) (values n) (values n)).map (fun (l, m1, m2) =>
          [neg (expVar n x z m1), neg (expVar n y z m2), neg (mulVar n m1 m2 l),
            pos (expMulVar n x y z l)])) ↔
      ExpMulInnerSemantics n τ x y z := by
  unfold ExpMulInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (expMulVar_pos n x y z))]
  rw [evalCNF_imp2Clauses_iff τ (product2 (values n) (values n))
    (fun q => mulVar n x y q.2)
    (fun q => expVar n q.2 z q.1)
    (fun q => expMulVar n x y z q.1)
    (by
      intro q _
      exact ⟨mulVar_pos n x y q.2, expVar_pos n q.2 z q.1,
        expMulVar_pos n x y z q.1⟩)]
  rw [evalCNF_imp3Clauses_iff τ (product3 (values n) (values n) (values n))
    (fun q => expVar n x z q.2.1)
    (fun q => expVar n y z q.2.2)
    (fun q => mulVar n q.2.1 q.2.2 q.1)
    (fun q => expMulVar n x y z q.1)
    (by
      intro q _
      exact ⟨expVar_pos n x z q.2.1, expVar_pos n y z q.2.2,
        mulVar_pos n q.2.1 q.2.2 q.1, expMulVar_pos n x y z q.1⟩)]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

def ExpMulSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ p, p ∈ symPairs n →
    ∀ z, z ∈ values n → ExpMulInnerSemantics n τ p.1 p.2 z

theorem expMulClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (expMulClauses n) ↔ ExpMulSemantics n τ := by
  unfold expMulClauses ExpMulSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h p hp z hz
    have hp_eval := h p hp
    cases p with
    | mk x y =>
        rw [evalCNF_flatMap] at hp_eval
        exact (expMulInner_correct n τ x y z).1 (hp_eval z hz)
  · intro h p hp
    cases p with
    | mk x y =>
        rw [evalCNF_flatMap]
        intro z hz
        exact (expMulInner_correct n τ x y z).2 (h (x, y) hp z hz)

def ExpAssocInnerSemantics (n : Nat) (τ : Assignment) (x y z : Nat) : Prop :=
  AtMostOneVars τ ((values n).map (fun l => exp2Var n x y z l)) ∧
  (∀ q, q ∈ product2 (values n) (values n) →
    (τ (expVar n x y q.2) → τ (expVar n q.2 z q.1) → τ (exp2Var n x y z q.1)) ∧
    (τ (mulVar n y z q.2) → τ (expVar n x q.2 q.1) → τ (exp2Var n x y z q.1)))

theorem expAssocInner_correct (n : Nat) (τ : Assignment) (x y z : Nat) :
    evalCNF τ
      (atMostOnePairwise ((values n).map (fun l => exp2Var n x y z l)) ++
        flatMap (product2 (values n) (values n)) (fun (l, m) => [
          [neg (expVar n x y m), neg (expVar n m z l), pos (exp2Var n x y z l)],
          [neg (mulVar n y z m), neg (expVar n x m l), pos (exp2Var n x y z l)]
        ])) ↔
      ExpAssocInnerSemantics n τ x y z := by
  unfold ExpAssocInnerSemantics
  rw [evalCNF_append]
  rw [evalCNF_atMostOnePairwise_iff τ _ (mapped_values_pos (exp2Var_pos n x y z))]
  rw [evalCNF_flatMap]
  constructor
  · intro h
    constructor
    · exact h.1
    · intro q hq
      have hqeval := h.2 q hq
      cases q with
      | mk l m =>
          simp [evalCNF,
            evalClause_imp2_iff τ (expVar_pos n x y m) (expVar_pos n m z l)
              (exp2Var_pos n x y z l),
            evalClause_imp2_iff τ (mulVar_pos n y z m) (expVar_pos n x m l)
              (exp2Var_pos n x y z l)] at hqeval
          exact hqeval
  · intro h
    constructor
    · exact h.1
    · intro q hq
      cases q with
      | mk l m =>
          have hqsem := h.2 (l, m) hq
          simp [evalCNF,
            evalClause_imp2_iff τ (expVar_pos n x y m) (expVar_pos n m z l)
              (exp2Var_pos n x y z l),
            evalClause_imp2_iff τ (mulVar_pos n y z m) (expVar_pos n x m l)
              (exp2Var_pos n x y z l)]
          exact hqsem

def ExpAssocSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ q, q ∈ product3 (values n) (values n) (values n) →
    ExpAssocInnerSemantics n τ q.1 q.2.1 q.2.2

theorem expAssocClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (expAssocClauses n) ↔ ExpAssocSemantics n τ := by
  unfold expAssocClauses ExpAssocSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h q hq
    cases q with
    | mk x yz =>
        cases yz with
        | mk y z =>
            exact (expAssocInner_correct n τ x y z).1 (h (x, y, z) hq)
  · intro h q hq
    cases q with
    | mk x yz =>
        cases yz with
        | mk y z =>
            exact (expAssocInner_correct n τ x y z).2 (h (x, y, z) hq)

def HSISemantics (n : Nat) (τ : Assignment) : Prop :=
  OperationTotalitySemantics n τ ∧
  UnitIdentitySemantics n τ ∧
  AddAssocSemantics n τ ∧
  MulAssocSemantics n τ ∧
  DistSemantics n τ ∧
  ExpAddSemantics n τ ∧
  ExpMulSemantics n τ ∧
  ExpAssocSemantics n τ

theorem hsiClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (hsiClauses n) ↔ HSISemantics n τ := by
  unfold hsiClauses HSISemantics
  simp [evalCNF_append, totalityClauses_correct, unitIdentityClauses_correct,
    addAssocClauses_correct, mulAssocClauses_correct, distClauses_correct,
    expAddClauses_correct, expMulClauses_correct, expAssocClauses_correct]

def WilkieDiseqSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ v, v ∈ values n → ¬(τ (termVar n 24 v) ∧ τ (termVar n 25 v))

theorem wilkieDiseqClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (wilkieDiseqClauses n) ↔ WilkieDiseqSemantics n τ := by
  unfold wilkieDiseqClauses WilkieDiseqSemantics
  rw [evalCNF_twoNegClauses_iff τ (values n)
    (fun v => termVar n 24 v)
    (fun v => termVar n 25 v)
    (by
      intro v _
      exact ⟨termVar_pos n 24 v, termVar_pos n 25 v⟩)]

def TermClausesSemantics (n : Nat) (τ : Assignment) (termIndex : Nat)
    (spec : TermSpec) : Prop :=
  ExactlyOneVars τ ((values n).map (termVar n termIndex)) ∧
  match spec.left, spec.right with
  | .const left, .const right =>
      ∀ v, v ∈ values n →
        τ (opVar n spec.op left right v) → τ (termVar n termIndex v)
  | .const left, .term right =>
      ∀ q, q ∈ product2 (values n) (values n) →
        τ (opVar n spec.op left q.1 q.2) → τ (termVar n right q.1) →
          τ (termVar n termIndex q.2)
  | .term left, .const right =>
      ∀ q, q ∈ product2 (values n) (values n) →
        τ (opVar n spec.op q.1 right q.2) → τ (termVar n left q.1) →
          τ (termVar n termIndex q.2)
  | .term left, .term right =>
      ∀ q, q ∈ product3 (values n) (values n) (values n) →
        τ (opVar n spec.op q.1 q.2.1 q.2.2) → τ (termVar n left q.1) →
          τ (termVar n right q.2.1) → τ (termVar n termIndex q.2.2)

theorem termClauses_correct (n : Nat) (τ : Assignment)
    (termIndex : Nat) (spec : TermSpec) :
    evalCNF τ (termClauses n termIndex spec) ↔
      TermClausesSemantics n τ termIndex spec := by
  cases spec with
  | mk op left right =>
      cases left with
      | const left =>
          cases right with
          | const right =>
              unfold termClauses TermClausesSemantics
              rw [evalCNF_append]
              rw [evalCNF_exactlyOnePairwise_iff τ _
                (mapped_values_pos (termVar_pos n termIndex))]
              rw [evalCNF_imp1Clauses_iff τ (values n)
                (fun v => opVar n op left right v)
                (fun v => termVar n termIndex v)
                (by
                  intro v _
                  exact ⟨opVar_pos n op left right v, termVar_pos n termIndex v⟩)]
          | term right =>
              unfold termClauses TermClausesSemantics
              rw [evalCNF_append]
              rw [evalCNF_exactlyOnePairwise_iff τ _
                (mapped_values_pos (termVar_pos n termIndex))]
              rw [evalCNF_imp2Clauses_iff τ (product2 (values n) (values n))
                (fun q => opVar n op left q.1 q.2)
                (fun q => termVar n right q.1)
                (fun q => termVar n termIndex q.2)
                (by
                  intro q _
                  exact ⟨opVar_pos n op left q.1 q.2, termVar_pos n right q.1,
                    termVar_pos n termIndex q.2⟩)]
      | term left =>
          cases right with
          | const right =>
              unfold termClauses TermClausesSemantics
              rw [evalCNF_append]
              rw [evalCNF_exactlyOnePairwise_iff τ _
                (mapped_values_pos (termVar_pos n termIndex))]
              rw [evalCNF_imp2Clauses_iff τ (product2 (values n) (values n))
                (fun q => opVar n op q.1 right q.2)
                (fun q => termVar n left q.1)
                (fun q => termVar n termIndex q.2)
                (by
                  intro q _
                  exact ⟨opVar_pos n op q.1 right q.2, termVar_pos n left q.1,
                    termVar_pos n termIndex q.2⟩)]
          | term right =>
              unfold termClauses TermClausesSemantics
              rw [evalCNF_append]
              rw [evalCNF_exactlyOnePairwise_iff τ _
                (mapped_values_pos (termVar_pos n termIndex))]
              rw [evalCNF_imp3Clauses_iff τ (product3 (values n) (values n) (values n))
                (fun q => opVar n op q.1 q.2.1 q.2.2)
                (fun q => termVar n left q.1)
                (fun q => termVar n right q.2.1)
                (fun q => termVar n termIndex q.2.2)
                (by
                  intro q _
                  exact ⟨opVar_pos n op q.1 q.2.1 q.2.2, termVar_pos n left q.1,
                    termVar_pos n right q.2.1, termVar_pos n termIndex q.2.2⟩)]

def WilkieTermClausesSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ p, p ∈ enumerate termSpecs → TermClausesSemantics n τ p.1 p.2

def WilkieClausesSemantics (n : Nat) (τ : Assignment) : Prop :=
  WilkieTermClausesSemantics n τ ∧ WilkieDiseqSemantics n τ

theorem wilkieClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (wilkieClauses n) ↔ WilkieClausesSemantics n τ := by
  unfold wilkieClauses WilkieClausesSemantics WilkieTermClausesSemantics
  rw [evalCNF_append]
  rw [evalCNF_flatMap]
  constructor
  · intro h
    constructor
    · intro p hp
      cases p with
      | mk termIndex spec =>
          exact (termClauses_correct n τ termIndex spec).1 (h.1 (termIndex, spec) hp)
    · exact (wilkieDiseqClauses_correct n τ).1 h.2
  · intro h
    constructor
    · intro p hp
      cases p with
      | mk termIndex spec =>
          exact (termClauses_correct n τ termIndex spec).2 (h.1 (termIndex, spec) hp)
    · exact (wilkieDiseqClauses_correct n τ).2 h.2

def CoreSemantics (n : Nat) (τ : Assignment) : Prop :=
  HSISemantics n τ ∧ WilkieClausesSemantics n τ

theorem coreClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ (coreClauses n) ↔ CoreSemantics n τ := by
  unfold coreClauses CoreSemantics
  rw [evalCNF_append]
  rw [hsiClauses_correct]
  rw [wilkieClauses_correct]

structure Algebra where
  add : Nat → Nat → Nat
  mul : Nat → Nat → Nat
  exp : Nat → Nat → Nat

def evalOp (A : Algebra) : Op → Nat → Nat → Nat
  | .add => A.add
  | .mul => A.mul
  | .exp => A.exp

noncomputable def decodedAlgebra (n : Nat) (τ : Assignment) : Algebra where
  add i j := selectValue n τ (fun k => addVar n (min i j) (max i j) k)
  mul i j := selectValue n τ (fun k => mulVar n (min i j) (max i j) k)
  exp i j := selectValue n τ (fun k => expVar n i j k)

def InDomain (n x : Nat) : Prop :=
  x ∈ values n

theorem InDomain_iff {n x : Nat} :
    InDomain n x ↔ 1 ≤ x ∧ x ≤ n := by
  exact mem_values_iff

theorem symPair_mem_of_domain {n i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) :
    (min i j, max i j) ∈ symPairs n := by
  rw [InDomain_iff] at hi hj
  unfold symPairs
  rw [mem_flatMap_iff]
  refine ⟨min i j, ?_, ?_⟩
  · rw [mem_values_iff]
    omega
  · apply List.mem_map.mpr
    refine ⟨max i j, ?_, rfl⟩
    rw [mem_rangeFromTo_iff]
    · constructor <;> omega
    · omega

theorem symPair_mem_of_domain_ordered {n i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hij : i ≤ j) :
    (i, j) ∈ symPairs n := by
  simpa [Nat.min_eq_left hij, Nat.max_eq_right hij] using
    (symPair_mem_of_domain hi hj)

theorem symIndex_lt_pairCount_of_domain {n i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) :
    symIndex n i j < pairCount n := by
  unfold symIndex pairCount
  exact indexOf_lt_length_of_mem (symPair_mem_of_domain hi hj)

theorem symIndex_inj_canonical
    {n i j i' j' : Nat}
    (hi : InDomain n i) (hj : InDomain n j)
    (hi' : InDomain n i') (hj' : InDomain n j')
    (h : symIndex n i j = symIndex n i' j') :
    (min i j, max i j) = (min i' j', max i' j') := by
  unfold symIndex at h
  exact indexOf_eq_of_mem
    (symPair_mem_of_domain hi hj)
    (symPair_mem_of_domain hi' hj') h

theorem addVar_block
    {n i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    1 ≤ addVar n i j k ∧ addVar n i j k ≤ pairCount n * n := by
  constructor
  · exact Nat.succ_le_of_lt (addVar_pos n i j k)
  · unfold addVar
    exact linearIndex_succ_le_mul (symIndex_lt_pairCount_of_domain hi hj) hk

theorem mulVar_block
    {n i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    pairCount n * n < mulVar n i j k ∧
      mulVar n i j k ≤ 2 * pairCount n * n := by
  let off := symIndex n i j * n + (k - 1) + 1
  have hoff : off ≤ pairCount n * n := by
    dsimp [off]
    exact linearIndex_succ_le_mul (symIndex_lt_pairCount_of_domain hi hj) hk
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold mulVar
    dsimp [off] at hoffPos
    simpa [Nat.add_assoc] using
      (Nat.lt_add_of_pos_right (n := pairCount n * n) hoffPos)
  · unfold mulVar
    dsimp [off] at hoff
    have htwice : 2 * pairCount n * n = pairCount n * n + pairCount n * n := by
      rw [Nat.two_mul, Nat.add_mul]
    rw [htwice]
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (pairCount n * n)

theorem expVar_block
    {n i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    2 * pairCount n * n < expVar n i j k ∧
      expVar n i j k ≤ primaryCount n := by
  let off := (i - 1) * n * n + (j - 1) * n + (k - 1) + 1
  have hiPred : i - 1 < n := valuePred_lt hi
  have hoffLinear :
      ((i - 1) * n + (j - 1)) * n + (k - 1) + 1 ≤ n * n * n :=
    linearIndex2_succ_le_mul_mul hiPred hj hk
  have hoff : off ≤ n * n * n := by
    dsimp [off]
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hoffLinear
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold expVar
    dsimp [off] at hoffPos
    simpa [Nat.add_assoc] using
      (Nat.lt_add_of_pos_right (n := 2 * pairCount n * n) hoffPos)
  · unfold expVar primaryCount
    dsimp [off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (2 * pairCount n * n)

theorem addVar_inj_canonical
    {n i j k i' j' k' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k')
    (h : addVar n i j k = addVar n i' j' k') :
    (min i j, max i j) = (min i' j', max i' j') ∧ k = k' := by
  unfold addVar at h
  have hlin := linearIndex_succ_inj hk hk' h
  exact ⟨symIndex_inj_canonical hi hj hi' hj' hlin.1, hlin.2⟩

theorem mulVar_inj_canonical
    {n i j k i' j' k' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k')
    (h : mulVar n i j k = mulVar n i' j' k') :
    (min i j, max i j) = (min i' j', max i' j') ∧ k = k' := by
  unfold mulVar at h
  have hlinEq :
      symIndex n i j * n + (k - 1) + 1 =
        symIndex n i' j' * n + (k' - 1) + 1 := by
    omega
  have hlin := linearIndex_succ_inj hk hk' hlinEq
  exact ⟨symIndex_inj_canonical hi hj hi' hj' hlin.1, hlin.2⟩

theorem expVar_inj
    {n i j k i' j' k' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k')
    (h : expVar n i j k = expVar n i' j' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  unfold expVar at h
  let base := 2 * pairCount n * n
  let leftOff := (i - 1) * n * n + (j - 1) * n + (k - 1) + 1
  let rightOff := (i' - 1) * n * n + (j' - 1) * n + (k' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq :
      (i - 1) * n * n + (j - 1) * n + (k - 1) + 1 =
        (i' - 1) * n * n + (j' - 1) * n + (k' - 1) + 1 :=
    by
      have hcancel := Nat.add_left_cancel hbase
      simpa [leftOff, rightOff] using hcancel
  have hlinEq :
      ((i - 1) * n + (j - 1)) * n + (k - 1) + 1 =
        ((i' - 1) * n + (j' - 1)) * n + (k' - 1) + 1 := by
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hoffEq
  have hkSplit := linearIndex_succ_inj hk hk' hlinEq
  have hijSplit : i - 1 = i' - 1 ∧ j = j' :=
    linearIndex_inj hj hj' hkSplit.1
  rw [InDomain_iff] at hi hi'
  exact ⟨by omega, hijSplit.2, hkSplit.2⟩

theorem add2Var_block
    {n i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    add2Base n < add2Var n i j k l ∧ add2Var n i j k l ≤ mul2Base n := by
  let off := (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1
  have hoff : off ≤ symAuxBlockSize n := by
    dsimp [off]
    unfold symAuxBlockSize
    exact linearIndex2_succ_le_mul_mul (symIndex_lt_pairCount_of_domain hi hk) hj hl
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold add2Var
    dsimp [off] at hoffPos
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := add2Base n) hoffPos)
  · unfold add2Var mul2Base
    dsimp [off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (add2Base n)

theorem mul2Var_block
    {n i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    mul2Base n < mul2Var n i j k l ∧ mul2Var n i j k l ≤ distBase n := by
  let off := (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1
  have hoff : off ≤ symAuxBlockSize n := by
    dsimp [off]
    unfold symAuxBlockSize
    exact linearIndex2_succ_le_mul_mul (symIndex_lt_pairCount_of_domain hi hk) hj hl
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold mul2Var
    dsimp [off] at hoffPos
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := mul2Base n) hoffPos)
  · unfold mul2Var distBase
    dsimp [off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (mul2Base n)

theorem add2Var_inj_canonical
    {n i j k l i' j' k' l' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k') (hl' : InDomain n l')
    (h : add2Var n i j k l = add2Var n i' j' k' l') :
    (min i k, max i k) = (min i' k', max i' k') ∧ j = j' ∧ l = l' := by
  unfold add2Var at h
  let base := add2Base n
  let leftOff := (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1
  let rightOff := (symIndex n i' k' * n + (j' - 1)) * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq :
      (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1 =
        (symIndex n i' k' * n + (j' - 1)) * n + (l' - 1) + 1 :=
    by
      have hcancel := Nat.add_left_cancel hbase
      simpa [leftOff, rightOff] using hcancel
  have hsplit := linearIndex_succ_inj hl hl' hoffEq
  have hpairJ := linearIndex_inj hj hj' hsplit.1
  exact ⟨symIndex_inj_canonical hi hk hi' hk' hpairJ.1, hpairJ.2, hsplit.2⟩

theorem mul2Var_inj_canonical
    {n i j k l i' j' k' l' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k') (hl' : InDomain n l')
    (h : mul2Var n i j k l = mul2Var n i' j' k' l') :
    (min i k, max i k) = (min i' k', max i' k') ∧ j = j' ∧ l = l' := by
  unfold mul2Var at h
  let base := mul2Base n
  let leftOff := (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1
  let rightOff := (symIndex n i' k' * n + (j' - 1)) * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq :
      (symIndex n i k * n + (j - 1)) * n + (l - 1) + 1 =
        (symIndex n i' k' * n + (j' - 1)) * n + (l' - 1) + 1 :=
    by
      have hcancel := Nat.add_left_cancel hbase
      simpa [leftOff, rightOff] using hcancel
  have hsplit := linearIndex_succ_inj hl hl' hoffEq
  have hpairJ := linearIndex_inj hj hj' hsplit.1
  exact ⟨symIndex_inj_canonical hi hk hi' hk' hpairJ.1, hpairJ.2, hsplit.2⟩

theorem distVar_block
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    distBase n < distVar n x y z l ∧ distVar n x y z l ≤ expAddBase n := by
  let high := (x - 1) * pairCount n + symIndex n y z
  let off := high * n + (l - 1) + 1
  have hhigh : high < n * pairCount n := by
    dsimp [high]
    exact linearIndex0_lt_mul (valuePred_lt hx) (symIndex_lt_pairCount_of_domain hy hz)
  have hoff : off ≤ symAuxBlockSize n := by
    dsimp [off]
    unfold symAuxBlockSize
    have h := linearIndex_succ_le_mul (n := n) (A := n * pairCount n) hhigh hl
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold distVar
    dsimp [high, off] at hoffPos
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := distBase n) hoffPos)
  · unfold distVar expAddBase
    dsimp [high, off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (distBase n)

theorem expAddVar_block
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    expAddBase n < expAddVar n x y z l ∧ expAddVar n x y z l ≤ expMulBase n := by
  let high := (x - 1) * pairCount n + symIndex n y z
  let off := high * n + (l - 1) + 1
  have hhigh : high < n * pairCount n := by
    dsimp [high]
    exact linearIndex0_lt_mul (valuePred_lt hx) (symIndex_lt_pairCount_of_domain hy hz)
  have hoff : off ≤ symAuxBlockSize n := by
    dsimp [off]
    unfold symAuxBlockSize
    have h := linearIndex_succ_le_mul (n := n) (A := n * pairCount n) hhigh hl
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold expAddVar
    dsimp [high, off] at hoffPos
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := expAddBase n) hoffPos)
  · unfold expAddVar expMulBase
    dsimp [high, off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (expAddBase n)

theorem distVar_inj_canonical
    {n x y z l x' y' z' l' : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l)
    (hx' : InDomain n x') (hy' : InDomain n y') (hz' : InDomain n z') (hl' : InDomain n l')
    (h : distVar n x y z l = distVar n x' y' z' l') :
    x = x' ∧ (min y z, max y z) = (min y' z', max y' z') ∧ l = l' := by
  unfold distVar at h
  let base := distBase n
  let leftHigh := (x - 1) * pairCount n + symIndex n y z
  let rightHigh := (x' - 1) * pairCount n + symIndex n y' z'
  let leftOff := leftHigh * n + (l - 1) + 1
  let rightOff := rightHigh * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftHigh, rightHigh, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq : leftHigh * n + (l - 1) + 1 = rightHigh * n + (l' - 1) + 1 := by
    have hcancel := Nat.add_left_cancel hbase
    simpa [leftOff, rightOff] using hcancel
  have hsplit := linearIndex_succ_inj hl hl' hoffEq
  have hhigh := linearIndex0_inj
    (symIndex_lt_pairCount_of_domain hy hz)
    (symIndex_lt_pairCount_of_domain hy' hz') hsplit.1
  have hxEq : x = x' := by
    rw [InDomain_iff] at hx hx'
    omega
  exact ⟨hxEq, symIndex_inj_canonical hy hz hy' hz' hhigh.2, hsplit.2⟩

theorem expAddVar_inj_canonical
    {n x y z l x' y' z' l' : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l)
    (hx' : InDomain n x') (hy' : InDomain n y') (hz' : InDomain n z') (hl' : InDomain n l')
    (h : expAddVar n x y z l = expAddVar n x' y' z' l') :
    x = x' ∧ (min y z, max y z) = (min y' z', max y' z') ∧ l = l' := by
  unfold expAddVar at h
  let base := expAddBase n
  let leftHigh := (x - 1) * pairCount n + symIndex n y z
  let rightHigh := (x' - 1) * pairCount n + symIndex n y' z'
  let leftOff := leftHigh * n + (l - 1) + 1
  let rightOff := rightHigh * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftHigh, rightHigh, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq : leftHigh * n + (l - 1) + 1 = rightHigh * n + (l' - 1) + 1 := by
    have hcancel := Nat.add_left_cancel hbase
    simpa [leftOff, rightOff] using hcancel
  have hsplit := linearIndex_succ_inj hl hl' hoffEq
  have hhigh := linearIndex0_inj
    (symIndex_lt_pairCount_of_domain hy hz)
    (symIndex_lt_pairCount_of_domain hy' hz') hsplit.1
  have hxEq : x = x' := by
    rw [InDomain_iff] at hx hx'
    omega
  exact ⟨hxEq, symIndex_inj_canonical hy hz hy' hz' hhigh.2, hsplit.2⟩

theorem expMulVar_block
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    expMulBase n < expMulVar n x y z l ∧ expMulVar n x y z l ≤ exp2Base n := by
  let off := (symIndex n x y * n + (z - 1)) * n + (l - 1) + 1
  have hoff : off ≤ symAuxBlockSize n := by
    dsimp [off]
    unfold symAuxBlockSize
    exact linearIndex2_succ_le_mul_mul (symIndex_lt_pairCount_of_domain hx hy) hz hl
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold expMulVar
    dsimp [off] at hoffPos
    simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := expMulBase n) hoffPos)
  · unfold expMulVar exp2Base
    dsimp [off] at hoff
    simpa [Nat.add_assoc] using Nat.add_le_add_left hoff (expMulBase n)

theorem expMulVar_inj_canonical
    {n x y z l x' y' z' l' : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l)
    (hx' : InDomain n x') (hy' : InDomain n y') (hz' : InDomain n z') (hl' : InDomain n l')
    (h : expMulVar n x y z l = expMulVar n x' y' z' l') :
    (min x y, max x y) = (min x' y', max x' y') ∧ z = z' ∧ l = l' := by
  unfold expMulVar at h
  let base := expMulBase n
  let leftOff := (symIndex n x y * n + (z - 1)) * n + (l - 1) + 1
  let rightOff := (symIndex n x' y' * n + (z' - 1)) * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq :
      (symIndex n x y * n + (z - 1)) * n + (l - 1) + 1 =
        (symIndex n x' y' * n + (z' - 1)) * n + (l' - 1) + 1 := by
    have hcancel := Nat.add_left_cancel hbase
    simpa [leftOff, rightOff] using hcancel
  have hsplit := linearIndex_succ_inj hl hl' hoffEq
  have hpairZ := linearIndex_inj hz hz' hsplit.1
  exact ⟨symIndex_inj_canonical hx hy hx' hy' hpairZ.1, hpairZ.2, hsplit.2⟩

theorem exp2Var_block
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    exp2Base n < exp2Var n x y z l ∧ exp2Var n x y z l ≤ wilkieTermBase n := by
  let high1 := (x - 1) * n + (y - 1)
  let high2 := high1 * n + (z - 1)
  let off := high2 * n + (l - 1) + 1
  have hhigh1 : high1 < n * n := by
    dsimp [high1]
    exact linearIndex_lt_mul (valuePred_lt hx) hy
  have hhigh2 : high2 < n * n * n := by
    dsimp [high2]
    have h := linearIndex_lt_mul (n := n) (A := n * n) hhigh1 hz
    simpa [Nat.mul_assoc] using h
  have hoff : off ≤ n * n * n * n := by
    dsimp [off]
    exact linearIndex_succ_le_mul (n := n) (A := n * n * n) hhigh2 hl
  have hoffPos : 0 < off := by
    dsimp [off]
    omega
  constructor
  · unfold exp2Var
    dsimp [high1, high2, off] at hoffPos
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using (Nat.lt_add_of_pos_right (n := exp2Base n) hoffPos)
  · unfold exp2Var wilkieTermBase
    dsimp [high1, high2, off] at hoff
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using Nat.add_le_add_left hoff (exp2Base n)

theorem exp2Var_inj
    {n x y z l x' y' z' l' : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l)
    (hx' : InDomain n x') (hy' : InDomain n y') (hz' : InDomain n z') (hl' : InDomain n l')
    (h : exp2Var n x y z l = exp2Var n x' y' z' l') :
    x = x' ∧ y = y' ∧ z = z' ∧ l = l' := by
  unfold exp2Var at h
  let base := exp2Base n
  let leftHigh1 := (x - 1) * n + (y - 1)
  let rightHigh1 := (x' - 1) * n + (y' - 1)
  let leftHigh2 := leftHigh1 * n + (z - 1)
  let rightHigh2 := rightHigh1 * n + (z' - 1)
  let leftOff := leftHigh2 * n + (l - 1) + 1
  let rightOff := rightHigh2 * n + (l' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftHigh1, rightHigh1, leftHigh2, rightHigh2, leftOff, rightOff]
    simpa [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hoffEq : leftHigh2 * n + (l - 1) + 1 =
      rightHigh2 * n + (l' - 1) + 1 := by
    have hcancel := Nat.add_left_cancel hbase
    simpa [leftOff, rightOff] using hcancel
  have hlSplit := linearIndex_succ_inj hl hl' hoffEq
  have hzSplit := linearIndex_inj hz hz' hlSplit.1
  have hySplit := linearIndex_inj hy hy' hzSplit.1
  have hxEq : x = x' := by
    rw [InDomain_iff] at hx hx'
    omega
  exact ⟨hxEq, hySplit.2, hzSplit.2, hlSplit.2⟩

theorem termVar_block
    {n termIndex value : Nat} :
    wilkieTermBase n < termVar n termIndex value := by
  unfold termVar
  have hoff : 0 < termIndex * n + (value - 1) + 1 := by omega
  simpa [Nat.add_assoc] using (Nat.lt_add_of_pos_right (n := wilkieTermBase n) hoff)

theorem termVar_inj
    {n termIndex value termIndex' value' : Nat}
    (hvalue : InDomain n value) (hvalue' : InDomain n value')
    (h : termVar n termIndex value = termVar n termIndex' value') :
    termIndex = termIndex' ∧ value = value' := by
  unfold termVar at h
  let base := wilkieTermBase n
  let leftOff := termIndex * n + (value - 1) + 1
  let rightOff := termIndex' * n + (value' - 1) + 1
  have hbase : base + leftOff = base + rightOff := by
    dsimp [base, leftOff, rightOff]
    simpa [Nat.add_assoc] using h
  have hoffEq : termIndex * n + (value - 1) + 1 =
      termIndex' * n + (value' - 1) + 1 := by
    have hcancel := Nat.add_left_cancel hbase
    simpa [leftOff, rightOff] using hcancel
  exact linearIndex_succ_inj hvalue hvalue' hoffEq

theorem mem_symPairs_domain {n : Nat} {p : Nat × Nat}
    (hp : p ∈ symPairs n) :
    InDomain n p.1 ∧ InDomain n p.2 := by
  unfold symPairs at hp
  rw [mem_flatMap_iff] at hp
  rcases hp with ⟨i, hi, hpairs⟩
  rcases List.mem_map.mp hpairs with ⟨j, hj, hpair⟩
  cases hpair
  have hiBounds : 1 ≤ i ∧ i ≤ n := (mem_values_iff).1 hi
  have hjBounds : i ≤ j ∧ j ≤ n := (mem_rangeFromTo_iff hiBounds.2).1 hj
  have hjValue : j ∈ values n := by
    rw [mem_values_iff]
    exact ⟨by omega, hjBounds.2⟩
  exact ⟨hi, hjValue⟩

theorem one_in_domain_of {n x : Nat} (hx : InDomain n x) :
    InDomain n 1 := by
  rw [InDomain_iff] at hx ⊢
  omega

theorem InDomain.of_le {n a b : Nat}
    (hb : InDomain n b) (ha_pos : 1 ≤ a) (hab : a ≤ b) :
    InDomain n a := by
  rw [InDomain_iff] at hb ⊢
  omega

structure Closed (n : Nat) (A : Algebra) : Prop where
  add_mem : ∀ {i j}, InDomain n i → InDomain n j → InDomain n (A.add i j)
  mul_mem : ∀ {i j}, InDomain n i → InDomain n j → InDomain n (A.mul i j)
  exp_mem : ∀ {i j}, InDomain n i → InDomain n j → InDomain n (A.exp i j)

theorem Closed.evalOp_mem
    {n : Nat} {A : Algebra} (C : Closed n A)
    (op : Op) {i j : Nat} (hi : InDomain n i) (hj : InDomain n j) :
    InDomain n (evalOp A op i j) := by
  cases op
  · exact C.add_mem hi hj
  · exact C.mul_mem hi hj
  · exact C.exp_mem hi hj

structure HSI (n : Nat) (A : Algebra) : Prop where
  add_comm :
    ∀ {i j}, InDomain n i → InDomain n j → A.add i j = A.add j i
  add_assoc :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.add i (A.add j k) = A.add (A.add i j) k
  mul_one :
    ∀ {i}, InDomain n i → A.mul i 1 = i
  mul_comm :
    ∀ {i j}, InDomain n i → InDomain n j → A.mul i j = A.mul j i
  mul_assoc :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.mul i (A.mul j k) = A.mul (A.mul i j) k
  distrib :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.mul i (A.add j k) = A.add (A.mul i j) (A.mul i k)
  one_exp :
    ∀ {i}, InDomain n i → A.exp 1 i = 1
  exp_one :
    ∀ {i}, InDomain n i → A.exp i 1 = i
  exp_add :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.exp i (A.add j k) = A.mul (A.exp i j) (A.exp i k)
  exp_mul :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.exp (A.mul i j) k = A.mul (A.exp i k) (A.exp j k)
  exp_assoc :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      A.exp (A.exp i j) k = A.exp i (A.mul j k)

theorem HSI.add_eq_of_canonical_eq
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j i' j' : Nat}
    (hi : InDomain n i) (hj : InDomain n j)
    (hi' : InDomain n i') (hj' : InDomain n j')
    (hcanon : (min i j, max i j) = (min i' j', max i' j')) :
    A.add i j = A.add i' j' := by
  by_cases hij : i ≤ j
  · by_cases hi'j' : i' ≤ j'
    · have hp : (i, j) = (i', j') := by
        simpa [Nat.min_eq_left hij, Nat.max_eq_right hij,
          Nat.min_eq_left hi'j', Nat.max_eq_right hi'j'] using hcanon
      cases hp
      rfl
    · have hj'i' : j' ≤ i' := Nat.le_of_not_ge hi'j'
      have hp : (i, j) = (j', i') := by
        simpa [Nat.min_eq_left hij, Nat.max_eq_right hij,
          Nat.min_eq_right hj'i', Nat.max_eq_left hj'i'] using hcanon
      have hi_eq : i = j' := congrArg Prod.fst hp
      have hj_eq : j = i' := congrArg Prod.snd hp
      have hcomm := H.add_comm hi hj
      simpa [hi_eq, hj_eq] using hcomm
  · have hji : j ≤ i := Nat.le_of_not_ge hij
    by_cases hi'j' : i' ≤ j'
    · have hp : (j, i) = (i', j') := by
        simpa [Nat.min_eq_right hji, Nat.max_eq_left hji,
          Nat.min_eq_left hi'j', Nat.max_eq_right hi'j'] using hcanon
      have hj_eq : j = i' := congrArg Prod.fst hp
      have hi_eq : i = j' := congrArg Prod.snd hp
      have hcomm := H.add_comm hi hj
      simpa [hi_eq, hj_eq] using hcomm
    · have hj'i' : j' ≤ i' := Nat.le_of_not_ge hi'j'
      have hp : (j, i) = (j', i') := by
        simpa [Nat.min_eq_right hji, Nat.max_eq_left hji,
          Nat.min_eq_right hj'i', Nat.max_eq_left hj'i'] using hcanon
      have hj_eq : j = j' := congrArg Prod.fst hp
      have hi_eq : i = i' := congrArg Prod.snd hp
      simp [hi_eq, hj_eq]

theorem HSI.mul_eq_of_canonical_eq
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j i' j' : Nat}
    (hi : InDomain n i) (hj : InDomain n j)
    (hi' : InDomain n i') (hj' : InDomain n j')
    (hcanon : (min i j, max i j) = (min i' j', max i' j')) :
    A.mul i j = A.mul i' j' := by
  by_cases hij : i ≤ j
  · by_cases hi'j' : i' ≤ j'
    · have hp : (i, j) = (i', j') := by
        simpa [Nat.min_eq_left hij, Nat.max_eq_right hij,
          Nat.min_eq_left hi'j', Nat.max_eq_right hi'j'] using hcanon
      cases hp
      rfl
    · have hj'i' : j' ≤ i' := Nat.le_of_not_ge hi'j'
      have hp : (i, j) = (j', i') := by
        simpa [Nat.min_eq_left hij, Nat.max_eq_right hij,
          Nat.min_eq_right hj'i', Nat.max_eq_left hj'i'] using hcanon
      have hi_eq : i = j' := congrArg Prod.fst hp
      have hj_eq : j = i' := congrArg Prod.snd hp
      have hcomm := H.mul_comm hi hj
      simpa [hi_eq, hj_eq] using hcomm
  · have hji : j ≤ i := Nat.le_of_not_ge hij
    by_cases hi'j' : i' ≤ j'
    · have hp : (j, i) = (i', j') := by
        simpa [Nat.min_eq_right hji, Nat.max_eq_left hji,
          Nat.min_eq_left hi'j', Nat.max_eq_right hi'j'] using hcanon
      have hj_eq : j = i' := congrArg Prod.fst hp
      have hi_eq : i = j' := congrArg Prod.snd hp
      have hcomm := H.mul_comm hi hj
      simpa [hi_eq, hj_eq] using hcomm
    · have hj'i' : j' ≤ i' := Nat.le_of_not_ge hi'j'
      have hp : (j, i) = (j', i') := by
        simpa [Nat.min_eq_right hji, Nat.max_eq_left hji,
          Nat.min_eq_right hj'i', Nat.max_eq_left hj'i'] using hcanon
      have hj_eq : j = j' := congrArg Prod.fst hp
      have hi_eq : i = i' := congrArg Prod.snd hp
      simp [hi_eq, hj_eq]

theorem HSI.add3_right_eq_of_canonical_eq
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k i' j' k' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k')
    (hcanon : (min i k, max i k) = (min i' k', max i' k')) (hjEq : j = j') :
    A.add (A.add i j) k = A.add (A.add i' j') k' := by
  subst j'
  by_cases hik : i ≤ k
  · by_cases hi'k' : i' ≤ k'
    · have hp : (i, k) = (i', k') := by
        simpa [Nat.min_eq_left hik, Nat.max_eq_right hik,
          Nat.min_eq_left hi'k', Nat.max_eq_right hi'k'] using hcanon
      cases hp
      rfl
    · have hk'i' : k' ≤ i' := Nat.le_of_not_ge hi'k'
      have hp : (i, k) = (k', i') := by
        simpa [Nat.min_eq_left hik, Nat.max_eq_right hik,
          Nat.min_eq_right hk'i', Nat.max_eq_left hk'i'] using hcanon
      have hi_eq : i = k' := congrArg Prod.fst hp
      have hk_eq : k = i' := congrArg Prod.snd hp
      have hij : InDomain n (A.add i j) := C.add_mem hi hj
      calc
        A.add (A.add i j) k
            = A.add k (A.add i j) := H.add_comm hij hk
        _ = A.add k (A.add j i) := by rw [H.add_comm hi hj]
        _ = A.add (A.add k j) i := H.add_assoc hk hj hi
        _ = A.add (A.add i' j) k' := by simp [hi_eq, hk_eq]
  · have hki : k ≤ i := Nat.le_of_not_ge hik
    by_cases hi'k' : i' ≤ k'
    · have hp : (k, i) = (i', k') := by
        simpa [Nat.min_eq_right hki, Nat.max_eq_left hki,
          Nat.min_eq_left hi'k', Nat.max_eq_right hi'k'] using hcanon
      have hk_eq : k = i' := congrArg Prod.fst hp
      have hi_eq : i = k' := congrArg Prod.snd hp
      have hij : InDomain n (A.add i j) := C.add_mem hi hj
      calc
        A.add (A.add i j) k
            = A.add k (A.add i j) := H.add_comm hij hk
        _ = A.add k (A.add j i) := by rw [H.add_comm hi hj]
        _ = A.add (A.add k j) i := H.add_assoc hk hj hi
        _ = A.add (A.add i' j) k' := by simp [hk_eq, hi_eq]
    · have hk'i' : k' ≤ i' := Nat.le_of_not_ge hi'k'
      have hp : (k, i) = (k', i') := by
        simpa [Nat.min_eq_right hki, Nat.max_eq_left hki,
          Nat.min_eq_right hk'i', Nat.max_eq_left hk'i'] using hcanon
      have hk_eq : k = k' := congrArg Prod.fst hp
      have hi_eq : i = i' := congrArg Prod.snd hp
      simp [hi_eq, hk_eq]

theorem HSI.mul3_right_eq_of_canonical_eq
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k i' j' k' : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hi' : InDomain n i') (hj' : InDomain n j') (hk' : InDomain n k')
    (hcanon : (min i k, max i k) = (min i' k', max i' k')) (hjEq : j = j') :
    A.mul (A.mul i j) k = A.mul (A.mul i' j') k' := by
  subst j'
  by_cases hik : i ≤ k
  · by_cases hi'k' : i' ≤ k'
    · have hp : (i, k) = (i', k') := by
        simpa [Nat.min_eq_left hik, Nat.max_eq_right hik,
          Nat.min_eq_left hi'k', Nat.max_eq_right hi'k'] using hcanon
      cases hp
      rfl
    · have hk'i' : k' ≤ i' := Nat.le_of_not_ge hi'k'
      have hp : (i, k) = (k', i') := by
        simpa [Nat.min_eq_left hik, Nat.max_eq_right hik,
          Nat.min_eq_right hk'i', Nat.max_eq_left hk'i'] using hcanon
      have hi_eq : i = k' := congrArg Prod.fst hp
      have hk_eq : k = i' := congrArg Prod.snd hp
      have hij : InDomain n (A.mul i j) := C.mul_mem hi hj
      calc
        A.mul (A.mul i j) k
            = A.mul k (A.mul i j) := H.mul_comm hij hk
        _ = A.mul k (A.mul j i) := by rw [H.mul_comm hi hj]
        _ = A.mul (A.mul k j) i := H.mul_assoc hk hj hi
        _ = A.mul (A.mul i' j) k' := by simp [hi_eq, hk_eq]
  · have hki : k ≤ i := Nat.le_of_not_ge hik
    by_cases hi'k' : i' ≤ k'
    · have hp : (k, i) = (i', k') := by
        simpa [Nat.min_eq_right hki, Nat.max_eq_left hki,
          Nat.min_eq_left hi'k', Nat.max_eq_right hi'k'] using hcanon
      have hk_eq : k = i' := congrArg Prod.fst hp
      have hi_eq : i = k' := congrArg Prod.snd hp
      have hij : InDomain n (A.mul i j) := C.mul_mem hi hj
      calc
        A.mul (A.mul i j) k
            = A.mul k (A.mul i j) := H.mul_comm hij hk
        _ = A.mul k (A.mul j i) := by rw [H.mul_comm hi hj]
        _ = A.mul (A.mul k j) i := H.mul_assoc hk hj hi
        _ = A.mul (A.mul i' j) k' := by simp [hk_eq, hi_eq]
    · have hk'i' : k' ≤ i' := Nat.le_of_not_ge hi'k'
      have hp : (k, i) = (k', i') := by
        simpa [Nat.min_eq_right hki, Nat.max_eq_left hki,
          Nat.min_eq_right hk'i', Nat.max_eq_left hk'i'] using hcanon
      have hk_eq : k = k' := congrArg Prod.fst hp
      have hi_eq : i = i' := congrArg Prod.snd hp
      simp [hi_eq, hk_eq]

structure DecodedBy (n : Nat) (τ : Assignment) (A : Algebra) : Prop where
  add_iff :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      (A.add i j = k ↔ τ (addVar n i j k))
  mul_iff :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      (A.mul i j = k ↔ τ (mulVar n i j k))
  exp_iff :
    ∀ {i j k}, InDomain n i → InDomain n j → InDomain n k →
      (A.exp i j = k ↔ τ (expVar n i j k))

structure EncodesAlgebra (n : Nat) (τ : Assignment) (A : Algebra) : Prop where
  decoded : DecodedBy n τ A
  add2_iff :
    ∀ {i j k l}, InDomain n i → InDomain n j → InDomain n k → InDomain n l →
      (A.add i (A.add j k) = l ∧ A.add (A.add i j) k = l ↔
        τ (add2Var n i j k l))
  mul2_iff :
    ∀ {i j k l}, InDomain n i → InDomain n j → InDomain n k → InDomain n l →
      (A.mul i (A.mul j k) = l ∧ A.mul (A.mul i j) k = l ↔
        τ (mul2Var n i j k l))
  dist_iff :
    ∀ {x y z l}, InDomain n x → InDomain n y → InDomain n z → InDomain n l →
      (A.mul x (A.add y z) = l ∧ A.add (A.mul x y) (A.mul x z) = l ↔
        τ (distVar n x y z l))
  expAdd_iff :
    ∀ {x y z l}, InDomain n x → InDomain n y → InDomain n z → InDomain n l →
      (A.exp x (A.add y z) = l ∧ A.mul (A.exp x y) (A.exp x z) = l ↔
        τ (expAddVar n x y z l))
  expMul_iff :
    ∀ {x y z l}, InDomain n x → InDomain n y → InDomain n z → InDomain n l →
      (A.exp (A.mul x y) z = l ∧ A.mul (A.exp x z) (A.exp y z) = l ↔
        τ (expMulVar n x y z l))
  exp2_iff :
    ∀ {x y z l}, InDomain n x → InDomain n y → InDomain n z → InDomain n l →
      (A.exp (A.exp x y) z = l ∧ A.exp x (A.mul y z) = l ↔
        τ (exp2Var n x y z l))

theorem encodesAlgebra_yields_hsiSemantics
    {n : Nat} {τ : Assignment} {A : Algebra}
    (C : Closed n A) (H : HSI n A) (E : EncodesAlgebra n τ A) :
    HSISemantics n τ := by
  let D := E.decoded
  refine ⟨?total, ?unit, ?addAssoc, ?mulAssoc, ?dist, ?expAdd, ?expMul, ?expAssoc⟩
  · refine ⟨?addTotal, ?mulTotal, ?expTotal⟩
    · intro p hp
      have hpdom := mem_symPairs_domain hp
      let r := A.add p.1 p.2
      have hr : InDomain n r := C.add_mem hpdom.1 hpdom.2
      exact ExactlyOneVars.map_of_unique (values_nodup n) hr
        ((D.add_iff hpdom.1 hpdom.2 hr).1 rfl)
        (by
          intro k hk hτ
          exact ((D.add_iff hpdom.1 hpdom.2 hk).2 hτ).symm)
        (by
          intro x hx y hy hEq
          exact addVar_inj_value hx hy hEq)
    · intro p hp
      have hpdom := mem_symPairs_domain hp
      let r := A.mul p.1 p.2
      have hr : InDomain n r := C.mul_mem hpdom.1 hpdom.2
      exact ExactlyOneVars.map_of_unique (values_nodup n) hr
        ((D.mul_iff hpdom.1 hpdom.2 hr).1 rfl)
        (by
          intro k hk hτ
          exact ((D.mul_iff hpdom.1 hpdom.2 hk).2 hτ).symm)
        (by
          intro x hx y hy hEq
          exact mulVar_inj_value hx hy hEq)
    · intro p hp
      have hpdom := (mem_product2_iff).1 hp
      let r := A.exp p.1 p.2
      have hr : InDomain n r := C.exp_mem hpdom.1 hpdom.2
      exact ExactlyOneVars.map_of_unique (values_nodup n) hr
        ((D.exp_iff hpdom.1 hpdom.2 hr).1 rfl)
        (by
          intro k hk hτ
          exact ((D.exp_iff hpdom.1 hpdom.2 hk).2 hτ).symm)
        (by
          intro x hx y hy hEq
          exact expVar_inj_value hx hy hEq)
  · refine ⟨?mulOne, ?oneExp, ?expOne⟩
    · intro x hx
      exact (D.mul_iff hx (one_in_domain_of hx) hx).1 (H.mul_one hx)
    · intro x hx
      exact (D.exp_iff (one_in_domain_of hx) hx (one_in_domain_of hx)).1 (H.one_exp hx)
    · intro x hx
      exact (D.exp_iff hx (one_in_domain_of hx) hx).1 (H.exp_one hx)
  · intro p hp j hj
    have hpdom := mem_symPairs_domain hp
    refine ⟨?addAtMost, ?addImplications⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.add p.1 (A.add j p.2))
        (by
          intro l hl hτ
          exact ((E.add2_iff hpdom.1 hj hpdom.2 hl).2 hτ).1.symm)
        (by
          intro x hx y hy hEq
          exact add2Var_inj_value hx hy hEq)
    · intro q hq
      cases q with
      | mk l m =>
          have hqdom : (l, m) ∈ product2 (values n) (values n) := hq
          rw [mem_product2_iff] at hqdom
          constructor
          · intro hjk him
            have hjkEq : A.add j p.2 = m := (D.add_iff hj hpdom.2 hqdom.2).2 hjk
            have himEq : A.add p.1 m = l := (D.add_iff hpdom.1 hqdom.2 hqdom.1).2 him
            have leftEq : A.add p.1 (A.add j p.2) = l := by
              rw [hjkEq]
              exact himEq
            have assocEq := H.add_assoc hpdom.1 hj hpdom.2
            have rightEq : A.add (A.add p.1 j) p.2 = l := assocEq.symm.trans leftEq
            exact (E.add2_iff hpdom.1 hj hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
          · intro hij hmk
            have hijEq : A.add p.1 j = m := (D.add_iff hpdom.1 hj hqdom.2).2 hij
            have hmkEq : A.add m p.2 = l := (D.add_iff hqdom.2 hpdom.2 hqdom.1).2 hmk
            have rightEq : A.add (A.add p.1 j) p.2 = l := by
              rw [hijEq]
              exact hmkEq
            have assocEq := H.add_assoc hpdom.1 hj hpdom.2
            have leftEq : A.add p.1 (A.add j p.2) = l := assocEq.trans rightEq
            exact (E.add2_iff hpdom.1 hj hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
  · intro p hp j hj
    have hpdom := mem_symPairs_domain hp
    refine ⟨?mulAtMost, ?mulImplications⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.mul p.1 (A.mul j p.2))
        (by
          intro l hl hτ
          exact ((E.mul2_iff hpdom.1 hj hpdom.2 hl).2 hτ).1.symm)
        (by
          intro x hx y hy hEq
          exact mul2Var_inj_value hx hy hEq)
    · intro q hq
      cases q with
      | mk l m =>
          have hqdom : (l, m) ∈ product2 (values n) (values n) := hq
          rw [mem_product2_iff] at hqdom
          constructor
          · intro hjk him
            have hjkEq : A.mul j p.2 = m := (D.mul_iff hj hpdom.2 hqdom.2).2 hjk
            have himEq : A.mul p.1 m = l := (D.mul_iff hpdom.1 hqdom.2 hqdom.1).2 him
            have leftEq : A.mul p.1 (A.mul j p.2) = l := by
              rw [hjkEq]
              exact himEq
            have assocEq := H.mul_assoc hpdom.1 hj hpdom.2
            have rightEq : A.mul (A.mul p.1 j) p.2 = l := assocEq.symm.trans leftEq
            exact (E.mul2_iff hpdom.1 hj hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
          · intro hij hmk
            have hijEq : A.mul p.1 j = m := (D.mul_iff hpdom.1 hj hqdom.2).2 hij
            have hmkEq : A.mul m p.2 = l := (D.mul_iff hqdom.2 hpdom.2 hqdom.1).2 hmk
            have rightEq : A.mul (A.mul p.1 j) p.2 = l := by
              rw [hijEq]
              exact hmkEq
            have assocEq := H.mul_assoc hpdom.1 hj hpdom.2
            have leftEq : A.mul p.1 (A.mul j p.2) = l := assocEq.trans rightEq
            exact (E.mul2_iff hpdom.1 hj hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
  · intro x hx p hp
    have hpdom := mem_symPairs_domain hp
    refine ⟨?distAtMost, ?distLeftImp, ?distRightImp⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.mul x (A.add p.1 p.2))
        (by
          intro l hl hτ
          exact ((E.dist_iff hx hpdom.1 hpdom.2 hl).2 hτ).1.symm)
        (by
          intro a ha b hb hEq
          exact distVar_inj_value ha hb hEq)
    · intro q hq
      cases q with
      | mk l m =>
          have hqdom : (l, m) ∈ product2 (values n) (values n) := hq
          rw [mem_product2_iff] at hqdom
          intro hyz hxm
          have hyzEq : A.add p.1 p.2 = m := (D.add_iff hpdom.1 hpdom.2 hqdom.2).2 hyz
          have hxmEq : A.mul x m = l := (D.mul_iff hx hqdom.2 hqdom.1).2 hxm
          have leftEq : A.mul x (A.add p.1 p.2) = l := by
            rw [hyzEq]
            exact hxmEq
          have distEq := H.distrib hx hpdom.1 hpdom.2
          have rightEq : A.add (A.mul x p.1) (A.mul x p.2) = l :=
            distEq.symm.trans leftEq
          exact (E.dist_iff hx hpdom.1 hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
    · intro q hq
      cases q with
      | mk l rest =>
          cases rest with
          | mk m1 m2 =>
              have hqdom : (l, m1, m2) ∈ product3 (values n) (values n) (values n) := hq
              rw [mem_product3_iff] at hqdom
              intro hxy hxz hmadd
              have hxyEq : A.mul x p.1 = m1 := (D.mul_iff hx hpdom.1 hqdom.2.1).2 hxy
              have hxzEq : A.mul x p.2 = m2 := (D.mul_iff hx hpdom.2 hqdom.2.2).2 hxz
              have haddEq : A.add m1 m2 = l := (D.add_iff hqdom.2.1 hqdom.2.2 hqdom.1).2 hmadd
              have rightEq : A.add (A.mul x p.1) (A.mul x p.2) = l := by
                rw [hxyEq, hxzEq]
                exact haddEq
              have distEq := H.distrib hx hpdom.1 hpdom.2
              have leftEq : A.mul x (A.add p.1 p.2) = l := distEq.trans rightEq
              exact (E.dist_iff hx hpdom.1 hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
  · intro x hx p hp
    have hpdom := mem_symPairs_domain hp
    refine ⟨?expAddAtMost, ?expAddLeftImp, ?expAddRightImp⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.exp x (A.add p.1 p.2))
        (by
          intro l hl hτ
          exact ((E.expAdd_iff hx hpdom.1 hpdom.2 hl).2 hτ).1.symm)
        (by
          intro a ha b hb hEq
          exact expAddVar_inj_value ha hb hEq)
    · intro q hq
      cases q with
      | mk l m =>
          have hqdom : (l, m) ∈ product2 (values n) (values n) := hq
          rw [mem_product2_iff] at hqdom
          intro hyz hxm
          have hyzEq : A.add p.1 p.2 = m := (D.add_iff hpdom.1 hpdom.2 hqdom.2).2 hyz
          have hxmEq : A.exp x m = l := (D.exp_iff hx hqdom.2 hqdom.1).2 hxm
          have leftEq : A.exp x (A.add p.1 p.2) = l := by
            rw [hyzEq]
            exact hxmEq
          have expAddEq := H.exp_add hx hpdom.1 hpdom.2
          have rightEq : A.mul (A.exp x p.1) (A.exp x p.2) = l :=
            expAddEq.symm.trans leftEq
          exact (E.expAdd_iff hx hpdom.1 hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
    · intro q hq
      cases q with
      | mk l rest =>
          cases rest with
          | mk m1 m2 =>
              have hqdom : (l, m1, m2) ∈ product3 (values n) (values n) (values n) := hq
              rw [mem_product3_iff] at hqdom
              intro hxy hxz hmadd
              have hxyEq : A.exp x p.1 = m1 := (D.exp_iff hx hpdom.1 hqdom.2.1).2 hxy
              have hxzEq : A.exp x p.2 = m2 := (D.exp_iff hx hpdom.2 hqdom.2.2).2 hxz
              have hmulEq : A.mul m1 m2 = l := (D.mul_iff hqdom.2.1 hqdom.2.2 hqdom.1).2 hmadd
              have rightEq : A.mul (A.exp x p.1) (A.exp x p.2) = l := by
                rw [hxyEq, hxzEq]
                exact hmulEq
              have expAddEq := H.exp_add hx hpdom.1 hpdom.2
              have leftEq : A.exp x (A.add p.1 p.2) = l := expAddEq.trans rightEq
              exact (E.expAdd_iff hx hpdom.1 hpdom.2 hqdom.1).1 ⟨leftEq, rightEq⟩
  · intro p hp z hz
    have hpdom := mem_symPairs_domain hp
    refine ⟨?expMulAtMost, ?expMulLeftImp, ?expMulRightImp⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.exp (A.mul p.1 p.2) z)
        (by
          intro l hl hτ
          exact ((E.expMul_iff hpdom.1 hpdom.2 hz hl).2 hτ).1.symm)
        (by
          intro a ha b hb hEq
          exact expMulVar_inj_value ha hb hEq)
    · intro q hq
      cases q with
      | mk l m =>
          have hqdom : (l, m) ∈ product2 (values n) (values n) := hq
          rw [mem_product2_iff] at hqdom
          intro hxy hmz
          have hxyEq : A.mul p.1 p.2 = m := (D.mul_iff hpdom.1 hpdom.2 hqdom.2).2 hxy
          have hmzEq : A.exp m z = l := (D.exp_iff hqdom.2 hz hqdom.1).2 hmz
          have leftEq : A.exp (A.mul p.1 p.2) z = l := by
            rw [hxyEq]
            exact hmzEq
          have expMulEq := H.exp_mul hpdom.1 hpdom.2 hz
          have rightEq : A.mul (A.exp p.1 z) (A.exp p.2 z) = l :=
            expMulEq.symm.trans leftEq
          exact (E.expMul_iff hpdom.1 hpdom.2 hz hqdom.1).1 ⟨leftEq, rightEq⟩
    · intro q hq
      cases q with
      | mk l rest =>
          cases rest with
          | mk m1 m2 =>
              have hqdom : (l, m1, m2) ∈ product3 (values n) (values n) (values n) := hq
              rw [mem_product3_iff] at hqdom
              intro hxz hyz hmul
              have hxzEq : A.exp p.1 z = m1 := (D.exp_iff hpdom.1 hz hqdom.2.1).2 hxz
              have hyzEq : A.exp p.2 z = m2 := (D.exp_iff hpdom.2 hz hqdom.2.2).2 hyz
              have hmulEq : A.mul m1 m2 = l := (D.mul_iff hqdom.2.1 hqdom.2.2 hqdom.1).2 hmul
              have rightEq : A.mul (A.exp p.1 z) (A.exp p.2 z) = l := by
                rw [hxzEq, hyzEq]
                exact hmulEq
              have expMulEq := H.exp_mul hpdom.1 hpdom.2 hz
              have leftEq : A.exp (A.mul p.1 p.2) z = l := expMulEq.trans rightEq
              exact (E.expMul_iff hpdom.1 hpdom.2 hz hqdom.1).1 ⟨leftEq, rightEq⟩
  · intro q hq
    have hqdom := (mem_product3_iff).1 hq
    refine ⟨?expAssocAtMost, ?expAssocImplications⟩
    · exact AtMostOneVars.map_of_unique (values_nodup n)
        (r := A.exp (A.exp q.1 q.2.1) q.2.2)
        (by
          intro l hl hτ
          exact ((E.exp2_iff hqdom.1 hqdom.2.1 hqdom.2.2 hl).2 hτ).1.symm)
        (by
          intro a ha b hb hEq
          exact exp2Var_inj_value ha hb hEq)
    · intro p hp
      cases p with
      | mk l m =>
          have hpdom : (l, m) ∈ product2 (values n) (values n) := hp
          rw [mem_product2_iff] at hpdom
          constructor
          · intro hxy hmz
            have hxyEq : A.exp q.1 q.2.1 = m :=
              (D.exp_iff hqdom.1 hqdom.2.1 hpdom.2).2 hxy
            have hmzEq : A.exp m q.2.2 = l :=
              (D.exp_iff hpdom.2 hqdom.2.2 hpdom.1).2 hmz
            have leftEq : A.exp (A.exp q.1 q.2.1) q.2.2 = l := by
              rw [hxyEq]
              exact hmzEq
            have assocEq := H.exp_assoc hqdom.1 hqdom.2.1 hqdom.2.2
            have rightEq : A.exp q.1 (A.mul q.2.1 q.2.2) = l :=
              assocEq.symm.trans leftEq
            exact (E.exp2_iff hqdom.1 hqdom.2.1 hqdom.2.2 hpdom.1).1 ⟨leftEq, rightEq⟩
          · intro hyz hxm
            have hyzEq : A.mul q.2.1 q.2.2 = m :=
              (D.mul_iff hqdom.2.1 hqdom.2.2 hpdom.2).2 hyz
            have hxmEq : A.exp q.1 m = l :=
              (D.exp_iff hqdom.1 hpdom.2 hpdom.1).2 hxm
            have rightEq : A.exp q.1 (A.mul q.2.1 q.2.2) = l := by
              rw [hyzEq]
              exact hxmEq
            have assocEq := H.exp_assoc hqdom.1 hqdom.2.1 hqdom.2.2
            have leftEq : A.exp (A.exp q.1 q.2.1) q.2.2 = l :=
              assocEq.trans rightEq
            exact (E.exp2_iff hqdom.1 hqdom.2.1 hqdom.2.2 hpdom.1).1 ⟨leftEq, rightEq⟩

theorem DecodedBy.op_iff
    {n : Nat} {τ : Assignment} {A : Algebra} (D : DecodedBy n τ A)
    {op : Op} {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    (evalOp A op i j = k ↔ τ (opVar n op i j k)) := by
  cases op <;> simp [evalOp, opVar]
  · exact D.add_iff hi hj hk
  · exact D.mul_iff hi hj hk
  · exact D.exp_iff hi hj hk

theorem decodedAlgebra_closed_decoded
    {n : Nat} {τ : Assignment} (T : OperationTotalitySemantics n τ) :
    Closed n (decodedAlgebra n τ) ∧ DecodedBy n τ (decodedAlgebra n τ) := by
  constructor
  · constructor
    · intro i j hi hj
      have hp := symPair_mem_of_domain hi hj
      have hexact := T.1 (min i j, max i j) hp
      have hExists := exists_value_of_exact_mapped hexact
      simpa [decodedAlgebra] using
        (selectValue_spec (n := n) (τ := τ)
          (f := fun k => addVar n (min i j) (max i j) k) hExists).1
    · intro i j hi hj
      have hp := symPair_mem_of_domain hi hj
      have hexact := T.2.1 (min i j, max i j) hp
      have hExists := exists_value_of_exact_mapped hexact
      simpa [decodedAlgebra] using
        (selectValue_spec (n := n) (τ := τ)
          (f := fun k => mulVar n (min i j) (max i j) k) hExists).1
    · intro i j hi hj
      have hp : (i, j) ∈ product2 (values n) (values n) := by
        rw [mem_product2_iff]
        exact ⟨hi, hj⟩
      have hexact := T.2.2 (i, j) hp
      have hExists := exists_value_of_exact_mapped hexact
      simpa [decodedAlgebra] using
        (selectValue_spec (n := n) (τ := τ)
          (f := fun k => expVar n i j k) hExists).1
  · constructor
    · intro i j k hi hj hk
      have hp := symPair_mem_of_domain hi hj
      have hexact := T.1 (min i j, max i j) hp
      have hiff := selectValue_eq_iff
        (n := n) (τ := τ)
        (f := fun r => addVar n (min i j) (max i j) r)
        hexact
        (by
          intro a b ha hb h
          exact addVar_inj_value ha hb h)
        hk
      simpa [decodedAlgebra, addVar_canon] using hiff
    · intro i j k hi hj hk
      have hp := symPair_mem_of_domain hi hj
      have hexact := T.2.1 (min i j, max i j) hp
      have hiff := selectValue_eq_iff
        (n := n) (τ := τ)
        (f := fun r => mulVar n (min i j) (max i j) r)
        hexact
        (by
          intro a b ha hb h
          exact mulVar_inj_value ha hb h)
        hk
      simpa [decodedAlgebra, mulVar_canon] using hiff
    · intro i j k hi hj hk
      have hp : (i, j) ∈ product2 (values n) (values n) := by
        rw [mem_product2_iff]
        exact ⟨hi, hj⟩
      have hexact := T.2.2 (i, j) hp
      have hiff := selectValue_eq_iff
        (n := n) (τ := τ)
        (f := fun r => expVar n i j r)
        hexact
        (by
          intro a b ha hb h
          exact expVar_inj_value ha hb h)
        hk
      simpa [decodedAlgebra] using hiff

theorem DecodedBy.mul_one
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (U : UnitIdentitySemantics n τ)
    {i : Nat} (hi : InDomain n i) :
    A.mul i 1 = i := by
  exact (D.mul_iff hi (one_in_domain_of hi) hi).2 (U.1 i hi)

theorem DecodedBy.one_exp
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (U : UnitIdentitySemantics n τ)
    {i : Nat} (hi : InDomain n i) :
    A.exp 1 i = 1 := by
  exact (D.exp_iff (one_in_domain_of hi) hi (one_in_domain_of hi)).2 (U.2.1 i hi)

theorem DecodedBy.exp_one
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (U : UnitIdentitySemantics n τ)
    {i : Nat} (hi : InDomain n i) :
    A.exp i 1 = i := by
  exact (D.exp_iff hi (one_in_domain_of hi) hi).2 (U.2.2 i hi)

theorem DecodedBy.add_comm
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A)
    {i j : Nat} (hi : InDomain n i) (hj : InDomain n j) :
    A.add i j = A.add j i := by
  let r := A.add i j
  have hr : InDomain n r := C.add_mem hi hj
  have hτ : τ (addVar n i j r) := (D.add_iff hi hj hr).1 rfl
  have hτ' : τ (addVar n j i r) := by
    simpa [addVar_comm] using hτ
  exact ((D.add_iff hj hi hr).2 hτ').symm

theorem DecodedBy.mul_comm
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A)
    {i j : Nat} (hi : InDomain n i) (hj : InDomain n j) :
    A.mul i j = A.mul j i := by
  let r := A.mul i j
  have hr : InDomain n r := C.mul_mem hi hj
  have hτ : τ (mulVar n i j r) := (D.mul_iff hi hj hr).1 rfl
  have hτ' : τ (mulVar n j i r) := by
    simpa [mulVar_comm] using hτ
  exact ((D.mul_iff hj hi hr).2 hτ').symm

theorem DecodedBy.add_assoc_canonical
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : AddAssocSemantics n τ)
    {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hp : (i, k) ∈ symPairs n) :
    A.add i (A.add j k) = A.add (A.add i j) k := by
  let mLeft := A.add j k
  have hmLeft : InDomain n mLeft := C.add_mem hj hk
  let lLeft := A.add i mLeft
  have hlLeft : InDomain n lLeft := C.add_mem hi hmLeft
  let mRight := A.add i j
  have hmRight : InDomain n mRight := C.add_mem hi hj
  let lRight := A.add mRight k
  have hlRight : InDomain n lRight := C.add_mem hmRight hk
  have inner := S (i, k) hp j hj
  have hLeftAux : τ (add2Var n i j k lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact (inner.2 (lLeft, mLeft) hq).1
      ((D.add_iff hj hk hmLeft).1 rfl)
      ((D.add_iff hi hmLeft hlLeft).1 rfl)
  have hRightAux : τ (add2Var n i j k lRight) := by
    have hq : (lRight, mRight) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlRight, hmRight⟩
    exact (inner.2 (lRight, mRight) hq).2
      ((D.add_iff hi hj hmRight).1 rfl)
      ((D.add_iff hmRight hk hlRight).1 rfl)
  have hVarEq :
      add2Var n i j k lLeft = add2Var n i j k lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact add2Var_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.add_assoc
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : AddAssocSemantics n τ)
    {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    A.add i (A.add j k) = A.add (A.add i j) k := by
  by_cases hik : i ≤ k
  · exact D.add_assoc_canonical C S hi hj hk
      (symPair_mem_of_domain_ordered hi hk hik)
  · have hki : k ≤ i := Nat.le_of_not_ge hik
    have hcanon := D.add_assoc_canonical C S hk hj hi
      (symPair_mem_of_domain_ordered hk hi hki)
    have hkj : InDomain n (A.add k j) := C.add_mem hk hj
    have hij : InDomain n (A.add i j) := C.add_mem hi hj
    have hji : InDomain n (A.add j i) := C.add_mem hj hi
    calc
      A.add i (A.add j k)
          = A.add i (A.add k j) := by
              rw [D.add_comm C hj hk]
      _ = A.add (A.add k j) i := by
              exact D.add_comm C hi hkj
      _ = A.add k (A.add j i) := by
              exact hcanon.symm
      _ = A.add k (A.add i j) := by
              rw [D.add_comm C hi hj]
      _ = A.add (A.add i j) k := by
              exact (D.add_comm C hij hk).symm

theorem DecodedBy.mul_assoc_canonical
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : MulAssocSemantics n τ)
    {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k)
    (hp : (i, k) ∈ symPairs n) :
    A.mul i (A.mul j k) = A.mul (A.mul i j) k := by
  let mLeft := A.mul j k
  have hmLeft : InDomain n mLeft := C.mul_mem hj hk
  let lLeft := A.mul i mLeft
  have hlLeft : InDomain n lLeft := C.mul_mem hi hmLeft
  let mRight := A.mul i j
  have hmRight : InDomain n mRight := C.mul_mem hi hj
  let lRight := A.mul mRight k
  have hlRight : InDomain n lRight := C.mul_mem hmRight hk
  have inner := S (i, k) hp j hj
  have hLeftAux : τ (mul2Var n i j k lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact (inner.2 (lLeft, mLeft) hq).1
      ((D.mul_iff hj hk hmLeft).1 rfl)
      ((D.mul_iff hi hmLeft hlLeft).1 rfl)
  have hRightAux : τ (mul2Var n i j k lRight) := by
    have hq : (lRight, mRight) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlRight, hmRight⟩
    exact (inner.2 (lRight, mRight) hq).2
      ((D.mul_iff hi hj hmRight).1 rfl)
      ((D.mul_iff hmRight hk hlRight).1 rfl)
  have hVarEq :
      mul2Var n i j k lLeft = mul2Var n i j k lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact mul2Var_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.mul_assoc
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : MulAssocSemantics n τ)
    {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    A.mul i (A.mul j k) = A.mul (A.mul i j) k := by
  by_cases hik : i ≤ k
  · exact D.mul_assoc_canonical C S hi hj hk
      (symPair_mem_of_domain_ordered hi hk hik)
  · have hki : k ≤ i := Nat.le_of_not_ge hik
    have hcanon := D.mul_assoc_canonical C S hk hj hi
      (symPair_mem_of_domain_ordered hk hi hki)
    have hkj : InDomain n (A.mul k j) := C.mul_mem hk hj
    have hij : InDomain n (A.mul i j) := C.mul_mem hi hj
    calc
      A.mul i (A.mul j k)
          = A.mul i (A.mul k j) := by
              rw [D.mul_comm C hj hk]
      _ = A.mul (A.mul k j) i := by
              exact D.mul_comm C hi hkj
      _ = A.mul k (A.mul j i) := by
              exact hcanon.symm
      _ = A.mul k (A.mul i j) := by
              rw [D.mul_comm C hi hj]
      _ = A.mul (A.mul i j) k := by
              exact (D.mul_comm C hij hk).symm

theorem DecodedBy.distrib_canonical
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : DistSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z)
    (hp : (y, z) ∈ symPairs n) :
    A.mul x (A.add y z) = A.add (A.mul x y) (A.mul x z) := by
  let mLeft := A.add y z
  have hmLeft : InDomain n mLeft := C.add_mem hy hz
  let lLeft := A.mul x mLeft
  have hlLeft : InDomain n lLeft := C.mul_mem hx hmLeft
  let m1 := A.mul x y
  have hm1 : InDomain n m1 := C.mul_mem hx hy
  let m2 := A.mul x z
  have hm2 : InDomain n m2 := C.mul_mem hx hz
  let lRight := A.add m1 m2
  have hlRight : InDomain n lRight := C.add_mem hm1 hm2
  have inner := S x hx (y, z) hp
  have hLeftAux : τ (distVar n x y z lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact inner.2.1 (lLeft, mLeft) hq
      ((D.add_iff hy hz hmLeft).1 rfl)
      ((D.mul_iff hx hmLeft hlLeft).1 rfl)
  have hRightAux : τ (distVar n x y z lRight) := by
    have hq : (lRight, m1, m2) ∈ product3 (values n) (values n) (values n) := by
      rw [mem_product3_iff]
      exact ⟨hlRight, hm1, hm2⟩
    exact inner.2.2 (lRight, m1, m2) hq
      ((D.mul_iff hx hy hm1).1 rfl)
      ((D.mul_iff hx hz hm2).1 rfl)
      ((D.add_iff hm1 hm2 hlRight).1 rfl)
  have hVarEq :
      distVar n x y z lLeft = distVar n x y z lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact distVar_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.distrib
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : DistSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    A.mul x (A.add y z) = A.add (A.mul x y) (A.mul x z) := by
  by_cases hyz : y ≤ z
  · exact D.distrib_canonical C S hx hy hz
      (symPair_mem_of_domain_ordered hy hz hyz)
  · have hzy : z ≤ y := Nat.le_of_not_ge hyz
    have hcanon := D.distrib_canonical C S hx hz hy
      (symPair_mem_of_domain_ordered hz hy hzy)
    have hxy : InDomain n (A.mul x y) := C.mul_mem hx hy
    have hxz : InDomain n (A.mul x z) := C.mul_mem hx hz
    calc
      A.mul x (A.add y z)
          = A.mul x (A.add z y) := by
              rw [D.add_comm C hy hz]
      _ = A.add (A.mul x z) (A.mul x y) := hcanon
      _ = A.add (A.mul x y) (A.mul x z) := by
              exact D.add_comm C hxz hxy

theorem DecodedBy.exp_add_canonical
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : ExpAddSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z)
    (hp : (y, z) ∈ symPairs n) :
    A.exp x (A.add y z) = A.mul (A.exp x y) (A.exp x z) := by
  let mLeft := A.add y z
  have hmLeft : InDomain n mLeft := C.add_mem hy hz
  let lLeft := A.exp x mLeft
  have hlLeft : InDomain n lLeft := C.exp_mem hx hmLeft
  let m1 := A.exp x y
  have hm1 : InDomain n m1 := C.exp_mem hx hy
  let m2 := A.exp x z
  have hm2 : InDomain n m2 := C.exp_mem hx hz
  let lRight := A.mul m1 m2
  have hlRight : InDomain n lRight := C.mul_mem hm1 hm2
  have inner := S x hx (y, z) hp
  have hLeftAux : τ (expAddVar n x y z lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact inner.2.1 (lLeft, mLeft) hq
      ((D.add_iff hy hz hmLeft).1 rfl)
      ((D.exp_iff hx hmLeft hlLeft).1 rfl)
  have hRightAux : τ (expAddVar n x y z lRight) := by
    have hq : (lRight, m1, m2) ∈ product3 (values n) (values n) (values n) := by
      rw [mem_product3_iff]
      exact ⟨hlRight, hm1, hm2⟩
    exact inner.2.2 (lRight, m1, m2) hq
      ((D.exp_iff hx hy hm1).1 rfl)
      ((D.exp_iff hx hz hm2).1 rfl)
      ((D.mul_iff hm1 hm2 hlRight).1 rfl)
  have hVarEq :
      expAddVar n x y z lLeft = expAddVar n x y z lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact expAddVar_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.exp_add
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : ExpAddSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    A.exp x (A.add y z) = A.mul (A.exp x y) (A.exp x z) := by
  by_cases hyz : y ≤ z
  · exact D.exp_add_canonical C S hx hy hz
      (symPair_mem_of_domain_ordered hy hz hyz)
  · have hzy : z ≤ y := Nat.le_of_not_ge hyz
    have hcanon := D.exp_add_canonical C S hx hz hy
      (symPair_mem_of_domain_ordered hz hy hzy)
    have hxy : InDomain n (A.exp x y) := C.exp_mem hx hy
    have hxz : InDomain n (A.exp x z) := C.exp_mem hx hz
    calc
      A.exp x (A.add y z)
          = A.exp x (A.add z y) := by
              rw [D.add_comm C hy hz]
      _ = A.mul (A.exp x z) (A.exp x y) := hcanon
      _ = A.mul (A.exp x y) (A.exp x z) := by
              exact D.mul_comm C hxz hxy

theorem DecodedBy.exp_mul_canonical
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : ExpMulSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z)
    (hp : (x, y) ∈ symPairs n) :
    A.exp (A.mul x y) z = A.mul (A.exp x z) (A.exp y z) := by
  let mLeft := A.mul x y
  have hmLeft : InDomain n mLeft := C.mul_mem hx hy
  let lLeft := A.exp mLeft z
  have hlLeft : InDomain n lLeft := C.exp_mem hmLeft hz
  let m1 := A.exp x z
  have hm1 : InDomain n m1 := C.exp_mem hx hz
  let m2 := A.exp y z
  have hm2 : InDomain n m2 := C.exp_mem hy hz
  let lRight := A.mul m1 m2
  have hlRight : InDomain n lRight := C.mul_mem hm1 hm2
  have inner := S (x, y) hp z hz
  have hLeftAux : τ (expMulVar n x y z lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact inner.2.1 (lLeft, mLeft) hq
      ((D.mul_iff hx hy hmLeft).1 rfl)
      ((D.exp_iff hmLeft hz hlLeft).1 rfl)
  have hRightAux : τ (expMulVar n x y z lRight) := by
    have hq : (lRight, m1, m2) ∈ product3 (values n) (values n) (values n) := by
      rw [mem_product3_iff]
      exact ⟨hlRight, hm1, hm2⟩
    exact inner.2.2 (lRight, m1, m2) hq
      ((D.exp_iff hx hz hm1).1 rfl)
      ((D.exp_iff hy hz hm2).1 rfl)
      ((D.mul_iff hm1 hm2 hlRight).1 rfl)
  have hVarEq :
      expMulVar n x y z lLeft = expMulVar n x y z lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact expMulVar_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.exp_mul
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : ExpMulSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    A.exp (A.mul x y) z = A.mul (A.exp x z) (A.exp y z) := by
  by_cases hxy : x ≤ y
  · exact D.exp_mul_canonical C S hx hy hz
      (symPair_mem_of_domain_ordered hx hy hxy)
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    have hcanon := D.exp_mul_canonical C S hy hx hz
      (symPair_mem_of_domain_ordered hy hx hyx)
    have hxz : InDomain n (A.exp x z) := C.exp_mem hx hz
    have hyz : InDomain n (A.exp y z) := C.exp_mem hy hz
    calc
      A.exp (A.mul x y) z
          = A.exp (A.mul y x) z := by
              rw [D.mul_comm C hx hy]
      _ = A.mul (A.exp y z) (A.exp x z) := hcanon
      _ = A.mul (A.exp x z) (A.exp y z) := by
              exact D.mul_comm C hyz hxz

theorem DecodedBy.exp_assoc
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A) (S : ExpAssocSemantics n τ)
    {x y z : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    A.exp (A.exp x y) z = A.exp x (A.mul y z) := by
  let mLeft := A.exp x y
  have hmLeft : InDomain n mLeft := C.exp_mem hx hy
  let lLeft := A.exp mLeft z
  have hlLeft : InDomain n lLeft := C.exp_mem hmLeft hz
  let mRight := A.mul y z
  have hmRight : InDomain n mRight := C.mul_mem hy hz
  let lRight := A.exp x mRight
  have hlRight : InDomain n lRight := C.exp_mem hx hmRight
  have hqOuter : (x, y, z) ∈ product3 (values n) (values n) (values n) := by
    rw [mem_product3_iff]
    exact ⟨hx, hy, hz⟩
  have inner := S (x, y, z) hqOuter
  have hLeftAux : τ (exp2Var n x y z lLeft) := by
    have hq : (lLeft, mLeft) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlLeft, hmLeft⟩
    exact (inner.2 (lLeft, mLeft) hq).1
      ((D.exp_iff hx hy hmLeft).1 rfl)
      ((D.exp_iff hmLeft hz hlLeft).1 rfl)
  have hRightAux : τ (exp2Var n x y z lRight) := by
    have hq : (lRight, mRight) ∈ product2 (values n) (values n) := by
      rw [mem_product2_iff]
      exact ⟨hlRight, hmRight⟩
    exact (inner.2 (lRight, mRight) hq).2
      ((D.mul_iff hy hz hmRight).1 rfl)
      ((D.exp_iff hx hmRight hlRight).1 rfl)
  have hVarEq :
      exp2Var n x y z lLeft = exp2Var n x y z lRight := by
    exact inner.1.unique
      (List.mem_map.mpr ⟨lLeft, hlLeft, rfl⟩)
      (List.mem_map.mpr ⟨lRight, hlRight, rfl⟩)
      hLeftAux hRightAux
  exact exp2Var_inj_value hlLeft hlRight hVarEq

theorem DecodedBy.hsi
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A)
    (U : UnitIdentitySemantics n τ)
    (AS : AddAssocSemantics n τ) (MS : MulAssocSemantics n τ)
    (DS : DistSemantics n τ)
    (EAS : ExpAddSemantics n τ) (EMS : ExpMulSemantics n τ)
    (ES : ExpAssocSemantics n τ) :
    HSI n A where
  add_comm hi hj := D.add_comm C hi hj
  add_assoc hi hj hk := D.add_assoc C AS hi hj hk
  mul_one hi := D.mul_one U hi
  mul_comm hi hj := D.mul_comm C hi hj
  mul_assoc hi hj hk := D.mul_assoc C MS hi hj hk
  distrib hi hj hk := D.distrib C DS hi hj hk
  one_exp hi := D.one_exp U hi
  exp_one hi := D.exp_one U hi
  exp_add hi hj hk := D.exp_add C EAS hi hj hk
  exp_mul hi hj hk := D.exp_mul C EMS hi hj hk
  exp_assoc hi hj hk := D.exp_assoc C ES hi hj hk

def x2 (A : Algebra) (z : Nat) : Nat :=
  A.mul z z

def x3 (A : Algebra) (z : Nat) : Nat :=
  A.mul (x2 A z) z

def x4 (A : Algebra) (z : Nat) : Nat :=
  A.mul (x3 A z) z

def wilkieP (A : Algebra) (x y z : Nat) : Nat :=
  let one_z := A.add 1 z
  let one_z_z2 := A.add one_z (x2 A z)
  let one_z3 := A.add 1 (x3 A z)
  let one_z2 := A.add 1 (x2 A z)
  let one_z2_z4 := A.add one_z2 (x4 A z)
  let first := A.add (A.exp one_z y) (A.exp one_z_z2 y)
  let second := A.add (A.exp one_z3 x) (A.exp one_z2_z4 x)
  A.mul (A.exp first x) (A.exp second y)

def WilkieFailsAt (A : Algebra) (x y z : Nat) : Prop :=
  wilkieP A x y z ≠ wilkieP A y x z

def Pterm (A : Algebra) (x : Nat) : Nat :=
  A.add 1 x

def Qterm (A : Algebra) (x : Nat) : Nat :=
  A.add (Pterm A x) (x2 A x)

def Rterm (A : Algebra) (x : Nat) : Nat :=
  A.add 1 (x3 A x)

def Sterm (A : Algebra) (x : Nat) : Nat :=
  A.add (A.add 1 (x2 A x)) (x4 A x)

theorem pqrs_terms_mem_of_closed
    {n : Nat} {A : Algebra} (C : Closed n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) :
    InDomain n (Pterm A x) ∧ InDomain n (Qterm A x) ∧
      InDomain n (Rterm A x) ∧ InDomain n (Sterm A x) := by
  have hx2 : InDomain n (x2 A x) := by
    unfold x2
    exact C.mul_mem hx hx
  have hx3 : InDomain n (x3 A x) := by
    unfold x3
    exact C.mul_mem hx2 hx
  have hx4 : InDomain n (x4 A x) := by
    unfold x4
    exact C.mul_mem hx3 hx
  have hP : InDomain n (Pterm A x) := by
    unfold Pterm
    exact C.add_mem h1 hx
  have hQ : InDomain n (Qterm A x) := by
    unfold Qterm
    exact C.add_mem hP hx2
  have hR : InDomain n (Rterm A x) := by
    unfold Rterm
    exact C.add_mem h1 hx3
  have hS : InDomain n (Sterm A x) := by
    unfold Sterm
    exact C.add_mem (C.add_mem h1 hx2) hx4
  exact ⟨hP, hQ, hR, hS⟩

theorem wilkie_factor_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (mul_one : ∀ a, mul a one = a)
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)) :
    let x2 := mul x x
    let x3 := mul x2 x
    let x4 := mul x3 x
    mul (add one x) (add (add one x2) x4) =
      mul (add (add one x) x2) (add one x3) := by
  intro x2 x3 x4
  have distrib_left : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c) := by
    intro a b c
    calc
      mul (add a b) c = mul c (add a b) := Std.Commutative.comm ..
      _ = add (mul c a) (mul c b) := distrib c a b
      _ = add (mul a c) (mul b c) := by ac_rfl
  have one_mul : ∀ a, mul one a = a := by
    intro a
    calc
      mul one a = mul a one := Std.Commutative.comm ..
      _ = a := mul_one a
  repeat rw [distrib]
  repeat rw [distrib_left]
  repeat rw [mul_one]
  repeat rw [one_mul]
  have hxx2 : mul x x2 = x3 := by
    dsimp [x2, x3]
    ac_rfl
  have hxx3 : mul x x3 = x4 := by
    dsimp [x3, x4]
    ac_rfl
  have hxx4 : mul x x4 = mul x2 x3 := by
    dsimp [x2, x3, x4]
    ac_rfl
  rw [hxx2, hxx3, hxx4]
  ac_rfl

theorem wilkie_factor_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) :
    A.mul (Pterm A x) (Sterm A x) =
      A.mul (Qterm A x) (Rterm A x) := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨x, hx⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := wilkie_factor_generic (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
  simpa [Pterm, Qterm, Rterm, Sterm, x2, x3, x4, addD, mulD, oneD, xD]
    using congrArg Subtype.val hD

theorem lee_sum_factor_generic
    {α : Type} (add mul exp : α → α → α) (one p t e : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (mul_one : ∀ a, mul a one = a) :
    add (exp p e) (exp (mul p t) e) =
      mul (exp p e) (add one (exp t e)) := by
  rw [exp_mul]
  calc
    add (exp p e) (mul (exp p e) (exp t e))
        = add (mul (exp p e) one) (mul (exp p e) (exp t e)) := by
          rw [mul_one]
    _ = mul (exp p e) (add one (exp t e)) := (distrib (exp p e) one (exp t e)).symm

theorem lee_product_sum_factor_generic
    {α : Type} (add mul exp : α → α → α) (one p r s t e : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (mul_one : ∀ a, mul a one = a)
    (hfactor : mul p s = mul (mul p t) r) :
    mul (exp p e) (add (exp r e) (exp s e)) =
      mul (exp r e) (mul (exp p e) (add one (exp t e))) := by
  have distrib_left : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c) := by
    intro a b c
    calc
      mul (add a b) c = mul c (add a b) := Std.Commutative.comm ..
      _ = add (mul c a) (mul c b) := distrib c a b
      _ = add (mul a c) (mul b c) := by ac_rfl
  have one_mul : ∀ a, mul one a = a := by
    intro a
    calc
      mul one a = mul a one := Std.Commutative.comm ..
      _ = a := mul_one a
  calc
    mul (exp p e) (add (exp r e) (exp s e))
        = add (mul (exp p e) (exp r e)) (mul (exp p e) (exp s e)) := distrib _ _ _
    _ = add (mul (exp p e) (exp r e)) (exp (mul (mul p t) r) e) := by
          rw [← exp_mul p s e, hfactor]
    _ = mul (exp r e) (mul (exp p e) (add one (exp t e))) := by
          rw [exp_mul, exp_mul]
          repeat rw [distrib]
          repeat rw [distrib_left]
          repeat rw [mul_one]
          repeat rw [one_mul]
          ac_rfl

theorem lee_product_sum_factor_exp_generic
    {α : Type} (add mul exp : α → α → α) (one p r s t e f : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    (mul_one : ∀ a, mul a one = a)
    (hfactor : mul p s = mul (mul p t) r) :
    mul (exp p (mul e f)) (exp (add (exp r e) (exp s e)) f) =
      mul (exp r (mul e f))
        (mul (exp p (mul e f)) (exp (add one (exp t e)) f)) := by
  have h := congrArg (fun z => exp z f)
    (lee_product_sum_factor_generic add mul exp one p r s t e
      distrib exp_mul mul_one hfactor)
  change exp (mul (exp p e) (add (exp r e) (exp s e))) f =
      exp (mul (exp r e) (mul (exp p e) (add one (exp t e)))) f at h
  repeat rw [exp_mul] at h
  repeat rw [exp_assoc] at h
  exact h

theorem lee_divisibility_generic
    {α : Type} (add mul exp : α → α → α) (one p q r s t x y : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    (mul_one : ∀ a, mul a one = a)
    (hq : q = mul p t)
    (hfactor : mul p s = mul q r) :
    mul (exp (add (exp p y) (exp q y)) x)
      (exp (add (exp r x) (exp s x)) y) =
    mul (exp (add (exp p x) (exp q x)) y)
      (exp (add (exp r y) (exp s y)) x) := by
  subst q
  have hfactor' : mul p s = mul (mul p t) r := hfactor
  rw [lee_sum_factor_generic add mul exp one p t y distrib exp_mul mul_one]
  rw [lee_sum_factor_generic add mul exp one p t x distrib exp_mul mul_one]
  repeat rw [exp_mul]
  repeat rw [exp_assoc]
  have hBx := lee_product_sum_factor_exp_generic add mul exp one p r s t x y
    distrib exp_mul exp_assoc mul_one hfactor'
  have hBy := lee_product_sum_factor_exp_generic add mul exp one p r s t y x
    distrib exp_mul exp_assoc mul_one hfactor'
  calc
    mul (mul (exp p (mul y x)) (exp (add one (exp t y)) x))
        (exp (add (exp r x) (exp s x)) y)
        = mul (exp (add one (exp t y)) x)
            (mul (exp p (mul x y)) (exp (add (exp r x) (exp s x)) y)) := by
              have hxy : mul y x = mul x y := Std.Commutative.comm ..
              rw [hxy]
              ac_rfl
    _ = mul (exp (add one (exp t y)) x)
          (mul (exp r (mul x y))
            (mul (exp p (mul x y)) (exp (add one (exp t x)) y))) := by
              rw [hBx]
    _ = mul (exp (add one (exp t x)) y)
          (mul (exp r (mul y x))
            (mul (exp p (mul y x)) (exp (add one (exp t y)) x))) := by
              have hxy : mul x y = mul y x := Std.Commutative.comm ..
              rw [hxy]
              ac_rfl
    _ = mul (mul (exp p (mul x y)) (exp (add one (exp t x)) y))
          (exp (add (exp r y) (exp s y)) x) := by
              have hBySym := hBy.symm
              rw [hBySym]
              have hxy : mul y x = mul x y := Std.Commutative.comm ..
              rw [hxy]
              ac_rfl

def wilkieCore (A : Algebra) (p q r s x y : Nat) : Nat :=
  A.mul
    (A.exp (A.add (A.exp p y) (A.exp q y)) x)
    (A.exp (A.add (A.exp r x) (A.exp s x)) y)

theorem wilkieCore_swap_pairs_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s x y : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x) (hy : InDomain n y) :
    wilkieCore A q p s r x y = wilkieCore A p q r s x y := by
  unfold wilkieCore
  rw [H.add_comm (C.exp_mem hq hy) (C.exp_mem hp hy)]
  rw [H.add_comm (C.exp_mem hs hx) (C.exp_mem hr hx)]

theorem wilkieCore_exchange_pairs_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s x y : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x) (hy : InDomain n y) :
    wilkieCore A r s p q x y = wilkieCore A p q r s y x := by
  unfold wilkieCore
  exact H.mul_comm
    (C.exp_mem (C.add_mem (C.exp_mem hr hy) (C.exp_mem hs hy)) hx)
    (C.exp_mem (C.add_mem (C.exp_mem hp hx) (C.exp_mem hq hx)) hy)

theorem lee_divisibility_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s t x y : Nat}
    (h1 : InDomain n 1)
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (ht : InDomain n t) (hx : InDomain n x) (hy : InDomain n y)
    (hdiv : q = A.mul p t)
    (hfactor : A.mul p s = A.mul q r) :
    wilkieCore A p q r s x y = wilkieCore A p q r s y x := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let pD : D := ⟨p, hp⟩
  let qD : D := ⟨q, hq⟩
  let rD : D := ⟨r, hr⟩
  let sD : D := ⟨s, hs⟩
  let tD : D := ⟨t, ht⟩
  let xD : D := ⟨x, hx⟩
  let yD : D := ⟨y, hy⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := lee_divisibility_generic
    (add := addD) (mul := mulD) (exp := expD) (one := oneD)
    (p := pD) (q := qD) (r := rD) (s := sD) (t := tD)
    (x := xD) (y := yD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_assoc := by
      intro a b c
      apply Subtype.ext
      exact H.exp_assoc a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (hq := by
      apply Subtype.ext
      exact hdiv)
    (hfactor := by
      apply Subtype.ext
      exact hfactor)
  simpa [wilkieCore, addD, mulD, expD, oneD, pD, qD, rD, sD, tD, xD, yD]
    using congrArg Subtype.val hD

theorem lee_q_eq_p_mul_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {v : Nat} (hv : InDomain n v)
    (hdiv : A.mul (Pterm A 4) v = Qterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 h4
  have hcore := lee_divisibility_hsi C H h1 hP hQ hR hS hv h4 h5
    hdiv.symm hfactor
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem lee_p_eq_q_mul_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {v : Nat} (hv : InDomain n v)
    (hdiv : A.mul (Qterm A 4) v = Pterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 h4
  have hcore := lee_divisibility_hsi C H h1 hQ hP hS hR hv h4 h5
    hdiv.symm hfactor.symm
  have hleft := wilkieCore_swap_pairs_hsi C H hP hQ hR hS h4 h5
  have hright := wilkieCore_swap_pairs_hsi C H hP hQ hR hS h5 h4
  have hmain :
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 =
        wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := by
    calc
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5
          = wilkieCore A (Qterm A 4) (Pterm A 4) (Sterm A 4) (Rterm A 4) 4 5 := hleft.symm
      _ = wilkieCore A (Qterm A 4) (Pterm A 4) (Sterm A 4) (Rterm A 4) 5 4 := hcore
      _ = wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := hright
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem lee_s_eq_r_mul_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {v : Nat} (hv : InDomain n v)
    (hdiv : A.mul (Rterm A 4) v = Sterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor0 := wilkie_factor_hsi C H h1 h4
  have hfactor : A.mul (Rterm A 4) (Qterm A 4) = A.mul (Sterm A 4) (Pterm A 4) := by
    calc
      A.mul (Rterm A 4) (Qterm A 4) = A.mul (Qterm A 4) (Rterm A 4) := H.mul_comm hR hQ
      _ = A.mul (Pterm A 4) (Sterm A 4) := hfactor0.symm
      _ = A.mul (Sterm A 4) (Pterm A 4) := H.mul_comm hP hS
  have hcore := lee_divisibility_hsi C H h1 hR hS hP hQ hv h4 h5
    hdiv.symm hfactor
  have hx := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS h4 h5
  have hy := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS h5 h4
  have hmain :
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 =
        wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := by
    calc
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5
          = wilkieCore A (Rterm A 4) (Sterm A 4) (Pterm A 4) (Qterm A 4) 5 4 := hy.symm
      _ = wilkieCore A (Rterm A 4) (Sterm A 4) (Pterm A 4) (Qterm A 4) 4 5 := hcore.symm
      _ = wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := hx
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem lee_r_eq_s_mul_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {v : Nat} (hv : InDomain n v)
    (hdiv : A.mul (Sterm A 4) v = Rterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor0 := wilkie_factor_hsi C H h1 h4
  have hfactor : A.mul (Sterm A 4) (Pterm A 4) = A.mul (Rterm A 4) (Qterm A 4) := by
    calc
      A.mul (Sterm A 4) (Pterm A 4) = A.mul (Pterm A 4) (Sterm A 4) := H.mul_comm hS hP
      _ = A.mul (Qterm A 4) (Rterm A 4) := hfactor0
      _ = A.mul (Rterm A 4) (Qterm A 4) := H.mul_comm hQ hR
  have hcore := lee_divisibility_hsi C H h1 hS hR hQ hP hv h4 h5
    hdiv.symm hfactor
  have hswapx := wilkieCore_swap_pairs_hsi C H hR hS hP hQ h4 h5
  have hswapy := wilkieCore_swap_pairs_hsi C H hR hS hP hQ h5 h4
  have hx := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS h4 h5
  have hy := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS h5 h4
  have hmain :
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 =
        wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := by
    calc
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5
          = wilkieCore A (Rterm A 4) (Sterm A 4) (Pterm A 4) (Qterm A 4) 5 4 := hy.symm
      _ = wilkieCore A (Sterm A 4) (Rterm A 4) (Qterm A 4) (Pterm A 4) 5 4 := hswapy.symm
      _ = wilkieCore A (Sterm A 4) (Rterm A 4) (Qterm A 4) (Pterm A 4) 4 5 := hcore.symm
      _ = wilkieCore A (Rterm A 4) (Sterm A 4) (Pterm A 4) (Qterm A 4) 4 5 := hswapx
      _ = wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := hx
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem leeConsequences_of_wilkieFails
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) (hFail : WilkieFailsAt A 4 5 4) :
    (∀ {v}, InDomain n v → A.mul (Pterm A 4) v ≠ Qterm A 4) ∧
    (∀ {v}, InDomain n v → A.mul (Qterm A 4) v ≠ Pterm A 4) ∧
    (∀ {v}, InDomain n v → A.mul (Rterm A 4) v ≠ Sterm A 4) ∧
    (∀ {v}, InDomain n v → A.mul (Sterm A 4) v ≠ Rterm A 4) := by
  constructor
  · intro v hv h
    exact hFail (lee_q_eq_p_mul_yields_wilkie C H h5 hv h)
  · constructor
    · intro v hv h
      exact hFail (lee_p_eq_q_mul_yields_wilkie C H h5 hv h)
    · constructor
      · intro v hv h
        exact hFail (lee_s_eq_r_mul_yields_wilkie C H h5 hv h)
      · intro v hv h
        exact hFail (lee_r_eq_s_mul_yields_wilkie C H h5 hv h)

def wilkieCoreGeneric {α : Type} (add mul exp : α → α → α)
    (p q r s x y : α) : α :=
  mul
    (exp (add (exp p y) (exp q y)) x)
    (exp (add (exp r x) (exp s x)) y)

def posCoeff {α : Type} (add : α → α → α) (one : α) : Nat → α
  | 0 => one
  | k + 1 => add (posCoeff add one k) one

theorem distrib_left_generic
    {α : Type} (add mul : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)) :
    ∀ a b c, mul (add a b) c = add (mul a c) (mul b c) := by
  intro a b c
  calc
    mul (add a b) c = mul c (add a b) := Std.Commutative.comm ..
    _ = add (mul c a) (mul c b) := distrib c a b
    _ = add (mul a c) (mul b c) := by ac_rfl

theorem one_mul_generic
    {α : Type} (mul : α → α → α) (one : α)
    [Std.Commutative mul]
    (mul_one : ∀ a, mul a one = a) :
    ∀ a, mul one a = a := by
  intro a
  calc
    mul one a = mul a one := Std.Commutative.comm ..
    _ = a := mul_one a

theorem common_factor_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    {p q r s t x y : α}
    (hr : r = mul t p) (hs : s = mul t q) :
    wilkieCoreGeneric add mul exp p q r s x y =
      wilkieCoreGeneric add mul exp p q r s y x := by
  subst r
  subst s
  unfold wilkieCoreGeneric
  have hsumx :
      add (exp (mul t p) x) (exp (mul t q) x) =
        mul (exp t x) (add (exp p x) (exp q x)) := by
    rw [exp_mul, exp_mul, distrib]
  have hsumy :
      add (exp (mul t p) y) (exp (mul t q) y) =
        mul (exp t y) (add (exp p y) (exp q y)) := by
    rw [exp_mul, exp_mul, distrib]
  rw [hsumx, hsumy]
  rw [exp_mul, exp_mul]
  rw [exp_assoc, exp_assoc]
  have hxy : mul x y = mul y x := Std.Commutative.comm ..
  rw [hxy]
  ac_rfl

theorem divides_inner_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    {p q r s x u : α}
    (hfactor : mul p s = mul q r) :
    mul (exp (add (exp p x) (exp q x)) u)
      (add (exp r (mul u x)) (exp s (mul u x))) =
    mul (add (exp p (mul u x)) (exp q (mul u x)))
      (exp (add (exp r x) (exp s x)) u) := by
  have distrib_left := distrib_left_generic add mul distrib
  calc
    mul (exp (add (exp p x) (exp q x)) u)
      (add (exp r (mul u x)) (exp s (mul u x)))
        = add
            (mul (exp (add (exp p x) (exp q x)) u)
              (exp r (mul u x)))
            (mul (exp (add (exp p x) (exp q x)) u)
              (exp s (mul u x))) := distrib _ _ _
    _ = add
            (exp (mul (add (exp p x) (exp q x)) (exp r x)) u)
            (exp (mul (add (exp p x) (exp q x)) (exp s x)) u) := by
          have hux : mul u x = mul x u := Std.Commutative.comm ..
          rw [hux]
          rw [← exp_assoc r x u, ← exp_assoc s x u]
          rw [← exp_mul, ← exp_mul]
    _ = add
            (exp (add (mul (exp p x) (exp r x)) (mul (exp q x) (exp r x))) u)
            (exp (add (mul (exp p x) (exp s x)) (mul (exp q x) (exp s x))) u) := by
          repeat rw [distrib_left]
    _ = add
            (exp (add (mul (exp p x) (exp r x)) (mul (exp p x) (exp s x))) u)
            (exp (add (mul (exp q x) (exp r x)) (mul (exp q x) (exp s x))) u) := by
          have hps : mul (exp p x) (exp s x) = mul (exp q x) (exp r x) := by
            rw [← exp_mul p s x, hfactor, exp_mul]
          rw [hps]
    _ = add
            (exp (mul (exp p x) (add (exp r x) (exp s x))) u)
            (exp (mul (exp q x) (add (exp r x) (exp s x))) u) := by
          repeat rw [distrib]
    _ = add
            (mul (exp p (mul x u)) (exp (add (exp r x) (exp s x)) u))
            (mul (exp q (mul x u)) (exp (add (exp r x) (exp s x)) u)) := by
          repeat rw [exp_mul]
          repeat rw [exp_assoc]
    _ = mul (add (exp p (mul u x)) (exp q (mul u x)))
        (exp (add (exp r x) (exp s x)) u) := by
          have hxu : mul x u = mul u x := Std.Commutative.comm ..
          rw [hxu]
          rw [distrib_left]

theorem divides_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    {p q r s x y u : α}
    (hfactor : mul p s = mul q r)
    (hy : y = mul u x) :
    wilkieCoreGeneric add mul exp p q r s x y =
      wilkieCoreGeneric add mul exp p q r s y x := by
  subst y
  unfold wilkieCoreGeneric
  let A := add (exp p x) (exp q x)
  let B := add (exp r x) (exp s x)
  let C := add (exp r (mul u x)) (exp s (mul u x))
  let D := add (exp p (mul u x)) (exp q (mul u x))
  have hinner :
      mul (exp A u) C = mul D (exp B u) := by
    simpa [A, B, C, D] using
      divides_inner_generic add mul exp distrib exp_mul exp_assoc
        (p := p) (q := q) (r := r) (s := s) (x := x) (u := u) hfactor
  calc
    mul (exp D x) (exp B (mul u x))
        = mul (exp D x) (exp (exp B u) x) := by
          rw [exp_assoc]
    _ = mul (exp D x) (exp (exp B u) x) := rfl
    _ = exp (mul D (exp B u)) x := by
          rw [exp_mul]
    _ = exp (mul (exp A u) C) x := by
          rw [hinner]
    _ = mul (exp (exp A u) x) (exp C x) := by
          rw [exp_mul]
    _ = mul (exp A (mul u x)) (exp C x) := by
          rw [exp_assoc]

theorem p_square_eq_q_of_add_idem_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (hxx : add x x = x) :
    mul (add one x) (add one x) =
      add (add one x) (mul x x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  rw [distrib_left]
  repeat rw [distrib]
  repeat rw [mul_one]
  repeat rw [one_mul]
  calc
    add (add one x) (add x (mul x x)) =
        add one (add (add x x) (mul x x)) := by ac_rfl
    _ = add one (add x (mul x x)) := by rw [hxx]
    _ = add (add one x) (mul x x) := by ac_rfl

theorem m08_r_eq_pq_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : x = add (add one one) x) :
    let x2 := mul x x
    let x3 := mul x2 x
    let p := add one x
    let q := add p x2
    let r := add one x3
    r = mul p q := by
  intro x2 x3 p q r
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  let two := add one one
  have hx2 : x2 = add (mul two x) x2 := by
    dsimp [x2, two]
    calc
      mul x x = mul (add (add one one) x) x := by rw [← h]
      _ = add (mul (add one one) x) (mul x x) := distrib_left _ _ _
  have hx3 : x3 = add (mul two x2) x3 := by
    dsimp [x3, two]
    calc
      mul x2 x = mul x2 (add (add one one) x) := by rw [← h]
      _ = add (mul x2 (add one one)) (mul x2 x) := distrib _ _ _
      _ = add (mul (add one one) x2) (mul x2 x) := by
            have hcomm : mul x2 (add one one) = mul (add one one) x2 :=
              Std.Commutative.comm ..
            rw [hcomm]
  have htwo_x2 : mul two x2 = add x2 x2 := by
    dsimp [two]
    calc
      mul (add one one) x2 = add (mul one x2) (mul one x2) := distrib_left _ _ _
      _ = add x2 x2 := by rw [one_mul]
  have htwo_x : mul two x = add x x := by
    dsimp [two]
    calc
      mul (add one one) x = add (mul one x) (mul one x) := distrib_left _ _ _
      _ = add x x := by rw [one_mul]
  have htwo_x_right : mul x two = add x x := by
    calc
      mul x two = mul two x := Std.Commutative.comm ..
      _ = add x x := htwo_x
  have htwo_x2_right : mul x2 two = add x2 x2 := by
    calc
      mul x2 two = mul two x2 := Std.Commutative.comm ..
      _ = add x2 x2 := htwo_x2
  have htwo_x2_insert : add x2 x2 = add (mul two x) (add x2 x2) := by
    conv =>
      lhs
      arg 1
      rw [hx2]
    ac_rfl
  calc
    r = add one x3 := by rfl
    _ = add one (add (mul two x2) x3) := by rw [← hx3]
    _ = add one (add (add x2 x2) x3) := by rw [htwo_x2]
    _ = add one (add (add (mul two x) (add x2 x2)) x3) := by
          exact congrArg (fun z => add one (add z x3)) htwo_x2_insert
    _ = add one (add (mul two x) (add (mul two x2) x3)) := by
          rw [← htwo_x2]
          ac_rfl
    _ = mul p q := by
          dsimp [p, q, x2, x3, two]
          rw [distrib_left]
          repeat rw [distrib]
          repeat rw [distrib_left]
          repeat rw [mul_one]
          repeat rw [one_mul]
          ac_rfl

theorem m08_s_eq_qq_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : x = add (add one one) x) :
    let x2 := mul x x
    let x3 := mul x2 x
    let x4 := mul x3 x
    let p := add one x
    let q := add p x2
    let s := add (add one x2) x4
    s = mul q q := by
  intro x2 x3 x4 p q s
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  let two := add one one
  have hx2 : x2 = add (mul two x) x2 := by
    dsimp [x2, two]
    calc
      mul x x = mul (add (add one one) x) x := by rw [← h]
      _ = add (mul (add one one) x) (mul x x) := distrib_left _ _ _
  have hx3 : x3 = add (mul two x2) x3 := by
    dsimp [x3, two]
    calc
      mul x2 x = mul x2 (add (add one one) x) := by rw [← h]
      _ = add (mul x2 (add one one)) (mul x2 x) := distrib _ _ _
      _ = add (mul (add one one) x2) (mul x2 x) := by
            have hcomm : mul x2 (add one one) = mul (add one one) x2 :=
              Std.Commutative.comm ..
            rw [hcomm]
  have hx4 : x4 = add (mul two x3) x4 := by
    dsimp [x4, two]
    calc
      mul x3 x = mul x3 (add (add one one) x) := by rw [← h]
      _ = add (mul x3 (add one one)) (mul x3 x) := distrib _ _ _
      _ = add (mul (add one one) x3) (mul x3 x) := by
            have hcomm : mul x3 (add one one) = mul (add one one) x3 :=
              Std.Commutative.comm ..
            rw [hcomm]
  have htwo_x : mul two x = add x x := by
    dsimp [two]
    calc
      mul (add one one) x = add (mul one x) (mul one x) := distrib_left _ _ _
      _ = add x x := by rw [one_mul]
  have htwo_x2 : mul two x2 = add x2 x2 := by
    dsimp [two]
    calc
      mul (add one one) x2 = add (mul one x2) (mul one x2) := distrib_left _ _ _
      _ = add x2 x2 := by rw [one_mul]
  have htwo_x3 : mul two x3 = add x3 x3 := by
    dsimp [two]
    calc
      mul (add one one) x3 = add (mul one x3) (mul one x3) := distrib_left _ _ _
      _ = add x3 x3 := by rw [one_mul]
  have htwo_x3_insert : add x3 x3 = add (mul two x2) (add x3 x3) := by
    conv =>
      lhs
      arg 1
      rw [hx3]
    ac_rfl
  calc
    s = add (add one x2) x4 := by rfl
    _ = add (add one x2) (add (mul two x3) x4) := by rw [← hx4]
    _ = add (add one x2) (add (add x3 x3) x4) := by rw [htwo_x3]
    _ = add (add one x2) (add (add (mul two x2) (add x3 x3)) x4) := by
          exact congrArg (fun z => add (add one x2) (add z x4)) htwo_x3_insert
    _ = add (add one (add (mul two x) x2))
          (add (add (mul two x2) (add x3 x3)) x4) := by
          rw [← hx2]
    _ = add one
          (add (mul two x)
            (add x2 (add (mul two x2) (add (add x3 x3) x4)))) := by
          ac_rfl
    _ = add one
          (add (mul two x)
            (add x2 (add (add x2 x2) (add (add x3 x3) x4)))) := by
          rw [htwo_x2]
    _ = mul q q := by
          dsimp [q, p, x2, x3, x4, two]
          rw [distrib_left]
          repeat rw [distrib]
          repeat rw [distrib_left]
          repeat rw [mul_one]
          repeat rw [one_mul]
          ac_rfl

theorem m02_r_eq_p_factor_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : one = add (add one one) x) :
    let x2 := mul x x
    let x3 := mul x2 x
    let p := add one x
    let r := add one x3
    let t := add (add one one) x2
    r = mul p t := by
  intro x2 x3 p r t
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  let two := add one one
  have hx : x = add (mul two x) x2 := by
    dsimp [x2, two]
    calc
      x = mul one x := (one_mul x).symm
      _ = mul (add (add one one) x) x := congrArg (fun z => mul z x) h
      _ = add (mul (add one one) x) (mul x x) := distrib_left _ _ _
  calc
    r = add one x3 := by rfl
    _ = add (add two x) x3 := by
          simpa [two] using congrArg (fun z => add z x3) h
    _ = add (add two (add (mul two x) x2)) x3 :=
          congrArg (fun z => add (add two z) x3) hx
    _ = add two (add (mul two x) (add x2 x3)) := by ac_rfl
    _ = mul p t := by
          dsimp [p, t, x2, x3, two]
          rw [distrib_left]
          repeat rw [distrib]
          repeat rw [distrib_left]
          repeat rw [mul_one]
          repeat rw [one_mul]
          ac_rfl

theorem m02_s_eq_q_factor_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : one = add (add one one) x) :
    let x2 := mul x x
    let x3 := mul x2 x
    let x4 := mul x3 x
    let p := add one x
    let q := add p x2
    let s := add (add one x2) x4
    let t := add (add one one) x2
    s = mul q t := by
  intro x2 x3 x4 p q s t
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  let two := add one one
  have hx : x = add (mul two x) x2 := by
    dsimp [x2, two]
    calc
      x = mul one x := (one_mul x).symm
      _ = mul (add (add one one) x) x := congrArg (fun z => mul z x) h
      _ = add (mul (add one one) x) (mul x x) := distrib_left _ _ _
  have hx2 : x2 = add (mul two x2) x3 := by
    dsimp [x2, x3, two]
    calc
      mul x x = mul one (mul x x) := (one_mul (mul x x)).symm
      _ = mul (add (add one one) x) (mul x x) :=
            congrArg (fun z => mul z (mul x x)) h
      _ = add (mul (add one one) (mul x x)) (mul x (mul x x)) := distrib_left _ _ _
      _ = add (mul (add one one) (mul x x)) (mul (mul x x) x) := by
            have hcomm : mul x (mul x x) = mul (mul x x) x := by ac_rfl
            rw [hcomm]
  have hx2_insert : add x2 x2 = add (mul two x2) (add x2 x3) := by
    conv =>
      lhs
      arg 1
      rw [hx2]
    ac_rfl
  calc
    s = add (add one x2) x4 := by rfl
    _ = add (add (add two x) x2) x4 := by
          simpa [two] using congrArg (fun z => add (add z x2) x4) h
    _ = add (add (add two (add (mul two x) x2)) x2) x4 :=
          congrArg (fun z => add (add (add two z) x2) x4) hx
    _ = add two (add (mul two x) (add (add x2 x2) x4)) := by ac_rfl
    _ = add two (add (mul two x) (add (add (mul two x2) (add x2 x3)) x4)) := by
          exact congrArg (fun z => add two (add (mul two x) (add z x4))) hx2_insert
    _ = add two (add (mul two x) (add x2 (add (mul two x2) (add x3 x4)))) := by
          ac_rfl
    _ = mul q t := by
          dsimp [q, p, t, x2, x3, x4, two]
          rw [distrib_left]
          repeat rw [distrib]
          repeat rw [distrib_left]
          repeat rw [mul_one]
          repeat rw [one_mul]
          ac_rfl

theorem exp_succ_coeff_generic
    {α : Type} (add mul exp : α → α → α) (one a u : α)
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_one : ∀ a, exp a one = a) :
    exp a (add u one) = mul (exp a u) a := by
  rw [exp_add, exp_one]

theorem exp_succ_coeff_mul_x_generic
    {α : Type} (add mul exp : α → α → α) (one a u x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c)) :
    exp a (mul (add u one) x) =
      mul (exp a (mul u x)) (exp a x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  calc
    exp a (mul (add u one) x)
        = exp a (add (mul u x) (mul one x)) := by rw [distrib_left]
    _ = exp a (add (mul u x) x) := by rw [one_mul]
    _ = mul (exp a (mul u x)) (exp a x) := exp_add _ _ _

theorem jackson_u_step_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    {p q r s x rn sn : α}
    (hfactor : mul p s = mul q r) :
    mul (add (exp p x) (exp q x))
      (add (mul rn (exp r x)) (mul sn (exp s x))) =
    mul (add (exp r x) (exp s x))
      (add (mul (exp p x) rn) (mul (exp q x) sn)) := by
  have distrib_left := distrib_left_generic add mul distrib
  have hps : mul (exp p x) (exp s x) = mul (exp q x) (exp r x) := by
    rw [← exp_mul p s x, hfactor, exp_mul]
  have hterm1 :
      mul (exp p x) (mul sn (exp s x)) =
        mul (exp r x) (mul (exp q x) sn) := by
    calc
      mul (exp p x) (mul sn (exp s x)) =
          mul sn (mul (exp p x) (exp s x)) := by ac_rfl
      _ = mul sn (mul (exp q x) (exp r x)) := by rw [hps]
      _ = mul (exp r x) (mul (exp q x) sn) := by ac_rfl
  have hterm2 :
      mul (exp q x) (mul rn (exp r x)) =
        mul (exp s x) (mul (exp p x) rn) := by
    calc
      mul (exp q x) (mul rn (exp r x)) =
          mul rn (mul (exp q x) (exp r x)) := by ac_rfl
      _ = mul rn (mul (exp p x) (exp s x)) := by rw [← hps]
      _ = mul (exp s x) (mul (exp p x) rn) := by ac_rfl
  calc
    mul (add (exp p x) (exp q x))
        (add (mul rn (exp r x)) (mul sn (exp s x)))
        = add
            (add (mul (exp p x) (mul rn (exp r x)))
              (mul (exp p x) (mul sn (exp s x))))
            (add (mul (exp q x) (mul rn (exp r x)))
              (mul (exp q x) (mul sn (exp s x)))) := by
              rw [distrib_left]
              repeat rw [distrib]
              try ac_rfl
    _ = add
          (add (mul (exp r x) (mul (exp p x) rn))
            (mul (exp r x) (mul (exp q x) sn)))
          (add (mul (exp s x) (mul (exp p x) rn))
            (mul (exp s x) (mul (exp q x) sn))) := by
          rw [hterm1, hterm2]
          ac_rfl
    _ = mul (add (exp r x) (exp s x))
          (add (mul (exp p x) rn) (mul (exp q x) sn)) := by
          rw [distrib_left]
          repeat rw [distrib]
          try ac_rfl

theorem jackson_n_step_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    {p q r s x pux qux : α}
    (hfactor : mul p s = mul q r) :
    mul (add (exp p x) (exp q x))
      (exp (add (mul pux r) (mul qux s)) x) =
    mul (add (exp r x) (exp s x))
      (exp (add (mul p pux) (mul q qux)) x) := by
  have distrib_left := distrib_left_generic add mul distrib
  let t := add (mul pux r) (mul qux s)
  let u := add (mul p pux) (mul q qux)
  have hpbase : mul p t = mul r u := by
    dsimp [t, u]
    have hterm :
        mul p (mul qux s) = mul r (mul q qux) := by
      calc
        mul p (mul qux s) = mul qux (mul p s) := by ac_rfl
        _ = mul qux (mul q r) := by rw [hfactor]
        _ = mul r (mul q qux) := by ac_rfl
    calc
      mul p (add (mul pux r) (mul qux s))
          = add (mul p (mul pux r)) (mul p (mul qux s)) := distrib _ _ _
      _ = add (mul r (mul p pux)) (mul r (mul q qux)) := by
            rw [hterm]
            ac_rfl
      _ = mul r (add (mul p pux) (mul q qux)) := (distrib _ _ _).symm
  have hqbase : mul q t = mul s u := by
    dsimp [t, u]
    have hterm :
        mul q (mul pux r) = mul s (mul p pux) := by
      calc
        mul q (mul pux r) = mul pux (mul q r) := by ac_rfl
        _ = mul pux (mul p s) := by rw [← hfactor]
        _ = mul s (mul p pux) := by ac_rfl
    calc
      mul q (add (mul pux r) (mul qux s))
          = add (mul q (mul pux r)) (mul q (mul qux s)) := distrib _ _ _
      _ = add (mul s (mul p pux)) (mul s (mul q qux)) := by
            rw [hterm]
            ac_rfl
      _ = mul s (add (mul p pux) (mul q qux)) := (distrib _ _ _).symm
  calc
    mul (add (exp p x) (exp q x)) (exp t x)
        = add (exp (mul p t) x) (exp (mul q t) x) := by
          rw [distrib_left]
          rw [← exp_mul p t x, ← exp_mul q t x]
    _ = add (exp (mul r u) x) (exp (mul s u) x) := by
          rw [hpbase, hqbase]
    _ = mul (add (exp r x) (exp s x)) (exp u x) := by
          rw [distrib_left]
          rw [← exp_mul r u x, ← exp_mul s u x]

theorem jackson_u_move_pos_generic
    {α : Type} (add mul exp : α → α → α) (one : α) (k : Nat)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_one : ∀ a, exp a one = a)
    {p q r s x rn sn : α}
    (hfactor : mul p s = mul q r) :
    let u := posCoeff add one k
    let A := add (exp p x) (exp q x)
    let B := add (exp r x) (exp s x)
    mul (exp A u)
      (add (mul rn (exp r (mul u x))) (mul sn (exp s (mul u x)))) =
    mul (exp B u)
      (add (mul (exp p (mul u x)) rn) (mul (exp q (mul u x)) sn)) := by
  induction k generalizing rn sn with
  | zero =>
      dsimp [posCoeff]
      have one_mul := one_mul_generic mul one mul_one
      rw [exp_one, exp_one, one_mul x]
      exact jackson_u_step_generic add mul exp distrib exp_mul hfactor
  | succ k ih =>
      dsimp [posCoeff]
      let u := posCoeff add one k
      let A := add (exp p x) (exp q x)
      let B := add (exp r x) (exp s x)
      have hA : exp A (add u one) = mul (exp A u) A :=
        exp_succ_coeff_generic add mul exp one A u exp_add exp_one
      have hB : exp B (add u one) = mul (exp B u) B :=
        exp_succ_coeff_generic add mul exp one B u exp_add exp_one
      have hr : exp r (mul (add u one) x) =
          mul (exp r (mul u x)) (exp r x) :=
        exp_succ_coeff_mul_x_generic add mul exp one r u x distrib mul_one exp_add
      have hs : exp s (mul (add u one) x) =
          mul (exp s (mul u x)) (exp s x) :=
        exp_succ_coeff_mul_x_generic add mul exp one s u x distrib mul_one exp_add
      have hp : exp p (mul (add u one) x) =
          mul (exp p (mul u x)) (exp p x) :=
        exp_succ_coeff_mul_x_generic add mul exp one p u x distrib mul_one exp_add
      have hq : exp q (mul (add u one) x) =
          mul (exp q (mul u x)) (exp q x) :=
        exp_succ_coeff_mul_x_generic add mul exp one q u x distrib mul_one exp_add
      calc
        mul (exp A (add u one))
          (add (mul rn (exp r (mul (add u one) x)))
            (mul sn (exp s (mul (add u one) x))))
            =
          mul (exp A u)
            (mul A
              (add (mul (mul rn (exp r (mul u x))) (exp r x))
                (mul (mul sn (exp s (mul u x))) (exp s x)))) := by
              rw [hA, hr, hs]
              ac_rfl
        _ =
          mul (exp A u)
            (mul B
              (add (mul (exp p x) (mul rn (exp r (mul u x))))
                (mul (exp q x) (mul sn (exp s (mul u x)))))) := by
              rw [jackson_u_step_generic add mul exp distrib exp_mul hfactor]
        _ =
          mul B
            (mul (exp A u)
              (add (mul (mul (exp p x) rn) (exp r (mul u x)))
                (mul (mul (exp q x) sn) (exp s (mul u x))))) := by
              ac_rfl
        _ =
          mul B
            (mul (exp B u)
              (add (mul (exp p (mul u x)) (mul (exp p x) rn))
                (mul (exp q (mul u x)) (mul (exp q x) sn)))) := by
              rw [ih (rn := mul (exp p x) rn) (sn := mul (exp q x) sn)]
        _ =
          mul (exp B (add u one))
            (add (mul (exp p (mul (add u one) x)) rn)
              (mul (exp q (mul (add u one) x)) sn)) := by
              rw [hB, hp, hq]
              ac_rfl

theorem jackson_n_move_pos_generic
    {α : Type} (add mul exp : α → α → α) (one : α) (k : Nat)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_one : ∀ a, exp a one = a)
    {p q r s x pux qux : α}
    (hfactor : mul p s = mul q r) :
    let n := posCoeff add one k
    let A := add (exp p x) (exp q x)
    let B := add (exp r x) (exp s x)
    mul (exp A n)
      (exp (add (mul pux (exp r n)) (mul qux (exp s n))) x) =
    mul (exp B n)
      (exp (add (mul (exp p n) pux) (mul (exp q n) qux)) x) := by
  induction k generalizing pux qux with
  | zero =>
      dsimp [posCoeff]
      simpa [exp_one] using
        (jackson_n_step_generic add mul exp distrib exp_mul
          (p := p) (q := q) (r := r) (s := s) (x := x)
          (pux := pux) (qux := qux) hfactor)
  | succ k ih =>
      dsimp [posCoeff]
      let n := posCoeff add one k
      let A := add (exp p x) (exp q x)
      let B := add (exp r x) (exp s x)
      have hA : exp A (add n one) = mul (exp A n) A :=
        exp_succ_coeff_generic add mul exp one A n exp_add exp_one
      have hB : exp B (add n one) = mul (exp B n) B :=
        exp_succ_coeff_generic add mul exp one B n exp_add exp_one
      have hp : exp p (add n one) = mul (exp p n) p :=
        exp_succ_coeff_generic add mul exp one p n exp_add exp_one
      have hq : exp q (add n one) = mul (exp q n) q :=
        exp_succ_coeff_generic add mul exp one q n exp_add exp_one
      have hr : exp r (add n one) = mul (exp r n) r :=
        exp_succ_coeff_generic add mul exp one r n exp_add exp_one
      have hs : exp s (add n one) = mul (exp s n) s :=
        exp_succ_coeff_generic add mul exp one s n exp_add exp_one
      calc
        mul (exp A (add n one))
          (exp
            (add (mul pux (exp r (add n one)))
              (mul qux (exp s (add n one)))) x)
            =
          mul (exp A n)
            (mul A
              (exp
                (add (mul (mul pux (exp r n)) r)
                  (mul (mul qux (exp s n)) s)) x)) := by
              rw [hA, hr, hs]
              ac_rfl
        _ =
          mul (exp A n)
            (mul B
              (exp
                (add (mul p (mul pux (exp r n)))
                  (mul q (mul qux (exp s n)))) x)) := by
              rw [jackson_n_step_generic add mul exp distrib exp_mul hfactor]
        _ =
          mul B
            (mul (exp A n)
              (exp
                (add (mul (mul p pux) (exp r n))
                  (mul (mul q qux) (exp s n))) x)) := by
              ac_rfl
        _ =
          mul B
            (mul (exp B n)
              (exp
                (add (mul (exp p n) (mul p pux))
                  (mul (exp q n) (mul q qux))) x)) := by
              rw [ih (pux := mul p pux) (qux := mul q qux)]
        _ =
          mul (exp B (add n one))
            (exp
              (add (mul (exp p (add n one)) pux)
                (mul (exp q (add n one)) qux)) x) := by
              rw [hB, hp, hq]
              ac_rfl

theorem jackson_linear_pos_generic
    {α : Type} (add mul exp : α → α → α) (one : α) (kn ku : Nat)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    (exp_one : ∀ a, exp a one = a)
    {p q r s x y : α}
    (hfactor : mul p s = mul q r)
    (hy : y = add (posCoeff add one kn) (mul (posCoeff add one ku) x)) :
    wilkieCoreGeneric add mul exp p q r s y x =
      wilkieCoreGeneric add mul exp p q r s x y := by
  subst y
  let n := posCoeff add one kn
  let u := posCoeff add one ku
  let A := add (exp p x) (exp q x)
  let B := add (exp r x) (exp s x)
  let C := add (mul (exp r n) (exp r (mul u x)))
    (mul (exp s n) (exp s (mul u x)))
  let D := add (mul (exp p (mul u x)) (exp r n))
    (mul (exp q (mul u x)) (exp s n))
  let E := add (mul (exp p n) (exp p (mul u x)))
    (mul (exp q n) (exp q (mul u x)))
  have hu :
      mul (exp A u) C = mul (exp B u) D := by
    simpa [A, B, C, D] using
      (jackson_u_move_pos_generic add mul exp one ku distrib mul_one exp_add exp_mul exp_one
        (p := p) (q := q) (r := r) (s := s) (x := x)
        (rn := exp r n) (sn := exp s n) hfactor)
  have hn :
      mul (exp A n) (exp D x) = mul (exp B n) (exp E x) := by
    simpa [A, B, D, E] using
      (jackson_n_move_pos_generic add mul exp one kn distrib exp_add exp_mul exp_one
        (p := p) (q := q) (r := r) (s := s) (x := x)
        (pux := exp p (mul u x)) (qux := exp q (mul u x)) hfactor)
  unfold wilkieCoreGeneric
  calc
    mul (exp A (add n (mul u x)))
        (exp (add (exp r (add n (mul u x))) (exp s (add n (mul u x)))) x)
        =
      mul (exp A n)
        (mul (exp A (mul u x)) (exp C x)) := by
          rw [exp_add, exp_add, exp_add]
          exact Std.Associative.assoc _ _ _
    _ = mul (exp A n)
        (mul (exp (exp A u) x) (exp C x)) := by
          rw [exp_assoc]
    _ = mul (exp A n)
        (exp (mul (exp A u) C) x) := by
          rw [← exp_mul]
    _ = mul (exp A n)
        (exp (mul (exp B u) D) x) := by
          rw [hu]
    _ = mul (exp A n)
        (mul (exp (exp B u) x) (exp D x)) := by
          rw [exp_mul]
    _ = mul (exp B (mul u x))
        (mul (exp A n) (exp D x)) := by
          rw [exp_assoc]
          ac_rfl
    _ = mul (exp B (mul u x))
        (mul (exp B n) (exp E x)) := by
          rw [hn]
    _ = mul (exp E x)
        (mul (exp B n) (exp B (mul u x))) := by
          ac_rfl
    _ = mul (exp E x) (exp B (add n (mul u x))) := by
          rw [exp_add]
    _ = mul
        (exp (add (exp p (add n (mul u x))) (exp q (add n (mul u x)))) x)
        (exp B (add n (mul u x))) := by
          dsimp [E]
          repeat rw [exp_add]

theorem jackson_u_move_generic
    {α : Type} (add mul exp : α → α → α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    {p q r s x u rn sn : α}
    (hfactor : mul p s = mul q r) :
    let A := add (exp p x) (exp q x)
    let B := add (exp r x) (exp s x)
    mul (exp A u)
      (add (mul rn (exp r (mul u x))) (mul sn (exp s (mul u x)))) =
    mul (exp B u)
      (add (mul (exp p (mul u x)) rn) (mul (exp q (mul u x)) sn)) := by
  intro A B
  have distrib_left := distrib_left_generic add mul distrib
  have hcross :
      mul (exp q x) (exp r x) = mul (exp p x) (exp s x) := by
    calc
      mul (exp q x) (exp r x) = exp (mul q r) x := (exp_mul q r x).symm
      _ = exp (mul p s) x := by rw [← hfactor]
      _ = mul (exp p x) (exp s x) := exp_mul p s x
  have hAr :
      mul A (exp r x) = mul B (exp p x) := by
    dsimp [A, B]
    rw [distrib_left]
    rw [distrib_left]
    rw [hcross]
    ac_rfl
  have hAs :
      mul A (exp s x) = mul B (exp q x) := by
    dsimp [A, B]
    rw [distrib_left]
    rw [distrib_left]
    rw [← hcross]
    ac_rfl
  have hArPow :
      mul (exp A u) (exp r (mul u x)) =
        mul (exp B u) (exp p (mul u x)) := by
    have h := congrArg (fun z => exp z u) hAr
    change exp (mul A (exp r x)) u = exp (mul B (exp p x)) u at h
    repeat rw [exp_mul] at h
    repeat rw [exp_assoc] at h
    have hxu : mul x u = mul u x := Std.Commutative.comm ..
    simpa [hxu] using h
  have hAsPow :
      mul (exp A u) (exp s (mul u x)) =
        mul (exp B u) (exp q (mul u x)) := by
    have h := congrArg (fun z => exp z u) hAs
    change exp (mul A (exp s x)) u = exp (mul B (exp q x)) u at h
    repeat rw [exp_mul] at h
    repeat rw [exp_assoc] at h
    have hxu : mul x u = mul u x := Std.Commutative.comm ..
    simpa [hxu] using h
  calc
    mul (exp A u)
      (add (mul rn (exp r (mul u x))) (mul sn (exp s (mul u x))))
        =
      add (mul rn (mul (exp A u) (exp r (mul u x))))
        (mul sn (mul (exp A u) (exp s (mul u x)))) := by
          rw [distrib]
          ac_rfl
    _ =
      add (mul rn (mul (exp B u) (exp p (mul u x))))
        (mul sn (mul (exp B u) (exp q (mul u x)))) := by
          rw [hArPow, hAsPow]
    _ =
      mul (exp B u)
        (add (mul (exp p (mul u x)) rn) (mul (exp q (mul u x)) sn)) := by
          rw [distrib]
          ac_rfl

theorem jackson_linear_n_pos_generic
    {α : Type} (add mul exp : α → α → α) (one : α) (kn : Nat)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_assoc : ∀ a b c, exp (exp a b) c = exp a (mul b c))
    (exp_one : ∀ a, exp a one = a)
    {p q r s x y u : α}
    (hfactor : mul p s = mul q r)
    (hy : y = add (posCoeff add one kn) (mul u x)) :
    wilkieCoreGeneric add mul exp p q r s y x =
      wilkieCoreGeneric add mul exp p q r s x y := by
  subst y
  let n := posCoeff add one kn
  let A := add (exp p x) (exp q x)
  let B := add (exp r x) (exp s x)
  let C := add (mul (exp r n) (exp r (mul u x)))
    (mul (exp s n) (exp s (mul u x)))
  let D := add (mul (exp p (mul u x)) (exp r n))
    (mul (exp q (mul u x)) (exp s n))
  let E := add (mul (exp p n) (exp p (mul u x)))
    (mul (exp q n) (exp q (mul u x)))
  have hu :
      mul (exp A u) C = mul (exp B u) D := by
    simpa [A, B, C, D] using
      (jackson_u_move_generic add mul exp distrib exp_mul exp_assoc
        (p := p) (q := q) (r := r) (s := s) (x := x) (u := u)
        (rn := exp r n) (sn := exp s n) hfactor)
  have hn :
      mul (exp A n) (exp D x) = mul (exp B n) (exp E x) := by
    simpa [A, B, D, E] using
      (jackson_n_move_pos_generic add mul exp one kn distrib exp_add exp_mul exp_one
        (p := p) (q := q) (r := r) (s := s) (x := x)
        (pux := exp p (mul u x)) (qux := exp q (mul u x)) hfactor)
  unfold wilkieCoreGeneric
  calc
    mul (exp A (add n (mul u x)))
        (exp (add (exp r (add n (mul u x))) (exp s (add n (mul u x)))) x)
        =
      mul (exp A n)
        (mul (exp A (mul u x)) (exp C x)) := by
          rw [exp_add, exp_add, exp_add]
          exact Std.Associative.assoc _ _ _
    _ = mul (exp A n)
        (mul (exp (exp A u) x) (exp C x)) := by
          rw [exp_assoc]
    _ = mul (exp A n)
        (exp (mul (exp A u) C) x) := by
          rw [← exp_mul]
    _ = mul (exp A n)
        (exp (mul (exp B u) D) x) := by
          rw [hu]
    _ = mul (exp A n)
        (mul (exp (exp B u) x) (exp D x)) := by
          rw [exp_mul]
    _ = mul (exp B (mul u x))
        (mul (exp A n) (exp D x)) := by
          rw [exp_assoc]
          ac_rfl
    _ = mul (exp B (mul u x))
        (mul (exp B n) (exp E x)) := by
          rw [hn]
    _ = mul (exp E x)
        (mul (exp B n) (exp B (mul u x))) := by
          ac_rfl
    _ = mul (exp E x) (exp B (add n (mul u x))) := by
          rw [exp_add]
    _ = mul
        (exp (add (exp p (add n (mul u x))) (exp q (add n (mul u x)))) x)
        (exp B (add n (mul u x))) := by
          dsimp [E]
          repeat rw [exp_add]

theorem jackson_linear_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {kn ku : Nat}
    (hlin :
      5 = A.add (posCoeff A.add 1 kn) (A.mul (posCoeff A.add 1 ku) 4)) :
    wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 =
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  let yD : D := ⟨5, h5⟩
  let pD : D := ⟨Pterm A 4, hP⟩
  let qD : D := ⟨Qterm A 4, hQ⟩
  let rD : D := ⟨Rterm A 4, hR⟩
  let sD : D := ⟨Sterm A 4, hS⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have coeff_val : ∀ k, (posCoeff addD oneD k).1 = posCoeff A.add 1 k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp [posCoeff, addD, oneD, ih]
  have hyD :
      yD = addD (posCoeff addD oneD kn) (mulD (posCoeff addD oneD ku) xD) := by
    apply Subtype.ext
    simp [addD, mulD, xD, yD, coeff_val, hlin]
  have hfactorD :
      mulD pD sD = mulD qD rD := by
    apply Subtype.ext
    exact wilkie_factor_hsi C H h1 h4
  have hD := jackson_linear_pos_generic
    (add := addD) (mul := mulD) (exp := expD) (one := oneD)
    (kn := kn) (ku := ku)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (exp_add := by
      intro a b c
      apply Subtype.ext
      exact H.exp_add a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_assoc := by
      intro a b c
      apply Subtype.ext
      exact H.exp_assoc a.2 b.2 c.2)
    (exp_one := by
      intro a
      apply Subtype.ext
      exact H.exp_one a.2)
    (p := pD) (q := qD) (r := rD) (s := sD) (x := xD) (y := yD)
    hfactorD hyD
  simpa [wilkieCoreGeneric, wilkieCore, addD, mulD, expD, oneD, xD, yD, pD, qD, rD, sD]
    using congrArg Subtype.val hD

theorem jackson_linear_n_pos_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {kn u : Nat} (hu : InDomain n u)
    (hlin :
      5 = A.add (posCoeff A.add 1 kn) (A.mul u 4)) :
    wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 =
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  let yD : D := ⟨5, h5⟩
  let uD : D := ⟨u, hu⟩
  let pD : D := ⟨Pterm A 4, hP⟩
  let qD : D := ⟨Qterm A 4, hQ⟩
  let rD : D := ⟨Rterm A 4, hR⟩
  let sD : D := ⟨Sterm A 4, hS⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have coeff_val : ∀ k, (posCoeff addD oneD k).1 = posCoeff A.add 1 k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp [posCoeff, addD, oneD, ih]
  have hyD :
      yD = addD (posCoeff addD oneD kn) (mulD uD xD) := by
    apply Subtype.ext
    simp [addD, mulD, xD, yD, uD, coeff_val, hlin]
  have hfactorD :
      mulD pD sD = mulD qD rD := by
    apply Subtype.ext
    exact wilkie_factor_hsi C H h1 h4
  have hD := jackson_linear_n_pos_generic
    (add := addD) (mul := mulD) (exp := expD) (one := oneD)
    (kn := kn)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (exp_add := by
      intro a b c
      apply Subtype.ext
      exact H.exp_add a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_assoc := by
      intro a b c
      apply Subtype.ext
      exact H.exp_assoc a.2 b.2 c.2)
    (exp_one := by
      intro a
      apply Subtype.ext
      exact H.exp_one a.2)
    (p := pD) (q := qD) (r := rD) (s := sD) (x := xD) (y := yD) (u := uD)
    hfactorD hyD
  simpa [wilkieCoreGeneric, wilkieCore, addD, mulD, expD, oneD, xD, yD, uD,
    pD, qD, rD, sD]
    using congrArg Subtype.val hD

theorem jackson_linear_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {kn ku : Nat}
    (hlin :
      5 = A.add (posCoeff A.add 1 kn) (A.mul (posCoeff A.add 1 ku) 4)) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have hcore := jackson_linear_hsi C H h5 (kn := kn) (ku := ku) hlin
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore.symm

theorem jackson_linear_n_pos_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {kn u : Nat} (hu : InDomain n u)
    (hlin :
      5 = A.add (posCoeff A.add 1 kn) (A.mul u 4)) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have hcore := jackson_linear_n_pos_hsi C H h5 (kn := kn) hu hlin
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore.symm

theorem jackson_small_quadratic_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    {i j k : Nat} (hi : i ∈ [1, 2, 3]) (hj : j ∈ [1, 2, 3])
    (hk : k ∈ [1, 2, 3])
  (hquad : A.add i (A.add (A.mul j 4) (A.mul k (x2 A 4))) = 5) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have hiD : InDomain n i := by
    rw [InDomain_iff] at h5 ⊢
    simp at hi
    omega
  have hjD : InDomain n j := by
    rw [InDomain_iff] at h5 ⊢
    simp at hj
    omega
  have hkD : InDomain n k := by
    rw [InDomain_iff] at h5 ⊢
    simp at hk
    omega
  let u := A.add j (A.mul k 4)
  have hkx : InDomain n (A.mul k 4) := C.mul_mem hkD h4
  have hu : InDomain n u := C.add_mem hjD hkx
  have hux :
      A.mul u 4 = A.add (A.mul j 4) (A.mul k (x2 A 4)) := by
    calc
      A.mul u 4 = A.mul (A.add j (A.mul k 4)) 4 := rfl
      _ = A.mul 4 (A.add j (A.mul k 4)) := H.mul_comm hu h4
      _ = A.add (A.mul 4 j) (A.mul 4 (A.mul k 4)) :=
            H.distrib h4 hjD hkx
      _ = A.add (A.mul j 4) (A.mul k (x2 A 4)) := by
            have hleft : A.mul 4 j = A.mul j 4 := H.mul_comm h4 hjD
            have hright : A.mul 4 (A.mul k 4) = A.mul k (x2 A 4) := by
              calc
                A.mul 4 (A.mul k 4) = A.mul (A.mul 4 k) 4 :=
                  H.mul_assoc h4 hkD h4
                _ = A.mul (A.mul k 4) 4 := by rw [H.mul_comm h4 hkD]
                _ = A.mul k (x2 A 4) := by
                  rw [x2]
                  exact (H.mul_assoc hkD h4 h4).symm
            rw [hleft, hright]
  have hbase : 5 = A.add i (A.mul u 4) := by
    rw [hux]
    exact hquad.symm
  simp at hi
  rcases hi with rfl | rfl | rfl
  · exact jackson_linear_n_pos_yields_wilkie C H h5 (kn := 0) hu (by
      simpa [posCoeff] using hbase)
  · exact jackson_linear_n_pos_yields_wilkie C H h5 (kn := 1) hu (by
      simpa [posCoeff, h112] using hbase)
  · exact jackson_linear_n_pos_yields_wilkie C H h5 (kn := 2) hu (by
      simpa [posCoeff, h112, h213] using hbase)

theorem jackson_small_linear_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    {i j : Nat} (hi : i ∈ [1, 2, 3]) (hj : j ∈ [1, 2, 3])
    (hlin : A.add i (A.mul j 4) = 5) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  simp at hi hj
  rcases hi with rfl | rfl | rfl
  · rcases hj with rfl | rfl | rfl
    · exact jackson_linear_yields_wilkie C H h5 (kn := 0) (ku := 0) (by
        simpa [posCoeff] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 0) (ku := 1) (by
        simpa [posCoeff, h112] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 0) (ku := 2) (by
        simpa [posCoeff, h112, h213] using hlin.symm)
  · rcases hj with rfl | rfl | rfl
    · exact jackson_linear_yields_wilkie C H h5 (kn := 1) (ku := 0) (by
        simpa [posCoeff, h112] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 1) (ku := 1) (by
        simpa [posCoeff, h112] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 1) (ku := 2) (by
        simpa [posCoeff, h112, h213] using hlin.symm)
  · rcases hj with rfl | rfl | rfl
    · exact jackson_linear_yields_wilkie C H h5 (kn := 2) (ku := 0) (by
        simpa [posCoeff, h112, h213] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 2) (ku := 1) (by
        simpa [posCoeff, h112, h213] using hlin.symm)
    · exact jackson_linear_yields_wilkie C H h5 (kn := 2) (ku := 2) (by
        simpa [posCoeff, h112, h213] using hlin.symm)

theorem jacksonConsequences_of_wilkieFails
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    (hFail : WilkieFailsAt A 4 5 4) :
    ∀ {i j z}, i ∈ [1, 2, 3] → j ∈ [1, 2, 3] → InDomain n z →
      ¬(A.add i z = 5 ∧ A.mul j 4 = z) := by
  intro i j z hi hj _hz hbad
  have hlin : A.add i (A.mul j 4) = 5 := by
    rw [hbad.2]
    exact hbad.1
  exact hFail (jackson_small_linear_yields_wilkie C H h5 h112 h213 hi hj hlin)

theorem common_factor_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s t x y : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s) (ht : InDomain n t)
    (hx : InDomain n x) (hy : InDomain n y)
    (hr_eq : r = A.mul t p) (hs_eq : s = A.mul t q) :
    wilkieCore A p q r s x y = wilkieCore A p q r s y x := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let pD : D := ⟨p, hp⟩
  let qD : D := ⟨q, hq⟩
  let rD : D := ⟨r, hr⟩
  let sD : D := ⟨s, hs⟩
  let tD : D := ⟨t, ht⟩
  let xD : D := ⟨x, hx⟩
  let yD : D := ⟨y, hy⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := common_factor_generic
    (add := addD) (mul := mulD) (exp := expD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_assoc := by
      intro a b c
      apply Subtype.ext
      exact H.exp_assoc a.2 b.2 c.2)
    (p := pD) (q := qD) (r := rD) (s := sD) (t := tD)
    (x := xD) (y := yD)
    (by
      apply Subtype.ext
      exact hr_eq)
    (by
      apply Subtype.ext
      exact hs_eq)
  simpa [wilkieCoreGeneric, wilkieCore, addD, mulD, expD, pD, qD, rD, sD, tD, xD, yD]
    using congrArg Subtype.val hD

theorem divides_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s x y u : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x) (hy : InDomain n y) (hu : InDomain n u)
    (hfactor : A.mul p s = A.mul q r)
    (hdiv : y = A.mul u x) :
    wilkieCore A p q r s x y = wilkieCore A p q r s y x := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let pD : D := ⟨p, hp⟩
  let qD : D := ⟨q, hq⟩
  let rD : D := ⟨r, hr⟩
  let sD : D := ⟨s, hs⟩
  let xD : D := ⟨x, hx⟩
  let yD : D := ⟨y, hy⟩
  let uD : D := ⟨u, hu⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := divides_generic
    (add := addD) (mul := mulD) (exp := expD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_assoc := by
      intro a b c
      apply Subtype.ext
      exact H.exp_assoc a.2 b.2 c.2)
    (p := pD) (q := qD) (r := rD) (s := sD)
    (x := xD) (y := yD) (u := uD)
    (by
      apply Subtype.ext
      exact hfactor)
    (by
      apply Subtype.ext
      exact hdiv)
  simpa [wilkieCoreGeneric, wilkieCore, addD, mulD, expD, pD, qD, rD, sD, xD, yD, uD]
    using congrArg Subtype.val hD

theorem lee_failure_pair_not_left_mul
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) (hFail : WilkieFailsAt A 4 5 4) :
    ∀ {v}, InDomain n v → A.mul 4 v ≠ 5 := by
  intro v hv hmul
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 h4
  have hdiv : 5 = A.mul v 4 := by
    calc
      5 = A.mul 4 v := hmul.symm
      _ = A.mul v 4 := H.mul_comm h4 hv
  have hcore := divides_hsi C H hP hQ hR hS h4 h5 hv hfactor hdiv
  exact hFail (by
    simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
      using hcore)

theorem q_eq_p_of_one_add_x2_eq_one_generic
    {α : Type} (add : α → α → α) (one x x2 : α)
    [Std.Associative add] [Std.Commutative add]
    (h : add one x2 = one) :
    add (add one x) x2 = add one x := by
  calc
    add (add one x) x2 = add x (add one x2) := by ac_rfl
    _ = add x one := by rw [h]
    _ = add one x := by ac_rfl

theorem q_eq_p_of_one_add_x2_eq_one_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 (x2 A 4) = 1) :
    Qterm A 4 = Pterm A 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have hx2 : InDomain n (x2 A 4) := by
    unfold x2
    exact C.mul_mem h4 h4
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  let x2D : D := ⟨x2 A 4, hx2⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  have hD := q_eq_p_of_one_add_x2_eq_one_generic
    (add := addD) (one := oneD) (x := xD) (x2 := x2D)
    (by
      apply Subtype.ext
      exact h)
  simpa [Pterm, Qterm, addD, oneD, xD, x2D]
    using congrArg Subtype.val hD

theorem m05_one_add_x2_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 (x2 A 4) = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, _hQ, _hR, _hS⟩
  have hQeq : Qterm A 4 = Pterm A 4 :=
    q_eq_p_of_one_add_x2_eq_one_hsi C H h5 h
  have hdiv : A.mul (Pterm A 4) 1 = Qterm A 4 := by
    rw [H.mul_one hP, hQeq]
  exact lee_q_eq_p_mul_yields_wilkie C H h5 h1 hdiv

theorem m06_x3_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x3 A 4 = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have hx2 : InDomain n (x2 A 4) := by
    unfold x2
    exact C.mul_mem h4 h4
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 h4
  have hu : InDomain n (A.mul 5 (x2 A 4)) := C.mul_mem h5 hx2
  have hdiv : 5 = A.mul (A.mul 5 (x2 A 4)) 4 := by
    calc
      5 = A.mul 5 1 := (H.mul_one h5).symm
      _ = A.mul 5 (x3 A 4) := by rw [← h]
      _ = A.mul 5 (A.mul (x2 A 4) 4) := rfl
      _ = A.mul (A.mul 5 (x2 A 4)) 4 := H.mul_assoc h5 hx2 h4
  have hcore := divides_hsi C H hP hQ hR hS h4 h5 hu hfactor hdiv
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem q_eq_p_mul_x_of_one_add_x2_eq_x2_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : add one (mul x x) = mul x x) :
    mul (add one x) x = add (add one x) (mul x x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  calc
    mul (add one x) x = add (mul one x) (mul x x) := distrib_left _ _ _
    _ = add x (mul x x) := by rw [one_mul]
    _ = add x (add one (mul x x)) := by rw [h]
    _ = add (add one x) (mul x x) := by ac_rfl

theorem q_eq_p_mul_x_of_one_add_x2_eq_x2_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 (x2 A 4) = x2 A 4) :
    A.mul (Pterm A 4) 4 = Qterm A 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := q_eq_p_mul_x_of_one_add_x2_eq_x2_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact h)
  simpa [Pterm, Qterm, x2, addD, mulD, oneD, xD]
    using congrArg Subtype.val hD

theorem m17_one_add_x2_eq_x2_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 (x2 A 4) = x2 A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have hdiv : A.mul (Pterm A 4) 4 = Qterm A 4 :=
    q_eq_p_mul_x_of_one_add_x2_eq_x2_hsi C H h5 h
  exact lee_q_eq_p_mul_yields_wilkie C H h5 h4 hdiv

theorem q_eq_p_mul_x2_of_x3_eq_p_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : mul (mul x x) x = add one x) :
    mul (add one x) (mul x x) = add (add one x) (mul x x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  calc
    mul (add one x) (mul x x) =
        add (mul one (mul x x)) (mul x (mul x x)) := distrib_left _ _ _
    _ = add (mul x x) (mul (mul x x) x) := by
          rw [one_mul]
          ac_rfl
    _ = add (mul x x) (add one x) := by rw [h]
    _ = add (add one x) (mul x x) := by ac_rfl

theorem q_eq_p_mul_x2_of_x3_eq_p_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x3 A 4 = Pterm A 4) :
    A.mul (Pterm A 4) (x2 A 4) = Qterm A 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := q_eq_p_mul_x2_of_x3_eq_p_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact h)
  simpa [Pterm, Qterm, x2, x3, addD, mulD, oneD, xD]
    using congrArg Subtype.val hD

theorem m14_x3_eq_p_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x3 A 4 = Pterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have hx2 : InDomain n (x2 A 4) := by
    unfold x2
    exact C.mul_mem h4 h4
  have hdiv : A.mul (Pterm A 4) (x2 A 4) = Qterm A 4 :=
    q_eq_p_mul_x2_of_x3_eq_p_hsi C H h5 h
  exact lee_q_eq_p_mul_yields_wilkie C H h5 hx2 hdiv

theorem p_square_eq_q_of_two_add_x_eq_p_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : add (add one one) x = add one x) :
    mul (add one x) (add one x) =
      add (add one x) (mul x x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  have hx_tail :
      add (add x x) (mul x x) = add x (mul x x) := by
    calc
      add (add x x) (mul x x) =
          mul x (add (add one one) x) := by
            rw [distrib]
            repeat rw [distrib]
            repeat rw [mul_one]
      _ = mul x (add one x) := by rw [h]
      _ = add x (mul x x) := by
            rw [distrib]
            rw [mul_one]
  calc
    mul (add one x) (add one x) =
        add (mul one (add one x)) (mul x (add one x)) := distrib_left _ _ _
    _ = add (add one x) (add (mul x one) (mul x x)) := by
          rw [one_mul, distrib]
    _ = add (add one x) (add x (mul x x)) := by rw [mul_one]
    _ = add one (add (add x x) (mul x x)) := by ac_rfl
    _ = add one (add x (mul x x)) := by rw [hx_tail]
    _ = add (add one x) (mul x x) := by ac_rfl

theorem p_square_eq_q_of_two_add_x_eq_p_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = Pterm A 4) :
    A.mul (Pterm A 4) (Pterm A 4) = Qterm A 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := p_square_eq_q_of_two_add_x_eq_p_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      simpa [Pterm, addD, oneD, xD, h112] using h)
  simpa [Pterm, Qterm, x2, addD, mulD, oneD, xD]
    using congrArg Subtype.val hD

theorem m12_two_add_x_eq_p_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = Pterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, _hQ, _hR, _hS⟩
  have hdiv : A.mul (Pterm A 4) (Pterm A 4) = Qterm A 4 :=
    p_square_eq_q_of_two_add_x_eq_p_hsi C H h5 h112 h
  exact lee_q_eq_p_mul_yields_wilkie C H h5 hP hdiv

theorem bl81845_common_factor_generic
    {α : Type} (add mul : α → α → α) (one k x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : mul x x = add k x) :
    let x2 := mul x x
    let x3 := mul x2 x
    let x4 := mul x3 x
    let p := add one x
    let q := add p x2
    let r := add one x3
    let s := add (add one x2) x4
    let t := add one k
    r = mul t p ∧ s = mul t q := by
  intro x2 x3 x4 p q r s t
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  constructor
  · calc
      r = add one (mul (mul x x) x) := by rfl
      _ = add one (mul (add k x) x) := by rw [h]
      _ = add one (add (mul k x) (mul x x)) := by rw [distrib_left]
      _ = add one (add (mul k x) (add k x)) := by rw [h]
      _ = mul (add one k) (add one x) := by
            rw [distrib_left]
            repeat rw [distrib]
            repeat rw [mul_one]
            repeat rw [one_mul]
            ac_rfl
      _ = mul t p := by rfl
  · have hx4sq : x4 = mul (mul x x) (mul x x) := by
      dsimp [x2, x3, x4]
      ac_rfl
    calc
      s = add (add one (mul x x)) x4 := by rfl
      _ = add (add one (mul x x)) (mul (mul x x) (mul x x)) := by
            rw [hx4sq]
      _ = add (add one (add k x)) (mul (add k x) (add k x)) := by
            rw [h]
      _ = mul (add one k) (add (add one x) (add k x)) := by
            rw [distrib_left]
            repeat rw [distrib]
            repeat rw [distrib_left]
            repeat rw [mul_one]
            repeat rw [one_mul]
            rw [h]
            ac_rfl
      _ = mul (add one k) (add (add one x) (mul x x)) := by
            rw [h]
      _ = mul t q := by rfl

theorem bl81845_common_factor_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) {k : Nat} (hk : InDomain n k)
    (h : x2 A 4 = A.add k 4) :
    Rterm A 4 = A.mul (A.add 1 k) (Pterm A 4) ∧
      Sterm A 4 = A.mul (A.add 1 k) (Qterm A 4) := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let kD : D := ⟨k, hk⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := bl81845_common_factor_generic
    (add := addD) (mul := mulD) (one := oneD) (k := kD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact h)
  constructor
  · simpa [Pterm, Rterm, x2, x3, addD, mulD, oneD, kD, xD]
      using congrArg Subtype.val hD.1
  · simpa [Pterm, Qterm, Sterm, x2, x3, x4, addD, mulD, oneD, kD, xD]
      using congrArg Subtype.val hD.2

theorem m13_x2_eq_p_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x2 A 4 = Pterm A 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have ht : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hfac := bl81845_common_factor_hsi C H h5 h1 (by
    simpa [Pterm] using h)
  have hcore := common_factor_hsi C H hP hQ hR hS ht h4 h5 hfac.1 hfac.2
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem m15_x2_eq_two_add_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x2 A 4 = A.add 2 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have ht : InDomain n (A.add 1 2) := C.add_mem h1 h2
  have hfac := bl81845_common_factor_hsi C H h5 h2 h
  have hcore := common_factor_hsi C H hP hQ hR hS ht h4 h5 hfac.1 hfac.2
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem m16_x2_eq_x_add_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : x2 A 4 = A.add 4 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have ht : InDomain n (Pterm A 4) := hP
  have hfac := bl81845_common_factor_hsi C H h5 h4 h
  have hcore := common_factor_hsi C H hP hQ hR hS ht h4 h5 hfac.1 hfac.2
  simpa [wilkieCore, wilkieP, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem r_eq_s_of_x_eq_one_add_x2_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (h : x = add one (mul x x)) :
    add one (mul (mul x x) x) =
      add (add one (mul x x)) (mul (mul (mul x x) x) x) := by
  have hx4sq :
      mul (mul (mul x x) x) x = mul (mul x x) (mul x x) := by ac_rfl
  calc
    add one (mul (mul x x) x) =
        add one (mul (mul x x) (add one (mul x x))) := by rw [← h]
    _ = add one (add (mul (mul x x) one) (mul (mul x x) (mul x x))) := by
          rw [distrib]
    _ = add one (add (mul x x) (mul (mul x x) (mul x x))) := by
          rw [mul_one]
    _ = add (add one (mul x x)) (mul (mul (mul x x) x) x) := by
          rw [hx4sq]
          ac_rfl

theorem r_eq_s_of_x_eq_one_add_x2_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : 4 = A.add 1 (x2 A 4)) :
    Rterm A 4 = Sterm A 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := r_eq_s_of_x_eq_one_add_x2_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact h)
  simpa [Rterm, Sterm, x2, x3, x4, addD, mulD, oneD, xD]
    using congrArg Subtype.val hD

theorem m11_one_add_x2_eq_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 (x2 A 4) = 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have hR : InDomain n (Rterm A 4) := by
    have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
    exact (pqrs_terms_mem_of_closed C h1 h4).2.2.1
  have hRS : Rterm A 4 = Sterm A 4 :=
    r_eq_s_of_x_eq_one_add_x2_hsi C H h5 h.symm
  have hdiv : A.mul (Rterm A 4) 1 = Sterm A 4 := by
    rw [H.mul_one hR, hRS]
  exact lee_s_eq_r_mul_yields_wilkie C H h5 h1 hdiv

theorem m09_x_add_x_eq_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 4 4 = 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, _hQ, _hR, _hS⟩
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := p_square_eq_q_of_add_idem_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact h)
  have hdiv : A.mul (Pterm A 4) (Pterm A 4) = Qterm A 4 := by
    simpa [Pterm, Qterm, x2, addD, mulD, oneD, xD] using congrArg Subtype.val hD
  exact lee_q_eq_p_mul_yields_wilkie C H h5 hP hdiv

theorem m03_x_add_x_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 4 4 = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have htwo : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hfactor := wilkie_factor_hsi C H h1 h4
  have htwoMul : A.mul (A.add 1 1) 4 = 1 := by
    calc
      A.mul (A.add 1 1) 4 = A.mul 4 (A.add 1 1) := H.mul_comm htwo h4
      _ = A.add (A.mul 4 1) (A.mul 4 1) := H.distrib h4 h1 h1
      _ = A.add 4 4 := by rw [H.mul_one h4]
      _ = 1 := h
  have hu : InDomain n (A.mul 5 (A.add 1 1)) := C.mul_mem h5 htwo
  have hdiv : 5 = A.mul (A.mul 5 (A.add 1 1)) 4 := by
    calc
      5 = A.mul 5 1 := (H.mul_one h5).symm
      _ = A.mul 5 (A.mul (A.add 1 1) 4) := by rw [htwoMul]
      _ = A.mul (A.mul 5 (A.add 1 1)) 4 := H.mul_assoc h5 htwo h4
  have hcore := divides_hsi C H hP hQ hR hS h4 h5 hu hfactor hdiv
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem m04_x_mul_x_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.mul 4 4 = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 h4
  have hu : InDomain n (A.mul 5 4) := C.mul_mem h5 h4
  have hdiv : 5 = A.mul (A.mul 5 4) 4 := by
    calc
      5 = A.mul 5 1 := (H.mul_one h5).symm
      _ = A.mul 5 (A.mul 4 4) := by rw [h]
      _ = A.mul (A.mul 5 4) 4 := H.mul_assoc h5 h4 h4
  have hcore := divides_hsi C H hP hQ hR hS h4 h5 hu hfactor hdiv
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem m08_factor_reductions_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = 4) :
    Rterm A 4 = A.mul (Pterm A 4) (Qterm A 4) ∧
      Sterm A 4 = A.mul (Qterm A 4) (Qterm A 4) := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hx : 4 = A.add (A.add 1 1) 4 := by
    calc
      4 = A.add 2 4 := h.symm
      _ = A.add (A.add 1 1) 4 := by rw [h112]
  have hxD : xD = addD (addD oneD oneD) xD := by
    apply Subtype.ext
    exact hx
  have hR := m08_r_eq_pq_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    hxD
  have hS := m08_s_eq_qq_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    hxD
  constructor
  · simpa [Pterm, Qterm, Rterm, x2, x3, addD, mulD, oneD, xD]
      using congrArg Subtype.val hR
  · simpa [Pterm, Qterm, Sterm, x2, x3, x4, addD, mulD, oneD, xD]
      using congrArg Subtype.val hS

theorem m08_two_add_x_eq_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  rcases m08_factor_reductions_hsi C H h5 h112 h with ⟨hR0, hS0⟩
  have hRFactor : Rterm A 4 = A.mul (Qterm A 4) (Pterm A 4) := by
    calc
      Rterm A 4 = A.mul (Pterm A 4) (Qterm A 4) := hR0
      _ = A.mul (Qterm A 4) (Pterm A 4) := H.mul_comm hP hQ
  have hcore := common_factor_hsi C H hP hQ hR hS hQ h4 h5 hRFactor hS0
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem m02_factor_reductions_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = 1) :
    Rterm A 4 = A.mul (Pterm A 4) (A.add (A.add 1 1) (x2 A 4)) ∧
      Sterm A 4 = A.mul (Qterm A 4) (A.add (A.add 1 1) (x2 A 4)) := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨4, h4⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hone : 1 = A.add (A.add 1 1) 4 := by
    calc
      1 = A.add 2 4 := h.symm
      _ = A.add (A.add 1 1) 4 := by rw [h112]
  have honeD : oneD = addD (addD oneD oneD) xD := by
    apply Subtype.ext
    exact hone
  have hR := m02_r_eq_p_factor_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    honeD
  have hS := m02_s_eq_q_factor_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    honeD
  constructor
  · simpa [Pterm, Rterm, x2, x3, addD, mulD, oneD, xD]
      using congrArg Subtype.val hR
  · simpa [Pterm, Qterm, Sterm, x2, x3, x4, addD, mulD, oneD, xD]
      using congrArg Subtype.val hS

theorem m02_two_add_x_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2)
    (h : A.add 2 4 = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have htwo : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hx2 : InDomain n (x2 A 4) := by
    unfold x2
    exact C.mul_mem h4 h4
  have ht : InDomain n (A.add (A.add 1 1) (x2 A 4)) := C.add_mem htwo hx2
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, hR, hS⟩
  rcases m02_factor_reductions_hsi C H h5 h112 h with ⟨hR0, hS0⟩
  have hRFactor : Rterm A 4 = A.mul (A.add (A.add 1 1) (x2 A 4)) (Pterm A 4) := by
    calc
      Rterm A 4 = A.mul (Pterm A 4) (A.add (A.add 1 1) (x2 A 4)) := hR0
      _ = A.mul (A.add (A.add 1 1) (x2 A 4)) (Pterm A 4) := H.mul_comm hP ht
  have hSFactor : Sterm A 4 = A.mul (A.add (A.add 1 1) (x2 A 4)) (Qterm A 4) := by
    calc
      Sterm A 4 = A.mul (Qterm A 4) (A.add (A.add 1 1) (x2 A 4)) := hS0
      _ = A.mul (A.add (A.add 1 1) (x2 A 4)) (Qterm A 4) := H.mul_comm hQ ht
  have hcore := common_factor_hsi C H hP hQ hR hS ht h4 h5 hRFactor hSFactor
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem m01_one_add_x_eq_one_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 4 = 1) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, _hR, _hS⟩
  have hP1 : Pterm A 4 = 1 := by
    simpa [Pterm] using h
  have hdiv : A.mul (Pterm A 4) (Qterm A 4) = Qterm A 4 := by
    calc
      A.mul (Pterm A 4) (Qterm A 4) = A.mul 1 (Qterm A 4) := by rw [hP1]
      _ = A.mul (Qterm A 4) 1 := H.mul_comm h1 hQ
      _ = Qterm A 4 := H.mul_one hQ
  exact lee_q_eq_p_mul_yields_wilkie C H h5 hQ hdiv

theorem m07_one_add_x_eq_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.add 1 4 = 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, _hQ, _hR, _hS⟩
  have hP4 : Pterm A 4 = 4 := by
    simpa [Pterm] using h
  have hx2 : InDomain n (x2 A 4) := by
    unfold x2
    exact C.mul_mem h4 h4
  have hleft_distrib :
      A.mul (A.add 1 4) 4 = A.add (A.mul 1 4) (A.mul 4 4) := by
    calc
      A.mul (A.add 1 4) 4 = A.mul 4 (A.add 1 4) :=
        H.mul_comm (C.add_mem h1 h4) h4
      _ = A.add (A.mul 4 1) (A.mul 4 4) := H.distrib h4 h1 h4
      _ = A.add (A.mul 1 4) (A.mul 4 4) := by
        rw [H.mul_comm h4 h1]
  have hdiv : A.mul (Pterm A 4) 4 = Qterm A 4 := by
    calc
      A.mul (Pterm A 4) 4 = A.mul (A.add 1 4) 4 := by rfl
      _ = A.add (A.mul 1 4) (A.mul 4 4) := hleft_distrib
      _ = A.add 4 (A.mul 4 4) := by
        rw [H.mul_comm h1 h4, H.mul_one h4]
      _ = A.add (Pterm A 4) (x2 A 4) := by
        rw [hP4]
        rfl
      _ = Qterm A 4 := by rfl
  exact lee_q_eq_p_mul_yields_wilkie C H h5 h4 hdiv

theorem m10_x_mul_x_eq_x_yields_wilkie
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h : A.mul 4 4 = 4) :
    wilkieP A 4 5 4 = wilkieP A 5 4 4 := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases pqrs_terms_mem_of_closed C h1 h4 with ⟨hP, hQ, _hR, _hS⟩
  have hx2eq : x2 A 4 = 4 := by
    simpa [x2] using h
  have hx3eq : x3 A 4 = 4 := by
    unfold x3
    rw [hx2eq, h]
  have hx4eq : x4 A 4 = 4 := by
    unfold x4
    rw [hx3eq, h]
  have hR : Rterm A 4 = Pterm A 4 := by
    simp [Rterm, Pterm, hx3eq]
  have hS : Sterm A 4 = Qterm A 4 := by
    simp [Sterm, Qterm, Pterm, x2, hx4eq, h]
  have hxLeft :
      InDomain n
        (A.exp
          (A.add (A.exp (Pterm A 4) 5) (A.exp (Qterm A 4) 5)) 4) :=
    C.exp_mem (C.add_mem (C.exp_mem hP h5) (C.exp_mem hQ h5)) h4
  have hxRight :
      InDomain n
        (A.exp
          (A.add (A.exp (Pterm A 4) 4) (A.exp (Qterm A 4) 4)) 5) :=
    C.exp_mem (C.add_mem (C.exp_mem hP h4) (C.exp_mem hQ h4)) h5
  have hcore :
      wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 4 5 =
        wilkieCore A (Pterm A 4) (Qterm A 4) (Rterm A 4) (Sterm A 4) 5 4 := by
    rw [hR, hS]
    unfold wilkieCore
    exact H.mul_comm hxLeft hxRight
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem fixedBurrisLeeConsequences_of_wilkieFails
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) (hFail : WilkieFailsAt A 4 5 4)
    (h112 : A.add 1 1 = 2) :
    A.add 1 4 ≠ 1 ∧
    A.add 2 4 ≠ 1 ∧
    A.add 4 4 ≠ 1 ∧
    A.mul 4 4 ≠ 1 ∧
    A.add 1 4 ≠ 4 ∧
    A.add 2 4 ≠ 4 ∧
    A.add 4 4 ≠ 4 ∧
    A.mul 4 4 ≠ 4 := by
  constructor
  · intro h
    exact hFail (m01_one_add_x_eq_one_yields_wilkie C H h5 h)
  · constructor
    · intro h
      exact hFail (m02_two_add_x_eq_one_yields_wilkie C H h5 h112 h)
    · constructor
      · intro h
        exact hFail (m03_x_add_x_eq_one_yields_wilkie C H h5 h)
      · constructor
        · intro h
          exact hFail (m04_x_mul_x_eq_one_yields_wilkie C H h5 h)
        · constructor
          · intro h
            exact hFail (m07_one_add_x_eq_x_yields_wilkie C H h5 h)
          · constructor
            · intro h
              exact hFail (m08_two_add_x_eq_x_yields_wilkie C H h5 h112 h)
            · constructor
              · intro h
                exact hFail (m09_x_add_x_eq_x_yields_wilkie C H h5 h)
              · intro h
                exact hFail (m10_x_mul_x_eq_x_yields_wilkie C H h5 h)

def wilkieTermExpr (A : Algebra) : Nat → Nat
  | 0 => Pterm A 4
  | 1 => A.exp (Pterm A 4) 5
  | 2 => A.exp (Pterm A 4) 4
  | 3 => x2 A 4
  | 4 => Qterm A 4
  | 5 => A.exp (Qterm A 4) 4
  | 6 => A.exp (Qterm A 4) 5
  | 7 => x3 A 4
  | 8 => Rterm A 4
  | 9 => A.exp (Rterm A 4) 4
  | 10 => A.exp (Rterm A 4) 5
  | 11 => x4 A 4
  | 12 => A.add 1 (x2 A 4)
  | 13 => Sterm A 4
  | 14 => A.exp (Sterm A 4) 4
  | 15 => A.exp (Sterm A 4) 5
  | 16 => A.add (A.exp (Pterm A 4) 5) (A.exp (Qterm A 4) 5)
  | 17 => A.add (A.exp (Pterm A 4) 4) (A.exp (Qterm A 4) 4)
  | 18 => A.exp (A.add (A.exp (Pterm A 4) 4) (A.exp (Qterm A 4) 4)) 5
  | 19 => A.exp (A.add (A.exp (Pterm A 4) 5) (A.exp (Qterm A 4) 5)) 4
  | 20 => A.add (A.exp (Rterm A 4) 4) (A.exp (Sterm A 4) 4)
  | 21 => A.add (A.exp (Rterm A 4) 5) (A.exp (Sterm A 4) 5)
  | 22 => A.exp (A.add (A.exp (Rterm A 4) 4) (A.exp (Sterm A 4) 4)) 5
  | 23 => A.exp (A.add (A.exp (Rterm A 4) 5) (A.exp (Sterm A 4) 5)) 4
  | 24 =>
      A.mul
        (A.exp (A.add (A.exp (Pterm A 4) 5) (A.exp (Qterm A 4) 5)) 4)
        (A.exp (A.add (A.exp (Rterm A 4) 4) (A.exp (Sterm A 4) 4)) 5)
  | 25 =>
      A.mul
        (A.exp (A.add (A.exp (Pterm A 4) 4) (A.exp (Qterm A 4) 4)) 5)
        (A.exp (A.add (A.exp (Rterm A 4) 5) (A.exp (Sterm A 4) 5)) 4)
  | _ => 1

theorem wilkieTermExpr_24 (A : Algebra) :
    wilkieTermExpr A 24 = wilkieP A 4 5 4 := by
  rfl

theorem wilkieTermExpr_25 (A : Algebra) :
    wilkieTermExpr A 25 = wilkieP A 5 4 4 := by
  rfl

def TermDecodedAt (n : Nat) (τ : Assignment) (A : Algebra) (termIndex : Nat) : Prop :=
  ∀ v, InDomain n v → (wilkieTermExpr A termIndex = v ↔ τ (termVar n termIndex v))

def EncodesWilkieTerms (n : Nat) (τ : Assignment) (A : Algebra) : Prop :=
  ∀ termIndex, TermDecodedAt n τ A termIndex

def argValue (A : Algebra) : Arg → Nat
  | .const value => value
  | .term termIndex => wilkieTermExpr A termIndex

def ArgDecoded (n : Nat) (τ : Assignment) (A : Algebra) : Arg → Prop
  | .const _ => True
  | .term termIndex => TermDecodedAt n τ A termIndex

def WilkieTermValuesInDomain (n : Nat) (A : Algebra) : Prop :=
  ∀ p, p ∈ enumerate termSpecs → InDomain n (wilkieTermExpr A p.1)

theorem wilkieTermValuesInDomain_of_closed
    {n : Nat} {A : Algebra} (C : Closed n A) (h5 : InDomain n 5) :
    WilkieTermValuesInDomain n A := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have m0 : InDomain n (wilkieTermExpr A 0) := C.add_mem h1 h4
  have m1 : InDomain n (wilkieTermExpr A 1) := C.exp_mem m0 h5
  have m2 : InDomain n (wilkieTermExpr A 2) := C.exp_mem m0 h4
  have m3 : InDomain n (wilkieTermExpr A 3) := C.mul_mem h4 h4
  have m4 : InDomain n (wilkieTermExpr A 4) := C.add_mem m0 m3
  have m5 : InDomain n (wilkieTermExpr A 5) := C.exp_mem m4 h4
  have m6 : InDomain n (wilkieTermExpr A 6) := C.exp_mem m4 h5
  have m7 : InDomain n (wilkieTermExpr A 7) := C.mul_mem m3 h4
  have m8 : InDomain n (wilkieTermExpr A 8) := C.add_mem h1 m7
  have m9 : InDomain n (wilkieTermExpr A 9) := C.exp_mem m8 h4
  have m10 : InDomain n (wilkieTermExpr A 10) := C.exp_mem m8 h5
  have m11 : InDomain n (wilkieTermExpr A 11) := C.mul_mem m7 h4
  have m12 : InDomain n (wilkieTermExpr A 12) := C.add_mem h1 m3
  have m13 : InDomain n (wilkieTermExpr A 13) := C.add_mem m12 m11
  have m14 : InDomain n (wilkieTermExpr A 14) := C.exp_mem m13 h4
  have m15 : InDomain n (wilkieTermExpr A 15) := C.exp_mem m13 h5
  have m16 : InDomain n (wilkieTermExpr A 16) := C.add_mem m1 m6
  have m17 : InDomain n (wilkieTermExpr A 17) := C.add_mem m2 m5
  have m18 : InDomain n (wilkieTermExpr A 18) := C.exp_mem m17 h5
  have m19 : InDomain n (wilkieTermExpr A 19) := C.exp_mem m16 h4
  have m20 : InDomain n (wilkieTermExpr A 20) := C.add_mem m9 m14
  have m21 : InDomain n (wilkieTermExpr A 21) := C.add_mem m10 m15
  have m22 : InDomain n (wilkieTermExpr A 22) := C.exp_mem m20 h5
  have m23 : InDomain n (wilkieTermExpr A 23) := C.exp_mem m21 h4
  have m24 : InDomain n (wilkieTermExpr A 24) := C.mul_mem m19 m22
  have m25 : InDomain n (wilkieTermExpr A 25) := C.mul_mem m18 m23
  intro p hp
  simp [enumerate, enumerateFrom, termSpecs] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h <;> assumption

def WilkieTermSpecArgsInDomain (n : Nat) (A : Algebra) : Prop :=
  ∀ p, p ∈ enumerate termSpecs →
    InDomain n (argValue A p.2.left) ∧ InDomain n (argValue A p.2.right)

def WilkieTermSpecsConsistent (A : Algebra) : Prop :=
  ∀ p, p ∈ enumerate termSpecs →
    wilkieTermExpr A p.1 =
      evalOp A p.2.op (argValue A p.2.left) (argValue A p.2.right)

theorem wilkieTermSpecsConsistent_all (A : Algebra) :
    WilkieTermSpecsConsistent A := by
  intro p hp
  simp [enumerate, enumerateFrom, termSpecs] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h; rfl

theorem wilkieTermSpecArgsInDomain_of_terms
    {n : Nat} {A : Algebra}
    (M : WilkieTermValuesInDomain n A) (h5 : InDomain n 5) :
    WilkieTermSpecArgsInDomain n A := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have m0 : InDomain n (wilkieTermExpr A 0) :=
    M (0, ⟨.add, .const 1, .const 4⟩) (by decide)
  have m1 : InDomain n (wilkieTermExpr A 1) :=
    M (1, ⟨.exp, .term 0, .const 5⟩) (by decide)
  have m2 : InDomain n (wilkieTermExpr A 2) :=
    M (2, ⟨.exp, .term 0, .const 4⟩) (by decide)
  have m3 : InDomain n (wilkieTermExpr A 3) :=
    M (3, ⟨.mul, .const 4, .const 4⟩) (by decide)
  have m4 : InDomain n (wilkieTermExpr A 4) :=
    M (4, ⟨.add, .term 0, .term 3⟩) (by decide)
  have m5 : InDomain n (wilkieTermExpr A 5) :=
    M (5, ⟨.exp, .term 4, .const 4⟩) (by decide)
  have m6 : InDomain n (wilkieTermExpr A 6) :=
    M (6, ⟨.exp, .term 4, .const 5⟩) (by decide)
  have m7 : InDomain n (wilkieTermExpr A 7) :=
    M (7, ⟨.mul, .term 3, .const 4⟩) (by decide)
  have m8 : InDomain n (wilkieTermExpr A 8) :=
    M (8, ⟨.add, .const 1, .term 7⟩) (by decide)
  have m9 : InDomain n (wilkieTermExpr A 9) :=
    M (9, ⟨.exp, .term 8, .const 4⟩) (by decide)
  have m10 : InDomain n (wilkieTermExpr A 10) :=
    M (10, ⟨.exp, .term 8, .const 5⟩) (by decide)
  have m11 : InDomain n (wilkieTermExpr A 11) :=
    M (11, ⟨.mul, .term 7, .const 4⟩) (by decide)
  have m12 : InDomain n (wilkieTermExpr A 12) :=
    M (12, ⟨.add, .const 1, .term 3⟩) (by decide)
  have m13 : InDomain n (wilkieTermExpr A 13) :=
    M (13, ⟨.add, .term 12, .term 11⟩) (by decide)
  have m14 : InDomain n (wilkieTermExpr A 14) :=
    M (14, ⟨.exp, .term 13, .const 4⟩) (by decide)
  have m15 : InDomain n (wilkieTermExpr A 15) :=
    M (15, ⟨.exp, .term 13, .const 5⟩) (by decide)
  have m16 : InDomain n (wilkieTermExpr A 16) :=
    M (16, ⟨.add, .term 1, .term 6⟩) (by decide)
  have m17 : InDomain n (wilkieTermExpr A 17) :=
    M (17, ⟨.add, .term 2, .term 5⟩) (by decide)
  have m18 : InDomain n (wilkieTermExpr A 18) :=
    M (18, ⟨.exp, .term 17, .const 5⟩) (by decide)
  have m19 : InDomain n (wilkieTermExpr A 19) :=
    M (19, ⟨.exp, .term 16, .const 4⟩) (by decide)
  have m20 : InDomain n (wilkieTermExpr A 20) :=
    M (20, ⟨.add, .term 9, .term 14⟩) (by decide)
  have m21 : InDomain n (wilkieTermExpr A 21) :=
    M (21, ⟨.add, .term 10, .term 15⟩) (by decide)
  have m22 : InDomain n (wilkieTermExpr A 22) :=
    M (22, ⟨.exp, .term 20, .const 5⟩) (by decide)
  have m23 : InDomain n (wilkieTermExpr A 23) :=
    M (23, ⟨.exp, .term 21, .const 4⟩) (by decide)
  have m24 : InDomain n (wilkieTermExpr A 24) :=
    M (24, ⟨.mul, .term 19, .term 22⟩) (by decide)
  have m25 : InDomain n (wilkieTermExpr A 25) :=
    M (25, ⟨.mul, .term 18, .term 23⟩) (by decide)
  intro p hp
  simp [enumerate, enumerateFrom, termSpecs] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    cases h
    constructor <;> simp [argValue] <;> first | exact h1 | exact h4 | exact h5 | assumption

def AddTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ i j k, InDomain n i ∧ InDomain n j ∧ InDomain n k ∧
    v = addVar n i j k ∧ A.add i j = k

def MulTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ i j k, InDomain n i ∧ InDomain n j ∧ InDomain n k ∧
    v = mulVar n i j k ∧ A.mul i j = k

def ExpTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ i j k, InDomain n i ∧ InDomain n j ∧ InDomain n k ∧
    v = expVar n i j k ∧ A.exp i j = k

def Add2TableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ i j k l, InDomain n i ∧ InDomain n j ∧ InDomain n k ∧ InDomain n l ∧
    v = add2Var n i j k l ∧
    A.add i (A.add j k) = l ∧ A.add (A.add i j) k = l

def Mul2TableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ i j k l, InDomain n i ∧ InDomain n j ∧ InDomain n k ∧ InDomain n l ∧
    v = mul2Var n i j k l ∧
    A.mul i (A.mul j k) = l ∧ A.mul (A.mul i j) k = l

def DistTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ x y z l, InDomain n x ∧ InDomain n y ∧ InDomain n z ∧ InDomain n l ∧
    v = distVar n x y z l ∧
    A.mul x (A.add y z) = l ∧ A.add (A.mul x y) (A.mul x z) = l

def ExpAddTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ x y z l, InDomain n x ∧ InDomain n y ∧ InDomain n z ∧ InDomain n l ∧
    v = expAddVar n x y z l ∧
    A.exp x (A.add y z) = l ∧ A.mul (A.exp x y) (A.exp x z) = l

def ExpMulTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ x y z l, InDomain n x ∧ InDomain n y ∧ InDomain n z ∧ InDomain n l ∧
    v = expMulVar n x y z l ∧
    A.exp (A.mul x y) z = l ∧ A.mul (A.exp x z) (A.exp y z) = l

def Exp2TableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ x y z l, InDomain n x ∧ InDomain n y ∧ InDomain n z ∧ InDomain n l ∧
    v = exp2Var n x y z l ∧
    A.exp (A.exp x y) z = l ∧ A.exp x (A.mul y z) = l

def TermTableTruth (n : Nat) (A : Algebra) (v : Nat) : Prop :=
  ∃ termIndex value, InDomain n value ∧
    v = termVar n termIndex value ∧ wilkieTermExpr A termIndex = value

def modelAssignment (n : Nat) (A : Algebra) : Assignment :=
  fun v =>
    if v ≤ pairCount n * n then AddTableTruth n A v
    else if v ≤ 2 * pairCount n * n then MulTableTruth n A v
    else if v ≤ primaryCount n then ExpTableTruth n A v
    else if v ≤ mul2Base n then Add2TableTruth n A v
    else if v ≤ distBase n then Mul2TableTruth n A v
    else if v ≤ expAddBase n then DistTableTruth n A v
    else if v ≤ expMulBase n then ExpAddTableTruth n A v
    else if v ≤ exp2Base n then ExpMulTableTruth n A v
    else if v ≤ wilkieTermBase n then Exp2TableTruth n A v
    else TermTableTruth n A v

theorem addTableTruth_addVar_iff
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    AddTableTruth n A (addVar n i j k) ↔ A.add i j = k := by
  constructor
  · intro h
    rcases h with ⟨i', j', k', hi', hj', hk', hvar, hvalue⟩
    have hsplit := addVar_inj_canonical hi hj hk hi' hj' hk' hvar
    have hadd := H.add_eq_of_canonical_eq hi hj hi' hj' hsplit.1
    calc
      A.add i j = A.add i' j' := hadd
      _ = k' := hvalue
      _ = k := hsplit.2.symm
  · intro h
    exact ⟨i, j, k, hi, hj, hk, rfl, h⟩

theorem mulTableTruth_mulVar_iff
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    MulTableTruth n A (mulVar n i j k) ↔ A.mul i j = k := by
  constructor
  · intro h
    rcases h with ⟨i', j', k', hi', hj', hk', hvar, hvalue⟩
    have hsplit := mulVar_inj_canonical hi hj hk hi' hj' hk' hvar
    have hmul := H.mul_eq_of_canonical_eq hi hj hi' hj' hsplit.1
    calc
      A.mul i j = A.mul i' j' := hmul
      _ = k' := hvalue
      _ = k := hsplit.2.symm
  · intro h
    exact ⟨i, j, k, hi, hj, hk, rfl, h⟩

theorem expTableTruth_expVar_iff
    {n : Nat} {A : Algebra}
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    ExpTableTruth n A (expVar n i j k) ↔ A.exp i j = k := by
  constructor
  · intro h
    rcases h with ⟨i', j', k', hi', hj', hk', hvar, hvalue⟩
    have hsplit := expVar_inj hi hj hk hi' hj' hk' hvar
    calc
      A.exp i j = A.exp i' j' := by simp [hsplit.1, hsplit.2.1]
      _ = k' := hvalue
      _ = k := hsplit.2.2.symm
  · intro h
    exact ⟨i, j, k, hi, hj, hk, rfl, h⟩

theorem modelAssignment_addVar_iff
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    modelAssignment n A (addVar n i j k) ↔ A.add i j = k := by
  have hblock := addVar_block hi hj hk
  unfold modelAssignment
  rw [if_pos hblock.2]
  exact addTableTruth_addVar_iff H hi hj hk

theorem modelAssignment_mulVar_iff
    {n : Nat} {A : Algebra} (H : HSI n A)
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    modelAssignment n A (mulVar n i j k) ↔ A.mul i j = k := by
  have hblock := mulVar_block hi hj hk
  unfold modelAssignment
  rw [if_neg (Nat.not_le_of_gt hblock.1)]
  rw [if_pos hblock.2]
  exact mulTableTruth_mulVar_iff H hi hj hk

theorem modelAssignment_expVar_iff
    {n : Nat} {A : Algebra}
    {i j k : Nat} (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    modelAssignment n A (expVar n i j k) ↔ A.exp i j = k := by
  have hblock := expVar_block hi hj hk
  have hprimary1 : pairCount n * n ≤ 2 * pairCount n * n := by
    have htwice : 2 * pairCount n * n = pairCount n * n + pairCount n * n := by
      rw [Nat.two_mul, Nat.add_mul]
    rw [htwice]
    exact Nat.le_add_right _ _
  have hnotAdd : ¬ expVar n i j k ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hprimary1 hblock.1)
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg (Nat.not_le_of_gt hblock.1)]
  rw [if_pos hblock.2]
  exact expTableTruth_expVar_iff hi hj hk

theorem add2TableTruth_add2Var_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    Add2TableTruth n A (add2Var n i j k l) ↔
      A.add i (A.add j k) = l ∧ A.add (A.add i j) k = l := by
  constructor
  · intro h
    rcases h with ⟨i', j', k', l', hi', hj', hk', hl', hvar, hleft', hright'⟩
    have hsplit := add2Var_inj_canonical hi hj hk hl hi' hj' hk' hl' hvar
    have hrightEq := H.add3_right_eq_of_canonical_eq C hi hj hk hi' hj' hk'
      hsplit.1 hsplit.2.1
    have hright : A.add (A.add i j) k = l := by
      calc
        A.add (A.add i j) k = A.add (A.add i' j') k' := hrightEq
        _ = l' := hright'
        _ = l := hsplit.2.2.symm
    have hleft : A.add i (A.add j k) = l := by
      calc
        A.add i (A.add j k) = A.add (A.add i j) k := H.add_assoc hi hj hk
        _ = l := hright
    exact ⟨hleft, hright⟩
  · intro h
    exact ⟨i, j, k, l, hi, hj, hk, hl, rfl, h.1, h.2⟩

theorem mul2TableTruth_mul2Var_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    Mul2TableTruth n A (mul2Var n i j k l) ↔
      A.mul i (A.mul j k) = l ∧ A.mul (A.mul i j) k = l := by
  constructor
  · intro h
    rcases h with ⟨i', j', k', l', hi', hj', hk', hl', hvar, hleft', hright'⟩
    have hsplit := mul2Var_inj_canonical hi hj hk hl hi' hj' hk' hl' hvar
    have hrightEq := H.mul3_right_eq_of_canonical_eq C hi hj hk hi' hj' hk'
      hsplit.1 hsplit.2.1
    have hright : A.mul (A.mul i j) k = l := by
      calc
        A.mul (A.mul i j) k = A.mul (A.mul i' j') k' := hrightEq
        _ = l' := hright'
        _ = l := hsplit.2.2.symm
    have hleft : A.mul i (A.mul j k) = l := by
      calc
        A.mul i (A.mul j k) = A.mul (A.mul i j) k := H.mul_assoc hi hj hk
        _ = l := hright
    exact ⟨hleft, hright⟩
  · intro h
    exact ⟨i, j, k, l, hi, hj, hk, hl, rfl, h.1, h.2⟩

theorem primary1_le_primaryCount (n : Nat) :
    pairCount n * n ≤ primaryCount n := by
  have htwice : 2 * pairCount n * n = pairCount n * n + pairCount n * n := by
    rw [Nat.two_mul, Nat.add_mul]
  unfold primaryCount
  rw [htwice]
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem primary2_le_primaryCount (n : Nat) :
    2 * pairCount n * n ≤ primaryCount n := by
  unfold primaryCount
  exact Nat.le_add_right _ _

theorem primary_le_mul2Base (n : Nat) :
    primaryCount n ≤ mul2Base n := by
  unfold mul2Base add2Base
  exact Nat.le_add_right _ _

theorem mul2Base_le_distBase (n : Nat) :
    mul2Base n ≤ distBase n := by
  unfold distBase
  exact Nat.le_add_right _ _

theorem distBase_le_expAddBase (n : Nat) :
    distBase n ≤ expAddBase n := by
  unfold expAddBase
  exact Nat.le_add_right _ _

theorem expAddBase_le_expMulBase (n : Nat) :
    expAddBase n ≤ expMulBase n := by
  unfold expMulBase
  exact Nat.le_add_right _ _

theorem expMulBase_le_exp2Base (n : Nat) :
    expMulBase n ≤ exp2Base n := by
  unfold exp2Base
  exact Nat.le_add_right _ _

theorem primary_le_distBase (n : Nat) :
    primaryCount n ≤ distBase n :=
  Nat.le_trans (primary_le_mul2Base n) (mul2Base_le_distBase n)

theorem primary_le_expAddBase (n : Nat) :
    primaryCount n ≤ expAddBase n :=
  Nat.le_trans (primary_le_distBase n) (distBase_le_expAddBase n)

theorem primary_le_expMulBase (n : Nat) :
    primaryCount n ≤ expMulBase n :=
  Nat.le_trans (primary_le_expAddBase n) (expAddBase_le_expMulBase n)

theorem primary_le_exp2Base (n : Nat) :
    primaryCount n ≤ exp2Base n :=
  Nat.le_trans (primary_le_expMulBase n) (expMulBase_le_exp2Base n)

theorem exp2Base_le_wilkieTermBase (n : Nat) :
    exp2Base n ≤ wilkieTermBase n := by
  unfold wilkieTermBase
  exact Nat.le_add_right _ _

theorem primary_le_wilkieTermBase (n : Nat) :
    primaryCount n ≤ wilkieTermBase n :=
  Nat.le_trans (primary_le_exp2Base n) (exp2Base_le_wilkieTermBase n)

theorem modelAssignment_add2Var_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    modelAssignment n A (add2Var n i j k l) ↔
      A.add i (A.add j k) = l ∧ A.add (A.add i j) k = l := by
  have hblock := add2Var_block hi hj hk hl
  have hnotAdd : ¬ add2Var n i j k l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (by
      unfold add2Base at hblock
      exact primary1_le_primaryCount n) hblock.1)
  have hnotMul : ¬ add2Var n i j k l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (by
      unfold add2Base at hblock
      exact primary2_le_primaryCount n) hblock.1)
  have hnotExp : ¬ add2Var n i j k l ≤ primaryCount n :=
    Nat.not_le_of_gt (by simpa [add2Base] using hblock.1)
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_pos hblock.2]
  exact add2TableTruth_add2Var_iff C H hi hj hk hl

theorem modelAssignment_mul2Var_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) (hl : InDomain n l) :
    modelAssignment n A (mul2Var n i j k l) ↔
      A.mul i (A.mul j k) = l ∧ A.mul (A.mul i j) k = l := by
  have hblock := mul2Var_block hi hj hk hl
  have hprimary_le_mul2 : primaryCount n ≤ mul2Base n := by
    unfold mul2Base add2Base
    exact Nat.le_add_right _ _
  have hnotAdd : ¬ mul2Var n i j k l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) hprimary_le_mul2) hblock.1)
  have hnotMul : ¬ mul2Var n i j k l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) hprimary_le_mul2) hblock.1)
  have hnotExp : ¬ mul2Var n i j k l ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hprimary_le_mul2 hblock.1)
  have hnotAdd2 : ¬ mul2Var n i j k l ≤ mul2Base n :=
    Nat.not_le_of_gt hblock.1
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_pos hblock.2]
  exact mul2TableTruth_mul2Var_iff C H hi hj hk hl

theorem distTableTruth_distVar_iff
    {n : Nat} {A : Algebra} (_C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    DistTableTruth n A (distVar n x y z l) ↔
      A.mul x (A.add y z) = l ∧ A.add (A.mul x y) (A.mul x z) = l := by
  constructor
  · intro h
    rcases h with ⟨x', y', z', l', hx', hy', hz', hl', hvar, hleft', hright'⟩
    have hsplit := distVar_inj_canonical hx hy hz hl hx' hy' hz' hl' hvar
    have hxEq := hsplit.1
    have hyzAdd := H.add_eq_of_canonical_eq hy hz hy' hz' hsplit.2.1
    have hleft : A.mul x (A.add y z) = l := by
      calc
        A.mul x (A.add y z) = A.mul x' (A.add y' z') := by
          simp [hxEq, hyzAdd]
        _ = l' := hleft'
        _ = l := hsplit.2.2.symm
    have hright : A.add (A.mul x y) (A.mul x z) = l := by
      calc
        A.add (A.mul x y) (A.mul x z) = A.mul x (A.add y z) := (H.distrib hx hy hz).symm
        _ = l := hleft
    exact ⟨hleft, hright⟩
  · intro h
    exact ⟨x, y, z, l, hx, hy, hz, hl, rfl, h.1, h.2⟩

theorem expAddTableTruth_expAddVar_iff
    {n : Nat} {A : Algebra} (_C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    ExpAddTableTruth n A (expAddVar n x y z l) ↔
      A.exp x (A.add y z) = l ∧ A.mul (A.exp x y) (A.exp x z) = l := by
  constructor
  · intro h
    rcases h with ⟨x', y', z', l', hx', hy', hz', hl', hvar, hleft', hright'⟩
    have hsplit := expAddVar_inj_canonical hx hy hz hl hx' hy' hz' hl' hvar
    have hxEq := hsplit.1
    have hyzAdd := H.add_eq_of_canonical_eq hy hz hy' hz' hsplit.2.1
    have hleft : A.exp x (A.add y z) = l := by
      calc
        A.exp x (A.add y z) = A.exp x' (A.add y' z') := by
          simp [hxEq, hyzAdd]
        _ = l' := hleft'
        _ = l := hsplit.2.2.symm
    have hright : A.mul (A.exp x y) (A.exp x z) = l := by
      calc
        A.mul (A.exp x y) (A.exp x z) = A.exp x (A.add y z) := (H.exp_add hx hy hz).symm
        _ = l := hleft
    exact ⟨hleft, hright⟩
  · intro h
    exact ⟨x, y, z, l, hx, hy, hz, hl, rfl, h.1, h.2⟩

theorem expMulTableTruth_expMulVar_iff
    {n : Nat} {A : Algebra} (_C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    ExpMulTableTruth n A (expMulVar n x y z l) ↔
      A.exp (A.mul x y) z = l ∧ A.mul (A.exp x z) (A.exp y z) = l := by
  constructor
  · intro h
    rcases h with ⟨x', y', z', l', hx', hy', hz', hl', hvar, hleft', hright'⟩
    have hsplit := expMulVar_inj_canonical hx hy hz hl hx' hy' hz' hl' hvar
    have hxyMul := H.mul_eq_of_canonical_eq hx hy hx' hy' hsplit.1
    have hleft : A.exp (A.mul x y) z = l := by
      calc
        A.exp (A.mul x y) z = A.exp (A.mul x' y') z' := by
          simp [hxyMul, hsplit.2.1]
        _ = l' := hleft'
        _ = l := hsplit.2.2.symm
    have hright : A.mul (A.exp x z) (A.exp y z) = l := by
      calc
        A.mul (A.exp x z) (A.exp y z) = A.exp (A.mul x y) z := (H.exp_mul hx hy hz).symm
        _ = l := hleft
    exact ⟨hleft, hright⟩
  · intro h
    exact ⟨x, y, z, l, hx, hy, hz, hl, rfl, h.1, h.2⟩

theorem modelAssignment_distVar_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    modelAssignment n A (distVar n x y z l) ↔
      A.mul x (A.add y z) = l ∧ A.add (A.mul x y) (A.mul x z) = l := by
  have hblock := distVar_block hx hy hz hl
  have hnotAdd : ¬ distVar n x y z l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) (primary_le_distBase n)) hblock.1)
  have hnotMul : ¬ distVar n x y z l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) (primary_le_distBase n)) hblock.1)
  have hnotExp : ¬ distVar n x y z l ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (primary_le_distBase n) hblock.1)
  have hnotAdd2 : ¬ distVar n x y z l ≤ mul2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (mul2Base_le_distBase n) hblock.1)
  have hnotMul2 : ¬ distVar n x y z l ≤ distBase n :=
    Nat.not_le_of_gt hblock.1
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_neg hnotMul2]
  rw [if_pos hblock.2]
  exact distTableTruth_distVar_iff C H hx hy hz hl

theorem modelAssignment_expAddVar_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    modelAssignment n A (expAddVar n x y z l) ↔
      A.exp x (A.add y z) = l ∧ A.mul (A.exp x y) (A.exp x z) = l := by
  have hblock := expAddVar_block hx hy hz hl
  have hnotAdd : ¬ expAddVar n x y z l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) (primary_le_expAddBase n)) hblock.1)
  have hnotMul : ¬ expAddVar n x y z l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) (primary_le_expAddBase n)) hblock.1)
  have hnotExp : ¬ expAddVar n x y z l ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (primary_le_expAddBase n) hblock.1)
  have hnotAdd2 : ¬ expAddVar n x y z l ≤ mul2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (mul2Base_le_distBase n) (distBase_le_expAddBase n)) hblock.1)
  have hnotMul2 : ¬ expAddVar n x y z l ≤ distBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (distBase_le_expAddBase n) hblock.1)
  have hnotDist : ¬ expAddVar n x y z l ≤ expAddBase n :=
    Nat.not_le_of_gt hblock.1
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_neg hnotMul2]
  rw [if_neg hnotDist]
  rw [if_pos hblock.2]
  exact expAddTableTruth_expAddVar_iff C H hx hy hz hl

theorem modelAssignment_expMulVar_iff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    modelAssignment n A (expMulVar n x y z l) ↔
      A.exp (A.mul x y) z = l ∧ A.mul (A.exp x z) (A.exp y z) = l := by
  have hblock := expMulVar_block hx hy hz hl
  have hnotAdd : ¬ expMulVar n x y z l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) (primary_le_expMulBase n)) hblock.1)
  have hnotMul : ¬ expMulVar n x y z l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) (primary_le_expMulBase n)) hblock.1)
  have hnotExp : ¬ expMulVar n x y z l ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (primary_le_expMulBase n) hblock.1)
  have hnotAdd2 : ¬ expMulVar n x y z l ≤ mul2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (mul2Base_le_distBase n)
        (Nat.le_trans (distBase_le_expAddBase n) (expAddBase_le_expMulBase n))) hblock.1)
  have hnotMul2 : ¬ expMulVar n x y z l ≤ distBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (distBase_le_expAddBase n) (expAddBase_le_expMulBase n)) hblock.1)
  have hnotDist : ¬ expMulVar n x y z l ≤ expAddBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (expAddBase_le_expMulBase n) hblock.1)
  have hnotExpAdd : ¬ expMulVar n x y z l ≤ expMulBase n :=
    Nat.not_le_of_gt hblock.1
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_neg hnotMul2]
  rw [if_neg hnotDist]
  rw [if_neg hnotExpAdd]
  rw [if_pos hblock.2]
  exact expMulTableTruth_expMulVar_iff C H hx hy hz hl

theorem exp2TableTruth_exp2Var_iff
    {n : Nat} {A : Algebra}
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    Exp2TableTruth n A (exp2Var n x y z l) ↔
      A.exp (A.exp x y) z = l ∧ A.exp x (A.mul y z) = l := by
  constructor
  · intro h
    rcases h with ⟨x', y', z', l', hx', hy', hz', hl', hvar, hleft', hright'⟩
    have hsplit := exp2Var_inj hx hy hz hl hx' hy' hz' hl' hvar
    constructor
    · calc
        A.exp (A.exp x y) z = A.exp (A.exp x' y') z' := by
          simp [hsplit.1, hsplit.2.1, hsplit.2.2.1]
        _ = l' := hleft'
        _ = l := hsplit.2.2.2.symm
    · calc
        A.exp x (A.mul y z) = A.exp x' (A.mul y' z') := by
          simp [hsplit.1, hsplit.2.1, hsplit.2.2.1]
        _ = l' := hright'
        _ = l := hsplit.2.2.2.symm
  · intro h
    exact ⟨x, y, z, l, hx, hy, hz, hl, rfl, h.1, h.2⟩

theorem modelAssignment_exp2Var_iff
    {n : Nat} {A : Algebra}
    {x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) (hl : InDomain n l) :
    modelAssignment n A (exp2Var n x y z l) ↔
      A.exp (A.exp x y) z = l ∧ A.exp x (A.mul y z) = l := by
  have hblock := exp2Var_block hx hy hz hl
  have hprimary_le_exp2 : primaryCount n ≤ exp2Base n := by
    unfold exp2Base expMulBase expAddBase distBase mul2Base add2Base
    omega
  have hmul2_le_exp2 : mul2Base n ≤ exp2Base n := by
    unfold exp2Base expMulBase expAddBase distBase
    omega
  have hdist_le_exp2 : distBase n ≤ exp2Base n := by
    unfold exp2Base expMulBase expAddBase
    omega
  have hexpAdd_le_exp2 : expAddBase n ≤ exp2Base n := by
    unfold exp2Base expMulBase
    omega
  have hexpMul_le_exp2 : expMulBase n ≤ exp2Base n := by
    unfold exp2Base
    omega
  have hnotAdd : ¬ exp2Var n x y z l ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) hprimary_le_exp2) hblock.1)
  have hnotMul : ¬ exp2Var n x y z l ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) hprimary_le_exp2) hblock.1)
  have hnotExp : ¬ exp2Var n x y z l ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hprimary_le_exp2 hblock.1)
  have hnotAdd2 : ¬ exp2Var n x y z l ≤ mul2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hmul2_le_exp2 hblock.1)
  have hnotMul2 : ¬ exp2Var n x y z l ≤ distBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hdist_le_exp2 hblock.1)
  have hnotDist : ¬ exp2Var n x y z l ≤ expAddBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hexpAdd_le_exp2 hblock.1)
  have hnotExpAdd : ¬ exp2Var n x y z l ≤ expMulBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt hexpMul_le_exp2 hblock.1)
  have hnotExpMul : ¬ exp2Var n x y z l ≤ exp2Base n :=
    Nat.not_le_of_gt hblock.1
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_neg hnotMul2]
  rw [if_neg hnotDist]
  rw [if_neg hnotExpAdd]
  rw [if_neg hnotExpMul]
  rw [if_pos hblock.2]
  exact exp2TableTruth_exp2Var_iff hx hy hz hl

theorem modelAssignment_decoded
    {n : Nat} {A : Algebra} (H : HSI n A) :
    DecodedBy n (modelAssignment n A) A where
  add_iff hi hj hk := (modelAssignment_addVar_iff H hi hj hk).symm
  mul_iff hi hj hk := (modelAssignment_mulVar_iff H hi hj hk).symm
  exp_iff hi hj hk := (modelAssignment_expVar_iff hi hj hk).symm

theorem modelAssignment_encodesAlgebra
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A) :
    EncodesAlgebra n (modelAssignment n A) A where
  decoded := modelAssignment_decoded H
  add2_iff hi hj hk hl := (modelAssignment_add2Var_iff C H hi hj hk hl).symm
  mul2_iff hi hj hk hl := (modelAssignment_mul2Var_iff C H hi hj hk hl).symm
  dist_iff hx hy hz hl := (modelAssignment_distVar_iff C H hx hy hz hl).symm
  expAdd_iff hx hy hz hl := (modelAssignment_expAddVar_iff C H hx hy hz hl).symm
  expMul_iff hx hy hz hl := (modelAssignment_expMulVar_iff C H hx hy hz hl).symm
  exp2_iff hx hy hz hl := (modelAssignment_exp2Var_iff hx hy hz hl).symm

theorem termTableTruth_termVar_iff
    {n : Nat} {A : Algebra}
    {termIndex value : Nat} (hvalue : InDomain n value) :
    TermTableTruth n A (termVar n termIndex value) ↔
      wilkieTermExpr A termIndex = value := by
  constructor
  · intro h
    rcases h with ⟨termIndex', value', hvalue', hvar, hexpr⟩
    have hsplit := termVar_inj hvalue hvalue' hvar
    calc
      wilkieTermExpr A termIndex = wilkieTermExpr A termIndex' := by simp [hsplit.1]
      _ = value' := hexpr
      _ = value := hsplit.2.symm
  · intro h
    exact ⟨termIndex, value, hvalue, rfl, h⟩

theorem modelAssignment_termVar_iff
    {n : Nat} {A : Algebra}
    {termIndex value : Nat} (hvalue : InDomain n value) :
    modelAssignment n A (termVar n termIndex value) ↔
      wilkieTermExpr A termIndex = value := by
  have hblock := termVar_block (n := n) (termIndex := termIndex) (value := value)
  have hnotAdd : ¬ termVar n termIndex value ≤ pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary1_le_primaryCount n) (primary_le_wilkieTermBase n)) hblock)
  have hnotMul : ¬ termVar n termIndex value ≤ 2 * pairCount n * n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (primary2_le_primaryCount n) (primary_le_wilkieTermBase n)) hblock)
  have hnotExp : ¬ termVar n termIndex value ≤ primaryCount n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (primary_le_wilkieTermBase n) hblock)
  have hnotAdd2 : ¬ termVar n termIndex value ≤ mul2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (mul2Base_le_distBase n)
        (Nat.le_trans (distBase_le_expAddBase n)
          (Nat.le_trans (expAddBase_le_expMulBase n)
            (Nat.le_trans (expMulBase_le_exp2Base n) (exp2Base_le_wilkieTermBase n))))) hblock)
  have hnotMul2 : ¬ termVar n termIndex value ≤ distBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (distBase_le_expAddBase n)
        (Nat.le_trans (expAddBase_le_expMulBase n)
          (Nat.le_trans (expMulBase_le_exp2Base n) (exp2Base_le_wilkieTermBase n)))) hblock)
  have hnotDist : ¬ termVar n termIndex value ≤ expAddBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (expAddBase_le_expMulBase n)
        (Nat.le_trans (expMulBase_le_exp2Base n) (exp2Base_le_wilkieTermBase n))) hblock)
  have hnotExpAdd : ¬ termVar n termIndex value ≤ expMulBase n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (Nat.le_trans (expMulBase_le_exp2Base n) (exp2Base_le_wilkieTermBase n)) hblock)
  have hnotExpMul : ¬ termVar n termIndex value ≤ exp2Base n :=
    Nat.not_le_of_gt (Nat.lt_of_le_of_lt (exp2Base_le_wilkieTermBase n) hblock)
  have hnotExp2 : ¬ termVar n termIndex value ≤ wilkieTermBase n :=
    Nat.not_le_of_gt hblock
  unfold modelAssignment
  rw [if_neg hnotAdd]
  rw [if_neg hnotMul]
  rw [if_neg hnotExp]
  rw [if_neg hnotAdd2]
  rw [if_neg hnotMul2]
  rw [if_neg hnotDist]
  rw [if_neg hnotExpAdd]
  rw [if_neg hnotExpMul]
  rw [if_neg hnotExp2]
  exact termTableTruth_termVar_iff hvalue

theorem modelAssignment_encodesWilkieTerms
    {n : Nat} {A : Algebra} :
    EncodesWilkieTerms n (modelAssignment n A) A := by
  intro termIndex value hvalue
  exact (modelAssignment_termVar_iff hvalue).symm

theorem simpEncLeeDivClauses_modelAssignment
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) (hFail : WilkieFailsAt A 4 5 4) :
    evalCNF (modelAssignment n A)
      ((values n).map (fun v => [neg (mulVar n 4 v 5)])) := by
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rw [evalCNF_negUnitClauses_iff]
  · intro v hv hτ
    have hmul : A.mul 4 v = 5 :=
      (modelAssignment_mulVar_iff H h4 hv h5).1 hτ
    exact lee_failure_pair_not_left_mul C H h5 hFail hv hmul
  · intro v _hv
    exact mulVar_pos n 4 v 5

theorem simpEncFixedUnitClauses_modelAssignment
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    (hFail : WilkieFailsAt A 4 5 4) :
    evalCNF (modelAssignment n A) [
      [pos (addVar n 1 1 2)],
      [pos (addVar n 2 1 3)],
      [neg (addVar n 1 4 1)],
      [neg (addVar n 2 4 1)],
      [neg (addVar n 4 4 1)],
      [neg (mulVar n 4 4 1)],
      [neg (addVar n 4 4 4)],
      [neg (mulVar n 4 4 4)],
      [neg (addVar n 1 4 4)],
      [neg (addVar n 2 4 4)],
      [neg (termVar n 12 1)],
      [neg (termVar n 7 1)],
      [neg (termVar n 12 4)]
    ] := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h3 : InDomain n 3 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rcases fixedBurrisLeeConsequences_of_wilkieFails C H h5 hFail h112 with
    ⟨m01, m02, m03, m04, m07, m08, m09, m10⟩
  simp [evalCNF, evalClause,
    evalLit_pos_of_pos (modelAssignment n A),
    evalLit_neg_of_pos (modelAssignment n A),
    addVar_pos, mulVar_pos, termVar_pos]
  exact ⟨
    (modelAssignment_addVar_iff H h1 h1 h2).2 h112,
    (modelAssignment_addVar_iff H h2 h1 h3).2 h213,
    (by
      intro hτ
      exact m01 ((modelAssignment_addVar_iff H h1 h4 h1).1 hτ)),
    (by
      intro hτ
      exact m02 ((modelAssignment_addVar_iff H h2 h4 h1).1 hτ)),
    (by
      intro hτ
      exact m03 ((modelAssignment_addVar_iff H h4 h4 h1).1 hτ)),
    (by
      intro hτ
      exact m04 ((modelAssignment_mulVar_iff H h4 h4 h1).1 hτ)),
    (by
      intro hτ
      exact m09 ((modelAssignment_addVar_iff H h4 h4 h4).1 hτ)),
    (by
      intro hτ
      exact m10 ((modelAssignment_mulVar_iff H h4 h4 h4).1 hτ)),
    (by
      intro hτ
      exact m07 ((modelAssignment_addVar_iff H h1 h4 h4).1 hτ)),
    (by
      intro hτ
      exact m08 ((modelAssignment_addVar_iff H h2 h4 h4).1 hτ)),
    (by
      intro hτ
      have hterm : A.add 1 (x2 A 4) = 1 := by
        simpa [wilkieTermExpr] using (modelAssignment_termVar_iff h1).1 hτ
      exact hFail (m05_one_add_x2_eq_one_yields_wilkie C H h5 hterm)),
    (by
      intro hτ
      have hterm : x3 A 4 = 1 := by
        simpa [wilkieTermExpr] using (modelAssignment_termVar_iff h1).1 hτ
      exact hFail (m06_x3_eq_one_yields_wilkie C H h5 hterm)),
    (by
      intro hτ
      have hterm : A.add 1 (x2 A 4) = 4 := by
        simpa [wilkieTermExpr] using (modelAssignment_termVar_iff h4).1 hτ
      exact hFail (m11_one_add_x2_eq_x_yields_wilkie C H h5 hterm))⟩

theorem simpEncValueBlockClauses_modelAssignment
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5) (h112 : A.add 1 1 = 2)
    (hFail : WilkieFailsAt A 4 5 4) :
    evalCNF (modelAssignment n A)
      (flatMap (values n) (fun value => [
        [neg (addVar n 2 4 value), neg (termVar n 0 value)],
        [neg (mulVar n 4 4 value), neg (termVar n 0 value)],
        [neg (termVar n 7 value), neg (termVar n 0 value)],
        [neg (mulVar n 4 4 value), neg (addVar n 2 4 value)],
        [neg (mulVar n 4 4 value), neg (addVar n 4 4 value)],
        [neg (termVar n 12 value), neg (mulVar n 4 4 value)]
      ])) := by
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rw [evalCNF_flatMap]
  intro value hv
  simp [evalCNF,
    evalClause_two_neg_iff (modelAssignment n A)
      (addVar_pos n 2 4 value) (termVar_pos n 0 value),
    evalClause_two_neg_iff (modelAssignment n A)
      (mulVar_pos n 4 4 value) (termVar_pos n 0 value),
    evalClause_two_neg_iff (modelAssignment n A)
      (termVar_pos n 7 value) (termVar_pos n 0 value),
    evalClause_two_neg_iff (modelAssignment n A)
      (mulVar_pos n 4 4 value) (addVar_pos n 2 4 value),
    evalClause_two_neg_iff (modelAssignment n A)
      (mulVar_pos n 4 4 value) (addVar_pos n 4 4 value),
    evalClause_two_neg_iff (modelAssignment n A)
      (termVar_pos n 12 value) (mulVar_pos n 4 4 value)]
  constructor
  · intro hleft hright
    have hadd : A.add 2 4 = value :=
      (modelAssignment_addVar_iff H h2 h4 hv).1 hleft
    have hP : Pterm A 4 = value := by
      simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hv).1 hright
    have hEq : A.add 2 4 = Pterm A 4 := hadd.trans hP.symm
    exact hFail (m12_two_add_x_eq_p_yields_wilkie C H h5 h112 hEq)
  constructor
  · intro hleft hright
    have hx2 : x2 A 4 = value :=
      (modelAssignment_mulVar_iff H h4 h4 hv).1 hleft
    have hP : Pterm A 4 = value := by
      simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hv).1 hright
    have hEq : x2 A 4 = Pterm A 4 := hx2.trans hP.symm
    exact hFail (m13_x2_eq_p_yields_wilkie C H h5 hEq)
  constructor
  · intro hleft hright
    have hx3 : x3 A 4 = value := by
      simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hv).1 hleft
    have hP : Pterm A 4 = value := by
      simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hv).1 hright
    have hEq : x3 A 4 = Pterm A 4 := hx3.trans hP.symm
    exact hFail (m14_x3_eq_p_yields_wilkie C H h5 hEq)
  constructor
  · intro hleft hright
    have hx2 : x2 A 4 = value :=
      (modelAssignment_mulVar_iff H h4 h4 hv).1 hleft
    have hadd : A.add 2 4 = value :=
      (modelAssignment_addVar_iff H h2 h4 hv).1 hright
    have hEq : x2 A 4 = A.add 2 4 := hx2.trans hadd.symm
    exact hFail (m15_x2_eq_two_add_x_yields_wilkie C H h5 hEq)
  constructor
  · intro hleft hright
    have hx2 : x2 A 4 = value :=
      (modelAssignment_mulVar_iff H h4 h4 hv).1 hleft
    have hadd : A.add 4 4 = value :=
      (modelAssignment_addVar_iff H h4 h4 hv).1 hright
    have hEq : x2 A 4 = A.add 4 4 := hx2.trans hadd.symm
    exact hFail (m16_x2_eq_x_add_x_yields_wilkie C H h5 hEq)
  · intro hleft hright
    have hone : A.add 1 (x2 A 4) = value := by
      simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hv).1 hleft
    have hx2 : x2 A 4 = value :=
      (modelAssignment_mulVar_iff H h4 h4 hv).1 hright
    have hEq : A.add 1 (x2 A 4) = x2 A 4 := hone.trans hx2.symm
    exact hFail (m17_one_add_x2_eq_x2_yields_wilkie C H h5 hEq)

theorem simpEncJacksonQuadraticClauses_modelAssignment
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    (hFail : WilkieFailsAt A 4 5 4) :
    evalCNF (modelAssignment n A)
      (flatMap (product3 [1, 2, 3] [1, 2, 3] [1, 2, 3]) (fun (i, j, k) =>
        (product4 (values n) (values n) (values n) (values n)).map
          (fun (x2Value, jxValue, kx2Value, tailValue) => [
            neg (termVar n 3 x2Value),
            neg (mulVar n j 4 jxValue),
            neg (mulVar n k x2Value kx2Value),
            neg (addVar n jxValue kx2Value tailValue),
            neg (addVar n i tailValue 5)
          ]))) := by
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  rw [evalCNF_flatMap]
  intro p hp
  rcases (mem_product3_iff).1 hp with ⟨hi, hj, hk⟩
  rcases p with ⟨i, j, k⟩
  have hiD : InDomain n i := by
    rw [InDomain_iff] at h5 ⊢
    simp at hi
    omega
  have hjD : InDomain n j := by
    rw [InDomain_iff] at h5 ⊢
    simp at hj
    omega
  have hkD : InDomain n k := by
    rw [InDomain_iff] at h5 ⊢
    simp at hk
    omega
  exact (evalCNF_fiveNegClauses_iff (modelAssignment n A)
    (product4 (values n) (values n) (values n) (values n))
    (fun q => termVar n 3 q.1)
    (fun q => mulVar n j 4 q.2.1)
    (fun q => mulVar n k q.1 q.2.2.1)
    (fun q => addVar n q.2.1 q.2.2.1 q.2.2.2)
    (fun q => addVar n i q.2.2.2 5)
    (by
      intro q _hq
      exact ⟨termVar_pos n 3 q.1,
        mulVar_pos n j 4 q.2.1,
        mulVar_pos n k q.1 q.2.2.1,
        addVar_pos n q.2.1 q.2.2.1 q.2.2.2,
        addVar_pos n i q.2.2.2 5⟩)).2 (by
      intro q hq hbad
      rcases (mem_product4_iff).1 hq with
        ⟨hx2Value, hjxValue, hkx2Value, htailValue⟩
      rcases q with ⟨x2Value, jxValue, kx2Value, tailValue⟩
      have hx2eq : x2 A 4 = x2Value := by
        simpa [wilkieTermExpr] using
          (modelAssignment_termVar_iff hx2Value).1 hbad.1
      have hjx : A.mul j 4 = jxValue :=
        (modelAssignment_mulVar_iff H hjD h4 hjxValue).1 hbad.2.1
      have hkx2raw : A.mul k x2Value = kx2Value :=
        (modelAssignment_mulVar_iff H hkD hx2Value hkx2Value).1 hbad.2.2.1
      have hkx2 : A.mul k (x2 A 4) = kx2Value := by
        rw [hx2eq]
        exact hkx2raw
      have htail : A.add jxValue kx2Value = tailValue :=
        (modelAssignment_addVar_iff H hjxValue hkx2Value htailValue).1 hbad.2.2.2.1
      have hfinal : A.add i tailValue = 5 :=
        (modelAssignment_addVar_iff H hiD htailValue h5).1 hbad.2.2.2.2
      have hquad :
          A.add i (A.add (A.mul j 4) (A.mul k (x2 A 4))) = 5 := by
        calc
          A.add i (A.add (A.mul j 4) (A.mul k (x2 A 4))) =
              A.add i (A.add jxValue kx2Value) := by rw [hjx, hkx2]
          _ = A.add i tailValue := by rw [htail]
          _ = 5 := hfinal
      exact hFail
        (jackson_small_quadratic_yields_wilkie C H h5 h112 h213 hi hj hk hquad))

theorem termDecodedAt_of_true_result
    {n : Nat} {τ : Assignment} {A : Algebra} {termIndex r : Nat}
    (hexact : ExactlyOneVars τ ((values n).map (termVar n termIndex)))
    (hr : InDomain n r) (hτr : τ (termVar n termIndex r))
    (hexpr : wilkieTermExpr A termIndex = r) :
    TermDecodedAt n τ A termIndex := by
  intro v hv
  constructor
  · intro h
    have hrv : r = v := hexpr.symm.trans h
    simpa [hrv] using hτr
  · intro hτv
    have hVarEq :
        termVar n termIndex r = termVar n termIndex v := by
      exact hexact.unique
        (List.mem_map.mpr ⟨r, hr, rfl⟩)
        (List.mem_map.mpr ⟨v, hv, rfl⟩)
        hτr hτv
    have hrv : r = v := termVar_inj_value hr hv hVarEq
    simp [hexpr, hrv]

theorem termDecodedAt_of_clause_semantics
    {n : Nat} {τ : Assignment} {A : Algebra} {termIndex : Nat} {spec : TermSpec}
    (D : DecodedBy n τ A) (C : Closed n A)
    (sem : TermClausesSemantics n τ termIndex spec)
    (hleft : InDomain n (argValue A spec.left))
    (hright : InDomain n (argValue A spec.right))
    (dleft : ArgDecoded n τ A spec.left)
    (dright : ArgDecoded n τ A spec.right)
    (hexpr : wilkieTermExpr A termIndex =
      evalOp A spec.op (argValue A spec.left) (argValue A spec.right)) :
    TermDecodedAt n τ A termIndex := by
  cases spec with
  | mk op left right =>
      cases left with
      | const leftValue =>
          cases right with
          | const rightValue =>
              let r := evalOp A op leftValue rightValue
              have hr : InDomain n r := by
                dsimp [r]
                exact C.evalOp_mem op hleft hright
              have hop : τ (opVar n op leftValue rightValue r) :=
                (D.op_iff hleft hright hr).1 rfl
              have hterm : τ (termVar n termIndex r) := sem.2 r hr hop
              exact termDecodedAt_of_true_result sem.1 hr hterm hexpr
          | term rightIndex =>
              let rightValue := wilkieTermExpr A rightIndex
              let r := evalOp A op leftValue rightValue
              have hr : InDomain n r := by
                dsimp [r]
                exact C.evalOp_mem op hleft hright
              have hop : τ (opVar n op leftValue rightValue r) :=
                (D.op_iff hleft hright hr).1 rfl
              have hrightτ : τ (termVar n rightIndex rightValue) :=
                (dright rightValue hright).1 rfl
              have hq : (rightValue, r) ∈ product2 (values n) (values n) := by
                rw [mem_product2_iff]
                exact ⟨hright, hr⟩
              have hterm : τ (termVar n termIndex r) := sem.2 (rightValue, r) hq hop hrightτ
              exact termDecodedAt_of_true_result sem.1 hr hterm hexpr
      | term leftIndex =>
          cases right with
          | const rightValue =>
              let leftValue := wilkieTermExpr A leftIndex
              let r := evalOp A op leftValue rightValue
              have hr : InDomain n r := by
                dsimp [r]
                exact C.evalOp_mem op hleft hright
              have hop : τ (opVar n op leftValue rightValue r) :=
                (D.op_iff hleft hright hr).1 rfl
              have hleftτ : τ (termVar n leftIndex leftValue) :=
                (dleft leftValue hleft).1 rfl
              have hq : (leftValue, r) ∈ product2 (values n) (values n) := by
                rw [mem_product2_iff]
                exact ⟨hleft, hr⟩
              have hterm : τ (termVar n termIndex r) := sem.2 (leftValue, r) hq hop hleftτ
              exact termDecodedAt_of_true_result sem.1 hr hterm hexpr
          | term rightIndex =>
              let leftValue := wilkieTermExpr A leftIndex
              let rightValue := wilkieTermExpr A rightIndex
              let r := evalOp A op leftValue rightValue
              have hr : InDomain n r := by
                dsimp [r]
                exact C.evalOp_mem op hleft hright
              have hop : τ (opVar n op leftValue rightValue r) :=
                (D.op_iff hleft hright hr).1 rfl
              have hleftτ : τ (termVar n leftIndex leftValue) :=
                (dleft leftValue hleft).1 rfl
              have hrightτ : τ (termVar n rightIndex rightValue) :=
                (dright rightValue hright).1 rfl
              have hq : (leftValue, rightValue, r) ∈
                  product3 (values n) (values n) (values n) := by
                rw [mem_product3_iff]
                exact ⟨hleft, hright, hr⟩
              have hterm : τ (termVar n termIndex r) := sem.2 (leftValue, rightValue, r) hq
                hop hleftτ hrightτ
              exact termDecodedAt_of_true_result sem.1 hr hterm hexpr

theorem termClausesSemantics_of_encoded_term
    {n : Nat} {τ : Assignment} {A : Algebra} {termIndex : Nat} {spec : TermSpec}
    (D : DecodedBy n τ A)
    (T : EncodesWilkieTerms n τ A)
    (htermDomain : InDomain n (wilkieTermExpr A termIndex))
    (hleft : InDomain n (argValue A spec.left))
    (hright : InDomain n (argValue A spec.right))
    (hmatch : wilkieTermExpr A termIndex =
      evalOp A spec.op (argValue A spec.left) (argValue A spec.right)) :
    TermClausesSemantics n τ termIndex spec := by
  refine ⟨?exactlyOne, ?implications⟩
  · let r := wilkieTermExpr A termIndex
    have hr : InDomain n r := htermDomain
    exact ExactlyOneVars.map_of_unique (values_nodup n) hr
      ((T termIndex r hr).1 rfl)
      (by
        intro v hv hτ
        exact ((T termIndex v hv).2 hτ).symm)
      (by
        intro x hx y hy hEq
        exact termVar_inj_value hx hy hEq)
  · cases spec with
    | mk op left right =>
        cases left with
        | const leftValue =>
            cases right with
            | const rightValue =>
                intro v hv hop
                have hopEq : evalOp A op leftValue rightValue = v :=
                  (D.op_iff hleft hright hv).2 hop
                exact (T termIndex v hv).1 (hmatch.trans hopEq)
            | term rightIndex =>
                intro q hq hop hrightτ
                cases q with
                | mk u v =>
                    have hqdom : (u, v) ∈ product2 (values n) (values n) := hq
                    rw [mem_product2_iff] at hqdom
                    have hrightEq : wilkieTermExpr A rightIndex = u :=
                      (T rightIndex u hqdom.1).2 hrightτ
                    have hopEq : evalOp A op leftValue u = v :=
                      (D.op_iff hleft hqdom.1 hqdom.2).2 hop
                    have htermEq : wilkieTermExpr A termIndex = v := by
                      rw [hmatch]
                      dsimp [argValue]
                      rw [hrightEq]
                      exact hopEq
                    exact (T termIndex v hqdom.2).1 htermEq
        | term leftIndex =>
            cases right with
            | const rightValue =>
                intro q hq hop hleftτ
                cases q with
                | mk u v =>
                    have hqdom : (u, v) ∈ product2 (values n) (values n) := hq
                    rw [mem_product2_iff] at hqdom
                    have hleftEq : wilkieTermExpr A leftIndex = u :=
                      (T leftIndex u hqdom.1).2 hleftτ
                    have hopEq : evalOp A op u rightValue = v :=
                      (D.op_iff hqdom.1 hright hqdom.2).2 hop
                    have htermEq : wilkieTermExpr A termIndex = v := by
                      rw [hmatch]
                      dsimp [argValue]
                      rw [hleftEq]
                      exact hopEq
                    exact (T termIndex v hqdom.2).1 htermEq
            | term rightIndex =>
                intro q hq hop hleftτ hrightτ
                cases q with
                | mk u rest =>
                    cases rest with
                    | mk v w =>
                        have hqdom : (u, v, w) ∈
                            product3 (values n) (values n) (values n) := hq
                        rw [mem_product3_iff] at hqdom
                        have hleftEq : wilkieTermExpr A leftIndex = u :=
                          (T leftIndex u hqdom.1).2 hleftτ
                        have hrightEq : wilkieTermExpr A rightIndex = v :=
                          (T rightIndex v hqdom.2.1).2 hrightτ
                        have hopEq : evalOp A op u v = w :=
                          (D.op_iff hqdom.1 hqdom.2.1 hqdom.2.2).2 hop
                        have htermEq : wilkieTermExpr A termIndex = w := by
                          rw [hmatch]
                          dsimp [argValue]
                          rw [hleftEq, hrightEq]
                          exact hopEq
                        exact (T termIndex w hqdom.2.2).1 htermEq

theorem encodesWilkieTerms_yields_termClausesSemantics
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A)
    (T : EncodesWilkieTerms n τ A)
    (M : WilkieTermValuesInDomain n A)
    (Args : WilkieTermSpecArgsInDomain n A)
    (Cons : WilkieTermSpecsConsistent A) :
    WilkieTermClausesSemantics n τ := by
  intro p hp
  exact termClausesSemantics_of_encoded_term D T (M p hp)
    (Args p hp).1 (Args p hp).2 (Cons p hp)

theorem encodesWilkieTerms_yields_diseqSemantics
    {n : Nat} {τ : Assignment} {A : Algebra}
    (T : EncodesWilkieTerms n τ A)
    (hFail : WilkieFailsAt A 4 5 4) :
    WilkieDiseqSemantics n τ := by
  intro v hv hboth
  have h24 : wilkieTermExpr A 24 = v := (T 24 v hv).2 hboth.1
  have h25 : wilkieTermExpr A 25 = v := (T 25 v hv).2 hboth.2
  have hExpr : wilkieTermExpr A 24 = wilkieTermExpr A 25 := h24.trans h25.symm
  exact hFail (by simpa [wilkieTermExpr_24, wilkieTermExpr_25] using hExpr)

theorem encodesWilkieTerms_yields_wilkieClausesSemantics
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A)
    (T : EncodesWilkieTerms n τ A)
    (M : WilkieTermValuesInDomain n A)
    (Args : WilkieTermSpecArgsInDomain n A)
    (Cons : WilkieTermSpecsConsistent A)
    (hFail : WilkieFailsAt A 4 5 4) :
    WilkieClausesSemantics n τ := by
  exact ⟨encodesWilkieTerms_yields_termClausesSemantics D T M Args Cons,
    encodesWilkieTerms_yields_diseqSemantics T hFail⟩

structure WilkieDecodedKeyTerms (n : Nat) (τ : Assignment) (A : Algebra) : Prop where
  t0 : TermDecodedAt n τ A 0
  t4 : TermDecodedAt n τ A 4
  t8 : TermDecodedAt n τ A 8
  t13 : TermDecodedAt n τ A 13
  t24 : TermDecodedAt n τ A 24
  t25 : TermDecodedAt n τ A 25
  m24 : InDomain n (wilkieTermExpr A 24)

theorem wilkieTermClauses_decode_key_terms
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A)
    (W : WilkieTermClausesSemantics n τ)
    (h5 : InDomain n 5) :
    WilkieDecodedKeyTerms n τ A := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have s0 : TermClausesSemantics n τ 0 ⟨.add, .const 1, .const 4⟩ :=
    W (0, ⟨.add, .const 1, .const 4⟩) (by decide)
  have m0 : InDomain n (wilkieTermExpr A 0) := C.add_mem h1 h4
  have t0 : TermDecodedAt n τ A 0 :=
    termDecodedAt_of_clause_semantics D C s0 h1 h4 trivial trivial rfl
  have s1 : TermClausesSemantics n τ 1 ⟨.exp, .term 0, .const 5⟩ :=
    W (1, ⟨.exp, .term 0, .const 5⟩) (by decide)
  have m1 : InDomain n (wilkieTermExpr A 1) := C.exp_mem m0 h5
  have t1 : TermDecodedAt n τ A 1 :=
    termDecodedAt_of_clause_semantics D C s1 m0 h5 t0 trivial rfl
  have s2 : TermClausesSemantics n τ 2 ⟨.exp, .term 0, .const 4⟩ :=
    W (2, ⟨.exp, .term 0, .const 4⟩) (by decide)
  have m2 : InDomain n (wilkieTermExpr A 2) := C.exp_mem m0 h4
  have t2 : TermDecodedAt n τ A 2 :=
    termDecodedAt_of_clause_semantics D C s2 m0 h4 t0 trivial rfl
  have s3 : TermClausesSemantics n τ 3 ⟨.mul, .const 4, .const 4⟩ :=
    W (3, ⟨.mul, .const 4, .const 4⟩) (by decide)
  have m3 : InDomain n (wilkieTermExpr A 3) := C.mul_mem h4 h4
  have t3 : TermDecodedAt n τ A 3 :=
    termDecodedAt_of_clause_semantics D C s3 h4 h4 trivial trivial rfl
  have s4 : TermClausesSemantics n τ 4 ⟨.add, .term 0, .term 3⟩ :=
    W (4, ⟨.add, .term 0, .term 3⟩) (by decide)
  have m4 : InDomain n (wilkieTermExpr A 4) := C.add_mem m0 m3
  have t4 : TermDecodedAt n τ A 4 :=
    termDecodedAt_of_clause_semantics D C s4 m0 m3 t0 t3 rfl
  have s5 : TermClausesSemantics n τ 5 ⟨.exp, .term 4, .const 4⟩ :=
    W (5, ⟨.exp, .term 4, .const 4⟩) (by decide)
  have m5 : InDomain n (wilkieTermExpr A 5) := C.exp_mem m4 h4
  have t5 : TermDecodedAt n τ A 5 :=
    termDecodedAt_of_clause_semantics D C s5 m4 h4 t4 trivial rfl
  have s6 : TermClausesSemantics n τ 6 ⟨.exp, .term 4, .const 5⟩ :=
    W (6, ⟨.exp, .term 4, .const 5⟩) (by decide)
  have m6 : InDomain n (wilkieTermExpr A 6) := C.exp_mem m4 h5
  have t6 : TermDecodedAt n τ A 6 :=
    termDecodedAt_of_clause_semantics D C s6 m4 h5 t4 trivial rfl
  have s7 : TermClausesSemantics n τ 7 ⟨.mul, .term 3, .const 4⟩ :=
    W (7, ⟨.mul, .term 3, .const 4⟩) (by decide)
  have m7 : InDomain n (wilkieTermExpr A 7) := C.mul_mem m3 h4
  have t7 : TermDecodedAt n τ A 7 :=
    termDecodedAt_of_clause_semantics D C s7 m3 h4 t3 trivial rfl
  have s8 : TermClausesSemantics n τ 8 ⟨.add, .const 1, .term 7⟩ :=
    W (8, ⟨.add, .const 1, .term 7⟩) (by decide)
  have m8 : InDomain n (wilkieTermExpr A 8) := C.add_mem h1 m7
  have t8 : TermDecodedAt n τ A 8 :=
    termDecodedAt_of_clause_semantics D C s8 h1 m7 trivial t7 rfl
  have s9 : TermClausesSemantics n τ 9 ⟨.exp, .term 8, .const 4⟩ :=
    W (9, ⟨.exp, .term 8, .const 4⟩) (by decide)
  have m9 : InDomain n (wilkieTermExpr A 9) := C.exp_mem m8 h4
  have t9 : TermDecodedAt n τ A 9 :=
    termDecodedAt_of_clause_semantics D C s9 m8 h4 t8 trivial rfl
  have s10 : TermClausesSemantics n τ 10 ⟨.exp, .term 8, .const 5⟩ :=
    W (10, ⟨.exp, .term 8, .const 5⟩) (by decide)
  have m10 : InDomain n (wilkieTermExpr A 10) := C.exp_mem m8 h5
  have t10 : TermDecodedAt n τ A 10 :=
    termDecodedAt_of_clause_semantics D C s10 m8 h5 t8 trivial rfl
  have s11 : TermClausesSemantics n τ 11 ⟨.mul, .term 7, .const 4⟩ :=
    W (11, ⟨.mul, .term 7, .const 4⟩) (by decide)
  have m11 : InDomain n (wilkieTermExpr A 11) := C.mul_mem m7 h4
  have t11 : TermDecodedAt n τ A 11 :=
    termDecodedAt_of_clause_semantics D C s11 m7 h4 t7 trivial rfl
  have s12 : TermClausesSemantics n τ 12 ⟨.add, .const 1, .term 3⟩ :=
    W (12, ⟨.add, .const 1, .term 3⟩) (by decide)
  have m12 : InDomain n (wilkieTermExpr A 12) := C.add_mem h1 m3
  have t12 : TermDecodedAt n τ A 12 :=
    termDecodedAt_of_clause_semantics D C s12 h1 m3 trivial t3 rfl
  have s13 : TermClausesSemantics n τ 13 ⟨.add, .term 12, .term 11⟩ :=
    W (13, ⟨.add, .term 12, .term 11⟩) (by decide)
  have m13 : InDomain n (wilkieTermExpr A 13) := C.add_mem m12 m11
  have t13 : TermDecodedAt n τ A 13 :=
    termDecodedAt_of_clause_semantics D C s13 m12 m11 t12 t11 rfl
  have s14 : TermClausesSemantics n τ 14 ⟨.exp, .term 13, .const 4⟩ :=
    W (14, ⟨.exp, .term 13, .const 4⟩) (by decide)
  have m14 : InDomain n (wilkieTermExpr A 14) := C.exp_mem m13 h4
  have t14 : TermDecodedAt n τ A 14 :=
    termDecodedAt_of_clause_semantics D C s14 m13 h4 t13 trivial rfl
  have s15 : TermClausesSemantics n τ 15 ⟨.exp, .term 13, .const 5⟩ :=
    W (15, ⟨.exp, .term 13, .const 5⟩) (by decide)
  have m15 : InDomain n (wilkieTermExpr A 15) := C.exp_mem m13 h5
  have t15 : TermDecodedAt n τ A 15 :=
    termDecodedAt_of_clause_semantics D C s15 m13 h5 t13 trivial rfl
  have s16 : TermClausesSemantics n τ 16 ⟨.add, .term 1, .term 6⟩ :=
    W (16, ⟨.add, .term 1, .term 6⟩) (by decide)
  have m16 : InDomain n (wilkieTermExpr A 16) := C.add_mem m1 m6
  have t16 : TermDecodedAt n τ A 16 :=
    termDecodedAt_of_clause_semantics D C s16 m1 m6 t1 t6 rfl
  have s17 : TermClausesSemantics n τ 17 ⟨.add, .term 2, .term 5⟩ :=
    W (17, ⟨.add, .term 2, .term 5⟩) (by decide)
  have m17 : InDomain n (wilkieTermExpr A 17) := C.add_mem m2 m5
  have t17 : TermDecodedAt n τ A 17 :=
    termDecodedAt_of_clause_semantics D C s17 m2 m5 t2 t5 rfl
  have s18 : TermClausesSemantics n τ 18 ⟨.exp, .term 17, .const 5⟩ :=
    W (18, ⟨.exp, .term 17, .const 5⟩) (by decide)
  have m18 : InDomain n (wilkieTermExpr A 18) := C.exp_mem m17 h5
  have t18 : TermDecodedAt n τ A 18 :=
    termDecodedAt_of_clause_semantics D C s18 m17 h5 t17 trivial rfl
  have s19 : TermClausesSemantics n τ 19 ⟨.exp, .term 16, .const 4⟩ :=
    W (19, ⟨.exp, .term 16, .const 4⟩) (by decide)
  have m19 : InDomain n (wilkieTermExpr A 19) := C.exp_mem m16 h4
  have t19 : TermDecodedAt n τ A 19 :=
    termDecodedAt_of_clause_semantics D C s19 m16 h4 t16 trivial rfl
  have s20 : TermClausesSemantics n τ 20 ⟨.add, .term 9, .term 14⟩ :=
    W (20, ⟨.add, .term 9, .term 14⟩) (by decide)
  have m20 : InDomain n (wilkieTermExpr A 20) := C.add_mem m9 m14
  have t20 : TermDecodedAt n τ A 20 :=
    termDecodedAt_of_clause_semantics D C s20 m9 m14 t9 t14 rfl
  have s21 : TermClausesSemantics n τ 21 ⟨.add, .term 10, .term 15⟩ :=
    W (21, ⟨.add, .term 10, .term 15⟩) (by decide)
  have m21 : InDomain n (wilkieTermExpr A 21) := C.add_mem m10 m15
  have t21 : TermDecodedAt n τ A 21 :=
    termDecodedAt_of_clause_semantics D C s21 m10 m15 t10 t15 rfl
  have s22 : TermClausesSemantics n τ 22 ⟨.exp, .term 20, .const 5⟩ :=
    W (22, ⟨.exp, .term 20, .const 5⟩) (by decide)
  have m22 : InDomain n (wilkieTermExpr A 22) := C.exp_mem m20 h5
  have t22 : TermDecodedAt n τ A 22 :=
    termDecodedAt_of_clause_semantics D C s22 m20 h5 t20 trivial rfl
  have s23 : TermClausesSemantics n τ 23 ⟨.exp, .term 21, .const 4⟩ :=
    W (23, ⟨.exp, .term 21, .const 4⟩) (by decide)
  have m23 : InDomain n (wilkieTermExpr A 23) := C.exp_mem m21 h4
  have t23 : TermDecodedAt n τ A 23 :=
    termDecodedAt_of_clause_semantics D C s23 m21 h4 t21 trivial rfl
  have s24 : TermClausesSemantics n τ 24 ⟨.mul, .term 19, .term 22⟩ :=
    W (24, ⟨.mul, .term 19, .term 22⟩) (by decide)
  have m24 : InDomain n (wilkieTermExpr A 24) := C.mul_mem m19 m22
  have t24 : TermDecodedAt n τ A 24 :=
    termDecodedAt_of_clause_semantics D C s24 m19 m22 t19 t22 rfl
  have s25 : TermClausesSemantics n τ 25 ⟨.mul, .term 18, .term 23⟩ :=
    W (25, ⟨.mul, .term 18, .term 23⟩) (by decide)
  have t25 : TermDecodedAt n τ A 25 :=
    termDecodedAt_of_clause_semantics D C s25 m18 m23 t18 t23 rfl
  exact {
    t0 := t0
    t4 := t4
    t8 := t8
    t13 := t13
    t24 := t24
    t25 := t25
    m24 := m24
  }

theorem wilkieTermClauses_decode_sides
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D : DecodedBy n τ A) (C : Closed n A)
    (W : WilkieTermClausesSemantics n τ)
    (h5 : InDomain n 5) :
    TermDecodedAt n τ A 24 ∧ TermDecodedAt n τ A 25 ∧
      InDomain n (wilkieTermExpr A 24) := by
  have decoded := wilkieTermClauses_decode_key_terms D C W h5
  exact ⟨decoded.t24, decoded.t25, decoded.m24⟩

theorem wilkieDiseq_yields_failure
    {n : Nat} {τ : Assignment} {A : Algebra}
    (D24 : TermDecodedAt n τ A 24) (D25 : TermDecodedAt n τ A 25)
    (h24mem : InDomain n (wilkieTermExpr A 24))
    (hDiseq : WilkieDiseqSemantics n τ) :
    WilkieFailsAt A 4 5 4 := by
  intro hEq
  have h24τ : τ (termVar n 24 (wilkieTermExpr A 24)) :=
    (D24 (wilkieTermExpr A 24) h24mem).1 rfl
  have h25expr : wilkieTermExpr A 25 = wilkieTermExpr A 24 := by
    simpa [wilkieTermExpr_24, wilkieTermExpr_25] using hEq.symm
  have h25τ : τ (termVar n 25 (wilkieTermExpr A 24)) :=
    (D25 (wilkieTermExpr A 24) h24mem).1 h25expr
  exact hDiseq (wilkieTermExpr A 24) h24mem ⟨h24τ, h25τ⟩

theorem core_satisfying_yields_countermodel
    {n : Nat} {τ : Assignment}
    (h5 : InDomain n 5) (h : evalCNF τ (coreClauses n)) :
    ∃ A, Closed n A ∧ HSI n A ∧ WilkieFailsAt A 4 5 4 := by
  have core := (coreClauses_correct n τ).1 h
  rcases core.1 with ⟨T, U, AS, MS, DS, EAS, EMS, ES⟩
  have CD := decodedAlgebra_closed_decoded T
  let A := decodedAlgebra n τ
  have hHSI : HSI n A := CD.2.hsi CD.1 U AS MS DS EAS EMS ES
  have hFail : WilkieFailsAt A 4 5 4 := by
    have decoded := wilkieTermClauses_decode_sides CD.2 CD.1 core.2.1 h5
    exact wilkieDiseq_yields_failure decoded.1 decoded.2.1 decoded.2.2 core.2.2
  exact ⟨A, CD.1, hHSI, hFail⟩

theorem core_satisfiable_yields_countermodel
    {n : Nat} (h5 : InDomain n 5) :
    Satisfiable (coreClauses n) →
      ∃ A, Closed n A ∧ HSI n A ∧ WilkieFailsAt A 4 5 4 := by
  intro hSat
  rcases hSat with ⟨τ, hτ⟩
  exact core_satisfying_yields_countermodel h5 hτ

theorem coreSemantics_of_encoded_countermodel
    {n : Nat} {τ : Assignment} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (E : EncodesAlgebra n τ A)
    (T : EncodesWilkieTerms n τ A)
    (M : WilkieTermValuesInDomain n A)
    (Args : WilkieTermSpecArgsInDomain n A)
    (Cons : WilkieTermSpecsConsistent A)
    (hFail : WilkieFailsAt A 4 5 4) :
    CoreSemantics n τ := by
  exact ⟨encodesAlgebra_yields_hsiSemantics C H E,
    encodesWilkieTerms_yields_wilkieClausesSemantics E.decoded T M Args Cons hFail⟩

def ExtraFixedSemantics (n : Nat) (τ : Assignment) : Prop :=
  τ (addVar n 1 1 2) ∧
  τ (addVar n 2 1 3) ∧
  ¬τ (addVar n 1 4 1) ∧
  ¬τ (addVar n 2 4 1) ∧
  ¬τ (addVar n 4 4 1) ∧
  ¬τ (mulVar n 4 4 1) ∧
  ¬τ (addVar n 4 4 4) ∧
  ¬τ (mulVar n 4 4 4) ∧
  ¬τ (addVar n 1 4 4) ∧
  ¬τ (addVar n 2 4 4)

def ExtraJacksonSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ j, j ∈ [1, 2, 3] →
    ∀ z, z ∈ values n →
      ∀ i, i ∈ [1, 2, 3] →
        ¬(τ (addVar n i z 5) ∧ τ (mulVar n j 4 z))

def ExtraZhangSemantics (n : Nat) (τ : Assignment) : Prop :=
  ∀ v, v ∈ values n →
    ∀ p, p ∈ product2 (values n) (values n) →
      ¬(τ (termVar n 0 p.1) ∧ τ (termVar n 4 p.2) ∧ τ (mulVar n p.1 v p.2)) ∧
      ¬(τ (termVar n 4 p.1) ∧ τ (termVar n 0 p.2) ∧ τ (mulVar n p.1 v p.2)) ∧
      ¬(τ (termVar n 8 p.1) ∧ τ (termVar n 13 p.2) ∧ τ (mulVar n p.1 v p.2)) ∧
      ¬(τ (termVar n 13 p.1) ∧ τ (termVar n 8 p.2) ∧ τ (mulVar n p.1 v p.2))

def ExtraClausesSemantics (n : Nat) (τ : Assignment) : Prop :=
  ExtraFixedSemantics n τ ∧ ExtraJacksonSemantics n τ ∧ ExtraZhangSemantics n τ

theorem extraJacksonClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ
      (flatMap [1, 2, 3] (fun j =>
        flatMap (values n) (fun z =>
          [1, 2, 3].map (fun i => [neg (addVar n i z 5), neg (mulVar n j 4 z)])))) ↔
      ExtraJacksonSemantics n τ := by
  unfold ExtraJacksonSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h j hj z hz i hi
    have hjEval := h j hj
    rw [evalCNF_flatMap] at hjEval
    have hzEval := hjEval z hz
    exact (evalCNF_twoNegClauses_iff τ [1, 2, 3]
      (fun i => addVar n i z 5)
      (fun i => mulVar n j 4 z)
      (by
        intro i _
        exact ⟨addVar_pos n i z 5, mulVar_pos n j 4 z⟩)).1 hzEval i hi
  · intro h j hj
    rw [evalCNF_flatMap]
    intro z hz
    exact (evalCNF_twoNegClauses_iff τ [1, 2, 3]
      (fun i => addVar n i z 5)
      (fun i => mulVar n j 4 z)
      (by
        intro i _
        exact ⟨addVar_pos n i z 5, mulVar_pos n j 4 z⟩)).2
      (fun i hi => h j hj z hz i hi)

theorem extraZhangBlock_correct (n : Nat) (τ : Assignment) (v i l : Nat) :
    evalCNF τ [
      [neg (termVar n 0 i), neg (termVar n 4 l), neg (mulVar n i v l)],
      [neg (termVar n 4 i), neg (termVar n 0 l), neg (mulVar n i v l)],
      [neg (termVar n 8 i), neg (termVar n 13 l), neg (mulVar n i v l)],
      [neg (termVar n 13 i), neg (termVar n 8 l), neg (mulVar n i v l)]
    ] ↔
      ¬(τ (termVar n 0 i) ∧ τ (termVar n 4 l) ∧ τ (mulVar n i v l)) ∧
      ¬(τ (termVar n 4 i) ∧ τ (termVar n 0 l) ∧ τ (mulVar n i v l)) ∧
      ¬(τ (termVar n 8 i) ∧ τ (termVar n 13 l) ∧ τ (mulVar n i v l)) ∧
      ¬(τ (termVar n 13 i) ∧ τ (termVar n 8 l) ∧ τ (mulVar n i v l)) := by
  simp [evalCNF,
    evalClause_three_neg_iff τ (termVar_pos n 0 i) (termVar_pos n 4 l) (mulVar_pos n i v l),
    evalClause_three_neg_iff τ (termVar_pos n 4 i) (termVar_pos n 0 l) (mulVar_pos n i v l),
    evalClause_three_neg_iff τ (termVar_pos n 8 i) (termVar_pos n 13 l) (mulVar_pos n i v l),
    evalClause_three_neg_iff τ (termVar_pos n 13 i) (termVar_pos n 8 l) (mulVar_pos n i v l)]

theorem extraZhangClauses_correct (n : Nat) (τ : Assignment) :
    evalCNF τ
      (flatMap (values n) (fun v =>
        flatMap (product2 (values n) (values n)) (fun (i, l) => [
          [neg (termVar n 0 i), neg (termVar n 4 l), neg (mulVar n i v l)],
          [neg (termVar n 4 i), neg (termVar n 0 l), neg (mulVar n i v l)],
          [neg (termVar n 8 i), neg (termVar n 13 l), neg (mulVar n i v l)],
          [neg (termVar n 13 i), neg (termVar n 8 l), neg (mulVar n i v l)]
        ]))) ↔
      ExtraZhangSemantics n τ := by
  unfold ExtraZhangSemantics
  rw [evalCNF_flatMap]
  constructor
  · intro h v hv p hp
    have hvEval := h v hv
    rw [evalCNF_flatMap] at hvEval
    cases p with
    | mk i l =>
        exact (extraZhangBlock_correct n τ v i l).1 (hvEval (i, l) hp)
  · intro h v hv
    rw [evalCNF_flatMap]
    intro p hp
    cases p with
    | mk i l =>
        exact (extraZhangBlock_correct n τ v i l).2 (h v hv (i, l) hp)

structure ExtraConstraints (n : Nat) (A : Algebra) : Prop where
  add_one_one : A.add 1 1 = 2
  add_two_one : A.add 2 1 = 3
  one_add_x_ne_one : A.add 1 4 ≠ 1
  two_add_x_ne_one : A.add 2 4 ≠ 1
  x_add_x_ne_one : A.add 4 4 ≠ 1
  x_mul_x_ne_one : A.mul 4 4 ≠ 1
  x_add_x_ne_x : A.add 4 4 ≠ 4
  x_mul_x_ne_x : A.mul 4 4 ≠ 4
  one_add_x_ne_x : A.add 1 4 ≠ 4
  two_add_x_ne_x : A.add 2 4 ≠ 4
  jackson :
    ∀ {i j z}, i ∈ [1, 2, 3] → j ∈ [1, 2, 3] → InDomain n z →
      ¬(A.add i z = 5 ∧ A.mul j 4 = z)
  zhang_pq_forward :
    ∀ {i l v}, InDomain n i → InDomain n l → InDomain n v →
      ¬(Pterm A 4 = i ∧ Qterm A 4 = l ∧ A.mul i v = l)
  zhang_pq_backward :
    ∀ {i l v}, InDomain n i → InDomain n l → InDomain n v →
      ¬(Qterm A 4 = i ∧ Pterm A 4 = l ∧ A.mul i v = l)
  zhang_rs_forward :
    ∀ {i l v}, InDomain n i → InDomain n l → InDomain n v →
      ¬(Rterm A 4 = i ∧ Sterm A 4 = l ∧ A.mul i v = l)
  zhang_rs_backward :
    ∀ {i l v}, InDomain n i → InDomain n l → InDomain n v →
      ¬(Sterm A 4 = i ∧ Rterm A 4 = l ∧ A.mul i v = l)

theorem extraConstraints_of_fixedAndWilkieFails
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A) (h5 : InDomain n 5)
    (hFail : WilkieFailsAt A 4 5 4)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    (m01 : A.add 1 4 ≠ 1)
    (m02 : A.add 2 4 ≠ 1)
    (m03 : A.add 4 4 ≠ 1)
    (m04 : A.mul 4 4 ≠ 1)
    (m07 : A.add 1 4 ≠ 4)
    (m08 : A.add 2 4 ≠ 4)
    (m09 : A.add 4 4 ≠ 4)
    (m10 : A.mul 4 4 ≠ 4) :
    ExtraConstraints n A := by
  have J :
      ∀ {i j z}, i ∈ [1, 2, 3] → j ∈ [1, 2, 3] → InDomain n z →
        ¬(A.add i z = 5 ∧ A.mul j 4 = z) :=
    jacksonConsequences_of_wilkieFails C H h5 h112 h213 hFail
  have L := leeConsequences_of_wilkieFails C H h5 hFail
  refine {
    add_one_one := h112
    add_two_one := h213
    one_add_x_ne_one := m01
    two_add_x_ne_one := m02
    x_add_x_ne_one := m03
    x_mul_x_ne_one := m04
    x_add_x_ne_x := m09
    x_mul_x_ne_x := m10
    one_add_x_ne_x := m07
    two_add_x_ne_x := m08
    jackson := ?jackson
    zhang_pq_forward := ?zhang_pq_forward
    zhang_pq_backward := ?zhang_pq_backward
    zhang_rs_forward := ?zhang_rs_forward
    zhang_rs_backward := ?zhang_rs_backward
  }
  · exact J
  · intro i l v _hi _hl hv hbad
    have hdiv : A.mul (Pterm A 4) v = Qterm A 4 := by
      rw [hbad.1, hbad.2.1]
      exact hbad.2.2
    exact L.1 hv hdiv
  · intro i l v _hi _hl hv hbad
    have hdiv : A.mul (Qterm A 4) v = Pterm A 4 := by
      rw [hbad.1, hbad.2.1]
      exact hbad.2.2
    exact L.2.1 hv hdiv
  · intro i l v _hi _hl hv hbad
    have hdiv : A.mul (Rterm A 4) v = Sterm A 4 := by
      rw [hbad.1, hbad.2.1]
      exact hbad.2.2
    exact L.2.2.1 hv hdiv
  · intro i l v _hi _hl hv hbad
    have hdiv : A.mul (Sterm A 4) v = Rterm A 4 := by
      rw [hbad.1, hbad.2.1]
      exact hbad.2.2
    exact L.2.2.2 hv hdiv

theorem extraConstraints_of_normalizedAndWilkieFails
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A) (h5 : InDomain n 5)
    (hFail : WilkieFailsAt A 4 5 4)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3) :
    ExtraConstraints n A := by
  rcases fixedBurrisLeeConsequences_of_wilkieFails C H h5 hFail h112 with
    ⟨m01, m02, m03, m04, m07, m08, m09, m10⟩
  exact extraConstraints_of_fixedAndWilkieFails C H h5 hFail h112 h213
    m01 m02 m03 m04 m07 m08 m09 m10

/--
The mathematical consequences from Zhang, Section 3, after relabeling the
counterexample so that the first three integers are 1, 2, 3 and the failing
pair is a = 4, b = 5.

The fields named `m..` are the subset of Burris-Lee Lemma 8.20 used by the
encoder.  The four `lee_...` fields are Zhang's L2-L5 consequences of Lee
Lemma 8.13.  The `jackson_linear` field is the finite linear fragment of
Jackson's lemma used by the simplified encoder.
-/
theorem mem_123_inDomain {n i : Nat}
    (h5 : InDomain n 5) (hi : i ∈ [1, 2, 3]) :
    InDomain n i := by
  rw [InDomain_iff] at h5 ⊢
  simp at hi
  omega

theorem extraConstraints_yields_extraSemantics_modelAssignment
    {n : Nat} {A : Algebra}
    (h5 : InDomain n 5) (H : HSI n A) (E : ExtraConstraints n A) :
    ExtraClausesSemantics n (modelAssignment n A) := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h3 : InDomain n 3 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  constructor
  · unfold ExtraFixedSemantics
    have t112 : modelAssignment n A (addVar n 1 1 2) :=
      (modelAssignment_addVar_iff H h1 h1 h2).2 E.add_one_one
    have t213 : modelAssignment n A (addVar n 2 1 3) :=
      (modelAssignment_addVar_iff H h2 h1 h3).2 E.add_two_one
    have n141 : ¬modelAssignment n A (addVar n 1 4 1) := by
      intro hτ
      exact E.one_add_x_ne_one ((modelAssignment_addVar_iff H h1 h4 h1).1 hτ)
    have n241 : ¬modelAssignment n A (addVar n 2 4 1) := by
      intro hτ
      exact E.two_add_x_ne_one ((modelAssignment_addVar_iff H h2 h4 h1).1 hτ)
    have n441 : ¬modelAssignment n A (addVar n 4 4 1) := by
      intro hτ
      exact E.x_add_x_ne_one ((modelAssignment_addVar_iff H h4 h4 h1).1 hτ)
    have nm441 : ¬modelAssignment n A (mulVar n 4 4 1) := by
      intro hτ
      exact E.x_mul_x_ne_one ((modelAssignment_mulVar_iff H h4 h4 h1).1 hτ)
    have n444 : ¬modelAssignment n A (addVar n 4 4 4) := by
      intro hτ
      exact E.x_add_x_ne_x ((modelAssignment_addVar_iff H h4 h4 h4).1 hτ)
    have nm444 : ¬modelAssignment n A (mulVar n 4 4 4) := by
      intro hτ
      exact E.x_mul_x_ne_x ((modelAssignment_mulVar_iff H h4 h4 h4).1 hτ)
    have n144 : ¬modelAssignment n A (addVar n 1 4 4) := by
      intro hτ
      exact E.one_add_x_ne_x ((modelAssignment_addVar_iff H h1 h4 h4).1 hτ)
    have n244 : ¬modelAssignment n A (addVar n 2 4 4) := by
      intro hτ
      exact E.two_add_x_ne_x ((modelAssignment_addVar_iff H h2 h4 h4).1 hτ)
    exact ⟨t112, t213, n141, n241, n441, nm441, n444, nm444, n144, n244⟩
  · constructor
    · intro j hj z hz i hi hboth
      have hiD : InDomain n i := mem_123_inDomain h5 hi
      have hjD : InDomain n j := mem_123_inDomain h5 hj
      have hadd : A.add i z = 5 := (modelAssignment_addVar_iff H hiD hz h5).1 hboth.1
      have hmul : A.mul j 4 = z := (modelAssignment_mulVar_iff H hjD h4 hz).1 hboth.2
      exact E.jackson hi hj hz ⟨hadd, hmul⟩
    · intro v hv p hp
      rcases (mem_product2_iff).1 hp with ⟨hi, hl⟩
      cases p with
      | mk i l =>
          constructor
          · intro h
            have hP : Pterm A 4 = i := by
              simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hi).1 h.1
            have hQ : Qterm A 4 = l := by
              simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hl).1 h.2.1
            have hmul : A.mul i v = l :=
              (modelAssignment_mulVar_iff H hi hv hl).1 h.2.2
            exact E.zhang_pq_forward hi hl hv ⟨hP, hQ, hmul⟩
          · constructor
            · intro h
              have hQ : Qterm A 4 = i := by
                simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hi).1 h.1
              have hP : Pterm A 4 = l := by
                simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hl).1 h.2.1
              have hmul : A.mul i v = l :=
                (modelAssignment_mulVar_iff H hi hv hl).1 h.2.2
              exact E.zhang_pq_backward hi hl hv ⟨hQ, hP, hmul⟩
            · constructor
              · intro h
                have hR : Rterm A 4 = i := by
                  simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hi).1 h.1
                have hS : Sterm A 4 = l := by
                  simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hl).1 h.2.1
                have hmul : A.mul i v = l :=
                  (modelAssignment_mulVar_iff H hi hv hl).1 h.2.2
                exact E.zhang_rs_forward hi hl hv ⟨hR, hS, hmul⟩
              · intro h
                have hS : Sterm A 4 = i := by
                  simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hi).1 h.1
                have hR : Rterm A 4 = l := by
                  simpa [wilkieTermExpr] using (modelAssignment_termVar_iff hl).1 h.2.1
                have hmul : A.mul i v = l :=
                  (modelAssignment_mulVar_iff H hi hv hl).1 h.2.2
                exact E.zhang_rs_backward hi hl hv ⟨hS, hR, hmul⟩

theorem simpEncExtraClauses_modelAssignment
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (h112 : A.add 1 1 = 2) (h213 : A.add 2 1 = 3)
    (hFail : WilkieFailsAt A 4 5 4) :
    evalCNF (modelAssignment n A) (simpEncExtraClauses n) := by
  have E := extraConstraints_of_normalizedAndWilkieFails
    C H h5 hFail h112 h213
  have hExtraSem :=
    extraConstraints_yields_extraSemantics_modelAssignment h5 H E
  unfold simpEncExtraClauses
  repeat rw [evalCNF_append]
  refine ⟨⟨⟨⟨⟨?fixed, ?valueBlock⟩, ?leeDiv⟩, ?jacksonLinear⟩,
    ?jacksonQuadratic⟩, ?zhangLee⟩
  · exact simpEncFixedUnitClauses_modelAssignment C H h5 h112 h213 hFail
  · exact simpEncValueBlockClauses_modelAssignment C H h5 h112 hFail
  · exact simpEncLeeDivClauses_modelAssignment C H h5 hFail
  · exact (extraJacksonClauses_correct n (modelAssignment n A)).2 hExtraSem.2.1
  · exact simpEncJacksonQuadraticClauses_modelAssignment C H h5 h112 h213 hFail
  · exact (extraZhangClauses_correct n (modelAssignment n A)).2 hExtraSem.2.2

def ViolatesWilkie (n : Nat) (A : Algebra) : Prop :=
  ∃ x y, InDomain n x ∧ InDomain n y ∧ WilkieFailsAt A x y x

structure Countermodel (n : Nat) (A : Algebra) : Prop where
  closed : Closed n A
  hsi : HSI n A
  wilkie_fails : WilkieFailsAt A 4 5 4

structure GeneralCountermodel (n : Nat) (A : Algebra) : Prop where
  closed : Closed n A
  hsi : HSI n A
  violates_wilkie : ViolatesWilkie n A

structure NormalizedCountermodel (n : Nat) (A : Algebra) : Prop where
  closed : Closed n A
  hsi : HSI n A
  wilkie_fails : WilkieFailsAt A 4 5 4
  add_one_one : A.add 1 1 = 2
  add_two_one : A.add 2 1 = 3

structure Relabeling (n : Nat) where
  toOld : Nat → Nat
  toNew : Nat → Nat
  toOld_mem : ∀ {x}, InDomain n x → InDomain n (toOld x)
  toNew_mem : ∀ {x}, InDomain n x → InDomain n (toNew x)
  left_inv : ∀ {x}, InDomain n x → toNew (toOld x) = x
  right_inv : ∀ {x}, InDomain n x → toOld (toNew x) = x

def relabelAlgebra {n : Nat} (ρ : Relabeling n) (A : Algebra) : Algebra where
  add i j := ρ.toNew (A.add (ρ.toOld i) (ρ.toOld j))
  mul i j := ρ.toNew (A.mul (ρ.toOld i) (ρ.toOld j))
  exp i j := ρ.toNew (A.exp (ρ.toOld i) (ρ.toOld j))

theorem Relabeling.eq_of_toOld_eq
    {n x y : Nat} (ρ : Relabeling n)
    (hx : InDomain n x) (hy : InDomain n y)
    (h : ρ.toOld x = ρ.toOld y) :
    x = y := by
  calc
    x = ρ.toNew (ρ.toOld x) := (ρ.left_inv hx).symm
    _ = ρ.toNew (ρ.toOld y) := by rw [h]
    _ = y := ρ.left_inv hy

theorem swapNat_left (a b : Nat) : swapNat a b a = b := by
  simp [swapNat]

theorem swapNat_right (a b : Nat) : swapNat a b b = a := by
  by_cases h : b = a
  · subst b
    simp [swapNat]
  · simp [swapNat, h]

theorem swapNat_fixed {a b x : Nat} (hxa : x ≠ a) (hxb : x ≠ b) :
    swapNat a b x = x := by
  simp [swapNat, hxa, hxb]

theorem swapNat_involutive (a b x : Nat) :
    swapNat a b (swapNat a b x) = x := by
  by_cases hxa : x = a
  · subst x
    rw [swapNat_left, swapNat_right]
  · by_cases hxb : x = b
    · subst x
      rw [swapNat_right, swapNat_left]
    · rw [swapNat_fixed hxa hxb, swapNat_fixed hxa hxb]

def idRelabeling (n : Nat) : Relabeling n where
  toOld x := x
  toNew x := x
  toOld_mem hx := hx
  toNew_mem hx := hx
  left_inv _ := rfl
  right_inv _ := rfl

def swapRelabeling (n a b : Nat)
    (ha : InDomain n a) (hb : InDomain n b) : Relabeling n where
  toOld x := swapNat a b x
  toNew x := swapNat a b x
  toOld_mem := by
    intro x hx
    by_cases hxa : x = a
    · rw [hxa, swapNat_left]
      exact hb
    · by_cases hxb : x = b
      · rw [hxb, swapNat_right]
        exact ha
      · rw [swapNat_fixed hxa hxb]
        exact hx
  toNew_mem := by
    intro x hx
    by_cases hxa : x = a
    · rw [hxa, swapNat_left]
      exact hb
    · by_cases hxb : x = b
      · rw [hxb, swapNat_right]
        exact ha
      · rw [swapNat_fixed hxa hxb]
        exact hx
  left_inv _ := swapNat_involutive a b _
  right_inv _ := swapNat_involutive a b _

def Relabeling.comp {n : Nat} (σ ρ : Relabeling n) : Relabeling n where
  toOld x := σ.toOld (ρ.toOld x)
  toNew x := ρ.toNew (σ.toNew x)
  toOld_mem hx := σ.toOld_mem (ρ.toOld_mem hx)
  toNew_mem hx := ρ.toNew_mem (σ.toNew_mem hx)
  left_inv := by
    intro x hx
    calc
      ρ.toNew (σ.toNew (σ.toOld (ρ.toOld x))) = ρ.toNew (ρ.toOld x) := by
        rw [σ.left_inv (ρ.toOld_mem hx)]
      _ = x := ρ.left_inv hx
  right_inv := by
    intro x hx
    have hs : InDomain n (σ.toNew x) := σ.toNew_mem hx
    calc
      σ.toOld (ρ.toOld (ρ.toNew (σ.toNew x))) = σ.toOld (σ.toNew x) := by
        rw [ρ.right_inv hs]
      _ = x := σ.right_inv hx

theorem relabelAlgebra_comp
    {n : Nat} {A : Algebra} (ρ σ : Relabeling n) :
    relabelAlgebra σ (relabelAlgebra ρ A) =
      relabelAlgebra (Relabeling.comp ρ σ) A := by
  cases ρ
  cases σ
  rfl

def bitVal : Bool → Nat
  | false => 0
  | true => 1

def boolLexLE : List Bool → List Bool → Prop
  | [], [] => True
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys =>
      (x = false ∧ y = true) ∨ (x = y ∧ boolLexLE xs ys)

def boolLexRank : List Bool → Nat
  | [] => 0
  | x :: xs => bitVal x * 2 ^ xs.length + boolLexRank xs

theorem boolLexRank_lt_pow_length (xs : List Bool) :
    boolLexRank xs < 2 ^ xs.length := by
  induction xs with
  | nil =>
      simp [boolLexRank]
  | cons x xs ih =>
      cases x <;> simp [boolLexRank, bitVal, Nat.pow_succ] <;> omega

theorem boolLexRank_le_iff_boolLexLE :
    ∀ {xs ys : List Bool}, xs.length = ys.length →
      (boolLexRank xs ≤ boolLexRank ys ↔ boolLexLE xs ys)
  | [], [], _ => by simp [boolLexRank, boolLexLE]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp at h
      have ih := boolLexRank_le_iff_boolLexLE (xs := xs) (ys := ys) h
      have hxBound := boolLexRank_lt_pow_length xs
      have hyBound := boolLexRank_lt_pow_length ys
      have hpow : 2 ^ xs.length = 2 ^ ys.length := by rw [h]
      cases x <;> cases y
      · simp [boolLexRank, boolLexLE, bitVal, ih]
      · simp [boolLexRank, boolLexLE, bitVal]
        omega
      · simp [boolLexRank, boolLexLE, bitVal]
        omega
      · simp [boolLexRank, boolLexLE, bitVal]
        rw [hpow]
        constructor
        · intro hle
          exact ih.mp (by omega)
        · intro hlex
          have hle := ih.mpr hlex
          omega

def lexEvalOp (A : Algebra) : Op → Nat → Nat → Nat
  | .add, x, y => A.add (min x y) (max x y)
  | .mul, x, y => A.mul (min x y) (max x y)
  | .exp, x, y => A.exp x y

def lexTable (n : Nat) (A : Algebra) : List Bool :=
  (lexTableEntries n).map (fun (op, x, y, value) =>
    decide (lexEvalOp A op x y = value))

def lexTableRank (n : Nat) (A : Algebra) : Nat :=
  boolLexRank (lexTable n A)

noncomputable def assignmentLexLeft (τ : Assignment) (pairs : List (Nat × Nat)) : List Bool :=
  pairs.map (fun p => by
    classical
    exact decide (τ p.1))

noncomputable def assignmentLexRight (τ : Assignment) (pairs : List (Nat × Nat)) : List Bool :=
  pairs.map (fun p => by
    classical
    exact decide (τ p.2))

theorem AssignmentLexLE_iff_boolLexLE
    (τ : Assignment) :
    ∀ pairs : List (Nat × Nat),
      AssignmentLexLE τ pairs ↔
        boolLexLE (assignmentLexLeft τ pairs) (assignmentLexRight τ pairs)
  | [] => by simp [AssignmentLexLE, assignmentLexLeft, assignmentLexRight, boolLexLE]
  | (a, b) :: rest => by
      classical
      have ih := AssignmentLexLE_iff_boolLexLE τ rest
      by_cases ha : τ a <;> by_cases hb : τ b <;>
        simp [AssignmentLexLE, assignmentLexLeft, assignmentLexRight, boolLexLE,
          ha, hb, ih]

theorem mem_rangeFromTo_bounds {lo hi x : Nat}
    (h : x ∈ rangeFromTo lo hi) :
    lo ≤ x ∧ x ≤ hi := by
  unfold rangeFromTo at h
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  have hdlt := List.mem_range.mp hd
  omega

theorem mem_strictPairs_domain {n : Nat} {p : Nat × Nat}
    (hp : p ∈ strictPairs n) :
    InDomain n p.1 ∧ InDomain n p.2 := by
  unfold strictPairs at hp
  rw [mem_flatMap_iff] at hp
  rcases hp with ⟨i, hi, hpairs⟩
  rcases List.mem_map.mp hpairs with ⟨j, hj, hpair⟩
  cases hpair
  have hjBounds := mem_rangeFromTo_bounds hj
  have hjValue : j ∈ values n := by
    rw [mem_values_iff]
    exact ⟨by omega, hjBounds.2⟩
  exact ⟨hi, hjValue⟩

theorem mem_lexPairsForOp_domain
    {n : Nat} {op : Op} {p : Nat × Nat}
    (hp : p ∈ lexPairsForOp n op) :
    InDomain n p.1 ∧ InDomain n p.2 := by
  cases op
  · exact mem_strictPairs_domain hp
  · exact mem_strictPairs_domain hp
  · unfold lexPairsForOp at hp
    exact (mem_product2_iff).1 hp

theorem mem_lexTableEntries_domain
    {n : Nat} {op : Op} {x y value : Nat}
    (h : (op, x, y, value) ∈ lexTableEntries n) :
    InDomain n x ∧ InDomain n y ∧ InDomain n value := by
  unfold lexTableEntries at h
  rw [mem_flatMap_iff] at h
  rcases h with ⟨op', hop', hpairs⟩
  rw [mem_flatMap_iff] at hpairs
  rcases hpairs with ⟨p, hp, hvalues⟩
  rcases p with ⟨x', y'⟩
  rcases List.mem_map.mp hvalues with ⟨value', hvalue, hentry⟩
  cases hentry
  have hpdom := mem_lexPairsForOp_domain hp
  exact ⟨hpdom.1, hpdom.2, hvalue⟩

def IsSimpEncLexTranspositionPair (n : Nat) (p : Nat × Nat) : Prop :=
  InDomain n p.1 ∧ InDomain n p.2 ∧ 5 < p.1 ∧ 5 < p.2 ∧ p.1 < p.2

def LexTranspositionLeadersForPairs
    (n : Nat) (A : Algebra) (pairs : List (Nat × Nat)) : Prop :=
  ∀ {left right : Nat}, (left, right) ∈ pairs →
    (hleft : InDomain n left) → (hright : InDomain n right) →
    boolLexLE (lexTable n A)
      (lexTable n
        (relabelAlgebra (swapRelabeling n left right
          hleft hright) A))

theorem simpEncLexTranspositionPairs_mem_spec
    {n : Nat} {p : Nat × Nat}
    (hp : p ∈ simpEncLexTranspositionPairs n) :
    IsSimpEncLexTranspositionPair n p := by
  unfold simpEncLexTranspositionPairs at hp
  rw [mem_flatMap_iff] at hp
  rcases hp with ⟨left, hleftMem, hrightList⟩
  rcases List.mem_map.mp hrightList with ⟨right, hrightMem, hpEq⟩
  cases hpEq
  have hleftBounds := mem_rangeFromTo_bounds hleftMem
  have hrightBounds := mem_rangeFromTo_bounds hrightMem
  constructor
  · rw [InDomain_iff]
    omega
  · constructor
    · rw [InDomain_iff]
      omega
    · omega

theorem swapNat_mem_domain
    {n left right x : Nat}
    (hleft : InDomain n left) (hright : InDomain n right)
    (hx : InDomain n x) :
    InDomain n (swapNat left right x) := by
  simpa [swapRelabeling] using
    (swapRelabeling n left right hleft hright).toOld_mem hx

theorem swapNat_eq_iff_eq_swapNat (left right x y : Nat) :
    swapNat left right x = y ↔ x = swapNat left right y := by
  constructor
  · intro h
    calc
      x = swapNat left right (swapNat left right x) := (swapNat_involutive left right x).symm
      _ = swapNat left right y := by rw [h]
  · intro h
    calc
      swapNat left right x = swapNat left right (swapNat left right y) := by rw [h]
      _ = y := swapNat_involutive left right y

theorem lexEvalOp_add_eq
    {n : Nat} {A : Algebra} (H : HSI n A)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y) :
    lexEvalOp A .add x y = A.add x y := by
  by_cases hxy : x ≤ y
  · simp [lexEvalOp, Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    simpa [lexEvalOp, Nat.min_eq_right hyx, Nat.max_eq_left hyx]
      using (H.add_comm hx hy).symm

theorem lexEvalOp_mul_eq
    {n : Nat} {A : Algebra} (H : HSI n A)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y) :
    lexEvalOp A .mul x y = A.mul x y := by
  by_cases hxy : x ≤ y
  · simp [lexEvalOp, Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    simpa [lexEvalOp, Nat.min_eq_right hyx, Nat.max_eq_left hyx]
      using (H.mul_comm hx hy).symm

theorem lexEvalOp_swapRelabeling_add
    {n left right : Nat} {A : Algebra} (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y) :
    lexEvalOp (relabelAlgebra (swapRelabeling n left right hleft hright) A) .add x y =
      swapNat left right (A.add (swapNat left right x) (swapNat left right y)) := by
  by_cases hxy : x ≤ y
  · simp [relabelAlgebra, swapRelabeling, lexEvalOp,
      Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    have hsx : InDomain n (swapNat left right x) :=
      swapNat_mem_domain hleft hright hx
    have hsy : InDomain n (swapNat left right y) :=
      swapNat_mem_domain hleft hright hy
    have hcomm : A.add (swapNat left right y) (swapNat left right x) =
        A.add (swapNat left right x) (swapNat left right y) :=
      H.add_comm hsy hsx
    simp [relabelAlgebra, swapRelabeling, lexEvalOp,
      Nat.min_eq_right hyx, Nat.max_eq_left hyx, hcomm]

theorem lexEvalOp_swapRelabeling_mul
    {n left right : Nat} {A : Algebra} (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y) :
    lexEvalOp (relabelAlgebra (swapRelabeling n left right hleft hright) A) .mul x y =
      swapNat left right (A.mul (swapNat left right x) (swapNat left right y)) := by
  by_cases hxy : x ≤ y
  · simp [relabelAlgebra, swapRelabeling, lexEvalOp,
      Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    have hsx : InDomain n (swapNat left right x) :=
      swapNat_mem_domain hleft hright hx
    have hsy : InDomain n (swapNat left right y) :=
      swapNat_mem_domain hleft hright hy
    have hcomm : A.mul (swapNat left right y) (swapNat left right x) =
        A.mul (swapNat left right x) (swapNat left right y) :=
      H.mul_comm hsy hsx
    simp [relabelAlgebra, swapRelabeling, lexEvalOp,
      Nat.min_eq_right hyx, Nat.max_eq_left hyx, hcomm]

theorem lexEvalOp_swapRelabeling_exp
    {n left right : Nat} {A : Algebra}
    (hleft : InDomain n left) (hright : InDomain n right)
    {x y : Nat} :
    lexEvalOp (relabelAlgebra (swapRelabeling n left right hleft hright) A) .exp x y =
      swapNat left right (A.exp (swapNat left right x) (swapNat left right y)) := by
  simp [relabelAlgebra, swapRelabeling, lexEvalOp]

theorem modelAssignment_lexEntryVar_iff
    {n : Nat} {A : Algebra} (H : HSI n A)
    {op : Op} {x y value : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hvalue : InDomain n value) :
    modelAssignment n A (lexEntryVar n (op, x, y, value)) ↔
      lexEvalOp A op x y = value := by
  cases op
  · simpa [lexEntryVar, opVar, lexEvalOp_add_eq H hx hy]
      using modelAssignment_addVar_iff H hx hy hvalue
  · simpa [lexEntryVar, opVar, lexEvalOp_mul_eq H hx hy]
      using modelAssignment_mulVar_iff H hx hy hvalue
  · simpa [lexEntryVar, opVar, lexEvalOp]
      using modelAssignment_expVar_iff hx hy hvalue

theorem modelAssignment_lexTranspositionImageVar_iff
    {n left right : Nat} {A : Algebra} (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right)
    {op : Op} {x y value : Nat}
    (hx : InDomain n x) (hy : InDomain n y) (hvalue : InDomain n value) :
    modelAssignment n A (lexTranspositionImageVar n left right (op, x, y, value)) ↔
      lexEvalOp (relabelAlgebra (swapRelabeling n left right hleft hright) A)
        op x y = value := by
  let sx := swapNat left right x
  let sy := swapNat left right y
  let sv := swapNat left right value
  have hsx : InDomain n sx := swapNat_mem_domain hleft hright hx
  have hsy : InDomain n sy := swapNat_mem_domain hleft hright hy
  have hsv : InDomain n sv := swapNat_mem_domain hleft hright hvalue
  cases op
  · have hmodel := modelAssignment_addVar_iff H hsx hsy hsv
    have hswap :
        (A.add sx sy = sv) ↔
          swapNat left right (A.add sx sy) = value := by
      simpa [sv] using
        (swapNat_eq_iff_eq_swapNat left right (A.add sx sy) value).symm
    rw [lexEvalOp_swapRelabeling_add H hleft hright hx hy]
    simpa [lexTranspositionImageVar, opVar, sx, sy, sv] using hmodel.trans hswap
  · have hmodel := modelAssignment_mulVar_iff H hsx hsy hsv
    have hswap :
        (A.mul sx sy = sv) ↔
          swapNat left right (A.mul sx sy) = value := by
      simpa [sv] using
        (swapNat_eq_iff_eq_swapNat left right (A.mul sx sy) value).symm
    rw [lexEvalOp_swapRelabeling_mul H hleft hright hx hy]
    simpa [lexTranspositionImageVar, opVar, sx, sy, sv] using hmodel.trans hswap
  · have hmodel := modelAssignment_expVar_iff (A := A) hsx hsy hsv
    have hswap :
        (A.exp sx sy = sv) ↔
          swapNat left right (A.exp sx sy) = value := by
      simpa [sv] using
        (swapNat_eq_iff_eq_swapNat left right (A.exp sx sy) value).symm
    rw [lexEvalOp_swapRelabeling_exp hleft hright]
    simpa [lexTranspositionImageVar, opVar, sx, sy, sv] using hmodel.trans hswap

theorem assignmentLexLeft_modelAssignment_eq_lexTable
    {n : Nat} {A : Algebra} (H : HSI n A) (left right : Nat) :
    assignmentLexLeft (modelAssignment n A)
        (lexTranspositionVarPairs n left right) =
      lexTable n A := by
  classical
  simp [assignmentLexLeft, lexTranspositionVarPairs, lexTable]
  intro op x y value hentry
  have hdom := mem_lexTableEntries_domain (n := n)
    (op := op) (x := x) (y := y) (value := value) hentry
  exact modelAssignment_lexEntryVar_iff H hdom.1 hdom.2.1 hdom.2.2

theorem assignmentLexRight_modelAssignment_eq_relabelLexTable
    {n left right : Nat} {A : Algebra} (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right) :
    assignmentLexRight (modelAssignment n A)
        (lexTranspositionVarPairs n left right) =
      lexTable n
        (relabelAlgebra (swapRelabeling n left right hleft hright) A) := by
  classical
  simp [assignmentLexRight, lexTranspositionVarPairs, lexTable]
  intro op x y value hentry
  have hdom := mem_lexTableEntries_domain (n := n)
    (op := op) (x := x) (y := y) (value := value) hentry
  exact modelAssignment_lexTranspositionImageVar_iff H
    hleft hright hdom.1 hdom.2.1 hdom.2.2

theorem modelAssignment_assignmentLexLE_iff_lexTransposition
    {n left right : Nat} {A : Algebra} (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right) :
    AssignmentLexLE (modelAssignment n A)
        (lexTranspositionVarPairs n left right) ↔
      boolLexLE (lexTable n A)
        (lexTable n
          (relabelAlgebra (swapRelabeling n left right hleft hright) A)) := by
  rw [AssignmentLexLE_iff_boolLexLE]
  rw [assignmentLexLeft_modelAssignment_eq_lexTable H left right]
  rw [assignmentLexRight_modelAssignment_eq_relabelLexTable H hleft hright]

theorem opVar_le_primaryCount
    {n : Nat} {op : Op} {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    opVar n op i j k ≤ primaryCount n := by
  cases op
  · exact Nat.le_trans (addVar_block hi hj hk).2 (primary1_le_primaryCount n)
  · exact Nat.le_trans (mulVar_block hi hj hk).2 (primary2_le_primaryCount n)
  · exact (expVar_block hi hj hk).2

theorem primary_lt_simpEncLexAuxStart (n : Nat) :
    primaryCount n < simpEncLexAuxStart n := by
  unfold simpEncLexAuxStart
  have h := primary_le_wilkieTermBase n
  omega

theorem opVar_lt_simpEncLexAuxStart
    {n : Nat} {op : Op} {i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    opVar n op i j k < simpEncLexAuxStart n := by
  exact Nat.lt_of_le_of_lt
    (opVar_le_primaryCount hi hj hk)
    (primary_lt_simpEncLexAuxStart n)

theorem addVar_lt_simpEncLexAuxStart
    {n i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    addVar n i j k < simpEncLexAuxStart n := by
  simpa [opVar] using
    (opVar_lt_simpEncLexAuxStart (op := Op.add) hi hj hk)

theorem mulVar_lt_simpEncLexAuxStart
    {n i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    mulVar n i j k < simpEncLexAuxStart n := by
  simpa [opVar] using
    (opVar_lt_simpEncLexAuxStart (op := Op.mul) hi hj hk)

theorem expVar_lt_simpEncLexAuxStart
    {n i j k : Nat}
    (hi : InDomain n i) (hj : InDomain n j) (hk : InDomain n k) :
    expVar n i j k < simpEncLexAuxStart n := by
  simpa [opVar] using
    (opVar_lt_simpEncLexAuxStart (op := Op.exp) hi hj hk)

theorem termVar_lt_simpEncLexAuxStart
    {n termIndex value : Nat}
    (hterm : termIndex < wilkieTermCount) (hvalue : InDomain n value) :
    termVar n termIndex value < simpEncLexAuxStart n := by
  have hlin :
      termIndex * n + (value - 1) < wilkieTermCount * n :=
    linearIndex_lt_mul (a := termIndex) (A := wilkieTermCount)
      hterm hvalue
  unfold termVar simpEncLexAuxStart
  omega

theorem wilkieTermBase_lt_simpEncLexAuxStart (n : Nat) :
    wilkieTermBase n < simpEncLexAuxStart n := by
  unfold simpEncLexAuxStart
  omega

theorem mul2Base_le_wilkieTermBase (n : Nat) :
    mul2Base n ≤ wilkieTermBase n :=
  Nat.le_trans (mul2Base_le_distBase n)
    (Nat.le_trans (distBase_le_expAddBase n)
      (Nat.le_trans (expAddBase_le_expMulBase n)
        (Nat.le_trans (expMulBase_le_exp2Base n)
          (exp2Base_le_wilkieTermBase n))))

theorem distBase_le_wilkieTermBase (n : Nat) :
    distBase n ≤ wilkieTermBase n :=
  Nat.le_trans (distBase_le_expAddBase n)
    (Nat.le_trans (expAddBase_le_expMulBase n)
      (Nat.le_trans (expMulBase_le_exp2Base n)
        (exp2Base_le_wilkieTermBase n)))

theorem expAddBase_le_wilkieTermBase (n : Nat) :
    expAddBase n ≤ wilkieTermBase n :=
  Nat.le_trans (expAddBase_le_expMulBase n)
    (Nat.le_trans (expMulBase_le_exp2Base n)
      (exp2Base_le_wilkieTermBase n))

theorem expMulBase_le_wilkieTermBase (n : Nat) :
    expMulBase n ≤ wilkieTermBase n :=
  Nat.le_trans (expMulBase_le_exp2Base n)
    (exp2Base_le_wilkieTermBase n)

theorem add2Var_lt_simpEncLexAuxStart
    {n i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j)
    (hk : InDomain n k) (hl : InDomain n l) :
    add2Var n i j k l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (add2Var_block hi hj hk hl).2
      (mul2Base_le_wilkieTermBase n))
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem mul2Var_lt_simpEncLexAuxStart
    {n i j k l : Nat}
    (hi : InDomain n i) (hj : InDomain n j)
    (hk : InDomain n k) (hl : InDomain n l) :
    mul2Var n i j k l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (mul2Var_block hi hj hk hl).2
      (distBase_le_wilkieTermBase n))
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem distVar_lt_simpEncLexAuxStart
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y)
    (hz : InDomain n z) (hl : InDomain n l) :
    distVar n x y z l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (distVar_block hx hy hz hl).2
      (expAddBase_le_wilkieTermBase n))
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem expAddVar_lt_simpEncLexAuxStart
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y)
    (hz : InDomain n z) (hl : InDomain n l) :
    expAddVar n x y z l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (expAddVar_block hx hy hz hl).2
      (expMulBase_le_wilkieTermBase n))
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem expMulVar_lt_simpEncLexAuxStart
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y)
    (hz : InDomain n z) (hl : InDomain n l) :
    expMulVar n x y z l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (expMulVar_block hx hy hz hl).2
      (exp2Base_le_wilkieTermBase n))
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem exp2Var_lt_simpEncLexAuxStart
    {n x y z l : Nat}
    (hx : InDomain n x) (hy : InDomain n y)
    (hz : InDomain n z) (hl : InDomain n l) :
    exp2Var n x y z l < simpEncLexAuxStart n :=
  Nat.lt_of_le_of_lt (exp2Var_block hx hy hz hl).2
    (wilkieTermBase_lt_simpEncLexAuxStart n)

theorem lexTranspositionVarPairs_positive
    (n left right : Nat) :
    PairVarsPositive (lexTranspositionVarPairs n left right) := by
  intro p hp
  unfold lexTranspositionVarPairs at hp
  rcases List.mem_map.mp hp with ⟨entry, _hentry, hpEq⟩
  cases entry with
  | mk op xyz =>
      cases xyz with
      | mk x yz =>
          cases yz with
          | mk y value =>
              cases hpEq
              exact ⟨opVar_pos n op x y value,
                opVar_pos n op (swapNat left right x) (swapNat left right y)
                  (swapNat left right value)⟩

theorem lexTranspositionVarPairs_below
    {n left right aux : Nat}
    (hleft : InDomain n left) (hright : InDomain n right)
    (haux : primaryCount n < aux) :
    PairVarsBelow (lexTranspositionVarPairs n left right) aux := by
  intro p hp
  unfold lexTranspositionVarPairs at hp
  rcases List.mem_map.mp hp with ⟨entry, hentry, hpEq⟩
  cases entry with
  | mk op xyz =>
      cases xyz with
      | mk x yz =>
          cases yz with
          | mk y value =>
              cases hpEq
              have hdom := mem_lexTableEntries_domain (n := n)
                (op := op) (x := x) (y := y) (value := value) hentry
              have hsx : InDomain n (swapNat left right x) :=
                swapNat_mem_domain hleft hright hdom.1
              have hsy : InDomain n (swapNat left right y) :=
                swapNat_mem_domain hleft hright hdom.2.1
              have hsv : InDomain n (swapNat left right value) :=
                swapNat_mem_domain hleft hright hdom.2.2
              exact ⟨
                Nat.lt_of_le_of_lt (opVar_le_primaryCount hdom.1 hdom.2.1 hdom.2.2) haux,
                Nat.lt_of_le_of_lt (opVar_le_primaryCount hsx hsy hsv) haux⟩

theorem lexTranspositionVarPairs_le_primaryCount
    {n left right : Nat}
    (hleft : InDomain n left) (hright : InDomain n right) :
    ∀ p, p ∈ lexTranspositionVarPairs n left right →
      p.1 ≤ primaryCount n ∧ p.2 ≤ primaryCount n := by
  intro p hp
  unfold lexTranspositionVarPairs at hp
  rcases List.mem_map.mp hp with ⟨entry, hentry, hpEq⟩
  cases entry with
  | mk op xyz =>
      cases xyz with
      | mk x yz =>
          cases yz with
          | mk y value =>
              cases hpEq
              have hdom := mem_lexTableEntries_domain (n := n)
                (op := op) (x := x) (y := y) (value := value) hentry
              have hsx : InDomain n (swapNat left right x) :=
                swapNat_mem_domain hleft hright hdom.1
              have hsy : InDomain n (swapNat left right y) :=
                swapNat_mem_domain hleft hright hdom.2.1
              have hsv : InDomain n (swapNat left right value) :=
                swapNat_mem_domain hleft hright hdom.2.2
              exact ⟨opVar_le_primaryCount hdom.1 hdom.2.1 hdom.2.2,
                opVar_le_primaryCount hsx hsy hsv⟩

theorem lexTranspositionClausesFrom_below
    {n left right aux : Nat}
    (hleft : InDomain n left) (hright : InDomain n right)
    (haux : primaryCount n < aux) :
    CNFBelow (lexTranspositionClausesFrom n left right aux)
      (aux + lexTranspositionAuxCount n left right) := by
  unfold lexTranspositionClausesFrom lexTranspositionAuxCount
  exact lexSmallerEqClausesFrom_below
    (lexTranspositionVarPairs_below hleft hright haux)

theorem lexTranspositionClausesFrom_satisfiable_iff_assignmentLexLE
    {n left right aux : Nat} {τ : Assignment}
    (hleft : InDomain n left) (hright : InDomain n right)
    (haux : primaryCount n < aux) :
    (∃ τ' : Assignment,
      (∀ v, v < aux → (τ' v ↔ τ v)) ∧
      evalCNF τ' (lexTranspositionClausesFrom n left right aux)) ↔
      AssignmentLexLE τ (lexTranspositionVarPairs n left right) := by
  unfold lexTranspositionClausesFrom
  exact lexSmallerEqClausesFrom_satisfiable_iff_assignmentLexLE
    (by omega)
    (lexTranspositionVarPairs_positive n left right)
    (lexTranspositionVarPairs_below hleft hright haux)

theorem lexTranspositionClausesFrom_satisfiable_of_assignment_agrees_primary
    {n left right aux : Nat} {τ : Assignment} {A : Algebra}
    (H : HSI n A)
    (hleft : InDomain n left) (hright : InDomain n right)
    (haux : primaryCount n < aux)
    (hprimary :
      ∀ v, v ≤ primaryCount n → (τ v ↔ modelAssignment n A v))
    (hlex :
      boolLexLE (lexTable n A)
        (lexTable n
          (relabelAlgebra (swapRelabeling n left right hleft hright) A))) :
    ∃ τ' : Assignment,
      (∀ v, v < aux → (τ' v ↔ τ v)) ∧
      evalCNF τ' (lexTranspositionClausesFrom n left right aux) := by
  have hmodelAssign :
      AssignmentLexLE (modelAssignment n A)
        (lexTranspositionVarPairs n left right) :=
    (modelAssignment_assignmentLexLE_iff_lexTransposition
      H hleft hright).2 hlex
  have hcongr :
      ∀ p, p ∈ lexTranspositionVarPairs n left right →
        (modelAssignment n A p.1 ↔ τ p.1) ∧
          (modelAssignment n A p.2 ↔ τ p.2) := by
    intro p hp
    have hle := lexTranspositionVarPairs_le_primaryCount hleft hright p hp
    exact ⟨(hprimary p.1 hle.1).symm, (hprimary p.2 hle.2).symm⟩
  have hassign :
      AssignmentLexLE τ (lexTranspositionVarPairs n left right) :=
    (AssignmentLexLE_congr (τ := modelAssignment n A) (σ := τ)
      (pairs := lexTranspositionVarPairs n left right) hcongr).1 hmodelAssign
  exact (lexTranspositionClausesFrom_satisfiable_iff_assignmentLexLE
    hleft hright haux).2 hassign

theorem simpEncLexClausesFromAux_satisfiable_of_pairs_lexLeaders
    {n aux : Nat} {pairs : List (Nat × Nat)}
    {τ : Assignment} {A : Algebra}
    (H : HSI n A)
    (hpairs : ∀ p, p ∈ pairs → IsSimpEncLexTranspositionPair n p)
    (haux : primaryCount n < aux)
    (hprimary :
      ∀ v, v ≤ primaryCount n → (τ v ↔ modelAssignment n A v))
    (hlexPairs : LexTranspositionLeadersForPairs n A pairs) :
    ∃ τ' : Assignment,
      (∀ v, v < aux → (τ' v ↔ τ v)) ∧
      evalCNF τ' (simpEncLexClausesFromAux n aux pairs) := by
  induction pairs generalizing aux τ with
  | nil =>
      refine ⟨τ, ?_, ?_⟩
      · intro v _hv
        rfl
      · exact trivial
  | cons p rest ih =>
      cases p with
      | mk left0 right0 =>
          have hp0 : IsSimpEncLexTranspositionPair n (left0, right0) :=
            hpairs (left0, right0) (by simp)
          have hlexHead :
              boolLexLE (lexTable n A)
                (lexTable n
                  (relabelAlgebra
                    (swapRelabeling n left0 right0 hp0.1 hp0.2.1) A)) :=
            hlexPairs (by simp) hp0.1 hp0.2.1
          rcases lexTranspositionClausesFrom_satisfiable_of_assignment_agrees_primary
              H hp0.1 hp0.2.1 haux hprimary hlexHead with
            ⟨τ1, hτ1Preserve, hhead⟩
          let nextAux := aux + lexTranspositionAuxCount n left0 right0
          have hauxNext : primaryCount n < nextAux := by
            have hpos : 0 < lexTranspositionAuxCount n left0 right0 := by
              unfold lexTranspositionAuxCount
              exact lexSmallerEqAuxCount_pos _
            dsimp [nextAux]
            omega
          have hprimary1 :
              ∀ v, v ≤ primaryCount n → (τ1 v ↔ modelAssignment n A v) := by
            intro v hv
            have hvlt : v < aux := by omega
            exact (hτ1Preserve v hvlt).trans (hprimary v hv)
          have hpairsTail :
              ∀ p, p ∈ rest → IsSimpEncLexTranspositionPair n p := by
            intro p hp
            exact hpairs p (by simp [hp])
          have hlexTail :
              LexTranspositionLeadersForPairs n A rest := by
            intro left right hmem hleft hright
            exact hlexPairs (by simp [hmem]) hleft hright
          rcases ih hpairsTail hauxNext hprimary1 hlexTail with
            ⟨τ2, hτ2Preserve, htail⟩
          have hhead₂ :
              evalCNF τ2 (lexTranspositionClausesFrom n left0 right0 aux) := by
            have hbelow :=
              lexTranspositionClausesFrom_below hp0.1 hp0.2.1 haux
            have hagree :
                ∀ v, v < nextAux → (τ2 v ↔ τ1 v) := by
              intro v hv
              exact hτ2Preserve v hv
            exact (evalCNF_congr_of_below hbelow hagree).2 hhead
          refine ⟨τ2, ?_, ?_⟩
          · intro v hv
            have hvnext : v < nextAux := by
              dsimp [nextAux]
              have hpos : 0 < lexTranspositionAuxCount n left0 right0 := by
                unfold lexTranspositionAuxCount
                exact lexSmallerEqAuxCount_pos _
              omega
            exact (hτ2Preserve v hvnext).trans (hτ1Preserve v hv)
          · simp [simpEncLexClausesFromAux, nextAux, evalCNF_append,
              hhead₂, htail]

def FixesProtectedLabels (ρ : Relabeling n) : Prop :=
  ∀ k, k ∈ [1, 2, 3, 4, 5] → ρ.toOld k = k

/--
Semantic form of the transposition lex leaders emitted by `simp_enc.py`:
for every transposition of unprotected labels, the current table is
lexicographically at most its image under that transposition.
-/
def LexTranspositionLeadersHold (n : Nat) (A : Algebra) : Prop :=
  ∀ {left right : Nat}
    (hleft : InDomain n left) (hright : InDomain n right),
    5 < left → 5 < right → left < right →
      boolLexLE (lexTable n A)
        (lexTable n (relabelAlgebra (swapRelabeling n left right hleft hright) A))

structure LexNormalizedCountermodel (n : Nat) (A : Algebra) : Prop where
  normalized : NormalizedCountermodel n A
  lex_leaders : LexTranspositionLeadersHold n A

theorem simpEncLexClauses_satisfiable_of_lexNormalizedCountermodel
    {n aux : Nat} {A : Algebra}
    (hA : LexNormalizedCountermodel n A)
    (haux : primaryCount n < aux) :
    ∃ τ' : Assignment,
      (∀ v, v < aux → (τ' v ↔ modelAssignment n A v)) ∧
      evalCNF τ' (simpEncLexClauses n aux) := by
  have hpairs :
      ∀ p, p ∈ simpEncLexTranspositionPairs n →
        IsSimpEncLexTranspositionPair n p := by
    intro p hp
    exact simpEncLexTranspositionPairs_mem_spec hp
  have hprimary :
      ∀ v, v ≤ primaryCount n →
        (modelAssignment n A v ↔ modelAssignment n A v) := by
    intro v hv
    rfl
  have hlexPairs :
      LexTranspositionLeadersForPairs n A
        (simpEncLexTranspositionPairs n) := by
    intro left right hmem hleft hright
    have hspec := simpEncLexTranspositionPairs_mem_spec hmem
    exact hA.lex_leaders hleft hright
      hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2
  unfold simpEncLexClauses
  exact simpEncLexClausesFromAux_satisfiable_of_pairs_lexLeaders
    hA.normalized.hsi hpairs haux hprimary hlexPairs

theorem idRelabeling_fixesProtectedLabels (n : Nat) :
    FixesProtectedLabels (idRelabeling n) := by
  intro k _hk
  rfl

theorem FixesProtectedLabels.comp
    {n : Nat} {ρ σ : Relabeling n}
    (hρ : FixesProtectedLabels ρ) (hσ : FixesProtectedLabels σ) :
    FixesProtectedLabels (Relabeling.comp ρ σ) := by
  intro k hk
  simp [Relabeling.comp, hσ k hk, hρ k hk]

theorem swapRelabeling_fixesProtectedLabels
    {n left right : Nat} (hleft : InDomain n left) (hright : InDomain n right)
    (hl : 5 < left) (hr : 5 < right) :
    FixesProtectedLabels (swapRelabeling n left right hleft hright) := by
  intro k hk
  have hk_le : k ≤ 5 := by
    simp at hk
    omega
  have hkl : k ≠ left := by omega
  have hkr : k ≠ right := by omega
  simp [swapRelabeling, swapNat_fixed hkl hkr]

theorem exists_nat_min_of_exists {P : Nat → Prop} (h : ∃ k, P k) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  classical
  rcases h with ⟨k, hk⟩
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hsmall : ∃ j, j < k ∧ P j
      · rcases hsmall with ⟨j, hjlt, hpj⟩
        exact ih j hjlt hpj
      · refine ⟨k, hk, ?_⟩
        intro j hpj
        by_cases hjlt : j < k
        · exact False.elim (hsmall ⟨j, hjlt, hpj⟩)
        · omega

theorem exists_protected_lex_min_relabeling (n : Nat) (A : Algebra) :
    ∃ ρ : Relabeling n,
      FixesProtectedLabels ρ ∧
      ∀ σ : Relabeling n, FixesProtectedLabels σ →
        lexTableRank n (relabelAlgebra ρ A) ≤
          lexTableRank n (relabelAlgebra σ A) := by
  let P : Nat → Prop := fun k =>
    ∃ ρ : Relabeling n, FixesProtectedLabels ρ ∧
      lexTableRank n (relabelAlgebra ρ A) = k
  have hP : ∃ k, P k := by
    refine ⟨lexTableRank n (relabelAlgebra (idRelabeling n) A), ?_⟩
    exact ⟨idRelabeling n, idRelabeling_fixesProtectedLabels n, rfl⟩
  rcases exists_nat_min_of_exists hP with ⟨m, hm, hmin⟩
  rcases hm with ⟨ρ, hρ, hrank⟩
  refine ⟨ρ, hρ, ?_⟩
  intro σ hσ
  have hσP : P (lexTableRank n (relabelAlgebra σ A)) :=
    ⟨σ, hσ, rfl⟩
  have hmle := hmin _ hσP
  simpa [hrank] using hmle

theorem exists_relabeling_with_lexTranspositionLeaders
    (n : Nat) (A : Algebra) :
    ∃ ρ : Relabeling n,
      FixesProtectedLabels ρ ∧
      LexTranspositionLeadersHold n (relabelAlgebra ρ A) := by
  rcases exists_protected_lex_min_relabeling n A with ⟨ρ, hρ, hmin⟩
  refine ⟨ρ, hρ, ?_⟩
  intro left right hleft hright hl hr _hlr
  let σ := swapRelabeling n left right hleft hright
  have hσ : FixesProtectedLabels σ :=
    swapRelabeling_fixesProtectedLabels hleft hright hl hr
  have hcomp : FixesProtectedLabels (Relabeling.comp ρ σ) :=
    hρ.comp hσ
  have hmin' := hmin (Relabeling.comp ρ σ) hcomp
  have hrel :
      relabelAlgebra σ (relabelAlgebra ρ A) =
        relabelAlgebra (Relabeling.comp ρ σ) A :=
    relabelAlgebra_comp ρ σ
  have hrank :
      lexTableRank n (relabelAlgebra ρ A) ≤
        lexTableRank n (relabelAlgebra σ (relabelAlgebra ρ A)) := by
    simpa [hrel] using hmin'
  exact (boolLexRank_le_iff_boolLexLE (xs := lexTable n (relabelAlgebra ρ A))
    (ys := lexTable n (relabelAlgebra σ (relabelAlgebra ρ A))) (by simp [lexTable])).1 hrank

def Relabeling.put {n : Nat} (ρ : Relabeling n)
    (l c : Nat) (hl : InDomain n l) (hc : InDomain n c) : Relabeling n :=
  Relabeling.comp (swapRelabeling n (ρ.toOld l) c (ρ.toOld_mem hl) hc) ρ

theorem Relabeling.put_toOld_self {n l c : Nat} (ρ : Relabeling n)
    (hl : InDomain n l) (hc : InDomain n c) :
    (ρ.put l c hl hc).toOld l = c := by
  simp [Relabeling.put, Relabeling.comp, swapRelabeling, swapNat_left]

theorem Relabeling.put_toOld_of_ne {n k l c : Nat} (ρ : Relabeling n)
    (hk : InDomain n k) (hl : InDomain n l) (hc : InDomain n c)
    (hkl : k ≠ l) (hkc : ρ.toOld k ≠ c) :
    (ρ.put l c hl hc).toOld k = ρ.toOld k := by
  unfold Relabeling.put Relabeling.comp swapRelabeling
  apply swapNat_fixed
  · intro hOld
    exact hkl (ρ.eq_of_toOld_eq hk hl hOld)
  · exact hkc

theorem relabeling_exists_of_distinct_one_four
    {n c2 c3 c4 c5 : Nat}
    (h5D : InDomain n 5)
    (hc2 : InDomain n c2) (hc3 : InDomain n c3)
    (hc4 : InDomain n c4) (hc5 : InDomain n c5)
    (h12 : 1 ≠ c2) (h13 : 1 ≠ c3) (h14 : 1 ≠ c4) (h15 : 1 ≠ c5)
    (h23 : c2 ≠ c3) (h24 : c2 ≠ c4) (h25 : c2 ≠ c5)
    (h34 : c3 ≠ c4) (h35 : c3 ≠ c5) (h45 : c4 ≠ c5) :
    ∃ ρ : Relabeling n,
      ρ.toOld 1 = 1 ∧
      ρ.toOld 2 = c2 ∧
      ρ.toOld 3 = c3 ∧
      ρ.toOld 4 = c4 ∧
      ρ.toOld 5 = c5 := by
  have h1D : InDomain n 1 := InDomain.of_le h5D (by omega) (by omega)
  have h2D : InDomain n 2 := InDomain.of_le h5D (by omega) (by omega)
  have h3D : InDomain n 3 := InDomain.of_le h5D (by omega) (by omega)
  have h4D : InDomain n 4 := InDomain.of_le h5D (by omega) (by omega)
  let ρ0 := idRelabeling n
  let ρ2 := ρ0.put 2 c2 h2D hc2
  have hρ2_1 : ρ2.toOld 1 = 1 := by
    simpa [ρ0, ρ2, idRelabeling] using
      Relabeling.put_toOld_of_ne ρ0 h1D h2D hc2 (by omega) h12
  have hρ2_2 : ρ2.toOld 2 = c2 := by
    simpa [ρ2] using Relabeling.put_toOld_self ρ0 h2D hc2
  let ρ3 := ρ2.put 3 c3 h3D hc3
  have hρ3_1 : ρ3.toOld 1 = 1 := by
    have hneq : ρ2.toOld 1 ≠ c3 := by
      rw [hρ2_1]
      exact h13
    calc
      ρ3.toOld 1 = ρ2.toOld 1 := by
        simpa [ρ3] using Relabeling.put_toOld_of_ne ρ2 h1D h3D hc3 (by omega) hneq
      _ = 1 := hρ2_1
  have hρ3_2 : ρ3.toOld 2 = c2 := by
    have hneq : ρ2.toOld 2 ≠ c3 := by
      rw [hρ2_2]
      exact h23
    simpa [ρ3] using Relabeling.put_toOld_of_ne ρ2 h2D h3D hc3 (by omega) hneq
  have hρ3_3 : ρ3.toOld 3 = c3 := by
    simpa [ρ3] using Relabeling.put_toOld_self ρ2 h3D hc3
  let ρ4 := ρ3.put 4 c4 h4D hc4
  have hρ4_1 : ρ4.toOld 1 = 1 := by
    have hneq : ρ3.toOld 1 ≠ c4 := by
      rw [hρ3_1]
      exact h14
    calc
      ρ4.toOld 1 = ρ3.toOld 1 := by
        simpa [ρ4] using Relabeling.put_toOld_of_ne ρ3 h1D h4D hc4 (by omega) hneq
      _ = 1 := hρ3_1
  have hρ4_2 : ρ4.toOld 2 = c2 := by
    have hneq : ρ3.toOld 2 ≠ c4 := by
      rw [hρ3_2]
      exact h24
    calc
      ρ4.toOld 2 = ρ3.toOld 2 := by
        simpa [ρ4] using Relabeling.put_toOld_of_ne ρ3 h2D h4D hc4 (by omega) hneq
      _ = c2 := hρ3_2
  have hρ4_3 : ρ4.toOld 3 = c3 := by
    have hneq : ρ3.toOld 3 ≠ c4 := by
      rw [hρ3_3]
      exact h34
    calc
      ρ4.toOld 3 = ρ3.toOld 3 := by
        simpa [ρ4] using Relabeling.put_toOld_of_ne ρ3 h3D h4D hc4 (by omega) hneq
      _ = c3 := hρ3_3
  have hρ4_4 : ρ4.toOld 4 = c4 := by
    simpa [ρ4] using Relabeling.put_toOld_self ρ3 h4D hc4
  let ρ5 := ρ4.put 5 c5 h5D hc5
  have hρ5_1 : ρ5.toOld 1 = 1 := by
    have hneq : ρ4.toOld 1 ≠ c5 := by
      rw [hρ4_1]
      exact h15
    calc
      ρ5.toOld 1 = ρ4.toOld 1 := by
        simpa [ρ5] using Relabeling.put_toOld_of_ne ρ4 h1D h5D hc5 (by omega) hneq
      _ = 1 := hρ4_1
  have hρ5_2 : ρ5.toOld 2 = c2 := by
    have hneq : ρ4.toOld 2 ≠ c5 := by
      rw [hρ4_2]
      exact h25
    calc
      ρ5.toOld 2 = ρ4.toOld 2 := by
        simpa [ρ5] using Relabeling.put_toOld_of_ne ρ4 h2D h5D hc5 (by omega) hneq
      _ = c2 := hρ4_2
  have hρ5_3 : ρ5.toOld 3 = c3 := by
    have hneq : ρ4.toOld 3 ≠ c5 := by
      rw [hρ4_3]
      exact h35
    calc
      ρ5.toOld 3 = ρ4.toOld 3 := by
        simpa [ρ5] using Relabeling.put_toOld_of_ne ρ4 h3D h5D hc5 (by omega) hneq
      _ = c3 := hρ4_3
  have hρ5_4 : ρ5.toOld 4 = c4 := by
    have hneq : ρ4.toOld 4 ≠ c5 := by
      rw [hρ4_4]
      exact h45
    calc
      ρ5.toOld 4 = ρ4.toOld 4 := by
        simpa [ρ5] using Relabeling.put_toOld_of_ne ρ4 h4D h5D hc5 (by omega) hneq
      _ = c4 := hρ4_4
  have hρ5_5 : ρ5.toOld 5 = c5 := by
    simpa [ρ5] using Relabeling.put_toOld_self ρ4 h5D hc5
  exact ⟨ρ5, hρ5_1, hρ5_2, hρ5_3, hρ5_4, hρ5_5⟩

theorem relabel_closed
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) :
    Closed n (relabelAlgebra ρ A) where
  add_mem hi hj := by
    exact ρ.toNew_mem (C.add_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))
  mul_mem hi hj := by
    exact ρ.toNew_mem (C.mul_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))
  exp_mem hi hj := by
    exact ρ.toNew_mem (C.exp_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))

theorem relabel_toOld_add
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) :
    ρ.toOld ((relabelAlgebra ρ A).add i j) =
      A.add (ρ.toOld i) (ρ.toOld j) := by
  exact ρ.right_inv (C.add_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))

theorem relabel_toOld_mul
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) :
    ρ.toOld ((relabelAlgebra ρ A).mul i j) =
      A.mul (ρ.toOld i) (ρ.toOld j) := by
  exact ρ.right_inv (C.mul_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))

theorem relabel_toOld_exp
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {i j : Nat}
    (hi : InDomain n i) (hj : InDomain n j) :
    ρ.toOld ((relabelAlgebra ρ A).exp i j) =
      A.exp (ρ.toOld i) (ρ.toOld j) := by
  exact ρ.right_inv (C.exp_mem (ρ.toOld_mem hi) (ρ.toOld_mem hj))

theorem relabel_hsi
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (H : HSI n A)
    (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1) :
    HSI n (relabelAlgebra ρ A) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  have htoNew1 : ρ.toNew 1 = 1 := by
    calc
      ρ.toNew 1 = ρ.toNew (ρ.toOld 1) := by rw [htoOld1]
      _ = 1 := ρ.left_inv h1
  refine {
    add_comm := ?add_comm
    add_assoc := ?add_assoc
    mul_one := ?mul_one
    mul_comm := ?mul_comm
    mul_assoc := ?mul_assoc
    distrib := ?distrib
    one_exp := ?one_exp
    exp_one := ?exp_one
    exp_add := ?exp_add
    exp_mul := ?exp_mul
    exp_assoc := ?exp_assoc
  }
  · intro i j hi hj
    apply ρ.eq_of_toOld_eq (CB.add_mem hi hj) (CB.add_mem hj hi)
    calc
      ρ.toOld (B.add i j) = A.add (ρ.toOld i) (ρ.toOld j) :=
        relabel_toOld_add ρ C hi hj
      _ = A.add (ρ.toOld j) (ρ.toOld i) :=
        H.add_comm (ρ.toOld_mem hi) (ρ.toOld_mem hj)
      _ = ρ.toOld (B.add j i) := (relabel_toOld_add ρ C hj hi).symm
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.add_mem hi (CB.add_mem hj hk))
      (CB.add_mem (CB.add_mem hi hj) hk)
    calc
      ρ.toOld (B.add i (B.add j k))
          = A.add (ρ.toOld i) (ρ.toOld (B.add j k)) :=
              relabel_toOld_add ρ C hi (CB.add_mem hj hk)
      _ = A.add (ρ.toOld i) (A.add (ρ.toOld j) (ρ.toOld k)) := by
              rw [relabel_toOld_add ρ C hj hk]
      _ = A.add (A.add (ρ.toOld i) (ρ.toOld j)) (ρ.toOld k) :=
              H.add_assoc (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.add (ρ.toOld (B.add i j)) (ρ.toOld k) := by
              rw [relabel_toOld_add ρ C hi hj]
      _ = ρ.toOld (B.add (B.add i j) k) :=
              (relabel_toOld_add ρ C (CB.add_mem hi hj) hk).symm
  · intro i hi
    apply ρ.eq_of_toOld_eq (CB.mul_mem hi h1) hi
    calc
      ρ.toOld (B.mul i 1) = A.mul (ρ.toOld i) (ρ.toOld 1) :=
        relabel_toOld_mul ρ C hi h1
      _ = A.mul (ρ.toOld i) 1 := by rw [htoOld1]
      _ = ρ.toOld i := H.mul_one (ρ.toOld_mem hi)
  · intro i j hi hj
    apply ρ.eq_of_toOld_eq (CB.mul_mem hi hj) (CB.mul_mem hj hi)
    calc
      ρ.toOld (B.mul i j) = A.mul (ρ.toOld i) (ρ.toOld j) :=
        relabel_toOld_mul ρ C hi hj
      _ = A.mul (ρ.toOld j) (ρ.toOld i) :=
        H.mul_comm (ρ.toOld_mem hi) (ρ.toOld_mem hj)
      _ = ρ.toOld (B.mul j i) := (relabel_toOld_mul ρ C hj hi).symm
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.mul_mem hi (CB.mul_mem hj hk))
      (CB.mul_mem (CB.mul_mem hi hj) hk)
    calc
      ρ.toOld (B.mul i (B.mul j k))
          = A.mul (ρ.toOld i) (ρ.toOld (B.mul j k)) :=
              relabel_toOld_mul ρ C hi (CB.mul_mem hj hk)
      _ = A.mul (ρ.toOld i) (A.mul (ρ.toOld j) (ρ.toOld k)) := by
              rw [relabel_toOld_mul ρ C hj hk]
      _ = A.mul (A.mul (ρ.toOld i) (ρ.toOld j)) (ρ.toOld k) :=
              H.mul_assoc (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.mul (ρ.toOld (B.mul i j)) (ρ.toOld k) := by
              rw [relabel_toOld_mul ρ C hi hj]
      _ = ρ.toOld (B.mul (B.mul i j) k) :=
              (relabel_toOld_mul ρ C (CB.mul_mem hi hj) hk).symm
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.mul_mem hi (CB.add_mem hj hk))
      (CB.add_mem (CB.mul_mem hi hj) (CB.mul_mem hi hk))
    calc
      ρ.toOld (B.mul i (B.add j k))
          = A.mul (ρ.toOld i) (ρ.toOld (B.add j k)) :=
              relabel_toOld_mul ρ C hi (CB.add_mem hj hk)
      _ = A.mul (ρ.toOld i) (A.add (ρ.toOld j) (ρ.toOld k)) := by
              rw [relabel_toOld_add ρ C hj hk]
      _ = A.add (A.mul (ρ.toOld i) (ρ.toOld j))
          (A.mul (ρ.toOld i) (ρ.toOld k)) :=
              H.distrib (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.add (ρ.toOld (B.mul i j)) (ρ.toOld (B.mul i k)) := by
              rw [relabel_toOld_mul ρ C hi hj, relabel_toOld_mul ρ C hi hk]
      _ = ρ.toOld (B.add (B.mul i j) (B.mul i k)) :=
              (relabel_toOld_add ρ C (CB.mul_mem hi hj) (CB.mul_mem hi hk)).symm
  · intro i hi
    apply ρ.eq_of_toOld_eq (CB.exp_mem h1 hi) h1
    calc
      ρ.toOld (B.exp 1 i) = A.exp (ρ.toOld 1) (ρ.toOld i) :=
        relabel_toOld_exp ρ C h1 hi
      _ = A.exp 1 (ρ.toOld i) := by rw [htoOld1]
      _ = 1 := H.one_exp (ρ.toOld_mem hi)
      _ = ρ.toOld 1 := htoOld1.symm
  · intro i hi
    apply ρ.eq_of_toOld_eq (CB.exp_mem hi h1) hi
    calc
      ρ.toOld (B.exp i 1) = A.exp (ρ.toOld i) (ρ.toOld 1) :=
        relabel_toOld_exp ρ C hi h1
      _ = A.exp (ρ.toOld i) 1 := by rw [htoOld1]
      _ = ρ.toOld i := H.exp_one (ρ.toOld_mem hi)
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.exp_mem hi (CB.add_mem hj hk))
      (CB.mul_mem (CB.exp_mem hi hj) (CB.exp_mem hi hk))
    calc
      ρ.toOld (B.exp i (B.add j k))
          = A.exp (ρ.toOld i) (ρ.toOld (B.add j k)) :=
              relabel_toOld_exp ρ C hi (CB.add_mem hj hk)
      _ = A.exp (ρ.toOld i) (A.add (ρ.toOld j) (ρ.toOld k)) := by
              rw [relabel_toOld_add ρ C hj hk]
      _ = A.mul (A.exp (ρ.toOld i) (ρ.toOld j))
          (A.exp (ρ.toOld i) (ρ.toOld k)) :=
              H.exp_add (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.mul (ρ.toOld (B.exp i j)) (ρ.toOld (B.exp i k)) := by
              rw [relabel_toOld_exp ρ C hi hj, relabel_toOld_exp ρ C hi hk]
      _ = ρ.toOld (B.mul (B.exp i j) (B.exp i k)) :=
              (relabel_toOld_mul ρ C (CB.exp_mem hi hj) (CB.exp_mem hi hk)).symm
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.exp_mem (CB.mul_mem hi hj) hk)
      (CB.mul_mem (CB.exp_mem hi hk) (CB.exp_mem hj hk))
    calc
      ρ.toOld (B.exp (B.mul i j) k)
          = A.exp (ρ.toOld (B.mul i j)) (ρ.toOld k) :=
              relabel_toOld_exp ρ C (CB.mul_mem hi hj) hk
      _ = A.exp (A.mul (ρ.toOld i) (ρ.toOld j)) (ρ.toOld k) := by
              rw [relabel_toOld_mul ρ C hi hj]
      _ = A.mul (A.exp (ρ.toOld i) (ρ.toOld k))
          (A.exp (ρ.toOld j) (ρ.toOld k)) :=
              H.exp_mul (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.mul (ρ.toOld (B.exp i k)) (ρ.toOld (B.exp j k)) := by
              rw [relabel_toOld_exp ρ C hi hk, relabel_toOld_exp ρ C hj hk]
      _ = ρ.toOld (B.mul (B.exp i k) (B.exp j k)) :=
              (relabel_toOld_mul ρ C (CB.exp_mem hi hk) (CB.exp_mem hj hk)).symm
  · intro i j k hi hj hk
    apply ρ.eq_of_toOld_eq
      (CB.exp_mem (CB.exp_mem hi hj) hk)
      (CB.exp_mem hi (CB.mul_mem hj hk))
    calc
      ρ.toOld (B.exp (B.exp i j) k)
          = A.exp (ρ.toOld (B.exp i j)) (ρ.toOld k) :=
              relabel_toOld_exp ρ C (CB.exp_mem hi hj) hk
      _ = A.exp (A.exp (ρ.toOld i) (ρ.toOld j)) (ρ.toOld k) := by
              rw [relabel_toOld_exp ρ C hi hj]
      _ = A.exp (ρ.toOld i) (A.mul (ρ.toOld j) (ρ.toOld k)) :=
              H.exp_assoc (ρ.toOld_mem hi) (ρ.toOld_mem hj) (ρ.toOld_mem hk)
      _ = A.exp (ρ.toOld i) (ρ.toOld (B.mul j k)) := by
              rw [relabel_toOld_mul ρ C hj hk]
      _ = ρ.toOld (B.exp i (B.mul j k)) :=
              (relabel_toOld_exp ρ C hi (CB.mul_mem hj hk)).symm

theorem relabel_toOld_x2
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {z : Nat} (hz : InDomain n z) :
    ρ.toOld (x2 (relabelAlgebra ρ A) z) = x2 A (ρ.toOld z) := by
  unfold x2
  exact relabel_toOld_mul ρ C hz hz

theorem relabel_toOld_x3
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {z : Nat} (hz : InDomain n z) :
    ρ.toOld (x3 (relabelAlgebra ρ A) z) = x3 A (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  unfold x3
  calc
    ρ.toOld (B.mul (x2 B z) z)
        = A.mul (ρ.toOld (x2 B z)) (ρ.toOld z) :=
            relabel_toOld_mul ρ C (CB.mul_mem hz hz) hz
    _ = A.mul (x2 A (ρ.toOld z)) (ρ.toOld z) := by
            rw [relabel_toOld_x2 ρ C hz]

theorem relabel_toOld_x4
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) {z : Nat} (hz : InDomain n z) :
    ρ.toOld (x4 (relabelAlgebra ρ A) z) = x4 A (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  unfold x4
  calc
    ρ.toOld (B.mul (x3 B z) z)
        = A.mul (ρ.toOld (x3 B z)) (ρ.toOld z) :=
            relabel_toOld_mul ρ C (CB.mul_mem (CB.mul_mem hz hz) hz) hz
    _ = A.mul (x3 A (ρ.toOld z)) (ρ.toOld z) := by
            rw [relabel_toOld_x3 ρ C hz]

theorem relabel_toOld_Pterm
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1)
    {z : Nat} (hz : InDomain n z) :
    ρ.toOld (Pterm (relabelAlgebra ρ A) z) = Pterm A (ρ.toOld z) := by
  unfold Pterm
  calc
    ρ.toOld ((relabelAlgebra ρ A).add 1 z)
        = A.add (ρ.toOld 1) (ρ.toOld z) := relabel_toOld_add ρ C h1 hz
    _ = A.add 1 (ρ.toOld z) := by rw [htoOld1]

theorem relabel_toOld_Qterm
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1)
    {z : Nat} (hz : InDomain n z) :
    ρ.toOld (Qterm (relabelAlgebra ρ A) z) = Qterm A (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  have hP : InDomain n (Pterm B z) := by
    unfold Pterm
    exact CB.add_mem h1 hz
  have hx2B : InDomain n (x2 B z) := by
    unfold x2
    exact CB.mul_mem hz hz
  unfold Qterm
  calc
    ρ.toOld (B.add (Pterm B z) (x2 B z))
        = A.add (ρ.toOld (Pterm B z)) (ρ.toOld (x2 B z)) :=
            relabel_toOld_add ρ C hP hx2B
    _ = A.add (Pterm A (ρ.toOld z)) (x2 A (ρ.toOld z)) := by
            rw [relabel_toOld_Pterm ρ C h1 htoOld1 hz, relabel_toOld_x2 ρ C hz]

theorem relabel_toOld_Rterm
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1)
    {z : Nat} (hz : InDomain n z) :
    ρ.toOld (Rterm (relabelAlgebra ρ A) z) = Rterm A (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  have hx3B : InDomain n (x3 B z) := by
    unfold x3 x2
    exact CB.mul_mem (CB.mul_mem hz hz) hz
  unfold Rterm
  calc
    ρ.toOld (B.add 1 (x3 B z))
        = A.add (ρ.toOld 1) (ρ.toOld (x3 B z)) :=
            relabel_toOld_add ρ C h1 hx3B
    _ = A.add 1 (x3 A (ρ.toOld z)) := by
            rw [htoOld1, relabel_toOld_x3 ρ C hz]

theorem relabel_toOld_Sterm
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1)
    {z : Nat} (hz : InDomain n z) :
    ρ.toOld (Sterm (relabelAlgebra ρ A) z) = Sterm A (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  have hx2B : InDomain n (x2 B z) := by
    unfold x2
    exact CB.mul_mem hz hz
  have hone_x2B : InDomain n (B.add 1 (x2 B z)) := CB.add_mem h1 hx2B
  have hx3B : InDomain n (x3 B z) := by
    unfold x3 x2
    exact CB.mul_mem (CB.mul_mem hz hz) hz
  have hx4B : InDomain n (x4 B z) := by
    unfold x4
    exact CB.mul_mem hx3B hz
  unfold Sterm
  calc
    ρ.toOld (B.add (B.add 1 (x2 B z)) (x4 B z))
        = A.add (ρ.toOld (B.add 1 (x2 B z))) (ρ.toOld (x4 B z)) :=
            relabel_toOld_add ρ C hone_x2B hx4B
    _ = A.add (A.add (ρ.toOld 1) (ρ.toOld (x2 B z))) (ρ.toOld (x4 B z)) := by
            rw [relabel_toOld_add ρ C h1 hx2B]
    _ = A.add (A.add 1 (x2 A (ρ.toOld z))) (x4 A (ρ.toOld z)) := by
            rw [htoOld1, relabel_toOld_x2 ρ C hz, relabel_toOld_x4 ρ C hz]

theorem relabel_toOld_wilkieCore
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A)
    {p q r s x y : Nat}
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x) (hy : InDomain n y) :
    ρ.toOld (wilkieCore (relabelAlgebra ρ A) p q r s x y) =
      wilkieCore A (ρ.toOld p) (ρ.toOld q) (ρ.toOld r) (ρ.toOld s)
        (ρ.toOld x) (ρ.toOld y) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  have hpy : InDomain n (B.exp p y) := CB.exp_mem hp hy
  have hqy : InDomain n (B.exp q y) := CB.exp_mem hq hy
  have hrx : InDomain n (B.exp r x) := CB.exp_mem hr hx
  have hsx : InDomain n (B.exp s x) := CB.exp_mem hs hx
  have hsumPQ : InDomain n (B.add (B.exp p y) (B.exp q y)) := CB.add_mem hpy hqy
  have hsumRS : InDomain n (B.add (B.exp r x) (B.exp s x)) := CB.add_mem hrx hsx
  have hleft : InDomain n (B.exp (B.add (B.exp p y) (B.exp q y)) x) :=
    CB.exp_mem hsumPQ hx
  have hright : InDomain n (B.exp (B.add (B.exp r x) (B.exp s x)) y) :=
    CB.exp_mem hsumRS hy
  unfold wilkieCore
  rw [relabel_toOld_mul ρ C hleft hright]
  rw [relabel_toOld_exp ρ C hsumPQ hx]
  rw [relabel_toOld_exp ρ C hsumRS hy]
  rw [relabel_toOld_add ρ C hpy hqy]
  rw [relabel_toOld_add ρ C hrx hsx]
  rw [relabel_toOld_exp ρ C hp hy]
  rw [relabel_toOld_exp ρ C hq hy]
  rw [relabel_toOld_exp ρ C hr hx]
  rw [relabel_toOld_exp ρ C hs hx]

theorem relabel_toOld_wilkieP
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    (C : Closed n A) (h1 : InDomain n 1) (htoOld1 : ρ.toOld 1 = 1)
    {x y z : Nat} (hx : InDomain n x) (hy : InDomain n y) (hz : InDomain n z) :
    ρ.toOld (wilkieP (relabelAlgebra ρ A) x y z) =
      wilkieP A (ρ.toOld x) (ρ.toOld y) (ρ.toOld z) := by
  let B := relabelAlgebra ρ A
  have CB : Closed n B := relabel_closed ρ C
  rcases pqrs_terms_mem_of_closed CB h1 hz with ⟨hPB, hQB, hRB, hSB⟩
  have hcore :=
    relabel_toOld_wilkieCore ρ C hPB hQB hRB hSB hx hy
  rw [relabel_toOld_Pterm ρ C h1 htoOld1 hz] at hcore
  rw [relabel_toOld_Qterm ρ C h1 htoOld1 hz] at hcore
  rw [relabel_toOld_Rterm ρ C h1 htoOld1 hz] at hcore
  rw [relabel_toOld_Sterm ρ C h1 htoOld1 hz] at hcore
  simpa [wilkieP, wilkieCore, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem normalizedCountermodel_of_relabeling
    {n : Nat} {A : Algebra} (ρ : Relabeling n)
    {x y : Nat}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    (hFail : WilkieFailsAt A x y x)
    (htoOld1 : ρ.toOld 1 = 1)
    (htoOld2 : ρ.toOld 2 = A.add 1 1)
    (htoOld3 : ρ.toOld 3 = A.add (A.add 1 1) 1)
    (htoOld4 : ρ.toOld 4 = x)
    (htoOld5 : ρ.toOld 5 = y) :
    NormalizedCountermodel n (relabelAlgebra ρ A) := by
  let B := relabelAlgebra ρ A
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h3 : InDomain n 3 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have CB : Closed n B := relabel_closed ρ C
  refine {
    closed := CB
    hsi := relabel_hsi ρ C H h1 htoOld1
    wilkie_fails := ?wilkie_fails
    add_one_one := ?add_one_one
    add_two_one := ?add_two_one
  }
  · intro hEq
    have hOldEq := congrArg ρ.toOld hEq
    rw [relabel_toOld_wilkieP ρ C h1 htoOld1 h4 h5 h4] at hOldEq
    rw [relabel_toOld_wilkieP ρ C h1 htoOld1 h5 h4 h4] at hOldEq
    rw [htoOld4, htoOld5] at hOldEq
    exact hFail hOldEq
  · apply ρ.eq_of_toOld_eq (CB.add_mem h1 h1) h2
    calc
      ρ.toOld (B.add 1 1) = A.add (ρ.toOld 1) (ρ.toOld 1) :=
        relabel_toOld_add ρ C h1 h1
      _ = A.add 1 1 := by rw [htoOld1]
      _ = ρ.toOld 2 := htoOld2.symm
  · apply ρ.eq_of_toOld_eq (CB.add_mem h2 h1) h3
    calc
      ρ.toOld (B.add 2 1) = A.add (ρ.toOld 2) (ρ.toOld 1) :=
        relabel_toOld_add ρ C h2 h1
      _ = A.add (A.add 1 1) 1 := by rw [htoOld2, htoOld1]
      _ = ρ.toOld 3 := htoOld3.symm

theorem lee_q_eq_p_mul_yields_wilkie_at
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y v : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (hv : InDomain n v)
    (hdiv : A.mul (Pterm A x) v = Qterm A x) :
    wilkieP A x y x = wilkieP A y x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 hx
  have hcore := lee_divisibility_hsi C H h1 hP hQ hR hS hv hx hy
    hdiv.symm hfactor
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hcore

theorem lee_p_eq_q_mul_yields_wilkie_at
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y v : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (hv : InDomain n v)
    (hdiv : A.mul (Qterm A x) v = Pterm A x) :
    wilkieP A x y x = wilkieP A y x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 hx
  have hcore := lee_divisibility_hsi C H h1 hQ hP hS hR hv hx hy
    hdiv.symm hfactor.symm
  have hleft := wilkieCore_swap_pairs_hsi C H hP hQ hR hS hx hy
  have hright := wilkieCore_swap_pairs_hsi C H hP hQ hR hS hy hx
  have hmain :
      wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) x y =
        wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) y x := by
    calc
      wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) x y
          = wilkieCore A (Qterm A x) (Pterm A x) (Sterm A x) (Rterm A x) x y := hleft.symm
      _ = wilkieCore A (Qterm A x) (Pterm A x) (Sterm A x) (Rterm A x) y x := hcore
      _ = wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) y x := hright
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem lee_s_eq_r_mul_yields_wilkie_at
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y v : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (hv : InDomain n v)
    (hdiv : A.mul (Rterm A x) v = Sterm A x) :
    wilkieP A x y x = wilkieP A y x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, hR, hS⟩
  have hfactor0 := wilkie_factor_hsi C H h1 hx
  have hfactor : A.mul (Rterm A x) (Qterm A x) = A.mul (Sterm A x) (Pterm A x) := by
    calc
      A.mul (Rterm A x) (Qterm A x) = A.mul (Qterm A x) (Rterm A x) := H.mul_comm hR hQ
      _ = A.mul (Pterm A x) (Sterm A x) := hfactor0.symm
      _ = A.mul (Sterm A x) (Pterm A x) := H.mul_comm hP hS
  have hcore := lee_divisibility_hsi C H h1 hR hS hP hQ hv hx hy
    hdiv.symm hfactor
  have hxex := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS hx hy
  have hyex := wilkieCore_exchange_pairs_hsi C H hP hQ hR hS hy hx
  have hmain :
      wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) x y =
        wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) y x := by
    calc
      wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) x y
          = wilkieCore A (Rterm A x) (Sterm A x) (Pterm A x) (Qterm A x) y x := hyex.symm
      _ = wilkieCore A (Rterm A x) (Sterm A x) (Pterm A x) (Qterm A x) x y := hcore.symm
      _ = wilkieCore A (Pterm A x) (Qterm A x) (Rterm A x) (Sterm A x) y x := hxex
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem wilkie_holds_of_two_eq_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (h : A.add 1 1 = 1) :
    wilkieP A x y x = wilkieP A y x x := by
  have hx2eq : A.mul x x = x := by
    calc
      A.mul x x = A.mul (A.exp x 1) (A.exp x 1) := by rw [H.exp_one hx]
      _ = A.exp x (A.add 1 1) := (H.exp_add hx h1 h1).symm
      _ = A.exp x 1 := by rw [h]
      _ = x := H.exp_one hx
  have hxx : A.add x x = x := by
    calc
      A.add x x = A.add (A.mul x 1) (A.mul x 1) := by rw [H.mul_one hx]
      _ = A.mul x (A.add 1 1) := (H.distrib hx h1 h1).symm
      _ = A.mul x 1 := by rw [h]
      _ = x := H.mul_one hx
  have hQP : Qterm A x = Pterm A x := by
    calc
      Qterm A x = A.add (Pterm A x) (x2 A x) := rfl
      _ = A.add (A.add 1 x) x := by rw [Pterm, x2, hx2eq]
      _ = A.add 1 (A.add x x) := (H.add_assoc h1 hx hx).symm
      _ = A.add 1 x := by rw [hxx]
      _ = Pterm A x := rfl
  have hP : InDomain n (Pterm A x) := by
    unfold Pterm
    exact C.add_mem h1 hx
  have hdiv : A.mul (Pterm A x) 1 = Qterm A x := by
    calc
      A.mul (Pterm A x) 1 = Pterm A x := H.mul_one hP
      _ = Qterm A x := hQP.symm
  exact lee_q_eq_p_mul_yields_wilkie_at C H h1 hx hy h1 hdiv

theorem triple_add_eq_two_of_three_eq_two_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {z : Nat} (h1 : InDomain n 1) (hz : InDomain n z)
    (h3 : A.add (A.add 1 1) 1 = A.add 1 1) :
    A.add (A.add z z) z = A.add z z := by
  have h2 : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have h3D : InDomain n (A.add (A.add 1 1) 1) := C.add_mem h2 h1
  have hleft : A.mul (A.add (A.add 1 1) 1) z = A.add (A.add z z) z := by
    calc
      A.mul (A.add (A.add 1 1) 1) z
          = A.mul z (A.add (A.add 1 1) 1) := H.mul_comm h3D hz
      _ = A.add (A.mul z (A.add 1 1)) (A.mul z 1) := H.distrib hz h2 h1
      _ = A.add (A.add (A.mul z 1) (A.mul z 1)) (A.mul z 1) := by
            rw [H.distrib hz h1 h1]
      _ = A.add (A.add z z) z := by rw [H.mul_one hz]
  have hright : A.mul (A.add 1 1) z = A.add z z := by
    calc
      A.mul (A.add 1 1) z = A.mul z (A.add 1 1) := H.mul_comm h2 hz
      _ = A.add (A.mul z 1) (A.mul z 1) := H.distrib hz h1 h1
      _ = A.add z z := by rw [H.mul_one hz]
  calc
    A.add (A.add z z) z = A.mul (A.add (A.add 1 1) 1) z := hleft.symm
    _ = A.mul (A.add 1 1) z := by rw [h3]
    _ = A.add z z := hright

theorem x3_eq_x2_of_three_eq_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = A.add 1 1) :
    x3 A x = x2 A x := by
  have h2 : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hExp2 : A.exp x (A.add 1 1) = x2 A x := by
    calc
      A.exp x (A.add 1 1) = A.mul (A.exp x 1) (A.exp x 1) :=
        H.exp_add hx h1 h1
      _ = x2 A x := by
        rw [H.exp_one hx]
        rfl
  have hExp3 : A.exp x (A.add (A.add 1 1) 1) = x3 A x := by
    calc
      A.exp x (A.add (A.add 1 1) 1) =
          A.mul (A.exp x (A.add 1 1)) (A.exp x 1) :=
            H.exp_add hx h2 h1
      _ = x3 A x := by
        rw [hExp2, H.exp_one hx]
        rfl
  calc
    x3 A x = A.exp x (A.add (A.add 1 1) 1) := hExp3.symm
    _ = A.exp x (A.add 1 1) := by rw [h3]
    _ = x2 A x := hExp2

theorem x4_eq_x2_of_three_eq_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = A.add 1 1) :
    x4 A x = x2 A x := by
  have hx3eq := x3_eq_x2_of_three_eq_two C H h1 hx h3
  calc
    x4 A x = A.mul (x3 A x) x := by rfl
    _ = A.mul (x2 A x) x := by rw [hx3eq]
    _ = x3 A x := by rfl
    _ = x2 A x := hx3eq

theorem rr_eq_s_of_three_eq_two_generic
    {α : Type} (add mul : α → α → α) (one x2 x3 x4 : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (hx3 : x3 = x2) (hx4 : x4 = x2)
    (hsq : mul x2 x2 = x4)
    (htriple : add (add x2 x2) x2 = add x2 x2) :
    mul (add one x3) (add one x3) = add (add one x2) x4 := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  subst x3
  calc
    mul (add one x2) (add one x2)
        = add (mul one (add one x2)) (mul x2 (add one x2)) := by
          rw [distrib_left]
    _ = add (add one x2) (add (mul x2 one) (mul x2 x2)) := by
          rw [one_mul, distrib]
    _ = add (add one x2) (add x2 x4) := by rw [mul_one, hsq]
    _ = add one (add (add x2 x2) x4) := by ac_rfl
    _ = add one (add (add x2 x2) x2) := by rw [hx4]
    _ = add one (add x2 x2) := by rw [htriple]
    _ = add (add one x2) x4 := by
          rw [hx4]
          ac_rfl

theorem rr_eq_s_of_three_eq_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = A.add 1 1) :
    A.mul (Rterm A x) (Rterm A x) = Sterm A x := by
  have hx2 : InDomain n (x2 A x) := by
    unfold x2
    exact C.mul_mem hx hx
  have hx3D : InDomain n (x3 A x) := by
    unfold x3
    exact C.mul_mem hx2 hx
  have hx4D : InDomain n (x4 A x) := by
    unfold x4
    exact C.mul_mem hx3D hx
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let x2D : D := ⟨x2 A x, hx2⟩
  let x3D : D := ⟨x3 A x, hx3D⟩
  let x4D : D := ⟨x4 A x, hx4D⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hx3eq := x3_eq_x2_of_three_eq_two C H h1 hx h3
  have hx4eq := x4_eq_x2_of_three_eq_two C H h1 hx h3
  have hsq : A.mul (x2 A x) (x2 A x) = x4 A x := by
    unfold x2 x4 x3
    exact H.mul_assoc (C.mul_mem hx hx) hx hx
  have htriple :=
    triple_add_eq_two_of_three_eq_two_hsi C H h1 hx2 h3
  have hD := rr_eq_s_of_three_eq_two_generic
    (add := addD) (mul := mulD) (one := oneD)
    (x2 := x2D) (x3 := x3D) (x4 := x4D)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact hx3eq)
    (by
      apply Subtype.ext
      exact hx4eq)
    (by
      apply Subtype.ext
      exact hsq)
    (by
      apply Subtype.ext
      exact htriple)
  simpa [Rterm, Sterm, addD, mulD, oneD, x2D, x3D, x4D]
    using congrArg Subtype.val hD

theorem wilkie_holds_of_three_eq_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (h3 : A.add (A.add 1 1) 1 = A.add 1 1) :
    wilkieP A x y x = wilkieP A y x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨_hP, _hQ, hR, _hS⟩
  exact lee_s_eq_r_mul_yields_wilkie_at C H h1 hx hy hR
    (rr_eq_s_of_three_eq_two C H h1 hx h3)

theorem pq_eq_p_of_p_alt_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (hx3 : mul (mul x x) x = x)
    (htriple_x : add (add x x) x = x)
    (hPalt : add one x = add one (add (add x x) (mul x x))) :
    mul (add one x) (add (add one x) (mul x x)) = add one x := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  calc
    mul (add one x) (add (add one x) (mul x x))
        = add (mul one (add (add one x) (mul x x)))
            (mul x (add (add one x) (mul x x))) := by
          rw [distrib_left]
    _ = add (add (add one x) (mul x x))
        (add (mul x (add one x)) (mul x (mul x x))) := by
          rw [one_mul, distrib]
    _ = add (add (add one x) (mul x x))
        (add (add (mul x one) (mul x x)) (mul x (mul x x))) := by
          rw [distrib]
    _ = add (add (add one x) (mul x x))
        (add (add x (mul x x)) (mul (mul x x) x)) := by
          rw [mul_one]
          ac_rfl
    _ = add (add (add one x) (mul x x))
        (add (add x (mul x x)) x) := by rw [hx3]
    _ = add one (add (add (add x x) x) (add (mul x x) (mul x x))) := by
          ac_rfl
    _ = add one (add x (add (mul x x) (mul x x))) := by rw [htriple_x]
    _ = add one (add (add (add x x) x) (add (mul x x) (mul x x))) := by
          exact congrArg (fun z => add one (add z (add (mul x x) (mul x x)))) htriple_x.symm
    _ = add (add one (add (add x x) (mul x x))) (add x (mul x x)) := by
          ac_rfl
    _ = add (add one x) (add x (mul x x)) := by rw [← hPalt]
    _ = add one (add (add x x) (mul x x)) := by ac_rfl
    _ = add one x := hPalt.symm

theorem p_cube_expansion_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a) :
    mul (mul (add one x) (add one x)) (add one x) =
      add one
        (add (add (add x x) x)
          (add (add (add (mul x x) (mul x x)) (mul x x)) (mul (mul x x) x))) := by
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  rw [distrib_left]
  repeat rw [distrib]
  repeat rw [distrib_left]
  repeat rw [mul_one]
  repeat rw [one_mul]
  ac_rfl

theorem p_alt_of_three_eq_one_generic
    {α : Type} (add mul : α → α → α) (one x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (hcube : mul (mul (add one x) (add one x)) (add one x) = add one x)
    (hx3 : mul (mul x x) x = x)
    (htriple_x : add (add x x) x = x)
    (htriple_x2 : add (add (mul x x) (mul x x)) (mul x x) = mul x x) :
    add one x = add one (add (add x x) (mul x x)) := by
  have hcube_expand :=
    p_cube_expansion_generic (add := add) (mul := mul) (one := one) (x := x)
      (distrib := distrib) (mul_one := mul_one)
  calc
    add one x = mul (mul (add one x) (add one x)) (add one x) := hcube.symm
    _ = add one
        (add (add (add x x) x)
          (add (add (add (mul x x) (mul x x)) (mul x x)) (mul (mul x x) x))) := hcube_expand
    _ = add one
        (add (add x x) (mul x x)) := by
          rw [htriple_x, htriple_x2, hx3]
          ac_rfl

theorem triple_add_eq_self_of_three_eq_one_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {z : Nat} (h1 : InDomain n 1) (hz : InDomain n z)
    (h3 : A.add (A.add 1 1) 1 = 1) :
    A.add (A.add z z) z = z := by
  have h2 : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have h3D : InDomain n (A.add (A.add 1 1) 1) := C.add_mem h2 h1
  have hleft : A.mul (A.add (A.add 1 1) 1) z = A.add (A.add z z) z := by
    calc
      A.mul (A.add (A.add 1 1) 1) z
          = A.mul z (A.add (A.add 1 1) 1) := H.mul_comm h3D hz
      _ = A.add (A.mul z (A.add 1 1)) (A.mul z 1) := H.distrib hz h2 h1
      _ = A.add (A.add (A.mul z 1) (A.mul z 1)) (A.mul z 1) := by
            rw [H.distrib hz h1 h1]
      _ = A.add (A.add z z) z := by rw [H.mul_one hz]
  calc
    A.add (A.add z z) z = A.mul (A.add (A.add 1 1) 1) z := hleft.symm
    _ = A.mul 1 z := by rw [h3]
    _ = A.mul z 1 := H.mul_comm h1 hz
    _ = z := H.mul_one hz

theorem x3_eq_self_of_three_eq_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = 1) :
    x3 A x = x := by
  have h2 : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hExp2 : A.exp x (A.add 1 1) = x2 A x := by
    calc
      A.exp x (A.add 1 1) = A.mul (A.exp x 1) (A.exp x 1) :=
        H.exp_add hx h1 h1
      _ = x2 A x := by
        rw [H.exp_one hx]
        rfl
  have hExp3 : A.exp x (A.add (A.add 1 1) 1) = x3 A x := by
    calc
      A.exp x (A.add (A.add 1 1) 1) =
          A.mul (A.exp x (A.add 1 1)) (A.exp x 1) :=
            H.exp_add hx h2 h1
      _ = x3 A x := by
        rw [hExp2, H.exp_one hx]
        rfl
  calc
    x3 A x = A.exp x (A.add (A.add 1 1) 1) := hExp3.symm
    _ = A.exp x 1 := by rw [h3]
    _ = x := H.exp_one hx

theorem p_alt_of_three_eq_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = 1) :
    Pterm A x = A.add 1 (A.add (A.add x x) (x2 A x)) := by
  have hP : InDomain n (Pterm A x) := by
    unfold Pterm
    exact C.add_mem h1 hx
  have h2 : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have hcube : A.mul (A.mul (Pterm A x) (Pterm A x)) (Pterm A x) = Pterm A x := by
    have hExp2 : A.exp (Pterm A x) (A.add 1 1) =
        A.mul (Pterm A x) (Pterm A x) := by
      calc
        A.exp (Pterm A x) (A.add 1 1) =
            A.mul (A.exp (Pterm A x) 1) (A.exp (Pterm A x) 1) :=
              H.exp_add hP h1 h1
        _ = A.mul (Pterm A x) (Pterm A x) := by rw [H.exp_one hP]
    have hExp3 : A.exp (Pterm A x) (A.add (A.add 1 1) 1) =
        A.mul (A.mul (Pterm A x) (Pterm A x)) (Pterm A x) := by
      calc
        A.exp (Pterm A x) (A.add (A.add 1 1) 1) =
            A.mul (A.exp (Pterm A x) (A.add 1 1)) (A.exp (Pterm A x) 1) :=
              H.exp_add hP h2 h1
        _ = A.mul (A.mul (Pterm A x) (Pterm A x)) (Pterm A x) := by
              rw [hExp2, H.exp_one hP]
    calc
      A.mul (A.mul (Pterm A x) (Pterm A x)) (Pterm A x) =
          A.exp (Pterm A x) (A.add (A.add 1 1) 1) := hExp3.symm
      _ = A.exp (Pterm A x) 1 := by rw [h3]
      _ = Pterm A x := H.exp_one hP
  have hx2 : InDomain n (x2 A x) := by
    unfold x2
    exact C.mul_mem hx hx
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨x, hx⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := p_alt_of_three_eq_one_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      exact hcube)
    (by
      apply Subtype.ext
      exact x3_eq_self_of_three_eq_one C H h1 hx h3)
    (by
      apply Subtype.ext
      exact triple_add_eq_self_of_three_eq_one_hsi C H h1 hx h3)
    (by
      apply Subtype.ext
      exact triple_add_eq_self_of_three_eq_one_hsi C H h1 hx2 h3)
  simpa [Pterm, x2, addD, mulD, oneD, xD] using congrArg Subtype.val hD

theorem pq_eq_p_of_three_eq_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x)
    (h3 : A.add (A.add 1 1) 1 = 1) :
    A.mul (Pterm A x) (Qterm A x) = Pterm A x := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let xD : D := ⟨x, hx⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := pq_eq_p_of_p_alt_generic
    (add := addD) (mul := mulD) (one := oneD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (by
      apply Subtype.ext
      simpa [x3, x2] using x3_eq_self_of_three_eq_one C H h1 hx h3)
    (by
      apply Subtype.ext
      exact triple_add_eq_self_of_three_eq_one_hsi C H h1 hx h3)
    (by
      apply Subtype.ext
      simpa [Pterm, x2] using p_alt_of_three_eq_one C H h1 hx h3)
  simpa [Pterm, Qterm, x2, addD, mulD, oneD, xD] using congrArg Subtype.val hD

theorem wilkie_holds_of_three_eq_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y : Nat}
    (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (h3 : A.add (A.add 1 1) 1 = 1) :
    wilkieP A x y x = wilkieP A y x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, _hR, _hS⟩
  have hpq : A.mul (Pterm A x) (Qterm A x) = Pterm A x :=
    pq_eq_p_of_three_eq_one C H h1 hx h3
  have hqp : A.mul (Qterm A x) (Pterm A x) = Pterm A x := by
    calc
      A.mul (Qterm A x) (Pterm A x) = A.mul (Pterm A x) (Qterm A x) :=
        H.mul_comm hQ hP
      _ = Pterm A x := hpq
  exact lee_p_eq_q_mul_yields_wilkie_at C H h1 hx hy hP hqp

theorem wilkieCore_right_one_generic
    {α : Type} (add mul exp : α → α → α) (one p q r s x : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (exp_one : ∀ a, exp a one = a)
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (hfactor : mul p s = mul q r) :
    mul (exp (add (exp p one) (exp q one)) x)
      (exp (add (exp r x) (exp s x)) one) =
    mul (exp (add (exp p x) (exp q x)) one)
      (exp (add (exp r one) (exp s one)) x) := by
  have distrib_left := distrib_left_generic add mul distrib
  have hpr : mul p (add r s) = mul r (add p q) := by
    calc
      mul p (add r s) = add (mul p r) (mul p s) := distrib p r s
      _ = add (mul p r) (mul q r) := by rw [hfactor]
      _ = mul r (add p q) := by
        rw [distrib]
        ac_rfl
  have hqs : mul q (add r s) = mul s (add p q) := by
    calc
      mul q (add r s) = add (mul q r) (mul q s) := distrib q r s
      _ = add (mul p s) (mul q s) := by rw [← hfactor]
      _ = mul s (add p q) := by
        rw [distrib]
        ac_rfl
  have hpbal :
      mul (exp p x) (exp (add r s) x) =
        mul (exp r x) (exp (add p q) x) := by
    calc
      mul (exp p x) (exp (add r s) x) =
          exp (mul p (add r s)) x := (exp_mul p (add r s) x).symm
      _ = exp (mul r (add p q)) x := by rw [hpr]
      _ = mul (exp r x) (exp (add p q) x) := exp_mul r (add p q) x
  have hqbal :
      mul (exp q x) (exp (add r s) x) =
        mul (exp s x) (exp (add p q) x) := by
    calc
      mul (exp q x) (exp (add r s) x) =
          exp (mul q (add r s)) x := (exp_mul q (add r s) x).symm
      _ = exp (mul s (add p q)) x := by rw [hqs]
      _ = mul (exp s x) (exp (add p q) x) := exp_mul s (add p q) x
  calc
    mul (exp (add (exp p one) (exp q one)) x)
        (exp (add (exp r x) (exp s x)) one)
        = mul (exp (add p q) x) (add (exp r x) (exp s x)) := by
          rw [exp_one p, exp_one q, exp_one]
    _ = add (mul (exp r x) (exp (add p q) x))
        (mul (exp s x) (exp (add p q) x)) := by
          rw [distrib]
          ac_rfl
    _ = add (mul (exp p x) (exp (add r s) x))
        (mul (exp q x) (exp (add r s) x)) := by
          rw [hpbal, hqbal]
    _ = mul (add (exp p x) (exp q x)) (exp (add r s) x) := by
          rw [distrib_left]
    _ = mul (exp (add (exp p x) (exp q x)) one)
        (exp (add (exp r one) (exp s one)) x) := by
          rw [exp_one, exp_one r, exp_one s]

theorem wilkie_holds_left_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {y : Nat} (h1 : InDomain n 1) (hy : InDomain n y) :
    wilkieP A 1 y 1 = wilkieP A y 1 1 := by
  rcases pqrs_terms_mem_of_closed C h1 h1 with ⟨hP, hQ, _hR, _hS⟩
  have hx2eq : x2 A 1 = 1 := by
    unfold x2
    exact H.mul_one h1
  have hx3eq : x3 A 1 = 1 := by
    unfold x3
    rw [hx2eq, H.mul_one h1]
  have hx4eq : x4 A 1 = 1 := by
    unfold x4
    rw [hx3eq, H.mul_one h1]
  have hR : Rterm A 1 = Pterm A 1 := by
    simp [Rterm, Pterm, hx3eq]
  have hS : Sterm A 1 = Qterm A 1 := by
    simp [Sterm, Qterm, Pterm, hx2eq, hx4eq]
  have hcore := wilkieCore_exchange_pairs_hsi C H hP hQ hP hQ h1 hy
  have hmain :
      wilkieCore A (Pterm A 1) (Qterm A 1) (Rterm A 1) (Sterm A 1) 1 y =
        wilkieCore A (Pterm A 1) (Qterm A 1) (Rterm A 1) (Sterm A 1) y 1 := by
    rw [hR, hS]
    exact hcore
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4] using hmain

theorem wilkie_holds_right_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) :
    wilkieP A x 1 x = wilkieP A 1 x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, hR, hS⟩
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let pD : D := ⟨Pterm A x, hP⟩
  let qD : D := ⟨Qterm A x, hQ⟩
  let rD : D := ⟨Rterm A x, hR⟩
  let sD : D := ⟨Sterm A x, hS⟩
  let xD : D := ⟨x, hx⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := wilkieCore_right_one_generic
    (add := addD) (mul := mulD) (exp := expD) (one := oneD)
    (p := pD) (q := qD) (r := rD) (s := sD) (x := xD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (exp_one := by
      intro a
      apply Subtype.ext
      exact H.exp_one a.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (hfactor := by
      apply Subtype.ext
      exact wilkie_factor_hsi C H h1 hx)
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4,
    addD, mulD, expD, oneD, pD, qD, rD, sD, xD]
    using congrArg Subtype.val hD

theorem left_two_factor_reductions_generic
    {α : Type} (add mul : α → α → α) (one : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a) :
    let two := add one one
    let x2 := mul two two
    let x3 := mul x2 two
    let x4 := mul x3 two
    let p := add one two
    let q := add p x2
    let r := add one x3
    let s := add (add one x2) x4
    r = mul p p ∧ s = mul p q := by
  intro two x2 x3 x4 p q r s
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  constructor
  · dsimp [r, p, x3, x2, two]
    rw [distrib_left]
    repeat rw [distrib]
    repeat rw [distrib_left]
    repeat rw [mul_one]
    repeat rw [one_mul]
    ac_rfl
  · dsimp [s, q, p, x4, x3, x2, two]
    rw [distrib_left]
    repeat rw [distrib]
    repeat rw [distrib_left]
    repeat rw [mul_one]
    repeat rw [one_mul]
    ac_rfl

theorem left_three_factor_reductions_generic
    {α : Type} (add mul : α → α → α) (one : α)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a) :
    let two := add one one
    let three := add two one
    let m := add (add one two) (mul two two)
    let x2 := mul three three
    let x3 := mul x2 three
    let x4 := mul x3 three
    let p := add one three
    let q := add p x2
    let r := add one x3
    let s := add (add one x2) x4
    r = mul m p ∧ s = mul m q := by
  intro two three m x2 x3 x4 p q r s
  have distrib_left := distrib_left_generic add mul distrib
  have one_mul := one_mul_generic mul one mul_one
  constructor
  · dsimp [r, m, p, x3, x2, three, two]
    repeat rw [distrib]
    repeat rw [distrib_left]
    repeat rw [mul_one]
    repeat rw [one_mul]
    ac_rfl
  · dsimp [s, m, q, p, x4, x3, x2, three, two]
    repeat rw [distrib]
    repeat rw [distrib_left]
    repeat rw [mul_one]
    repeat rw [one_mul]
    ac_rfl

theorem wilkieCore_right_posCoeff_generic
    {α : Type} (add mul exp : α → α → α) (one : α) (k : Nat)
    [Std.Associative add] [Std.Commutative add]
    [Std.Associative mul] [Std.Commutative mul]
    (distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mul_one : ∀ a, mul a one = a)
    (exp_add : ∀ a b c, exp a (add b c) = mul (exp a b) (exp a c))
    (exp_mul : ∀ a b c, exp (mul a b) c = mul (exp a c) (exp b c))
    (exp_one : ∀ a, exp a one = a)
    {p q r s x : α}
    (hfactor : mul p s = mul q r) :
    let z := posCoeff add one k
    wilkieCoreGeneric add mul exp p q r s x z =
      wilkieCoreGeneric add mul exp p q r s z x := by
  intro z
  let A := add (exp p x) (exp q x)
  let B := add (exp r x) (exp s x)
  have one_mul := one_mul_generic mul one mul_one
  have h := jackson_n_move_pos_generic
    (add := add) (mul := mul) (exp := exp) (one := one) (k := k)
    (distrib := distrib) (exp_add := exp_add) (exp_mul := exp_mul)
    (exp_one := exp_one)
    (p := p) (q := q) (r := r) (s := s) (x := x)
    (pux := one) (qux := one) hfactor
  dsimp [z, A, B] at h
  unfold wilkieCoreGeneric
  calc
    mul (exp (add (exp p z) (exp q z)) x) (exp (add (exp r x) (exp s x)) z)
        =
      mul (exp (add (exp r x) (exp s x)) z)
        (exp (add (mul (exp p z) one) (mul (exp q z) one)) x) := by
          rw [mul_one, mul_one]
          ac_rfl
    _ =
      mul (exp (add (exp p x) (exp q x)) z)
        (exp (add (mul one (exp r z)) (mul one (exp s z))) x) := by
          exact h.symm
    _ =
      mul (exp (add (exp p x) (exp q x)) z) (exp (add (exp r z) (exp s z)) x) := by
          rw [one_mul, one_mul]

theorem wilkieCore_right_posCoeff_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {p q r s x : Nat}
    (h1 : InDomain n 1)
    (hp : InDomain n p) (hq : InDomain n q)
    (hr : InDomain n r) (hs : InDomain n s)
    (hx : InDomain n x)
    (k : Nat)
    (hfactor : A.mul p s = A.mul q r) :
    wilkieCore A p q r s x (posCoeff A.add 1 k) =
      wilkieCore A p q r s (posCoeff A.add 1 k) x := by
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let expD : D → D → D := fun a b => ⟨A.exp a.1 b.1, C.exp_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  let pD : D := ⟨p, hp⟩
  let qD : D := ⟨q, hq⟩
  let rD : D := ⟨r, hr⟩
  let sD : D := ⟨s, hs⟩
  let xD : D := ⟨x, hx⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have coeff_val : ∀ k, (posCoeff addD oneD k).1 = posCoeff A.add 1 k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp [posCoeff, addD, oneD, ih]
  have hD := wilkieCore_right_posCoeff_generic
    (add := addD) (mul := mulD) (exp := expD) (one := oneD) (k := k)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
    (exp_add := by
      intro a b c
      apply Subtype.ext
      exact H.exp_add a.2 b.2 c.2)
    (exp_mul := by
      intro a b c
      apply Subtype.ext
      exact H.exp_mul a.2 b.2 c.2)
    (exp_one := by
      intro a
      apply Subtype.ext
      exact H.exp_one a.2)
    (p := pD) (q := qD) (r := rD) (s := sD) (x := xD)
    (by
      apply Subtype.ext
      exact hfactor)
  simpa [wilkieCoreGeneric, wilkieCore, addD, mulD, expD, oneD, pD, qD, rD, sD,
    xD, coeff_val]
    using congrArg Subtype.val hD

theorem left_two_factor_reductions_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h1 : InDomain n 1) :
    let two := A.add 1 1
    Rterm A two = A.mul (Pterm A two) (Pterm A two) ∧
      Sterm A two = A.mul (Pterm A two) (Qterm A two) := by
  intro two
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := left_two_factor_reductions_generic
    (add := addD) (mul := mulD) (one := oneD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
  constructor
  · simpa [two, Pterm, Rterm, x2, x3, x4, addD, mulD, oneD]
      using congrArg Subtype.val hD.1
  · simpa [two, Pterm, Qterm, Sterm, x2, x3, x4, addD, mulD, oneD]
      using congrArg Subtype.val hD.2

theorem left_three_factor_reductions_hsi
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    (h1 : InDomain n 1) :
    let two := A.add 1 1
    let three := A.add two 1
    Rterm A three = A.mul (Qterm A two) (Pterm A three) ∧
      Sterm A three = A.mul (Qterm A two) (Qterm A three) := by
  intro two three
  let D := {v : Nat // InDomain n v}
  let addD : D → D → D := fun a b => ⟨A.add a.1 b.1, C.add_mem a.2 b.2⟩
  let mulD : D → D → D := fun a b => ⟨A.mul a.1 b.1, C.mul_mem a.2 b.2⟩
  let oneD : D := ⟨1, h1⟩
  letI : Std.Associative addD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.add_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative addD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.add_comm a.2 b.2⟩
  letI : Std.Associative mulD := ⟨by
    intro a b c
    apply Subtype.ext
    exact (H.mul_assoc a.2 b.2 c.2).symm⟩
  letI : Std.Commutative mulD := ⟨by
    intro a b
    apply Subtype.ext
    exact H.mul_comm a.2 b.2⟩
  have hD := left_three_factor_reductions_generic
    (add := addD) (mul := mulD) (one := oneD)
    (distrib := by
      intro a b c
      apply Subtype.ext
      exact H.distrib a.2 b.2 c.2)
    (mul_one := by
      intro a
      apply Subtype.ext
      exact H.mul_one a.2)
  constructor
  · simpa [two, three, Pterm, Qterm, Rterm, x2, x3, x4, addD, mulD, oneD]
      using congrArg Subtype.val hD.1
  · simpa [two, three, Pterm, Qterm, Sterm, x2, x3, x4, addD, mulD, oneD]
      using congrArg Subtype.val hD.2

theorem wilkie_holds_left_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {y : Nat} (h1 : InDomain n 1) (hy : InDomain n y) :
    wilkieP A (A.add 1 1) y (A.add 1 1) =
      wilkieP A y (A.add 1 1) (A.add 1 1) := by
  let two := A.add 1 1
  have htwo : InDomain n two := C.add_mem h1 h1
  rcases pqrs_terms_mem_of_closed C h1 htwo with ⟨hP, hQ, hR, hS⟩
  rcases left_two_factor_reductions_hsi C H h1 with ⟨hRfac, hSfac⟩
  have hcore := common_factor_hsi C H hP hQ hR hS hP htwo hy hRfac hSfac
  simpa [two, wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem wilkie_holds_left_three
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {y : Nat} (h1 : InDomain n 1) (hy : InDomain n y) :
    wilkieP A (A.add (A.add 1 1) 1) y (A.add (A.add 1 1) 1) =
      wilkieP A y (A.add (A.add 1 1) 1) (A.add (A.add 1 1) 1) := by
  let two := A.add 1 1
  let three := A.add two 1
  have htwo : InDomain n two := C.add_mem h1 h1
  have hthree : InDomain n three := C.add_mem htwo h1
  rcases pqrs_terms_mem_of_closed C h1 htwo with ⟨_hP2, hQ2, _hR2, _hS2⟩
  rcases pqrs_terms_mem_of_closed C h1 hthree with ⟨hP, hQ, hR, hS⟩
  rcases left_three_factor_reductions_hsi C H h1 with ⟨hRfac, hSfac⟩
  have hcore := common_factor_hsi C H hP hQ hR hS hQ2 hthree hy hRfac hSfac
  simpa [two, three, wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem wilkie_holds_right_posCoeff
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) (k : Nat) :
    wilkieP A x (posCoeff A.add 1 k) x =
      wilkieP A (posCoeff A.add 1 k) x x := by
  rcases pqrs_terms_mem_of_closed C h1 hx with ⟨hP, hQ, hR, hS⟩
  have hfactor := wilkie_factor_hsi C H h1 hx
  have hcore :=
    wilkieCore_right_posCoeff_hsi C H h1 hP hQ hR hS hx k hfactor
  simpa [wilkieCore, wilkieP, Pterm, Qterm, Rterm, Sterm, x2, x3, x4]
    using hcore

theorem wilkie_holds_right_two
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) :
    wilkieP A x (A.add 1 1) x = wilkieP A (A.add 1 1) x x := by
  simpa [posCoeff] using wilkie_holds_right_posCoeff C H h1 hx 1

theorem wilkie_holds_right_three
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x : Nat} (h1 : InDomain n 1) (hx : InDomain n x) :
    wilkieP A x (A.add (A.add 1 1) 1) x =
      wilkieP A (A.add (A.add 1 1) 1) x x := by
  simpa [posCoeff] using wilkie_holds_right_posCoeff C H h1 hx 2

theorem wilkie_failure_pair_distinct_from_one
    {n : Nat} {A : Algebra} (C : Closed n A) (H : HSI n A)
    {x y : Nat} (h1 : InDomain n 1) (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    1 ≠ x ∧ 1 ≠ y ∧ x ≠ y := by
  refine ⟨?x_ne_one, ?y_ne_one, ?x_ne_y⟩
  · intro hx1
    subst x
    exact hFail (wilkie_holds_left_one C H h1 hy)
  · intro hy1
    subst y
    exact hFail (wilkie_holds_right_one C H h1 hx)
  · intro hxy
    subst y
    exact hFail rfl

/--
The remaining Burris-Lee Corollary 8.16 content after the elementary proof
that the failing pair is disjoint from `1` and from itself, and after the
integer-value collapses `1 + 1 = 1`, `3 = 1`, and `3 = 2` have been ruled out.
-/
theorem burrisLee_successor_integer_values_distinct_from_failure_pair_except_integer_collapses
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    A.add 1 1 ≠ x ∧
    A.add 1 1 ≠ y ∧
    A.add (A.add 1 1) 1 ≠ x ∧
    A.add (A.add 1 1) 1 ≠ y := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  refine ⟨?h2x, ?h2y, ?h3x, ?h3y⟩
  · intro hEq
    exact hFail (by
      simpa [hEq] using wilkie_holds_left_two C H h1 hy)
  · intro hEq
    exact hFail (by
      simpa [hEq] using wilkie_holds_right_two C H h1 hx)
  · intro hEq
    exact hFail (by
      simpa [hEq] using wilkie_holds_left_three C H h1 hy)
  · intro hEq
    exact hFail (by
      simpa [hEq] using wilkie_holds_right_three C H h1 hx)

theorem burrisLee_successor_integer_values_distinct_from_failure_pair_except_three_eq_two
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ x ∧
    A.add 1 1 ≠ y ∧
    A.add (A.add 1 1) 1 ≠ x ∧
    A.add (A.add 1 1) 1 ≠ y := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h13 : 1 ≠ A.add (A.add 1 1) 1 := by
    intro hEq
    exact hFail (wilkie_holds_of_three_eq_one C H h1 hx hy hEq.symm)
  rcases burrisLee_successor_integer_values_distinct_from_failure_pair_except_integer_collapses
      C H h5 hx hy hFail with
    ⟨h24, h25, h34, h35⟩
  exact ⟨h13, h24, h25, h34, h35⟩

theorem burrisLee_successor_integer_values_distinct_from_failure_pair
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ x ∧
    A.add 1 1 ≠ y ∧
    A.add (A.add 1 1) 1 ≠ x ∧
    A.add (A.add 1 1) 1 ≠ y := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h23 : A.add 1 1 ≠ A.add (A.add 1 1) 1 := by
    intro hEq
    exact hFail (wilkie_holds_of_three_eq_two C H h1 hx hy hEq.symm)
  rcases burrisLee_successor_integer_values_distinct_from_failure_pair_except_three_eq_two
      C H h5 hx hy hFail with
    ⟨h13, h24, h25, h34, h35⟩
  exact ⟨h13, h23, h24, h25, h34, h35⟩

theorem burrisLee_integer_values_distinct_from_failure_pair
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    1 ≠ A.add 1 1 ∧
    1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ x ∧
    A.add 1 1 ≠ y ∧
    A.add (A.add 1 1) 1 ≠ x ∧
    A.add (A.add 1 1) 1 ≠ y := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h12 : 1 ≠ A.add 1 1 := by
    intro hEq
    exact hFail (wilkie_holds_of_two_eq_one C H h1 hx hy hEq.symm)
  rcases burrisLee_successor_integer_values_distinct_from_failure_pair
      C H h5 hx hy hFail with
    ⟨h13, h23, h24, h25, h34, h35⟩
  exact ⟨h12, h13, h23, h24, h25, h34, h35⟩

/--
Burris-Lee Corollaries 8.5 and 8.16, in the exact form needed for the
normalization bridge: under a genuine Wilkie failure, the first three
integers and the failing pair are five distinct domain elements.
-/
theorem burrisLee_normalization_values_distinct_of_wilkie_failure
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    InDomain n (A.add 1 1) ∧
    InDomain n (A.add (A.add 1 1) 1) ∧
    1 ≠ A.add 1 1 ∧
    1 ≠ A.add (A.add 1 1) 1 ∧
    1 ≠ x ∧
    1 ≠ y ∧
    A.add 1 1 ≠ A.add (A.add 1 1) 1 ∧
    A.add 1 1 ≠ x ∧
    A.add 1 1 ≠ y ∧
    A.add (A.add 1 1) 1 ≠ x ∧
    A.add (A.add 1 1) 1 ≠ y ∧
    x ≠ y := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2D : InDomain n (A.add 1 1) := C.add_mem h1 h1
  have h3D : InDomain n (A.add (A.add 1 1) 1) := C.add_mem h2D h1
  rcases wilkie_failure_pair_distinct_from_one C H h1 hx hy hFail with
    ⟨h14, h15, h45⟩
  rcases burrisLee_integer_values_distinct_from_failure_pair
      C H h5 hx hy hFail with
    ⟨h12, h13, h23, h24, h25, h34, h35⟩
  exact ⟨h2D, h3D, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩

/--
This is the remaining Burris-Lee/Zhang normalization content:
from a genuine Wilkie failure, the first three integers and a failing pair can
be chosen as five distinct elements, and the finite domain can be permuted so
that they are labeled `1,2,3,4,5`.
-/
theorem normalizingRelabeling_exists_of_wilkie_failure
    {n : Nat} {A : Algebra}
    (C : Closed n A) (H : HSI n A)
    (h5 : InDomain n 5)
    {x y : Nat} (hx : InDomain n x) (hy : InDomain n y)
    (hFail : WilkieFailsAt A x y x) :
    ∃ ρ : Relabeling n,
      ρ.toOld 1 = 1 ∧
      ρ.toOld 2 = A.add 1 1 ∧
      ρ.toOld 3 = A.add (A.add 1 1) 1 ∧
      ρ.toOld 4 = x ∧
      ρ.toOld 5 = y := by
  rcases burrisLee_normalization_values_distinct_of_wilkie_failure
      C H h5 hx hy hFail with
    ⟨h2D, h3D, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩
  exact relabeling_exists_of_distinct_one_four h5 h2D h3D hx hy
    h12 h13 h14 h15 h23 h24 h25 h34 h35 h45

theorem normalizedCountermodel_of_generalCountermodel
    {n : Nat} (h5 : InDomain n 5) :
    (∃ A, GeneralCountermodel n A) → ∃ A, NormalizedCountermodel n A := by
  intro h
  rcases h with ⟨A, hA⟩
  rcases hA.violates_wilkie with ⟨x, y, hx, hy, hFail⟩
  rcases normalizingRelabeling_exists_of_wilkie_failure
      hA.closed hA.hsi h5 hx hy hFail with
    ⟨ρ, htoOld1, htoOld2, htoOld3, htoOld4, htoOld5⟩
  exact ⟨relabelAlgebra ρ A,
    normalizedCountermodel_of_relabeling ρ hA.closed hA.hsi h5 hFail
      htoOld1 htoOld2 htoOld3 htoOld4 htoOld5⟩

theorem normalizedCountermodel_to_generalCountermodel
    {n : Nat} {A : Algebra} (h5 : InDomain n 5)
    (h : NormalizedCountermodel n A) :
    GeneralCountermodel n A where
  closed := h.closed
  hsi := h.hsi
  violates_wilkie := by
    have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
    exact ⟨4, 5, h4, h5, h.wilkie_fails⟩

theorem lexNormalizedCountermodel_of_normalizedCountermodel
    {n : Nat} (h5 : InDomain n 5) :
    (∃ A, NormalizedCountermodel n A) →
      ∃ A, LexNormalizedCountermodel n A := by
  intro h
  rcases h with ⟨A, hA⟩
  rcases exists_relabeling_with_lexTranspositionLeaders n A with
    ⟨ρ, hρ, hlex⟩
  have htoOld1 : ρ.toOld 1 = 1 := hρ 1 (by simp)
  have htoOld2 : ρ.toOld 2 = A.add 1 1 := by
    rw [hA.add_one_one]
    exact hρ 2 (by simp)
  have htoOld3 : ρ.toOld 3 = A.add (A.add 1 1) 1 := by
    rw [hA.add_one_one, hA.add_two_one]
    exact hρ 3 (by simp)
  have htoOld4 : ρ.toOld 4 = 4 := hρ 4 (by simp)
  have htoOld5 : ρ.toOld 5 = 5 := hρ 5 (by simp)
  have hnorm :
      NormalizedCountermodel n (relabelAlgebra ρ A) :=
    normalizedCountermodel_of_relabeling ρ hA.closed hA.hsi h5
      hA.wilkie_fails htoOld1 htoOld2 htoOld3 htoOld4 htoOld5
  exact ⟨relabelAlgebra ρ A, ⟨hnorm, hlex⟩⟩

theorem lexNormalizedCountermodel_to_generalCountermodel
    {n : Nat} {A : Algebra} (h5 : InDomain n 5)
    (h : LexNormalizedCountermodel n A) :
    GeneralCountermodel n A :=
  normalizedCountermodel_to_generalCountermodel h5 h.normalized

def LexSymmetryBreakingCorrectnessTarget (n : Nat) : Prop :=
  (∃ A, GeneralCountermodel n A) ↔ ∃ A, LexNormalizedCountermodel n A

theorem lex_symmetry_breaking_correct
    {n : Nat} (h5 : InDomain n 5) :
    LexSymmetryBreakingCorrectnessTarget n := by
  constructor
  · intro h
    exact lexNormalizedCountermodel_of_normalizedCountermodel h5
      (normalizedCountermodel_of_generalCountermodel h5 h)
  · intro h
    rcases h with ⟨A, hA⟩
    exact ⟨A, lexNormalizedCountermodel_to_generalCountermodel h5 hA⟩

theorem hsiClauses_below {n : Nat} :
    CNFBelow (hsiClauses n) (simpEncLexAuxStart n) := by
  have htotality : CNFBelow (totalityClauses n) (simpEncLexAuxStart n) := by
    unfold totalityClauses
    repeat rw [CNFBelow_append]
    refine ⟨⟨?addTotal, ?mulTotal⟩, ?expTotal⟩
    · apply CNFBelow_flatMap
      intro p hp
      rcases mem_symPairs_domain hp with ⟨hi, hj⟩
      rcases p with ⟨i, j⟩
      apply CNFBelow_exactlyOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨k, hk, rfl⟩
      exact addVar_lt_simpEncLexAuxStart hi hj hk
    · apply CNFBelow_flatMap
      intro p hp
      rcases mem_symPairs_domain hp with ⟨hi, hj⟩
      rcases p with ⟨i, j⟩
      apply CNFBelow_exactlyOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨k, hk, rfl⟩
      exact mulVar_lt_simpEncLexAuxStart hi hj hk
    · apply CNFBelow_flatMap
      intro p hp
      rcases (mem_product2_iff).1 hp with ⟨hi, hj⟩
      rcases p with ⟨i, j⟩
      apply CNFBelow_exactlyOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨k, hk, rfl⟩
      exact expVar_lt_simpEncLexAuxStart hi hj hk
  have hunit : CNFBelow (unitIdentityClauses n) (simpEncLexAuxStart n) := by
    unfold unitIdentityClauses
    repeat rw [CNFBelow_append]
    refine ⟨⟨?mulUnit, ?expOneBase⟩, ?expOneExponent⟩
    · apply CNFBelow_map
      intro x hx lit hlit
      simp at hlit
      rcases hlit with rfl
      exact litVar_pos_lt_of (mulVar_lt_simpEncLexAuxStart hx (one_in_domain_of hx) hx)
    · apply CNFBelow_map
      intro x hx lit hlit
      simp at hlit
      rcases hlit with rfl
      exact litVar_pos_lt_of (expVar_lt_simpEncLexAuxStart (one_in_domain_of hx) hx
        (one_in_domain_of hx))
    · apply CNFBelow_map
      intro x hx lit hlit
      simp at hlit
      rcases hlit with rfl
      exact litVar_pos_lt_of (expVar_lt_simpEncLexAuxStart hx (one_in_domain_of hx) hx)
  have haddAssoc : CNFBelow (addAssocClauses n) (simpEncLexAuxStart n) := by
    unfold addAssocClauses
    apply CNFBelow_flatMap
    intro p hp
    rcases mem_symPairs_domain hp with ⟨hi, hk⟩
    rcases p with ⟨i, k⟩
    apply CNFBelow_flatMap
    intro j hj
    rw [CNFBelow_append]
    constructor
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact add2Var_lt_simpEncLexAuxStart hi hj hk hl
    · apply CNFBelow_flatMap
      intro q hq
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      intro clause hclause lit hlit
      simp at hclause
      rcases hclause with rfl | rfl
      all_goals
        simp at hlit
        rcases hlit with rfl | rfl | rfl
        all_goals
          simp [litVar_neg, litVar_pos]
          first
          | exact addVar_lt_simpEncLexAuxStart hj hk hm
          | exact addVar_lt_simpEncLexAuxStart hi hm hl
          | exact add2Var_lt_simpEncLexAuxStart hi hj hk hl
          | exact addVar_lt_simpEncLexAuxStart hi hj hm
          | exact addVar_lt_simpEncLexAuxStart hm hk hl
  have hmulAssoc : CNFBelow (mulAssocClauses n) (simpEncLexAuxStart n) := by
    unfold mulAssocClauses
    apply CNFBelow_flatMap
    intro p hp
    rcases mem_symPairs_domain hp with ⟨hi, hk⟩
    rcases p with ⟨i, k⟩
    apply CNFBelow_flatMap
    intro j hj
    rw [CNFBelow_append]
    constructor
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact mul2Var_lt_simpEncLexAuxStart hi hj hk hl
    · apply CNFBelow_flatMap
      intro q hq
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      intro clause hclause lit hlit
      simp at hclause
      rcases hclause with rfl | rfl
      all_goals
        simp at hlit
        rcases hlit with rfl | rfl | rfl
        all_goals
          simp [litVar_neg, litVar_pos]
          first
          | exact mulVar_lt_simpEncLexAuxStart hj hk hm
          | exact mulVar_lt_simpEncLexAuxStart hi hm hl
          | exact mul2Var_lt_simpEncLexAuxStart hi hj hk hl
          | exact mulVar_lt_simpEncLexAuxStart hi hj hm
          | exact mulVar_lt_simpEncLexAuxStart hm hk hl
  have hdist : CNFBelow (distClauses n) (simpEncLexAuxStart n) := by
    unfold distClauses
    apply CNFBelow_flatMap
    intro x hx
    apply CNFBelow_flatMap
    intro p hp
    rcases mem_symPairs_domain hp with ⟨hy, hz⟩
    rcases p with ⟨y, z⟩
    repeat rw [CNFBelow_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact distVar_lt_simpEncLexAuxStart hx hy hz hl
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl
      · exact litVar_neg_lt_of (addVar_lt_simpEncLexAuxStart hy hz hm)
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hx hm hl)
      · exact litVar_pos_lt_of (distVar_lt_simpEncLexAuxStart hx hy hz hl)
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product3_iff).1 hq with ⟨hl, hm1, hm2⟩
      rcases q with ⟨l, m1, m2⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl | rfl
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hx hy hm1)
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hx hz hm2)
      · exact litVar_neg_lt_of (addVar_lt_simpEncLexAuxStart hm1 hm2 hl)
      · exact litVar_pos_lt_of (distVar_lt_simpEncLexAuxStart hx hy hz hl)
  have hexpAdd : CNFBelow (expAddClauses n) (simpEncLexAuxStart n) := by
    unfold expAddClauses
    apply CNFBelow_flatMap
    intro x hx
    apply CNFBelow_flatMap
    intro p hp
    rcases mem_symPairs_domain hp with ⟨hy, hz⟩
    rcases p with ⟨y, z⟩
    repeat rw [CNFBelow_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact expAddVar_lt_simpEncLexAuxStart hx hy hz hl
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl
      · exact litVar_neg_lt_of (addVar_lt_simpEncLexAuxStart hy hz hm)
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hx hm hl)
      · exact litVar_pos_lt_of (expAddVar_lt_simpEncLexAuxStart hx hy hz hl)
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product3_iff).1 hq with ⟨hl, hm1, hm2⟩
      rcases q with ⟨l, m1, m2⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl | rfl
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hx hy hm1)
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hx hz hm2)
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hm1 hm2 hl)
      · exact litVar_pos_lt_of (expAddVar_lt_simpEncLexAuxStart hx hy hz hl)
  have hexpMul : CNFBelow (expMulClauses n) (simpEncLexAuxStart n) := by
    unfold expMulClauses
    apply CNFBelow_flatMap
    intro p hp
    rcases mem_symPairs_domain hp with ⟨hx, hy⟩
    rcases p with ⟨x, y⟩
    apply CNFBelow_flatMap
    intro z hz
    repeat rw [CNFBelow_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact expMulVar_lt_simpEncLexAuxStart hx hy hz hl
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hx hy hm)
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hm hz hl)
      · exact litVar_pos_lt_of (expMulVar_lt_simpEncLexAuxStart hx hy hz hl)
    · apply CNFBelow_map
      intro q hq lit hlit
      rcases (mem_product3_iff).1 hq with ⟨hl, hm1, hm2⟩
      rcases q with ⟨l, m1, m2⟩
      simp at hlit
      rcases hlit with rfl | rfl | rfl | rfl
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hx hz hm1)
      · exact litVar_neg_lt_of (expVar_lt_simpEncLexAuxStart hy hz hm2)
      · exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hm1 hm2 hl)
      · exact litVar_pos_lt_of (expMulVar_lt_simpEncLexAuxStart hx hy hz hl)
  have hexpAssoc : CNFBelow (expAssocClauses n) (simpEncLexAuxStart n) := by
    unfold expAssocClauses
    apply CNFBelow_flatMap
    intro p hp
    rcases (mem_product3_iff).1 hp with ⟨hx, hy, hz⟩
    rcases p with ⟨x, y, z⟩
    rw [CNFBelow_append]
    constructor
    · apply CNFBelow_atMostOnePairwise
      intro v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact exp2Var_lt_simpEncLexAuxStart hx hy hz hl
    · apply CNFBelow_flatMap
      intro q hq
      rcases (mem_product2_iff).1 hq with ⟨hl, hm⟩
      rcases q with ⟨l, m⟩
      intro clause hclause lit hlit
      simp at hclause
      rcases hclause with rfl | rfl
      all_goals
        simp at hlit
        rcases hlit with rfl | rfl | rfl
        all_goals
          simp [litVar_neg, litVar_pos]
          first
          | exact expVar_lt_simpEncLexAuxStart hx hy hm
          | exact expVar_lt_simpEncLexAuxStart hm hz hl
          | exact exp2Var_lt_simpEncLexAuxStart hx hy hz hl
          | exact mulVar_lt_simpEncLexAuxStart hy hz hm
          | exact expVar_lt_simpEncLexAuxStart hx hm hl
  unfold hsiClauses
  repeat rw [CNFBelow_append]
  exact ⟨⟨⟨⟨⟨⟨⟨htotality, hunit⟩, haddAssoc⟩, hmulAssoc⟩, hdist⟩,
    hexpAdd⟩, hexpMul⟩, hexpAssoc⟩

def TermSpecArgBelowAux (n : Nat) : Arg → Prop
  | .const value => InDomain n value
  | .term termIndex => termIndex < wilkieTermCount

theorem termClauses_below
    {n termIndex : Nat} {spec : TermSpec}
    (hterm : termIndex < wilkieTermCount)
    (hleft : TermSpecArgBelowAux n spec.left)
    (hright : TermSpecArgBelowAux n spec.right) :
    CNFBelow (termClauses n termIndex spec) (simpEncLexAuxStart n) := by
  cases spec with
  | mk op left right =>
      unfold termClauses
      rw [CNFBelow_append]
      constructor
      · apply CNFBelow_exactlyOnePairwise
        intro v hv
        rcases List.mem_map.mp hv with ⟨value, hvalue, rfl⟩
        exact termVar_lt_simpEncLexAuxStart hterm hvalue
      · cases left with
        | const leftValue =>
            cases right with
            | const rightValue =>
                simp [TermSpecArgBelowAux] at hleft hright
                apply CNFBelow_map
                intro v hv lit hlit
                simp at hlit
                rcases hlit with rfl | rfl
                · exact litVar_neg_lt_of
                    (opVar_lt_simpEncLexAuxStart (op := op) hleft hright hv)
                · exact litVar_pos_lt_of
                    (termVar_lt_simpEncLexAuxStart hterm hv)
            | term rightIndex =>
                simp [TermSpecArgBelowAux] at hleft hright
                apply CNFBelow_map
                intro q hq lit hlit
                rcases (mem_product2_iff).1 hq with ⟨hu, hv⟩
                rcases q with ⟨u, v⟩
                simp at hlit
                rcases hlit with rfl | rfl | rfl
                · exact litVar_neg_lt_of
                    (opVar_lt_simpEncLexAuxStart (op := op) hleft hu hv)
                · exact litVar_neg_lt_of
                    (termVar_lt_simpEncLexAuxStart hright hu)
                · exact litVar_pos_lt_of
                    (termVar_lt_simpEncLexAuxStart hterm hv)
        | term leftIndex =>
            cases right with
            | const rightValue =>
                simp [TermSpecArgBelowAux] at hleft hright
                apply CNFBelow_map
                intro q hq lit hlit
                rcases (mem_product2_iff).1 hq with ⟨hu, hv⟩
                rcases q with ⟨u, v⟩
                simp at hlit
                rcases hlit with rfl | rfl | rfl
                · exact litVar_neg_lt_of
                    (opVar_lt_simpEncLexAuxStart (op := op) hu hright hv)
                · exact litVar_neg_lt_of
                    (termVar_lt_simpEncLexAuxStart hleft hu)
                · exact litVar_pos_lt_of
                    (termVar_lt_simpEncLexAuxStart hterm hv)
            | term rightIndex =>
                simp [TermSpecArgBelowAux] at hleft hright
                apply CNFBelow_map
                intro q hq lit hlit
                rcases (mem_product3_iff).1 hq with ⟨hu, hv, hw⟩
                rcases q with ⟨u, v, w⟩
                simp at hlit
                rcases hlit with rfl | rfl | rfl | rfl
                · exact litVar_neg_lt_of
                    (opVar_lt_simpEncLexAuxStart (op := op) hu hv hw)
                · exact litVar_neg_lt_of
                    (termVar_lt_simpEncLexAuxStart hleft hu)
                · exact litVar_neg_lt_of
                    (termVar_lt_simpEncLexAuxStart hright hv)
                · exact litVar_pos_lt_of
                    (termVar_lt_simpEncLexAuxStart hterm hw)

theorem termSpecArgBelowAux_of_enumerate
    {n : Nat} (h5 : InDomain n 5) {p : Nat × TermSpec}
    (hp : p ∈ enumerate termSpecs) :
    p.1 < wilkieTermCount ∧
      TermSpecArgBelowAux n p.2.left ∧
      TermSpecArgBelowAux n p.2.right := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  simp [enumerate, enumerateFrom, termSpecs] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals
    subst p
    simp [TermSpecArgBelowAux, wilkieTermCount, termSpecs, h1, h4, h5]

theorem wilkieDiseqClauses_below
    {n : Nat} :
    CNFBelow (wilkieDiseqClauses n) (simpEncLexAuxStart n) := by
  have h24 : 24 < wilkieTermCount := by decide
  have h25 : 25 < wilkieTermCount := by decide
  unfold wilkieDiseqClauses
  apply CNFBelow_map
  intro v hv lit hlit
  simp at hlit
  rcases hlit with rfl | rfl
  · exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart h24 hv)
  · exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart h25 hv)

theorem wilkieClauses_below
    {n : Nat} (h5 : InDomain n 5) :
    CNFBelow (wilkieClauses n) (simpEncLexAuxStart n) := by
  unfold wilkieClauses
  rw [CNFBelow_append]
  constructor
  · apply CNFBelow_flatMap
    intro p hp
    have hspec := termSpecArgBelowAux_of_enumerate h5 hp
    exact termClauses_below hspec.1 hspec.2.1 hspec.2.2
  · exact wilkieDiseqClauses_below

theorem coreClauses_below
    {n : Nat} (h5 : InDomain n 5) :
    CNFBelow (coreClauses n) (simpEncLexAuxStart n) := by
  unfold coreClauses
  rw [CNFBelow_append]
  exact ⟨hsiClauses_below, wilkieClauses_below h5⟩

theorem simpEncExtraClauses_below
    {n : Nat} (h5 : InDomain n 5) :
    CNFBelow (simpEncExtraClauses n) (simpEncLexAuxStart n) := by
  have h1 : InDomain n 1 := InDomain.of_le h5 (by omega) (by omega)
  have h2 : InDomain n 2 := InDomain.of_le h5 (by omega) (by omega)
  have h3 : InDomain n 3 := InDomain.of_le h5 (by omega) (by omega)
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  have ht0 : 0 < wilkieTermCount := by decide
  have ht3 : 3 < wilkieTermCount := by decide
  have ht4 : 4 < wilkieTermCount := by decide
  have ht7 : 7 < wilkieTermCount := by decide
  have ht8 : 8 < wilkieTermCount := by decide
  have ht12 : 12 < wilkieTermCount := by decide
  have ht13 : 13 < wilkieTermCount := by decide
  unfold simpEncExtraClauses
  repeat rw [CNFBelow_append]
  refine ⟨⟨⟨⟨⟨?fixed, ?valueBlock⟩, ?leeDiv⟩, ?jacksonLinear⟩,
    ?jacksonQuadratic⟩, ?zhangLee⟩
  · intro clause hclause lit hlit
    simp at hclause
    rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      simp at hlit
      rcases hlit with rfl
      simp [litVar_pos, litVar_neg]
      first
      | exact addVar_lt_simpEncLexAuxStart h1 h1 h2
      | exact addVar_lt_simpEncLexAuxStart h2 h1 h3
      | exact addVar_lt_simpEncLexAuxStart h1 h4 h1
      | exact addVar_lt_simpEncLexAuxStart h2 h4 h1
      | exact addVar_lt_simpEncLexAuxStart h4 h4 h1
      | exact mulVar_lt_simpEncLexAuxStart h4 h4 h1
      | exact addVar_lt_simpEncLexAuxStart h4 h4 h4
      | exact mulVar_lt_simpEncLexAuxStart h4 h4 h4
      | exact addVar_lt_simpEncLexAuxStart h1 h4 h4
      | exact addVar_lt_simpEncLexAuxStart h2 h4 h4
      | exact termVar_lt_simpEncLexAuxStart ht12 h1
      | exact termVar_lt_simpEncLexAuxStart ht7 h1
      | exact termVar_lt_simpEncLexAuxStart ht12 h4
  · apply CNFBelow_flatMap
    intro value hvalue
    intro clause hclause lit hlit
    simp at hclause
    rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp at hlit
      rcases hlit with rfl | rfl
      all_goals
        simp [litVar_neg]
        first
        | exact addVar_lt_simpEncLexAuxStart h2 h4 hvalue
        | exact termVar_lt_simpEncLexAuxStart ht0 hvalue
        | exact mulVar_lt_simpEncLexAuxStart h4 h4 hvalue
        | exact termVar_lt_simpEncLexAuxStart ht7 hvalue
        | exact addVar_lt_simpEncLexAuxStart h4 h4 hvalue
        | exact termVar_lt_simpEncLexAuxStart ht12 hvalue
        | exact litVar_neg_lt_of (addVar_lt_simpEncLexAuxStart h2 h4 hvalue)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht0 hvalue)
        | exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart h4 h4 hvalue)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht7 hvalue)
        | exact litVar_neg_lt_of (addVar_lt_simpEncLexAuxStart h4 h4 hvalue)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht12 hvalue)
  · apply CNFBelow_map
    intro v hv lit hlit
    simp at hlit
    rcases hlit with rfl
    simp [litVar_neg]
    exact mulVar_lt_simpEncLexAuxStart h4 hv h5
  · apply CNFBelow_flatMap
    intro j hj
    apply CNFBelow_flatMap
    intro z hz
    apply CNFBelow_map
    intro i hi lit hlit
    have hiD : InDomain n i := mem_123_inDomain h5 hi
    have hjD : InDomain n j := mem_123_inDomain h5 hj
    simp at hlit
    rcases hlit with rfl | rfl
    · simp [litVar_neg]
      exact addVar_lt_simpEncLexAuxStart hiD hz h5
    · simp [litVar_neg]
      exact mulVar_lt_simpEncLexAuxStart hjD h4 hz
  · apply CNFBelow_flatMap
    intro p hp
    rcases (mem_product3_iff).1 hp with ⟨hi, hj, hk⟩
    rcases p with ⟨i, j, k⟩
    have hiD : InDomain n i := mem_123_inDomain h5 hi
    have hjD : InDomain n j := mem_123_inDomain h5 hj
    have hkD : InDomain n k := mem_123_inDomain h5 hk
    apply CNFBelow_map
    intro q hq lit hlit
    rcases (mem_product4_iff).1 hq with ⟨hx2Value, hjxValue, hkx2Value, htailValue⟩
    rcases q with ⟨x2Value, jxValue, kx2Value, tailValue⟩
    simp at hlit
    rcases hlit with rfl | rfl | rfl | rfl | rfl
    · simp [litVar_neg]
      exact termVar_lt_simpEncLexAuxStart ht3 hx2Value
    · simp [litVar_neg]
      exact mulVar_lt_simpEncLexAuxStart hjD h4 hjxValue
    · simp [litVar_neg]
      exact mulVar_lt_simpEncLexAuxStart hkD hx2Value hkx2Value
    · simp [litVar_neg]
      exact addVar_lt_simpEncLexAuxStart hjxValue hkx2Value htailValue
    · simp [litVar_neg]
      exact addVar_lt_simpEncLexAuxStart hiD htailValue h5
  · apply CNFBelow_flatMap
    intro v hv
    apply CNFBelow_flatMap
    intro p hp
    rcases (mem_product2_iff).1 hp with ⟨hi, hl⟩
    rcases p with ⟨i, l⟩
    intro clause hclause lit hlit
    simp at hclause
    rcases hclause with rfl | rfl | rfl | rfl
    all_goals
      simp at hlit
      rcases hlit with rfl | rfl | rfl
      all_goals
        simp [litVar_neg]
        first
        | exact termVar_lt_simpEncLexAuxStart ht0 hi
        | exact termVar_lt_simpEncLexAuxStart ht4 hl
        | exact termVar_lt_simpEncLexAuxStart ht4 hi
        | exact termVar_lt_simpEncLexAuxStart ht0 hl
        | exact termVar_lt_simpEncLexAuxStart ht8 hi
        | exact termVar_lt_simpEncLexAuxStart ht13 hl
        | exact termVar_lt_simpEncLexAuxStart ht13 hi
        | exact termVar_lt_simpEncLexAuxStart ht8 hl
        | exact mulVar_lt_simpEncLexAuxStart hi hv hl
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht0 hi)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht4 hl)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht4 hi)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht0 hl)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht8 hi)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht13 hl)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht13 hi)
        | exact litVar_neg_lt_of (termVar_lt_simpEncLexAuxStart ht8 hl)
        | exact litVar_neg_lt_of (mulVar_lt_simpEncLexAuxStart hi hv hl)

theorem core_correctness_forward
    {n : Nat} (h5 : InDomain n 5) :
    Satisfiable (coreClauses n) → ∃ A, Countermodel n A := by
  intro h
  rcases core_satisfiable_yields_countermodel h5 h with ⟨A, hClosed, hHSI, hFail⟩
  exact ⟨A, ⟨hClosed, hHSI, hFail⟩⟩

theorem simpEncEncode_satisfiable_of_lexNormalizedCountermodel
    {n : Nat} (h5 : InDomain n 5) {A : Algebra}
    (hA : LexNormalizedCountermodel n A) :
    Satisfiable (encode n) := by
  let aux := simpEncLexAuxStart n
  rcases simpEncLexClauses_satisfiable_of_lexNormalizedCountermodel
      hA (by simpa [aux] using primary_lt_simpEncLexAuxStart n) with
    ⟨τlex, hpreserve, hlex⟩
  let τ : Assignment := fun v =>
    if v < aux then modelAssignment n A v else τlex v
  have hτModelBelow :
      ∀ v, v < aux → (τ v ↔ modelAssignment n A v) := by
    intro v hv
    simp [τ, hv]
  have hτLexAll : ∀ v, τ v ↔ τlex v := by
    intro v
    by_cases hv : v < aux
    · simp [τ, hv, hpreserve v hv]
    · simp [τ, hv]
  have hCoreModel : evalCNF (modelAssignment n A) (coreClauses n) := by
    have M : WilkieTermValuesInDomain n A :=
      wilkieTermValuesInDomain_of_closed hA.normalized.closed h5
    have Args : WilkieTermSpecArgsInDomain n A :=
      wilkieTermSpecArgsInDomain_of_terms M h5
    have Cons : WilkieTermSpecsConsistent A :=
      wilkieTermSpecsConsistent_all A
    exact (coreClauses_correct n (modelAssignment n A)).2
      (coreSemantics_of_encoded_countermodel
        hA.normalized.closed hA.normalized.hsi
        (modelAssignment_encodesAlgebra hA.normalized.closed hA.normalized.hsi)
        modelAssignment_encodesWilkieTerms M Args Cons
        hA.normalized.wilkie_fails)
  have hCore : evalCNF τ (coreClauses n) := by
    exact (evalCNF_congr_of_below
      (cnf := coreClauses n)
      (coreClauses_below h5)
      hτModelBelow).2 hCoreModel
  have hExtraModel : evalCNF (modelAssignment n A) (simpEncExtraClauses n) :=
    simpEncExtraClauses_modelAssignment
      hA.normalized.closed hA.normalized.hsi h5
      hA.normalized.add_one_one hA.normalized.add_two_one
      hA.normalized.wilkie_fails
  have hExtra : evalCNF τ (simpEncExtraClauses n) := by
    exact (evalCNF_congr_of_below
      (cnf := simpEncExtraClauses n)
      (simpEncExtraClauses_below h5)
      hτModelBelow).2 hExtraModel
  have hLex : evalCNF τ (simpEncLexClauses n (simpEncLexAuxStart n)) := by
    have hlexAux : evalCNF τlex (simpEncLexClauses n aux) := hlex
    have hτLexAux : evalCNF τ (simpEncLexClauses n aux) :=
      (evalCNF_congr hτLexAll (simpEncLexClauses n aux)).2 hlexAux
    simpa [aux] using hτLexAux
  refine ⟨τ, ?_⟩
  unfold encode
  rw [evalCNF_append]
  constructor
  · rw [evalCNF_append]
    exact ⟨hCore, hLex⟩
  · exact hExtra

theorem simpEncEncode_satisfiable_yields_generalCountermodel
    {n : Nat} (h5 : InDomain n 5) :
    Satisfiable (encode n) → ∃ A, GeneralCountermodel n A := by
  intro hSat
  rcases hSat with ⟨τ, hτ⟩
  have hCore : evalCNF τ (coreClauses n) := by
    unfold encode at hτ
    rw [evalCNF_append] at hτ
    have hCoreLex :
        evalCNF τ (coreClauses n ++ simpEncLexClauses n (simpEncLexAuxStart n)) := hτ.1
    rw [evalCNF_append] at hCoreLex
    exact hCoreLex.1
  rcases core_correctness_forward h5 ⟨τ, hCore⟩ with ⟨A, hA⟩
  have h4 : InDomain n 4 := InDomain.of_le h5 (by omega) (by omega)
  exact ⟨A, {
    closed := hA.closed
    hsi := hA.hsi
    violates_wilkie := ⟨4, 5, h4, h5, hA.wilkie_fails⟩
  }⟩

theorem simpEncEncode_satisfiable_of_generalCountermodel
    {n : Nat} (h5 : InDomain n 5) :
    (∃ A, GeneralCountermodel n A) → Satisfiable (encode n) := by
  intro h
  rcases (lex_symmetry_breaking_correct h5).1 h with ⟨A, hA⟩
  exact simpEncEncode_satisfiable_of_lexNormalizedCountermodel h5 hA

def SimpEncEncoderCorrectnessTarget (n : Nat) : Prop :=
  Satisfiable (encode n) ↔ ∃ A, GeneralCountermodel n A

theorem simpEnc_encoder_correctness_general
    {n : Nat} (h5 : InDomain n 5) :
    SimpEncEncoderCorrectnessTarget n := by
  constructor
  · exact simpEncEncode_satisfiable_yields_generalCountermodel h5
  · exact simpEncEncode_satisfiable_of_generalCountermodel h5

end Wilkies
