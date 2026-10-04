import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-! # 定理21の有限CMI情報核

旧 `Theorem21.lean` の有限ゴール・決定論的出力に対するエントロピー差API。
最適化・ODE・平均場段階から独立した計算核として、namespaceと公開宣言名を保つ。
-/

namespace Tomabechi.Theorem21

/-- The summand `-p log (p/q)` used in finite conditional entropy. The zero
case is defined as zero, avoiding any `log 0` convention in probability
calculations. -/
noncomputable def finiteConditionalEntropyTerm (p q : ℝ) : ℝ :=
  if p = 0 then 0 else -p * Real.log (p / q)

/-- Conditional entropy of a finite goal variable `G` given a finite context
variable `X`, expressed directly from their joint probability masses. -/
noncomputable def finiteConditionalEntropyGivenInput
    {X G : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) : ℝ := by
  classical
  exact ∑ x : X, ∑ g : G,
    finiteConditionalEntropyTerm (mass x g) (∑ g' : G, mass x g')

/-- Residual conditional entropy of `G` after observing `X` and the
deterministic output `action X G`. For each observed `(x,y)`, the denominator
is the joint mass of all goals producing that output. -/
noncomputable def finiteConditionalEntropyGivenInputAndOutput
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y) : ℝ := by
  classical
  exact ∑ x : X, ∑ g : G,
    finiteConditionalEntropyTerm (mass x g)
      (∑ g' : G, if action x g' = action x g then mass x g' else 0)

/-- Finite conditional mutual information for deterministic output, defined by
the standard entropy difference `H(G|X) - H(G|X,Y)`. -/
noncomputable def finiteConditionalMutualInformation
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y) : ℝ := by
  exact finiteConditionalEntropyGivenInput mass -
    finiteConditionalEntropyGivenInputAndOutput mass action

/-- Increasing the denominator of a nonnegative entropy mass can only
increase its entropy contribution. This scalar inequality is the key
nonnegativity fact for deterministic conditional mutual information. -/
theorem finiteConditionalEntropyTerm_difference_nonneg
    (p q total : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hqt : q ≤ total) :
    0 ≤ finiteConditionalEntropyTerm p total -
      finiteConditionalEntropyTerm p q := by
  by_cases hpz : p = 0
  · simp [finiteConditionalEntropyTerm, hpz]
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have htotal_pos : 0 < total := lt_of_lt_of_le hq_pos hqt
  have hratio : 1 ≤ total / q := (one_le_div hq_pos).2 hqt
  have hlog : 0 ≤ Real.log (total / q) := Real.log_nonneg hratio
  have hid : finiteConditionalEntropyTerm p total -
      finiteConditionalEntropyTerm p q = p * Real.log (total / q) := by
    unfold finiteConditionalEntropyTerm
    rw [if_neg hpz, if_neg hpz]
    rw [Real.log_div hpz htotal_pos.ne', Real.log_div hpz hq_pos.ne',
      Real.log_div htotal_pos.ne' hq_pos.ne']
    ring
  rw [hid]
  exact mul_nonneg hp hlog

/-- A finite conditional-entropy contribution is nonnegative whenever its
mass does not exceed the conditioning fiber. -/
theorem finiteConditionalEntropyTerm_nonneg_of_le
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    0 ≤ finiteConditionalEntropyTerm p q := by
  by_cases hpz : p = 0
  · simp [finiteConditionalEntropyTerm, hpz]
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hratio0 : 0 ≤ p / q := div_nonneg hp hq_pos.le
  have hratio1 : p / q ≤ 1 := (div_le_one hq_pos).2 hpq
  have hlog : Real.log (p / q) ≤ 0 := Real.log_nonpos hratio0 hratio1
  unfold finiteConditionalEntropyTerm
  rw [if_neg hpz]
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hlog

/-- A finite conditional-entropy contribution is bounded by its denominator.
The inequality follows from `-r log r ≤ 1-r` on `[0,1]`. -/
theorem finiteConditionalEntropyTerm_le_denominator
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    finiteConditionalEntropyTerm p q ≤ q := by
  by_cases hpz : p = 0
  · simp [finiteConditionalEntropyTerm, hpz]
    exact le_trans hp hpq
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hratio0 : 0 ≤ p / q := div_nonneg hp hq_pos.le
  have hratio1 : p / q ≤ 1 := (div_le_one hq_pos).2 hpq
  have hid : finiteConditionalEntropyTerm p q =
      q * Real.negMulLog (p / q) := by
    unfold finiteConditionalEntropyTerm Real.negMulLog
    rw [if_neg hpz, Real.log_div hpz hq_pos.ne']
    field_simp <;> ring
  rw [hid]
  calc
    q * Real.negMulLog (p / q) ≤ q * (1 - p / q) :=
      mul_le_mul_of_nonneg_left
        (Real.negMulLog_le_one_sub_self hratio0) hq_pos.le
    _ = q - p := by field_simp
    _ ≤ q := sub_le_self q hp

/-- For a nonnegative finite joint mass, conditional entropy is bounded by
the goal alphabet size times total mass. In particular, a normalized model
has conditional entropy at most `card G`. -/
theorem finiteConditionalEntropyGivenInput_le_card_mul_total
    {X G : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (hmass_nonneg : ∀ x g, 0 ≤ mass x g) :
    finiteConditionalEntropyGivenInput mass ≤
      (Fintype.card G : ℝ) * ∑ x : X, ∑ g : G, mass x g := by
  classical
  unfold finiteConditionalEntropyGivenInput
  calc
    (∑ x : X, ∑ g : G,
        finiteConditionalEntropyTerm (mass x g) (∑ g' : G, mass x g')) ≤
      ∑ x : X, ∑ g : G, (∑ g' : G, mass x g') := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro g _
        have hpq : mass x g ≤ ∑ g' : G, mass x g' :=
          Finset.single_le_sum (s := Finset.univ)
            (fun g' _ => hmass_nonneg x g') (Finset.mem_univ g)
        exact finiteConditionalEntropyTerm_le_denominator
          (mass x g) (∑ g' : G, mass x g') (hmass_nonneg x g) hpq
    _ = (Fintype.card G : ℝ) * ∑ x : X, ∑ g : G, mass x g := by
        calc
          (∑ x : X, ∑ g : G, (∑ g' : G, mass x g')) =
              ∑ x : X, (Fintype.card G : ℝ) * (∑ g' : G, mass x g') := by
            apply Finset.sum_congr rfl
            intro x _
            simp
          _ = (Fintype.card G : ℝ) * ∑ x : X, ∑ g : G, mass x g := by
            rw [← Finset.mul_sum]

/-- The residual conditional entropy after a deterministic observation is
nonnegative: each goal mass is bounded by the mass of its output fiber. -/
theorem finiteConditionalEntropyGivenInputAndOutput_nonneg
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y)
    (hmass_nonneg : ∀ x g, 0 ≤ mass x g) :
    0 ≤ finiteConditionalEntropyGivenInputAndOutput mass action := by
  classical
  unfold finiteConditionalEntropyGivenInputAndOutput
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro g _
  let fiber : ℝ := ∑ g' : G,
    if action x g' = action x g then mass x g' else 0
  have hpq : mass x g ≤ fiber := by
    calc
      mass x g = (if action x g = action x g then mass x g else 0) := by simp
      _ ≤ ∑ g' ∈ Finset.univ,
          (if action x g' = action x g then mass x g' else 0) := by
        apply Finset.single_le_sum
          (f := fun g' => if action x g' = action x g then mass x g' else 0)
          (s := Finset.univ)
        · intro g' _
          by_cases h : action x g' = action x g
          · simpa [h] using hmass_nonneg x g'
          · simp [h]
        · exact Finset.mem_univ g
  change 0 ≤ finiteConditionalEntropyTerm (mass x g) fiber
  exact finiteConditionalEntropyTerm_nonneg_of_le
    (mass x g) fiber (hmass_nonneg x g) hpq

/-- Deterministic conditional mutual information never exceeds the input
conditional entropy, since the residual conditional entropy is nonnegative. -/
theorem finiteConditionalMutualInformation_le_entropy
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y)
    (hmass_nonneg : ∀ x g, 0 ≤ mass x g) :
    finiteConditionalMutualInformation mass action ≤
      finiteConditionalEntropyGivenInput mass := by
  unfold finiteConditionalMutualInformation
  have hresidual := finiteConditionalEntropyGivenInputAndOutput_nonneg
    mass action hmass_nonneg
  linarith

/-- A nonnegative finite joint mass bounds deterministic conditional mutual
information by the goal alphabet size times its total mass. -/
theorem finiteConditionalMutualInformation_le_card_mul_total
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y)
    (hmass_nonneg : ∀ x g, 0 ≤ mass x g) :
    finiteConditionalMutualInformation mass action ≤
      (Fintype.card G : ℝ) * ∑ x : X, ∑ g : G, mass x g := by
  exact le_trans
    (finiteConditionalMutualInformation_le_entropy mass action hmass_nonneg)
    (finiteConditionalEntropyGivenInput_le_card_mul_total mass hmass_nonneg)

/-- Conditional mutual information of a deterministic output is nonnegative
for every nonnegative finite joint mass. The proof compares, term by term,
the total mass at an input with the mass in the output fiber containing the
current goal. No normalization assumption is needed. -/
theorem finiteConditionalMutualInformation_nonneg
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y)
    (hmass_nonneg : ∀ x g, 0 ≤ mass x g) :
    0 ≤ finiteConditionalMutualInformation mass action := by
  classical
  unfold finiteConditionalMutualInformation finiteConditionalEntropyGivenInput
    finiteConditionalEntropyGivenInputAndOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro g _
  let total : ℝ := ∑ g' : G, mass x g'
  let fiber : ℝ := ∑ g' : G,
    if action x g' = action x g then mass x g' else 0
  have hpq : mass x g ≤ fiber := by
    calc
      mass x g = (if action x g = action x g then mass x g else 0) := by simp
      _ ≤ ∑ g' ∈ Finset.univ,
          (if action x g' = action x g then mass x g' else 0) :=
        by
          apply Finset.single_le_sum
            (f := fun g' => if action x g' = action x g then mass x g' else 0)
            (s := Finset.univ)
          · intro g' _
            by_cases h : action x g' = action x g
            · simpa [h] using hmass_nonneg x g'
            · simp [h]
          · exact Finset.mem_univ g
  have hqt : fiber ≤ total := by
    dsimp [fiber, total]
    apply Finset.sum_le_sum
    intro g' _
    by_cases h : action x g' = action x g <;>
      simp [h, hmass_nonneg x g']
  change 0 ≤ finiteConditionalEntropyTerm (mass x g) total -
    finiteConditionalEntropyTerm (mass x g) fiber
  exact finiteConditionalEntropyTerm_difference_nonneg
    (mass x g) fiber total (hmass_nonneg x g) hpq hqt

/-- The information-theoretic clause of Theorem 21 for finite variables.
If the action distinguishes every pair of goal values having positive
conditional mass at a context, observing `(X, action X G)` determines `G`
almost surely. Thus `I(G;Y|X)=H(G|X)`, and the assumed positive residual
goal entropy gives strictly positive conditional mutual information. -/
theorem theorem21_finite_information_capacity
    {X G Y : Type*} [Fintype X] [Fintype G]
    (mass : X → G → ℝ) (action : X → G → Y)
    (hmass_nonneg : ∀ x g, 0 ≤ mass x g)
    (_hmass_total : (∑ x : X, ∑ g : G, mass x g) = 1)
    (hinjective_on_support : ∀ x g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hentropy_positive : 0 < finiteConditionalEntropyGivenInput mass) :
    finiteConditionalMutualInformation mass action =
        finiteConditionalEntropyGivenInput mass ∧
      0 < finiteConditionalMutualInformation mass action := by
  classical
  have hresidual : finiteConditionalEntropyGivenInputAndOutput mass action = 0 := by
    unfold finiteConditionalEntropyGivenInputAndOutput
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro g _
    by_cases hzero : mass x g = 0
    · simp [finiteConditionalEntropyTerm, hzero]
    · have hpos : 0 < mass x g := lt_of_le_of_ne (hmass_nonneg x g) (Ne.symm hzero)
      have hfiber :
          (∑ g' : G, if action x g' = action x g then mass x g' else 0) = mass x g := by
        rw [Finset.sum_eq_single g]
        · simp
        · intro g' _ hne
          by_cases hact : action x g' = action x g
          · have hmass_zero : mass x g' = 0 := by
              by_contra hmass_ne
              have hpos' : 0 < mass x g' :=
                lt_of_le_of_ne (hmass_nonneg x g') (Ne.symm hmass_ne)
              have heq := hinjective_on_support x g hpos g' hact
              exact hne heq
            simp [hact, hmass_zero]
          · simp [hact]
        · intro hnot
          exact (hnot (Finset.mem_univ g)).elim
      have hratio : mass x g / mass x g = 1 := div_self (ne_of_gt hpos)
      simp [finiteConditionalEntropyTerm, hzero, hfiber, hratio]
  constructor
  · simp [finiteConditionalMutualInformation, hresidual]
  · simpa [finiteConditionalMutualInformation, hresidual] using hentropy_positive


end Tomabechi.Theorem21
