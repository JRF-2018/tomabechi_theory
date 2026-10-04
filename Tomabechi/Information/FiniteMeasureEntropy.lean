import Tomabechi.Information.FiniteCMI
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic

/-! 有限ゴール条件付きエントロピーの測度論的基礎。-/

namespace Tomabechi.Theorem21

/-- Conditional entropy density at one input, for a finite goal space. -/
noncomputable def conditionalGoalEntropyAt
    {G : Type*} [Fintype G] (mass : G → ℝ) : ℝ :=
  ∑ g : G, finiteConditionalEntropyTerm (mass g) 1

/-- The finite entropy summand is measurable as a function of its mass. -/
theorem measurable_finiteConditionalEntropyTerm_one :
    Measurable (fun p : ℝ => finiteConditionalEntropyTerm p 1) := by
  unfold finiteConditionalEntropyTerm
  refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const ?_
  fun_prop

/-- Measurability of each conditional goal mass gives measurability of its
finite entropy density. -/
theorem conditionalGoalEntropyAt_aestronglyMeasurable
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => conditionalGoalEntropyAt (mass x)) μ := by
  unfold conditionalGoalEntropyAt
  exact Finset.univ.aestronglyMeasurable_fun_sum fun g _ =>
    (measurable_finiteConditionalEntropyTerm_one.comp_aemeasurable
      (hmass_meas g).aemeasurable).aestronglyMeasurable

/-- The binary entropy summand `-p log p` has absolute value at most one on
the probability interval. -/
theorem finiteConditionalEntropyTerm_one_abs_le_one
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖finiteConditionalEntropyTerm p 1‖ ≤ 1 := by
  by_cases hpz : p = 0
  · simp [finiteConditionalEntropyTerm, hpz]
  · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    have hlog := Real.abs_log_mul_self_lt p hp hp1
    simpa [finiteConditionalEntropyTerm, hpz, div_one, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hp0, mul_comm] using le_of_lt hlog

/-- For a probability vector on a finite goal space, the entropy density is
bounded by the number of goals. The coarse bound is sufficient to prove
integrability on any probability input space. -/
theorem conditionalGoalEntropyAt_norm_le_card
    {G : Type*} [Fintype G] (mass : G → ℝ)
    (hmass_nonneg : ∀ g, 0 ≤ mass g)
    (hmass_sum_one : ∑ g : G, mass g = 1) :
    ‖conditionalGoalEntropyAt mass‖ ≤ (Fintype.card G : ℝ) := by
  have hmass_le_one : ∀ g, mass g ≤ 1 := by
    intro g
    rw [← hmass_sum_one]
    exact Finset.single_le_sum (s := Finset.univ)
      (fun g _ => hmass_nonneg g) (Finset.mem_univ g)
  unfold conditionalGoalEntropyAt
  calc
    ‖∑ g : G, finiteConditionalEntropyTerm (mass g) 1‖ ≤
        ∑ g : G, ‖finiteConditionalEntropyTerm (mass g) 1‖ := norm_sum_le _ _
    _ ≤ ∑ _g : G, (1 : ℝ) := Finset.sum_le_sum fun g _ => by
      have h := finiteConditionalEntropyTerm_one_abs_le_one
        (mass g) (hmass_nonneg g) (hmass_le_one g)
      simpa [Real.norm_eq_abs] using h
    _ = (Fintype.card G : ℝ) := by simp

/-- Measurability and normalization of a finite conditional law imply
integrability of its entropy density: each probability is at most one, and
the finite entropy sum has the preceding uniform bound. -/
theorem conditionalGoalEntropy_integrable_of_ae_probability
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (mass : X → G → ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x => conditionalGoalEntropyAt (mass x)) μ)
    (hmass_nonneg_ae : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1) :
    MeasureTheory.Integrable (fun x => conditionalGoalEntropyAt (mass x)) μ := by
  have hbound : ∀ᵐ x ∂μ,
      ‖conditionalGoalEntropyAt (mass x)‖ ≤ (Fintype.card G : ℝ) := by
    filter_upwards [hmass_nonneg_ae, hmass_sum_one_ae] with x hnonneg hsum
    exact conditionalGoalEntropyAt_norm_le_card (mass x) hnonneg hsum
  exact (MeasureTheory.integrable_const (Fintype.card G : ℝ)).mono' hmeas hbound

/-- Conditional entropy of a finite goal given a general measurable input,
defined as the integral of the finite conditional entropy density. -/
noncomputable def conditionalGoalEntropy
    {X G : Type*} [MeasurableSpace X] [Fintype G]
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ) : ℝ :=
  ∫ x, conditionalGoalEntropyAt (mass x) ∂μ


end Tomabechi.Theorem21
