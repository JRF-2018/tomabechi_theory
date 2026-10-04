import Theorem22
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # 共有エントロピー収支解析

定理15(I)と定理23が共用する区間積分、一般化エントロピー、および有限・可算層の収支核。
証明本文と公開namespace `Tomabechi.Theorem23` は旧モジュールから移動したまま保持する。
-/

namespace Tomabechi.Theorem23

open Filter
open scoped Topology

/-- On an increasing interval, Lebesgue interval integration is integration
against the volume measure restricted to its half-open interval. -/
theorem intervalIntegral_eq_integral_restrict_Ioc
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, f t =
      ∫ t, f t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
  rw [intervalIntegral.integral_of_le hab]
  simp [Set.uIoc_of_le hab]

/-- Absolute continuity and the a.e. entropy balance yield the endpoint
production identity used in the proof of equation (23.1).
日本語要約：絶対連続性とa.e.微分収支から、エントロピー差を生成率の区間積分に等置する。 -/
theorem entropy_balance_of_absolute_continuity
    (entropyAlong : ℝ → ℝ) (production : ℝ → ℝ) (a b : ℝ)
    (hac : AbsolutelyContinuousOnInterval entropyAlong a b)
    (hderiv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → deriv entropyAlong t = production t) :
    entropyAlong b - entropyAlong a = ∫ t in a..b, production t := by
  have hcongr : (∫ t in a..b, deriv entropyAlong t) =
      ∫ t in a..b, production t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)
  rw [← hac.integral_deriv_eq_sub, hcongr]

/-- The full differential-form entropy bridge used in Theorem 23: absolute
continuity and the a.e. balance law give the endpoint entropy difference,
while the second-law sign `Π_gen ≥ 0` gives nonnegative total production.
Persistent strict dissipation is still a separate condition (23-A).
日本語要約：微分収支に第二法則のa.e.非負性を加え、端点エントロピー差と積分生成率の非負性を得る。 -/
theorem entropy_balance_and_nonnegative_production
    (entropyAlong : ℝ → ℝ) (production : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval entropyAlong a b)
    (hderiv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → deriv entropyAlong t = production t)
    (hproductionNonnegative : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → 0 ≤ production t) :
    entropyAlong b - entropyAlong a = ∫ t in a..b, production t ∧
      0 ≤ ∫ t in a..b, production t := by
  refine ⟨entropy_balance_of_absolute_continuity entropyAlong production a b
      hac hderiv, ?_⟩
  have hnonnegativeOnRestrict :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] production := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hproductionNonnegative] with t ht
    intro htIcc
    exact ht (Set.Icc_subset_uIcc htIcc)
  exact intervalIntegral.integral_nonneg_of_ae_restrict hab
    hnonnegativeOnRestrict

/-- Sustained strict entropy production rules out exact recurrence when the
source's a.e. entropy production equation is given on an absolutely
continuous complete-state trajectory. Thus the endpoint balance used in the
short order argument is derived from the differential form of the omitted
Theorem 15 balance, rather than postulated separately.
日本語要約：完全状態に一価なエントロピーが定義され、絶対連続な収支と条件23-Aが成り立つとき、状態の再帰を排除する。 -/
theorem complete_state_never_repeats_of_absolute_continuity
    {State : Type*} (entropy : State → ℝ) (state : ℝ → State)
    (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hac : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval (fun t => entropy (state t)) t₁ t₂)
    (hproduction : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => entropy (state s)) t = production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) : state t₂ ≠ state t₁ := by
  intro hsame
  have hbalance := entropy_balance_of_absolute_continuity
    (fun t => entropy (state t)) production t₁ t₂
    (hac t₁ t₂ ht₁ ht₂ ht) (hproduction t₁ t₂ ht₁ ht₂ ht)
  have hentropy : entropy (state t₂) = entropy (state t₁) :=
    congrArg entropy hsame
  have hpos := hstrict t₁ t₂ ht₁ ht₂ ht
  rw [← hbalance, hentropy] at hpos
  simp at hpos

/-- The integral form of the entropy balance alone suffices for
nonrecurrence; absolute continuity and the pointwise derivative equation are
one route to this balance, while the A6′ finite-sum limit theorem is another.
日本語要約：全区間の積分収支と条件23-Aから完全状態の非再帰を直接導く。-/
theorem complete_state_never_repeats_of_strict_entropy_balance
    {State : Type*} (entropy : State → ℝ) (state : ℝ → State)
    (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hbalance : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      entropy (state t₂) - entropy (state t₁) =
        ∫ t in t₁..t₂, production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) : state t₂ ≠ state t₁ := by
  intro hsame
  have hentropy : entropy (state t₂) = entropy (state t₁) :=
    congrArg entropy hsame
  have hdiff := hbalance t₁ t₂ ht₁ ht₂ ht
  rw [hentropy] at hdiff
  have hpositive := hstrict t₁ t₂ ht₁ ht₂ ht
  linarith [hdiff]

/-- The complete-state form of Theorem 23's entropy clause. The a.e.
second-law inequality yields nondecreasing generalized entropy, while
Condition 23-A's strict integral inequality rules out recurrence. The entropy
functional is a single-valued function of the complete state, as required by
the source proof. The caller's `State` is intended to contain the physical,
all-layer, environment, memory, and history variables needed to make entropy
single-valued; it must not be enlarged by an artificial clock coordinate just
to force non-recurrence. Lean cannot decide that semantic exclusion from an
arbitrary type, so it remains part of the interpretation of this interface.
日本語要約：第二法則による非減少、条件23-Aによる厳密増加、および完全状態の非再帰をまとめる。 -/
theorem complete_state_entropy_and_nonrecurrence
    {State : Type*} (entropy : State → ℝ) (state : ℝ → State)
    (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hac : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval (fun t => entropy (state t)) t₁ t₂)
    (hproduction : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => entropy (state s)) t = production t)
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ entropy (state t₂) - entropy (state t₁) ∧
      0 < entropy (state t₂) - entropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hbalance := entropy_balance_and_nonnegative_production
    (fun t => entropy (state t)) production t₁ t₂ ht.le
    (hac t₁ t₂ ht₁ ht₂ ht)
    (hproduction t₁ t₂ ht₁ ht₂ ht)
    (hproductionNonnegative t₁ t₂ ht₁ ht₂ ht)
  refine ⟨?_, ?_, ?_⟩
  · rw [hbalance.1]
    exact hbalance.2
  · rw [hbalance.1]
    exact hstrict t₁ t₂ ht₁ ht₂ ht
  · exact complete_state_never_repeats_of_absolute_continuity entropy state
      production alive hstrict hac hproduction t₁ t₂ ht₁ ht₂ ht

/-- Intervalwise continuous production makes the strict-integral form of Condition 23-A
follow from local persistent activity: production is nonnegative throughout
each alive interval and is strictly positive at some point of that interval.
Combined with the a.e. entropy balance, this gives strict entropy growth and
nonrecurrence without postulating the integral inequality itself.
日本語要約：生成率の連続性・区間上の非負性と、各生存区間内で一度は正になる条件から条件23-Aを導き、非再帰を示す。-/
theorem complete_state_entropy_and_nonrecurrence_of_continuous_production
    {State : Type*} (entropy : State → ℝ) (state : ℝ → State)
    (production : ℝ → ℝ) (alive : Set ℝ)
    (hproductionContinuous : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn production (Set.Icc t₁ t₂))
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ production t)
    (hpersistentActivity : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∃ t, t ∈ Set.Icc t₁ t₂ ∧ 0 < production t)
    (hac : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval (fun t => entropy (state t)) t₁ t₂)
    (hproductionDerivative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => entropy (state s)) t = production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ entropy (state t₂) - entropy (state t₁) ∧
      0 < entropy (state t₂) - entropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hstrict : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, production t := by
    intro a b ha hb hab
    apply intervalIntegral.integral_pos hab
      (hproductionContinuous a b ha hb hab)
    · intro t hbt
      exact hproductionNonnegative a b ha hb hab t
        (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc hbt)
    · exact hpersistentActivity a b ha hb hab
  have hproductionNonnegativeAE : ∀ a b : ℝ, a ∈ alive → b ∈ alive →
      a < b → ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b → 0 ≤ production t := by
    intro a b ha hb hab
    exact Filter.Eventually.of_forall fun t ht =>
      hproductionNonnegative a b ha hb hab t ht
  exact complete_state_entropy_and_nonrecurrence entropy state production alive
    hstrict hac hproductionDerivative hproductionNonnegativeAE t₁ t₂ ht₁ ht₂ ht

/-- Data for the generalized entropy used in Theorem 23: physical entropy
plus a weighted sum of layer entropies. `Summable` over `ℝ` makes each
weighted layer series absolutely convergent (and hence its total entropy
well-defined). The balance law and its differentiability consequences remain
separate hypotheses, since they do not follow from summability alone.
日本語要約：物理エントロピー、層別エントロピー、正の重みと状態ごとの絶対収束をまとめるデータ構造。 -/
structure GeneralizedEntropyModel (State Layer : Type*) where
  physicalEntropy : State → ℝ
  layerEntropy : Layer → State → ℝ
  layerWeight : Layer → ℝ
  layerWeight_pos : ∀ a, 0 < layerWeight a
  weightedLayerTerms_summable : ∀ z,
    Summable (fun a => layerWeight a * layerEntropy a z)

/-- Total entropy production in the finite-layer specialization.
日本語要約：有限個の層の重み付き総エントロピー生成率を定義する。 -/
def finiteGeneralizedEntropyProduction
    {Layer : Type*} [Fintype Layer] (layerWeight : Layer → ℝ)
    (physicalProduction : ℝ → ℝ) (layerProduction : Layer → ℝ → ℝ)
    (t : ℝ) : ℝ :=
  physicalProduction t +
    ∑ layer : Layer, layerWeight layer * layerProduction layer t

/-- Nonnegative physical and layerwise production imply nonnegative total
production almost everywhere on a finite-layer interval. Positivity of every
layer weight is essential here.
日本語要約：各成分生成率のa.e.非負性と層重みの非負性から総生成率非負を導く。 -/
theorem finite_generalized_production_nonnegative_of_components
    {Layer : Type*} [Fintype Layer]
    (layerWeight : Layer → ℝ) (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (a b : ℝ)
    (hweight : ∀ layer, 0 ≤ layerWeight layer)
    (hphysical : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → 0 ≤ physicalProduction t)
    (hlayers : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → 0 ≤ layerProduction layer t) :
    ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        0 ≤ finiteGeneralizedEntropyProduction layerWeight
          physicalProduction layerProduction t := by
  have hAllLayers : ∀ᵐ t ∂MeasureTheory.volume,
      ∀ layer, t ∈ Set.uIcc a b → 0 ≤ layerProduction layer t :=
    MeasureTheory.ae_all_iff.mpr hlayers
  filter_upwards [hphysical, hAllLayers] with t hphys hlayersAt
  intro ht
  simp only [finiteGeneralizedEntropyProduction]
  apply add_nonneg (hphys ht)
  apply Finset.sum_nonneg
  intro layer hmem
  exact mul_nonneg (hweight layer) (hlayersAt layer ht)

/-- Package the componentwise second-law premises over every alive interval.
The result has exactly the a.e. production-sign interface accepted by the
finite-layer entropy/nonrecurrence theorem.
日本語要約：各生存区間での成分別第二法則を総生成率の符号条件へまとめる。 -/
theorem finite_generalized_production_nonnegative_on_alive
    {Layer : Type*} [Fintype Layer]
    (layerWeight : Layer → ℝ) (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hweight : ∀ layer, 0 ≤ layerWeight layer)
    (hphysical : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ physicalProduction t)
    (hlayers : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ layerProduction layer t) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          0 ≤ finiteGeneralizedEntropyProduction layerWeight
            physicalProduction layerProduction t := by
  intro t₁ t₂ ht₁ ht₂ ht
  exact finite_generalized_production_nonnegative_of_components
    layerWeight physicalProduction layerProduction t₁ t₂ hweight
    (hphysical t₁ t₂ ht₁ ht₂ ht)
    (fun layer => hlayers layer t₁ t₂ ht₁ ht₂ ht)

/-- For countably many layers, componentwise a.e. second-law inequalities
imply the same inequality for the total production. The summable derivative
majorant ensures that the weighted production series is genuinely summable
at almost every time, rather than relying on the default value of `tsum` for
divergent series.
日本語要約：可算各層のa.e.第二法則と一様可算和可能上界から、総生成率のa.e.非負性を導く。-/
theorem countable_generalized_production_nonnegative_on_alive
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (alive : Set ℝ)
    (hphysical : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ physicalProduction t)
    (hlayers : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ layerProduction layer t) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          0 ≤ physicalProduction t +
            ∑' layer, model.layerWeight layer * layerProduction layer t := by
  intro t₁ t₂ ht₁ ht₂ ht
  have hphysicalAE := hphysical t₁ t₂ ht₁ ht₂ ht
  have hlayersAE : ∀ᵐ t ∂MeasureTheory.volume,
      ∀ layer : Layer, t ∈ Set.uIcc t₁ t₂ →
        0 ≤ layerProduction layer t :=
    MeasureTheory.ae_all_iff.mpr (fun layer =>
      hlayers layer t₁ t₂ ht₁ ht₂ ht)
  filter_upwards [hphysicalAE, hlayersAE] with t hphys hlayersAt
  intro htmem
  have htermsNonneg : ∀ layer : Layer,
      0 ≤ model.layerWeight layer * layerProduction layer t := by
    intro layer
    exact mul_nonneg (le_of_lt (model.layerWeight_pos layer))
      (hlayersAt layer htmem)
  have htermsSummable : Summable
      (fun layer : Layer => model.layerWeight layer * layerProduction layer t) :=
    hboundSummable.of_norm_bounded (fun layer => hderivativeBound layer t)
  exact add_nonneg (hphys htmem) (tsum_nonneg htermsNonneg)

/-- In the finite-layer entropy model, componentwise continuity and
nonnegativity turn persistent activity of any one component into the strict
integral-production clause of Condition 23-A for the weighted total.
日本語要約：有限層で各成分が連続・非負なら、物理層または認知層の持続的活動から総生成率の区間積分が正と示す。-/
theorem finite_generalized_production_strict_integral_of_component_activity
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hphysicalContinuous : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn physicalProduction (Set.Icc t₁ t₂))
    (hlayerContinuous : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn (layerProduction layer) (Set.Icc t₁ t₂))
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ layerProduction layer t)
    (hactivity : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      (∃ t ∈ Set.Icc t₁ t₂, 0 < physicalProduction t) ∨
      ∃ layer t, t ∈ Set.Icc t₁ t₂ ∧ 0 < layerProduction layer t) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂,
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t := by
  intro t₁ t₂ ht₁ ht₂ ht
  have hcontinuous : ContinuousOn
      (finiteGeneralizedEntropyProduction model.layerWeight
        physicalProduction layerProduction) (Set.Icc t₁ t₂) := by
    unfold finiteGeneralizedEntropyProduction
    apply (hphysicalContinuous t₁ t₂ ht₁ ht₂ ht).add
    apply continuousOn_finsetSum
    intro layer _
    exact (hlayerContinuous layer t₁ t₂ ht₁ ht₂ ht).const_mul
      (model.layerWeight layer)
  apply intervalIntegral.integral_pos ht hcontinuous
  · intro t hti
    unfold finiteGeneralizedEntropyProduction
    apply add_nonneg (hphysicalNonnegative t₁ t₂ ht₁ ht₂ ht t
      (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc hti))
    apply Finset.sum_nonneg
    intro layer _
    exact mul_nonneg (model.layerWeight_pos layer).le
      (hlayerNonnegative layer t₁ t₂ ht₁ ht₂ ht t
        (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc hti))
  · rcases hactivity t₁ t₂ ht₁ ht₂ ht with hphys | hlayer
    · obtain ⟨t, htI, htpos⟩ := hphys
      refine ⟨t, htI, ?_⟩
      unfold finiteGeneralizedEntropyProduction
      have hsum : 0 ≤ ∑ layer : Layer,
          model.layerWeight layer * layerProduction layer t := by
        apply Finset.sum_nonneg
        intro layer _
        exact mul_nonneg (model.layerWeight_pos layer).le
          (hlayerNonnegative layer t₁ t₂ ht₁ ht₂ ht t
            (Set.Icc_subset_uIcc htI))
      linarith
    · obtain ⟨layer, t, htI, htpos⟩ := hlayer
      refine ⟨t, htI, ?_⟩
      unfold finiteGeneralizedEntropyProduction
      have hsum : 0 < ∑ i : Layer,
          model.layerWeight i * layerProduction i t := by
        have hterm : 0 < model.layerWeight layer * layerProduction layer t :=
          mul_pos (model.layerWeight_pos layer) htpos
        exact lt_of_lt_of_le hterm (Finset.single_le_sum
          (fun i _ => mul_nonneg (model.layerWeight_pos i).le
            (hlayerNonnegative i t₁ t₂ ht₁ ht₂ ht t
              (Set.Icc_subset_uIcc htI))) (Finset.mem_univ layer))
      have hphys : 0 ≤ physicalProduction t :=
        hphysicalNonnegative t₁ t₂ ht₁ ht₂ ht t (Set.Icc_subset_uIcc htI)
      linarith

/-- Countable-layer analogue of the finite component-activity result. A
uniform summable bound makes the weighted production series continuous on
each alive interval. If the physical layer or any one cognitive layer is
strictly active somewhere in that interval, nonnegativity of every other
component makes the total production integral strictly positive.
日本語要約：一様可算和可能上界で総生成率の連続性を得て、物理層またはいずれかの認知層の活動から条件23-Aを導く。-/
theorem countable_generalized_production_strict_integral_of_component_activity
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (alive : Set ℝ)
    (hphysicalContinuous : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn physicalProduction (Set.Icc t₁ t₂))
    (hlayerContinuous : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn (layerProduction layer) (Set.Icc t₁ t₂))
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ layerProduction layer t)
    (hactivity : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      (∃ t ∈ Set.Icc t₁ t₂, 0 < physicalProduction t) ∨
      ∃ layer t, t ∈ Set.Icc t₁ t₂ ∧ 0 < layerProduction layer t) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂,
        (physicalProduction t +
          ∑' layer, model.layerWeight layer * layerProduction layer t) := by
  intro t₁ t₂ ht₁ ht₂ ht
  let weightedProduction : Layer → ℝ → ℝ := fun layer t =>
    model.layerWeight layer * layerProduction layer t
  have hweightedContinuous : ∀ layer,
      ContinuousOn (weightedProduction layer) (Set.Icc t₁ t₂) := by
    intro layer
    exact (hlayerContinuous layer t₁ t₂ ht₁ ht₂ ht).const_mul
      (model.layerWeight layer)
  have htotalContinuous : ContinuousOn
      (fun t => physicalProduction t + ∑' layer, weightedProduction layer t)
      (Set.Icc t₁ t₂) := by
    apply (hphysicalContinuous t₁ t₂ ht₁ ht₂ ht).add
    exact continuousOn_tsum hweightedContinuous hboundSummable
      (fun layer t _ => hderivativeBound layer t)
  apply intervalIntegral.integral_pos ht htotalContinuous
  · intro t htIoc
    have hti : t ∈ Set.uIcc t₁ t₂ :=
      Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc htIoc
    have hphys := hphysicalNonnegative t₁ t₂ ht₁ ht₂ ht t hti
    have htermsNonnegative : ∀ layer,
        0 ≤ weightedProduction layer t := by
      intro layer
      exact mul_nonneg (model.layerWeight_pos layer).le
        (hlayerNonnegative layer t₁ t₂ ht₁ ht₂ ht t hti)
    exact add_nonneg hphys (tsum_nonneg htermsNonnegative)
  · rcases hactivity t₁ t₂ ht₁ ht₂ ht with hphysActivity | hlayerActivity
    · obtain ⟨t, htIcc, htpositive⟩ := hphysActivity
      refine ⟨t, htIcc, ?_⟩
      have htermsNonnegative : ∀ layer,
          0 ≤ weightedProduction layer t := by
        intro layer
        exact mul_nonneg (model.layerWeight_pos layer).le
          (hlayerNonnegative layer t₁ t₂ ht₁ ht₂ ht t
            (Set.Icc_subset_uIcc htIcc))
      have hsumNonnegative : 0 ≤ ∑' layer : Layer, weightedProduction layer t :=
        tsum_nonneg htermsNonnegative
      linarith
    · obtain ⟨layer, t, htIcc, htpositive⟩ := hlayerActivity
      refine ⟨t, htIcc, ?_⟩
      have htermsSummable : Summable (weightedProduction · t) :=
        hboundSummable.of_norm_bounded (fun i => hderivativeBound i t)
      have htermsNonnegative : ∀ i, 0 ≤ weightedProduction i t := by
        intro i
        exact mul_nonneg (model.layerWeight_pos i).le
          (hlayerNonnegative i t₁ t₂ ht₁ ht₂ ht t
            (Set.Icc_subset_uIcc htIcc))
      have htermPositive : 0 < weightedProduction layer t :=
        mul_pos (model.layerWeight_pos layer) htpositive
      have hsumPositive : 0 < ∑' i, weightedProduction i t :=
        htermsSummable.tsum_pos htermsNonnegative layer htermPositive
      have hphys : 0 ≤ physicalProduction t :=
        hphysicalNonnegative t₁ t₂ ht₁ ht₂ ht t (Set.Icc_subset_uIcc htIcc)
      linarith

/-- The state functional corresponding to physical entropy plus the
absolutely convergent weighted layer-entropy series.
日本語要約：物理エントロピーと収束する層別重み付き和から状態汎関数を定義する。 -/
noncomputable def GeneralizedEntropyModel.totalEntropy
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (z : State) : ℝ :=
  model.physicalEntropy z +
    ∑' a, model.layerWeight a * model.layerEntropy a z

/-- Finite partial sum of a countably infinite generalized entropy model,
using an explicit enumeration of all layers by natural numbers. -/
noncomputable def enumeratedPartialTotalEntropy
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (n : ℕ) (t : ℝ) : ℝ :=
  model.physicalEntropy (state t) +
    ∑ i : Fin n, model.layerWeight (enumeration i.val) *
      model.layerEntropy (enumeration i.val) (state t)

/-- The finite `Fin n` model induced by the first `n` layers of an enumeration. -/
noncomputable def enumeratedFiniteLayerModel
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (n : ℕ) :
    GeneralizedEntropyModel State (Fin n) where
  physicalEntropy := model.physicalEntropy
  layerEntropy i := model.layerEntropy (enumeration i.val)
  layerWeight i := model.layerWeight (enumeration i.val)
  layerWeight_pos i := model.layerWeight_pos (enumeration i.val)
  weightedLayerTerms_summable z := Summable.of_finite

/-- The production rate paired with `enumeratedPartialTotalEntropy`. -/
def enumeratedPartialTotalProduction
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  physicalProduction t +
    ∑ i : Fin n, model.layerWeight (enumeration i.val) *
      layerProduction (enumeration i.val) t

/-- The statewise absolute convergence built into `GeneralizedEntropyModel`
implies convergence of the enumerated finite-layer entropies at every time.
This supplies the endpoint-limit premise in the A6′ balance theorem directly
from the model definition (for countably infinite layers with an enumeration).
日本語要約：層と自然数の全単射のもとで、状態ごとの総和可能性から有限層エントロピー和の各時刻収束を導く。-/
theorem enumerated_partial_total_entropy_tendsto
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State) (t : ℝ) :
    Tendsto
      (fun n => enumeratedPartialTotalEntropy model enumeration state n t)
      atTop (𝓝 (model.totalEntropy (state t))) := by
  let term : Layer → ℝ := fun layer =>
    model.layerWeight layer * model.layerEntropy layer (state t)
  have hsumLayer : Summable term := model.weightedLayerTerms_summable (state t)
  have hsumNat : Summable (fun n => term (enumeration n)) :=
    hsumLayer.comp_injective enumeration.injective
  have htsum : (∑' layer, term layer) = ∑' n, term (enumeration n) := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      Equiv.tsum_eq enumeration.symm (fun n => term (enumeration n))
  have hpartial : Tendsto
      (fun n => model.physicalEntropy (state t) +
        ∑ k ∈ Finset.range n, term (enumeration k))
      atTop (𝓝 (model.physicalEntropy (state t) + ∑' n, term (enumeration n))) :=
    hsumNat.hasSum.tendsto_sum_nat.const_add (model.physicalEntropy (state t))
  convert hpartial using 1
  · ext n
    change model.physicalEntropy (state t) +
      (∑ i : Fin n, term (enumeration i.val)) =
        model.physicalEntropy (state t) +
          ∑ k ∈ Finset.range n, term (enumeration k)
    rw [Fin.sum_univ_eq_sum_range (fun k => term (enumeration k)) n]
  · simp [GeneralizedEntropyModel.totalEntropy, term, htsum]

/-- 有限個の層では、各成分の a.e. 微分式を足すと一般化総エントロピーの
微分式になる。成分の微分式自体は仮定であり、力学からは導かない。

With finitely many layers, componentwise a.e. derivative equations sum to
the derivative equation for generalized total entropy. The component
equations remain assumptions.
日本語要約：有限層の成分別微分式を足し、総エントロピーの微分式を導く。 -/
theorem finite_layer_total_entropy_derivative_of_component_derivatives
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (hphysical : ∀ᵐ t ∂MeasureTheory.volume,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t) :
    ∀ᵐ t ∂MeasureTheory.volume,
      deriv (fun s => model.physicalEntropy (state s) +
        ∑ layer : Layer, model.layerWeight layer *
          model.layerEntropy layer (state s)) t =
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t := by
  classical
  have hAllLayers : ∀ᵐ t ∂MeasureTheory.volume,
      ∀ layer, HasDerivAt
        (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t :=
    MeasureTheory.ae_all_iff.mpr hlayers
  filter_upwards [hphysical, hAllLayers] with t hphys hlayersAt
  have hsum : HasDerivAt
      (fun s => ∑ layer : Layer,
        model.layerWeight layer * model.layerEntropy layer (state s))
      (∑ layer : Layer,
        model.layerWeight layer * layerProduction layer t) t := by
    apply HasDerivAt.fun_sum (u := Finset.univ)
    intro layer _
    exact (hlayersAt layer).const_mul (model.layerWeight layer)
  have htotal : HasDerivAt
      (fun s => model.physicalEntropy (state s) +
        ∑ layer : Layer, model.layerWeight layer *
          model.layerEntropy layer (state s))
      (physicalProduction t +
        ∑ layer : Layer, model.layerWeight layer * layerProduction layer t) t := by
    exact hphys.add hsum
  simpa [finiteGeneralizedEntropyProduction] using htotal.deriv

/-- Explicitly identify the finite-layer derivative formula with the
`GeneralizedEntropyModel.totalEntropy` state functional. This is the direct
bridge needed to use componentwise balance laws in the complete-state form
of Theorem 23; no interchange of an infinite series and differentiation is
claimed.
日本語要約：有限層の成分微分式を、定義済みの総エントロピー汎関数の a.e. 微分式へ接続する。 -/
theorem finite_layer_model_total_entropy_derivative_of_component_derivatives
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (hphysical : ∀ᵐ t ∂MeasureTheory.volume,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t) :
    ∀ᵐ t ∂MeasureTheory.volume,
      deriv (fun s => model.totalEntropy (state s)) t =
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t := by
  have hfinite := finite_layer_total_entropy_derivative_of_component_derivatives
    model state physicalProduction layerProduction hphysical hlayers
  filter_upwards [hfinite] with t ht
  simpa [GeneralizedEntropyModel.totalEntropy, tsum_fintype,
    finiteGeneralizedEntropyProduction] using ht

/-- For countably many entropy layers, pointwise component differentiability
and a summable bound on every layer's production rate justify differentiating
the weighted entropy series term by term. The majorant is uniform in time.
This supplies an infinite-layer route to the balance law without asserting
that summability of entropy values alone permits exchanging differentiation
and `tsum`.
日本語要約：可算層で全時刻の成分微分式と、時刻一様な可算和可能上界を課すと、層和の微分を項別微分の和へ交換できる。値の総和可能性だけでは微分交換しない。-/
theorem countable_layer_model_total_entropy_derivative_of_component_derivatives
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hphysical : ∀ t,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t) :
    ∀ t, deriv (fun s => model.totalEntropy (state s)) t =
      physicalProduction t +
        ∑' layer, model.layerWeight layer * layerProduction layer t := by
  intro t
  have hseries : HasDerivAt
      (fun s => ∑' layer, model.layerWeight layer *
        model.layerEntropy layer (state s))
      (∑' layer, model.layerWeight layer * layerProduction layer t) t := by
    exact hasDerivAt_tsum
      (g := fun layer s => model.layerWeight layer *
        model.layerEntropy layer (state s))
      (g' := fun layer s => model.layerWeight layer * layerProduction layer s)
      hboundSummable
      (by
        intro layer s
        simpa using (hlayers layer s).const_mul (model.layerWeight layer))
      (by
        intro layer s
        exact hderivativeBound layer s)
      (model.weightedLayerTerms_summable (state 0)) t
  have htotal : HasDerivAt
      (fun s => model.physicalEntropy (state s) +
        ∑' layer, model.layerWeight layer * model.layerEntropy layer (state s))
      (physicalProduction t +
        ∑' layer, model.layerWeight layer * layerProduction layer t) t :=
    (hphysical t).add hseries
  simpa [GeneralizedEntropyModel.totalEntropy] using htotal.deriv

/-- Theorem 15's closed-system exchange equation (A7) cancels the cognitive
layer production in the derivative of generalized entropy. The conclusion is
`S_gen' = Π_gen` almost everywhere (here pointwise under stronger regularity).
The termwise differentiation route uses a summable uniform majorant, which is
stronger than the source paper's uniform-integrability premise A6′.
日本語要約：定理15のA7交換式と可算層項別微分から、総エントロピー微分が総生成率に等しいと導く。-/
theorem countable_layer_model_total_entropy_derivative_of_exchange_equation
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (totalProduction : ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hphysical : ∀ t,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t)
    (hA7 : ∀ t, physicalProduction t =
      -(∑' layer, model.layerWeight layer * layerProduction layer t) +
        totalProduction t) :
    ∀ t, deriv (fun s => model.totalEntropy (state s)) t =
      totalProduction t := by
  intro t
  rw [countable_layer_model_total_entropy_derivative_of_component_derivatives
    model state physicalProduction layerProduction derivativeBound
    hboundSummable hderivativeBound hphysical hlayers t, hA7 t]
  ring

/-- A6′'s uniform-integrability and almost-everywhere convergence premises
give convergence of finite production partial sums in L¹ on any finite
measure time domain. This is the Vitali step needed to weaken the stronger
uniform summable-majorant route above.
日本語要約：有限測度領域ではA6′の一様可積分性とa.e.収束から生成率部分和のL¹収束が従う。-/
theorem countable_layer_partial_rates_tendsto_L1_of_uniformIntegrable
    {Time : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (partialRate : ℕ → Time → ℝ) (totalRate : Time → ℝ)
    (hmeasurable : ∀ n,
      MeasureTheory.AEStronglyMeasurable (partialRate n)
        μ)
    (huniformIntegrable : MeasureTheory.UniformIntegrable partialRate 1 μ)
    (haeTendsto : ∀ᵐ t ∂μ,
      Tendsto (fun n => partialRate n t) atTop (𝓝 (totalRate t))) :
      Tendsto
      (fun n => MeasureTheory.eLpNorm
        (partialRate n - totalRate) 1 μ)
      atTop (𝓝 0) := by
  have htotalMemLp : MeasureTheory.MemLp totalRate 1 μ :=
    huniformIntegrable.memLp_of_ae_tendsto haeTendsto
  exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae
    (by norm_num) (by norm_num) hmeasurable htotalMemLp
    huniformIntegrable.unifIntegrable haeTendsto

/-- Passing finite-layer entropy balances to the limit using the A6′ Vitali
criterion. Endpoint convergence and L¹ convergence of the production rates
preserve the integrated balance for the countable total.
日本語要約：端点の部分和収束とA6′型の一様可積分性から、有限層の収支式を
可算層全体の積分収支へ移す。-/
theorem countable_layer_entropy_balance_of_uniformIntegrable
    {Time : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (partialEntropy : ℕ → ℝ → ℝ) (totalEntropy : ℝ → ℝ)
    (partialRate : ℕ → Time → ℝ) (totalRate : Time → ℝ)
    (a b : ℝ)
    (hmeasurable : ∀ n,
      MeasureTheory.AEStronglyMeasurable (partialRate n) μ)
    (huniformIntegrable : MeasureTheory.UniformIntegrable partialRate 1 μ)
    (haeTendsto : ∀ᵐ t ∂μ,
      Tendsto (fun n => partialRate n t) atTop (𝓝 (totalRate t)))
    (hstart : Tendsto (fun n => partialEntropy n a) atTop
      (𝓝 (totalEntropy a)))
    (hend : Tendsto (fun n => partialEntropy n b) atTop
      (𝓝 (totalEntropy b)))
    (hpartialBalance : ∀ n,
      partialEntropy n b - partialEntropy n a =
        ∫ t, partialRate n t ∂μ) :
    totalEntropy b - totalEntropy a = ∫ t, totalRate t ∂μ := by
  have hL1 := countable_layer_partial_rates_tendsto_L1_of_uniformIntegrable
    μ partialRate totalRate hmeasurable huniformIntegrable haeTendsto
  have hIntegral : Tendsto (fun n => ∫ t, partialRate n t ∂μ) atTop
      (𝓝 (∫ t, totalRate t ∂μ)) :=
    MeasureTheory.tendsto_integral_of_L1' totalRate
      (Filter.Eventually.of_forall fun n =>
        (huniformIntegrable.memLp n).integrable le_rfl)
      hL1
  have hEndpoints : Tendsto
      (fun n => partialEntropy n b - partialEntropy n a) atTop
      (𝓝 (totalEntropy b - totalEntropy a)) := hend.sub hstart
  have hEndpoints' : Tendsto (fun n => ∫ t, partialRate n t ∂μ) atTop
      (𝓝 (totalEntropy b - totalEntropy a)) := by
    apply Tendsto.congr' ?_ hEndpoints
    exact Filter.Eventually.of_forall fun n => hpartialBalance n
  exact (tendsto_nhds_unique hIntegral hEndpoints').symm

/-- A6′-style L¹ convergence now gives the integrated balance for an actual
`GeneralizedEntropyModel`: its endpoint limits come from the model's
statewise summability, so they are no longer separate assumptions. The
finite partial balance equations remain explicit inputs, as does the
identification of the limiting rate with the physical total production.
日本語要約：総エントロピーモデルの状態ごとの絶対収束で端点極限を補い、A6′型条件から総収支を導く。有限部分和の収支は仮定として残す。-/
theorem enumerated_countable_layer_entropy_balance_of_uniformIntegrable
    {State Layer Time : Type*} [Countable Layer] [MeasurableSpace Time]
    (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (partialRate : ℕ → Time → ℝ) (totalRate : Time → ℝ)
    (a b : ℝ)
    (hmeasurable : ∀ n,
      MeasureTheory.AEStronglyMeasurable (partialRate n) μ)
    (huniformIntegrable : MeasureTheory.UniformIntegrable partialRate 1 μ)
    (haeTendsto : ∀ᵐ t ∂μ,
      Tendsto (fun n => partialRate n t) atTop (𝓝 (totalRate t)))
    (hpartialBalance : ∀ n,
      enumeratedPartialTotalEntropy model enumeration state n b -
        enumeratedPartialTotalEntropy model enumeration state n a =
          ∫ t, partialRate n t ∂μ) :
    model.totalEntropy (state b) - model.totalEntropy (state a) =
      ∫ t, totalRate t ∂μ := by
  exact countable_layer_entropy_balance_of_uniformIntegrable
    μ (fun n t => enumeratedPartialTotalEntropy model enumeration state n t)
    (fun t => model.totalEntropy (state t)) partialRate totalRate a b
    hmeasurable huniformIntegrable haeTendsto
    (enumerated_partial_total_entropy_tendsto model enumeration state a)
    (enumerated_partial_total_entropy_tendsto model enumeration state b)
    hpartialBalance

/-- End-to-end (23.1) via the A6′-style route on a countably infinite layer
model. On each alive interval, finite-layer balances and uniform
integrability of the finite production rates yield the total entropy balance;
Condition 23-A then gives strict growth and rules out exact recurrence.
The interval measures must be finite, and the finite balances, a.e. limit,
uniform integrability, and strict production remain explicit inputs.
日本語要約：区間ごとのA6′型条件から総収支を導き、条件23-Aのもとで総エントロピーの厳密増加と完全状態の非再帰を示す。-/
theorem enumerated_countable_layer_nonrecurrence_of_uniformIntegrable
    {State Layer Time : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (alive : Set ℝ) [MeasurableSpace Time]
    (μ : ℝ → ℝ → MeasureTheory.Measure Time)
    (hfinite : ∀ a b, MeasureTheory.IsFiniteMeasure (μ a b))
    (partialRate : ℝ → ℝ → ℕ → Time → ℝ)
    (totalRate : ℝ → ℝ → Time → ℝ)
    (hmeasurable : ∀ a b n,
      MeasureTheory.AEStronglyMeasurable (partialRate a b n) (μ a b))
    (huniformIntegrable : ∀ a b,
      MeasureTheory.UniformIntegrable (partialRate a b) 1 (μ a b))
    (haeTendsto : ∀ a b,
      ∀ᵐ t ∂(μ a b),
        Tendsto (fun n => partialRate a b n t) atTop
          (𝓝 (totalRate a b t)))
    (hpartialBalance : ∀ a b n,
      enumeratedPartialTotalEntropy model enumeration state n b -
        enumeratedPartialTotalEntropy model enumeration state n a =
          ∫ t, partialRate a b n t ∂(μ a b))
    (hstrict : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t, totalRate a b t ∂(μ a b)) :
    ∀ a b, a ∈ alive → b ∈ alive → a < b →
      0 < model.totalEntropy (state b) - model.totalEntropy (state a) ∧
        state b ≠ state a := by
  intro a b ha hb hab
  letI : MeasureTheory.IsFiniteMeasure (μ a b) := hfinite a b
  have hbalance := enumerated_countable_layer_entropy_balance_of_uniformIntegrable
    model enumeration state (μ a b) (partialRate a b) (totalRate a b)
    a b (hmeasurable a b) (huniformIntegrable a b)
    (haeTendsto a b) (hpartialBalance a b)
  have hgrowth : 0 < model.totalEntropy (state b) -
      model.totalEntropy (state a) := by
    rw [hbalance]
    exact hstrict a b ha hb hab
  refine ⟨hgrowth, ?_⟩
  intro hsame
  have hentropy : model.totalEntropy (state b) =
      model.totalEntropy (state a) := congrArg model.totalEntropy hsame
  linarith

/-- A uniform summable bound on all weighted layer derivatives makes their
total entropy series globally Lipschitz, hence absolutely continuous on every
finite interval. Only the physical entropy's absolute continuity must still
be supplied separately when forming the complete generalized entropy.
日本語要約：層別生成率に時刻一様な可算和可能上界があれば、重み付き層エントロピー和は大域Lipschitzとなり、任意有限区間で絶対連続である。-/
theorem countable_layer_entropy_series_absolutely_continuous
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => ∑' layer, model.layerWeight layer *
        model.layerEntropy layer (state t)) a b := by
  have hboundNonneg : ∀ layer, 0 ≤ derivativeBound layer := by
    intro layer
    have h := hderivativeBound layer 0
    have hn := norm_nonneg
      (model.layerWeight layer * layerProduction layer 0)
    linarith
  have hsumBoundNonneg :
      0 ≤ (∑' layer : Layer, derivativeBound layer) :=
    tsum_nonneg hboundNonneg
  let C : NNReal :=
    ⟨(∑' layer : Layer, derivativeBound layer), hsumBoundNonneg⟩
  have hseries : ∀ t, HasDerivAt
      (fun s => ∑' layer, model.layerWeight layer *
        model.layerEntropy layer (state s))
      (∑' layer, model.layerWeight layer * layerProduction layer t) t := by
    intro t
    exact hasDerivAt_tsum
      (g := fun layer s => model.layerWeight layer *
        model.layerEntropy layer (state s))
      (g' := fun layer s => model.layerWeight layer * layerProduction layer s)
      hboundSummable
      (by
        intro layer s
        simpa using (hlayers layer s).const_mul (model.layerWeight layer))
      (by
        intro layer s
        exact hderivativeBound layer s)
      (model.weightedLayerTerms_summable (state 0)) t
  have hderivativeBoundTotal : ∀ t,
      ‖deriv (fun s => ∑' layer, model.layerWeight layer *
        model.layerEntropy layer (state s)) t‖₊ ≤ C := by
    intro t
    have hsummable : Summable
        (fun layer => model.layerWeight layer * layerProduction layer t) :=
      hboundSummable.of_norm_bounded (fun layer => hderivativeBound layer t)
    have hnorm : ‖∑' layer, model.layerWeight layer *
        layerProduction layer t‖ ≤ ∑' layer, derivativeBound layer := by
      calc
        _ ≤ ∑' layer, ‖model.layerWeight layer * layerProduction layer t‖ :=
          norm_tsum_le_tsum_norm hsummable.norm
        _ ≤ ∑' layer, derivativeBound layer :=
          hsummable.norm.tsum_le_tsum (fun layer => hderivativeBound layer t)
            hboundSummable
    rw [(hseries t).deriv]
    change ‖∑' layer, model.layerWeight layer *
        layerProduction layer t‖₊ ≤ ∑' layer, derivativeBound layer
    exact_mod_cast hnorm
  have hlipschitz : LipschitzWith C
      (fun t => ∑' layer, model.layerWeight layer *
        model.layerEntropy layer (state t)) :=
    lipschitzWith_of_nnnorm_deriv_le
      (fun t => (hseries t).differentiableAt) hderivativeBoundTotal
  exact hlipschitz.lipschitzOnWith.absolutelyContinuousOnInterval

/-- 有限層では、成分ごとの端点収支と区間積分可能性から総エントロピーの
収支を導く。各成分の収支は明示的な仮定として残る。

For finitely many entropy layers, componentwise endpoint balance laws sum to
the balance law for total entropy. Interval integrability is explicit; the
individual component balances remain assumptions.
日本語要約：成分の端点収支と可積分性から有限和の総収支を導く。 -/
theorem finite_layer_entropy_balance_of_component_balances
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ) (layerProduction : Layer → ℝ → ℝ)
    (a b : ℝ)
    (hphysical : model.physicalEntropy (state b) -
      model.physicalEntropy (state a) =
        ∫ t in a..b, physicalProduction t)
    (hlayers : ∀ layer,
      model.layerEntropy layer (state b) -
        model.layerEntropy layer (state a) =
          ∫ t in a..b, layerProduction layer t)
    (hphysicalInt : IntervalIntegrable physicalProduction
      MeasureTheory.volume a b)
    (hlayersInt : ∀ layer, IntervalIntegrable (layerProduction layer)
      MeasureTheory.volume a b) :
    model.totalEntropy (state b) - model.totalEntropy (state a) =
      ∫ t in a..b,
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t := by
  classical
  have hweightedInt (layer : Layer) :
      IntervalIntegrable
        (fun t => model.layerWeight layer * layerProduction layer t)
        MeasureTheory.volume a b :=
    (hlayersInt layer).const_mul (model.layerWeight layer)
  have hsumInt : IntervalIntegrable
      (∑ layer ∈ Finset.univ,
        fun t => model.layerWeight layer * layerProduction layer t)
      MeasureTheory.volume a b := by
    exact IntervalIntegrable.sum Finset.univ
      (fun layer _ => hweightedInt layer)
  have hsumLambda : IntervalIntegrable
      (fun t => ∑ layer : Layer,
        model.layerWeight layer * layerProduction layer t)
      MeasureTheory.volume a b := by
    apply hsumInt.congr
    intro t ht
    simp
  have hsumIntegral :
      (∑ layer : Layer, model.layerWeight layer *
        (∫ t in a..b, layerProduction layer t)) =
      ∫ t in a..b, ∑ layer : Layer,
        model.layerWeight layer * layerProduction layer t := by
    have h := intervalIntegral.integral_finsetSum
      (s := Finset.univ)
      (f := fun layer t => model.layerWeight layer * layerProduction layer t)
      (fun layer _ => hweightedInt layer)
    simpa [intervalIntegral.integral_const_mul] using h.symm
  have hendpointSum :
      (∑ layer : Layer, model.layerWeight layer *
        model.layerEntropy layer (state b)) -
      (∑ layer : Layer, model.layerWeight layer *
        model.layerEntropy layer (state a)) =
      ∑ layer : Layer, model.layerWeight layer *
        (model.layerEntropy layer (state b) -
          model.layerEntropy layer (state a)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro layer _
    ring
  calc
      model.totalEntropy (state b) - model.totalEntropy (state a) =
        (model.physicalEntropy (state b) - model.physicalEntropy (state a)) +
          ∑ layer : Layer, model.layerWeight layer *
            (model.layerEntropy layer (state b) -
              model.layerEntropy layer (state a)) := by
        simp only [GeneralizedEntropyModel.totalEntropy, tsum_fintype]
        rw [add_sub_add_comm, hendpointSum]
    _ = (∫ t in a..b, physicalProduction t) +
          ∑ layer : Layer, model.layerWeight layer *
            (∫ t in a..b, layerProduction layer t) := by
        rw [hphysical]
        congr 1
        apply Finset.sum_congr rfl
        intro layer _
        rw [hlayers layer]
    _ = ∫ t in a..b,
          finiteGeneralizedEntropyProduction model.layerWeight
            physicalProduction layerProduction t := by
        simp only [finiteGeneralizedEntropyProduction]
        rw [intervalIntegral.integral_add hphysicalInt hsumLambda]
        exact congrArg (fun x : ℝ =>
          (∫ t in a..b, physicalProduction t) + x) hsumIntegral

/-- 有限層の成分微分式から総エントロピー収支を導く。絶対連続性と a.e.
微分式から各端点収支を得て、有限和と積分可能性を使って総収支へまとめる。
成分の微分式自体は明示的な仮定である。

Finite-layer entropy balance from component differential laws. Absolute
continuity and the a.e. derivative equation give each endpoint balance;
finite additivity and interval integrability give the total balance.
日本語要約：各成分の絶対連続性・微分式から総エントロピーの端点収支を導く。 -/
theorem finite_layer_entropy_balance_of_component_derivatives
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ) (layerProduction : Layer → ℝ → ℝ)
    (a b : ℝ)
    (hphysicalAC : AbsolutelyContinuousOnInterval
      (fun t => model.physicalEntropy (state t)) a b)
    (hphysicalDeriv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.physicalEntropy (state s)) t =
          physicalProduction t)
    (hlayersAC : ∀ layer, AbsolutelyContinuousOnInterval
      (fun t => model.layerEntropy layer (state t)) a b)
    (hlayersDeriv : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.layerEntropy layer (state s)) t =
          layerProduction layer t)
    (hphysicalInt : IntervalIntegrable physicalProduction
      MeasureTheory.volume a b)
    (hlayersInt : ∀ layer, IntervalIntegrable (layerProduction layer)
      MeasureTheory.volume a b) :
    model.totalEntropy (state b) - model.totalEntropy (state a) =
      ∫ t in a..b,
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t := by
  apply finite_layer_entropy_balance_of_component_balances
    model state physicalProduction layerProduction a b
  · exact entropy_balance_of_absolute_continuity
      (fun t => model.physicalEntropy (state t)) physicalProduction a b
      hphysicalAC hphysicalDeriv
  · intro layer
    exact entropy_balance_of_absolute_continuity
      (fun t => model.layerEntropy layer (state t))
      (layerProduction layer) a b (hlayersAC layer) (hlayersDeriv layer)
  · exact hphysicalInt
  · exact hlayersInt

/-- The first `n` enumerated layers satisfy the finite entropy balance as soon
as each included component has its own absolute continuity and a.e.
derivative law. This derives the finite-balance premise used by the A6′ limit
route from component-level Theorem 15 balance data.
日本語要約：有限個の採用層について、各成分の絶対連続性・微分式から有限部分和の収支を導く。-/
theorem enumerated_partial_entropy_balance_of_component_derivatives
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (n : ℕ) (a b : ℝ)
    (hphysicalAC : AbsolutelyContinuousOnInterval
      (fun t => model.physicalEntropy (state t)) a b)
    (hphysicalDeriv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.physicalEntropy (state s)) t =
          physicalProduction t)
    (hlayersAC : ∀ layer, AbsolutelyContinuousOnInterval
      (fun t => model.layerEntropy layer (state t)) a b)
    (hlayersDeriv : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.layerEntropy layer (state s)) t =
          layerProduction layer t)
    (hphysicalInt : IntervalIntegrable physicalProduction
      MeasureTheory.volume a b)
    (hlayersInt : ∀ layer, IntervalIntegrable (layerProduction layer)
      MeasureTheory.volume a b) :
    enumeratedPartialTotalEntropy model enumeration state n b -
      enumeratedPartialTotalEntropy model enumeration state n a =
        ∫ t in a..b,
          enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n t := by
  let truncModel := enumeratedFiniteLayerModel model enumeration n
  have hfinite := finite_layer_entropy_balance_of_component_derivatives
    truncModel state physicalProduction
    (fun i => layerProduction (enumeration i.val)) a b hphysicalAC
    hphysicalDeriv (fun i => hlayersAC (enumeration i.val))
    (fun i => hlayersDeriv (enumeration i.val)) hphysicalInt
    (fun i => hlayersInt (enumeration i.val))
  calc
    enumeratedPartialTotalEntropy model enumeration state n b -
        enumeratedPartialTotalEntropy model enumeration state n a =
      truncModel.totalEntropy (state b) - truncModel.totalEntropy (state a) := by
        simp [truncModel, enumeratedPartialTotalEntropy,
          enumeratedFiniteLayerModel, GeneralizedEntropyModel.totalEntropy]
    _ = ∫ t in a..b,
        finiteGeneralizedEntropyProduction truncModel.layerWeight
          physicalProduction (fun i => layerProduction (enumeration i.val)) t :=
      hfinite
    _ = ∫ t in a..b,
        enumeratedPartialTotalProduction model enumeration
          physicalProduction layerProduction n t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp [finiteGeneralizedEntropyProduction,
        enumeratedPartialTotalProduction, truncModel,
        enumeratedFiniteLayerModel]

/-- Fully connected A6′-style proof of (23.1) for enumerated countably
infinite layers. The finite partial balances are derived from the component
derivative laws; the UI and a.e.-limit premises are imposed on the actual
finite weighted production sums over each alive interval. The interval measure
is the finite restriction of Lebesgue measure to `uIoc a b`.
日本語要約：成分別微分式から有限収支を導き、区間ごとのA6′型条件と23-Aを用いて可算層の総エントロピー厳密増加・非再帰を示す。-/
theorem enumerated_countable_layer_nonrecurrence_of_component_derivatives_and_uniformIntegrable
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (alive : Set ℝ)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (production : ℝ → ℝ)
    (hphysicalAC : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) a b)
    (hphysicalDeriv : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b →
          deriv (fun s => model.physicalEntropy (state s)) t =
            physicalProduction t)
    (hlayersAC : ∀ layer a b, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => model.layerEntropy layer (state t)) a b)
    (hlayersDeriv : ∀ layer a b, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b →
          deriv (fun s => model.layerEntropy layer (state s)) t =
            layerProduction layer t)
    (hphysicalInt : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      IntervalIntegrable physicalProduction MeasureTheory.volume a b)
    (hlayersInt : ∀ layer a b, a ∈ alive → b ∈ alive → a < b →
      IntervalIntegrable (layerProduction layer) MeasureTheory.volume a b)
    (huniformIntegrable : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      MeasureTheory.UniformIntegrable
        (fun n t => enumeratedPartialTotalProduction model enumeration
          physicalProduction layerProduction n t)
        1 (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (haeTendsto : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Tendsto
          (fun n => enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n t)
          atTop (𝓝 (production t)))
    (hstrict : ∀ a b, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, production t) :
    ∀ a b, a ∈ alive → b ∈ alive → a < b →
      0 < model.totalEntropy (state b) - model.totalEntropy (state a) ∧
        state b ≠ state a := by
  intro a b ha hb hab
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  have hpartialBalance : ∀ n,
      enumeratedPartialTotalEntropy model enumeration state n b -
        enumeratedPartialTotalEntropy model enumeration state n a =
          ∫ t, enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n t ∂μ := by
    intro n
    rw [← intervalIntegral_eq_integral_restrict_Ioc
      (enumeratedPartialTotalProduction model enumeration
        physicalProduction layerProduction n) a b hab.le]
    exact enumerated_partial_entropy_balance_of_component_derivatives
      model enumeration state physicalProduction layerProduction n a b
      (hphysicalAC a b ha hb hab) (hphysicalDeriv a b ha hb hab)
      (fun layer => hlayersAC layer a b ha hb hab)
      (fun layer => hlayersDeriv layer a b ha hb hab)
      (hphysicalInt a b ha hb hab)
      (fun layer => hlayersInt layer a b ha hb hab)
  have hbalance := enumerated_countable_layer_entropy_balance_of_uniformIntegrable
    model enumeration state μ
    (fun n t => enumeratedPartialTotalProduction model enumeration
      physicalProduction layerProduction n t)
    production a b
    (fun n => (huniformIntegrable a b ha hb hab).aestronglyMeasurable n)
    (huniformIntegrable a b ha hb hab) (haeTendsto a b ha hb hab)
    hpartialBalance
  have hstrictMeasure : 0 < ∫ t, production t ∂μ := by
    rw [← intervalIntegral_eq_integral_restrict_Ioc production a b hab.le]
    exact hstrict a b ha hb hab
  have hgrowth : 0 < model.totalEntropy (state b) -
      model.totalEntropy (state a) := by
    rw [hbalance]
    exact hstrictMeasure
  refine ⟨hgrowth, ?_⟩
  intro hsame
  have hentropy : model.totalEntropy (state b) =
      model.totalEntropy (state a) := congrArg model.totalEntropy hsame
  linarith

/-- Finite-layer form of Theorem 23's entropy clause. Component balances and
their interval integrability give the total balance on every alive interval;
Condition 23-A for the summed production then gives strict entropy growth and
rules out recurrence of the complete state. This is a finite-layer
specialization. Component balance laws remain explicit hypotheses, so this
does not claim to derive the omitted Theorem 15 dynamics.
日本語要約：有限層の総収支、第二法則、条件23-Aからエントロピー増加と完全状態非再帰を示す。 -/
theorem finite_layer_model_entropy_growth_and_nonrecurrence
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂,
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t)
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          0 ≤ finiteGeneralizedEntropyProduction model.layerWeight
            physicalProduction layerProduction t)
    (hphysicalBalance : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      model.physicalEntropy (state t₂) - model.physicalEntropy (state t₁) =
        ∫ t in t₁..t₂, physicalProduction t)
    (hlayerBalance : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      model.layerEntropy layer (state t₂) -
        model.layerEntropy layer (state t₁) =
          ∫ t in t₁..t₂, layerProduction layer t)
    (hphysicalIntegrable : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable physicalProduction MeasureTheory.volume t₁ t₂)
    (hlayerIntegrable : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable (layerProduction layer) MeasureTheory.volume t₁ t₂)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hbalance := finite_layer_entropy_balance_of_component_balances
    model state physicalProduction layerProduction t₁ t₂
    (hphysicalBalance t₁ t₂ ht₁ ht₂ ht)
    (fun layer => hlayerBalance layer t₁ t₂ ht₁ ht₂ ht)
    (hphysicalIntegrable t₁ t₂ ht₁ ht₂ ht)
    (fun layer => hlayerIntegrable layer t₁ t₂ ht₁ ht₂ ht)
  have hproductionNonnegativeOnRestrict :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc t₁ t₂)]
        (finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hproductionNonnegative t₁ t₂ ht₁ ht₂ ht] with t hprod
    intro htIcc
    exact hprod (Set.Icc_subset_uIcc htIcc)
  have hproductionIntegralNonnegative :=
    intervalIntegral.integral_nonneg_of_ae_restrict ht.le
      hproductionNonnegativeOnRestrict
  refine ⟨?_, ?_, ?_⟩
  · rw [hbalance]
    exact hproductionIntegralNonnegative
  · rw [hbalance]
    exact hstrict t₁ t₂ ht₁ ht₂ ht
  · intro hsame
    have hsameEntropy : model.totalEntropy (state t₂) =
        model.totalEntropy (state t₁) := congrArg model.totalEntropy hsame
    have hpositive := hstrict t₁ t₂ ht₁ ht₂ ht
    rw [← hbalance, hsameEntropy] at hpositive
    simp at hpositive

/-- Finite-layer entropy balances plus componentwise second laws and persistent
activity imply Theorem 23's strict entropy growth and nonrecurrence. The strict
integral condition on total production is derived from continuity and activity
of at least one component on every alive interval.
日本語要約：有限層の成分収支と成分別第二法則・持続的活動から、総生成率の厳密積分を導いて完全状態非再帰を示す。-/
theorem finite_layer_model_entropy_growth_and_nonrecurrence_of_component_activity
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hphysicalContinuous : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn physicalProduction (Set.Icc t₁ t₂))
    (hlayerContinuous : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
        ContinuousOn (layerProduction layer) (Set.Icc t₁ t₂))
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
        ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ layerProduction layer t)
    (hactivity : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      (∃ t ∈ Set.Icc t₁ t₂, 0 < physicalProduction t) ∨
      ∃ layer t, t ∈ Set.Icc t₁ t₂ ∧ 0 < layerProduction layer t)
    (hphysicalBalance : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      model.physicalEntropy (state t₂) - model.physicalEntropy (state t₁) =
        ∫ t in t₁..t₂, physicalProduction t)
    (hlayerBalance : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      model.layerEntropy layer (state t₂) - model.layerEntropy layer (state t₁) =
        ∫ t in t₁..t₂, layerProduction layer t)
    (hphysicalIntegrable : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable physicalProduction MeasureTheory.volume t₁ t₂)
    (hlayerIntegrable : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable (layerProduction layer) MeasureTheory.volume t₁ t₂)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hstrict := finite_generalized_production_strict_integral_of_component_activity
    model physicalProduction layerProduction alive hphysicalContinuous
    hlayerContinuous hphysicalNonnegative hlayerNonnegative hactivity
  have hproductionNonnegative := finite_generalized_production_nonnegative_on_alive
    model.layerWeight physicalProduction layerProduction alive
    (fun layer => (model.layerWeight_pos layer).le)
    (fun a b ha hb hab => Filter.Eventually.of_forall fun t ht =>
      hphysicalNonnegative a b ha hb hab t ht)
    (fun layer a b ha hb hab => Filter.Eventually.of_forall fun t ht =>
      hlayerNonnegative layer a b ha hb hab t ht)
  exact finite_layer_model_entropy_growth_and_nonrecurrence
    model state physicalProduction layerProduction alive hstrict
    hproductionNonnegative hphysicalBalance hlayerBalance
    hphysicalIntegrable hlayerIntegrable t₁ t₂ ht₁ ht₂ ht

/-- 有限層の各成分について絶対連続性と a.e. 微分式を仮定し、端点収支を
経由して定理23の厳密増加・非再帰を導く。微分式と積分可能性は入力であり、
省略された定理15の力学から自動的に従うとは主張しない。

End-to-end finite-layer form of Theorem 23's entropy conclusion from
component differential laws. The differential laws and interval
integrability remain explicit inputs.
日本語要約：有限層の成分微分式を総収支へ接続し厳密増加・非再帰を導く。 -/
theorem finite_layer_model_nonrecurrence_of_component_derivatives
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂,
        finiteGeneralizedEntropyProduction model.layerWeight
          physicalProduction layerProduction t)
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          0 ≤ finiteGeneralizedEntropyProduction model.layerWeight
            physicalProduction layerProduction t)
    (hphysicalAC : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) t₁ t₂)
    (hphysicalDeriv : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => model.physicalEntropy (state s)) t =
            physicalProduction t)
    (hlayersAC : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.layerEntropy layer (state t)) t₁ t₂)
    (hlayersDeriv : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => model.layerEntropy layer (state s)) t =
            layerProduction layer t)
    (hphysicalIntegrable : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable physicalProduction MeasureTheory.volume t₁ t₂)
    (hlayerIntegrable : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable (layerProduction layer) MeasureTheory.volume t₁ t₂)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  apply finite_layer_model_entropy_growth_and_nonrecurrence
    model state physicalProduction layerProduction alive hstrict
    hproductionNonnegative
  · intro a b ha hb hab
    exact entropy_balance_of_absolute_continuity
      (fun t => model.physicalEntropy (state t)) physicalProduction a b
      (hphysicalAC a b ha hb hab)
      (hphysicalDeriv a b ha hb hab)
  · intro layer a b ha hb hab
    exact entropy_balance_of_absolute_continuity
      (fun t => model.layerEntropy layer (state t))
      (layerProduction layer) a b (hlayersAC layer a b ha hb hab)
      (hlayersDeriv layer a b ha hb hab)
  · exact hphysicalIntegrable
  · exact hlayerIntegrable
  · exact ht₁
  · exact ht₂
  · exact ht

/-- Finite-layer differential form of Theorem 23 where Condition 23-A's strict
integral is derived from component activity. Componentwise continuity and
nonnegativity imply positivity of total production on each alive interval
once some physical or layer production is positive there.
日本語要約：成分微分式・絶対連続性に加え成分別の連続性・非負性と持続的活動から、有限層の厳密増加・非再帰を導く。-/
theorem finite_layer_model_nonrecurrence_of_component_derivatives_and_activity
    {State Layer : Type*} [Fintype Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ) (alive : Set ℝ)
    (hphysicalContinuous : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ContinuousOn physicalProduction (Set.Icc t₁ t₂))
    (hlayerContinuous : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
        ContinuousOn (layerProduction layer) (Set.Icc t₁ t₂))
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
        ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ layerProduction layer t)
    (hactivity : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      (∃ t ∈ Set.Icc t₁ t₂, 0 < physicalProduction t) ∨
      ∃ layer t, t ∈ Set.Icc t₁ t₂ ∧ 0 < layerProduction layer t)
    (hphysicalAC : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) t₁ t₂)
    (hphysicalDeriv : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => model.physicalEntropy (state s)) t =
            physicalProduction t)
    (hlayersAC : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.layerEntropy layer (state t)) t₁ t₂)
    (hlayersDeriv : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => model.layerEntropy layer (state s)) t =
            layerProduction layer t)
    (hphysicalIntegrable : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable physicalProduction MeasureTheory.volume t₁ t₂)
    (hlayerIntegrable : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      IntervalIntegrable (layerProduction layer) MeasureTheory.volume t₁ t₂)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hstrict := finite_generalized_production_strict_integral_of_component_activity
    model physicalProduction layerProduction alive hphysicalContinuous
    hlayerContinuous hphysicalNonnegative hlayerNonnegative hactivity
  have hproductionNonnegative := finite_generalized_production_nonnegative_on_alive
    model.layerWeight physicalProduction layerProduction alive
    (fun layer => (model.layerWeight_pos layer).le)
    (fun a b ha hb hab => Filter.Eventually.of_forall fun t ht =>
      hphysicalNonnegative a b ha hb hab t ht)
    (fun layer a b ha hb hab => Filter.Eventually.of_forall fun t ht =>
      hlayerNonnegative layer a b ha hb hab t ht)
  exact finite_layer_model_nonrecurrence_of_component_derivatives
    model state physicalProduction layerProduction alive hstrict
    hproductionNonnegative hphysicalAC hphysicalDeriv hlayersAC hlayersDeriv
    hphysicalIntegrable hlayerIntegrable t₁ t₂ ht₁ ht₂ ht

/-- Theorem 23's nonrecurrence conclusion specialized to an explicit
physical-plus-layer entropy model. The model supplies a well-defined
absolutely convergent series; absolute continuity, the entropy balance,
second-law sign, and strict production are still stated as hypotheses.
日本語要約：一般化エントロピーモデルの総和を完全状態の条件付き非再帰定理へつなぐ。 -/
theorem generalized_entropy_model_nonrecurrence
    {State Layer : Type*} (model : GeneralizedEntropyModel State Layer)
    (state : ℝ → State) (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hac : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.totalEntropy (state t)) t₁ t₂)
    (hproduction : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ →
          deriv (fun s => model.totalEntropy (state s)) t = production t)
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive →
      t₁ < t₂ → ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  exact complete_state_entropy_and_nonrecurrence model.totalEntropy state
    production alive hstrict hac hproduction hproductionNonnegative
    t₁ t₂ ht₁ ht₂ ht

/-- End-to-end infinite-layer specialization of Theorem 23.1. A countably
summable uniform bound and pointwise component derivative laws produce the
generalized entropy balance; absolute continuity, the second-law sign, and
Condition 23-A then give entropy growth and complete-state nonrecurrence.
日本語要約：無限可算層の一様微分上界と成分微分式から総収支を作り、絶対連続性・第二法則・条件23-Aの下で非再帰を結論する。-/
theorem countable_layer_model_nonrecurrence_of_component_derivatives
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hphysical : ∀ t,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t)
    (production : ℝ → ℝ)
    (hproductionDef : ∀ t, production t =
      physicalProduction t +
        ∑' layer, model.layerWeight layer * layerProduction layer t)
    (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hphysicalAC : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) t₁ t₂)
    (hproductionNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hproductionDerivative : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b →
          deriv (fun s => model.totalEntropy (state s)) t = production t := by
    intro a b ha hb hab
    have hderiv := countable_layer_model_total_entropy_derivative_of_component_derivatives
      model state physicalProduction layerProduction derivativeBound
      hboundSummable hderivativeBound hphysical hlayers
    filter_upwards [Filter.Eventually.of_forall hderiv] with t hderivAtT
    intro _
    rw [hproductionDef]
    exact hderivAtT
  have hac : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => model.totalEntropy (state t)) a b := by
    intro a b ha hb hab
    have hlayerAC := countable_layer_entropy_series_absolutely_continuous
      model state layerProduction derivativeBound hboundSummable
      hderivativeBound hlayers a b
    have hsumAC := (hphysicalAC a b ha hb hab).add hlayerAC
    exact hsumAC.congr (by
      intro t ht
      simp [GeneralizedEntropyModel.totalEntropy])
  exact generalized_entropy_model_nonrecurrence model state production alive
    hstrict hac hproductionDerivative hproductionNonnegative t₁ t₂ ht₁ ht₂ ht

/-- A real-valued entropy curve with an everywhere derivative and continuous
derivative on a compact interval is C¹ there, hence absolutely continuous.
This removes a separate absolute-continuity premise when the production rate
is already known to be continuous.
日本語要約：区間上で導関数が連続な全時刻微分可能関数の絶対連続性を示す。-/
theorem absolutely_continuous_of_hasDerivAt_continuousOn
    (f derivative : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hderiv : ∀ t, HasDerivAt f (derivative t) t)
    (hderivativeContinuous : ContinuousOn derivative (Set.Icc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  have hunique : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hderivOn : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt f (derivative t) (Set.Icc a b) t := by
    intro t ht
    exact (hderiv t).hasDerivWithinAt
  have hderivWithin : ∀ t ∈ Set.Icc a b,
      derivWithin f (Set.Icc a b) t = derivative t := by
    intro t ht
    exact (hderivOn t ht).derivWithin (hunique t ht)
  have hdiffOn : DifferentiableOn ℝ f (Set.Icc a b) := by
    intro t ht
    exact (hderiv t).differentiableAt.differentiableWithinAt
  have hderivWithinContinuous :
      ContinuousOn (derivWithin f (Set.Icc a b)) (Set.Icc a b) := by
    apply hderivativeContinuous.congr
    intro t ht
    exact hderivWithin t ht
  have hC1 : ContDiffOn ℝ 1 f (Set.Icc a b) :=
    (contDiffOn_one_iff_derivWithin hunique).2
      ⟨hdiffOn, hderivWithinContinuous⟩
  have hC1' : ContDiffOn ℝ 1 f (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab.le] using hC1
  exact hC1'.absolutelyContinuousOnInterval

/-- The countable-layer nonrecurrence theorem with the second law stated for
the physical and individual cognitive layers. Nonnegativity of the total
production is derived from those componentwise assumptions and the same
uniform summable majorant used for differentiation.
日本語要約：物理層・各認知層の第二法則から総生成率非負を導き、可算層の微分収支と合わせて非再帰を示す。-/
theorem countable_layer_model_nonrecurrence_of_component_derivatives_and_second_law
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hphysical : ∀ t,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t)
    (production : ℝ → ℝ)
    (hproductionDef : ∀ t, production t =
      physicalProduction t +
        ∑' layer, model.layerWeight layer * layerProduction layer t)
    (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hphysicalAC : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) t₁ t₂)
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ layerProduction layer t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hproductionExpressionNonnegative :=
    countable_generalized_production_nonnegative_on_alive
      model physicalProduction layerProduction derivativeBound hboundSummable
      hderivativeBound alive hphysicalNonnegative hlayerNonnegative
  have hproductionNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc t₁ t₂ → 0 ≤ production t := by
    intro a b ha hb hab
    filter_upwards
      [hproductionExpressionNonnegative a b ha hb hab] with t htprod
    intro htmem
    rw [hproductionDef]
    exact htprod htmem
  exact countable_layer_model_nonrecurrence_of_component_derivatives
    model state physicalProduction layerProduction derivativeBound
    hboundSummable hderivativeBound hphysical hlayers production hproductionDef
    alive hstrict hphysicalAC hproductionNonnegative t₁ t₂ ht₁ ht₂ ht

/-- A countable-layer end-to-end version of Theorem 23.1 in which both
parts of Condition 23-A are derived from component assumptions: continuity,
componentwise second-law inequalities, and activity of at least one component
on every alive interval. The derivative and uniform-majorant assumptions
still provide the entropy balance and continuity of total production.
日本語要約：層ごとの微分・連続性・第二法則・区間ごとの活動から条件23-Aを構成し、可算層総エントロピーの非再帰を導く。-/
theorem countable_layer_model_nonrecurrence_of_component_derivatives_and_activity
    {State Layer : Type*} [Countable Layer]
    (model : GeneralizedEntropyModel State Layer) (state : ℝ → State)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (derivativeBound : Layer → ℝ)
    (hboundSummable : Summable derivativeBound)
    (hderivativeBound : ∀ layer t,
      ‖model.layerWeight layer * layerProduction layer t‖ ≤
        derivativeBound layer)
    (hphysical : ∀ t,
      HasDerivAt (fun s => model.physicalEntropy (state s))
        (physicalProduction t) t)
    (hlayers : ∀ layer t,
      HasDerivAt (fun s => model.layerEntropy layer (state s))
        (layerProduction layer t) t)
    (totalProduction : ℝ → ℝ)
    (hA7 : ∀ t, physicalProduction t =
      -(∑' layer, model.layerWeight layer * layerProduction layer t) +
        totalProduction t)
    (alive : Set ℝ)
    (hphysicalContinuous : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ContinuousOn physicalProduction (Set.Icc t₁ t₂))
    (hlayerContinuous : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ContinuousOn (layerProduction layer) (Set.Icc t₁ t₂))
    (hphysicalNonnegative : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ physicalProduction t)
    (hlayerNonnegative : ∀ (layer : Layer) (t₁ t₂ : ℝ),
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      ∀ t ∈ Set.uIcc t₁ t₂, 0 ≤ layerProduction layer t)
    (hactivity : ∀ t₁ t₂ : ℝ,
      t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      (∃ t ∈ Set.Icc t₁ t₂, 0 < physicalProduction t) ∨
      ∃ layer t, t ∈ Set.Icc t₁ t₂ ∧ 0 < layerProduction layer t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) :
    0 ≤ model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      0 < model.totalEntropy (state t₂) - model.totalEntropy (state t₁) ∧
      state t₂ ≠ state t₁ := by
  have hproductionDef : ∀ t, totalProduction t =
      physicalProduction t +
        ∑' layer, model.layerWeight layer * layerProduction layer t := by
    intro t
    rw [hA7 t]
    ring
  have hstrictExpression :=
    countable_generalized_production_strict_integral_of_component_activity
      model physicalProduction layerProduction derivativeBound hboundSummable
      hderivativeBound alive hphysicalContinuous hlayerContinuous
      hphysicalNonnegative hlayerNonnegative hactivity
  have hstrict : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      0 < ∫ t in a..b, totalProduction t := by
    intro a b ha hb hab
    simpa only [hproductionDef] using hstrictExpression a b ha hb hab
  have hphysicalAE : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b → 0 ≤ physicalProduction t := by
    intro a b ha hb hab
    exact Filter.Eventually.of_forall (fun t ht =>
      hphysicalNonnegative a b ha hb hab t ht)
  have hlayerAE : ∀ (layer : Layer) (a b : ℝ),
      a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b → 0 ≤ layerProduction layer t := by
    intro layer a b ha hb hab
    exact Filter.Eventually.of_forall (fun t ht =>
      hlayerNonnegative layer a b ha hb hab t ht)
  have hproductionExpressionNonnegative :=
    countable_generalized_production_nonnegative_on_alive
      model physicalProduction layerProduction derivativeBound hboundSummable
      hderivativeBound alive hphysicalAE hlayerAE
  have hproductionNonnegative : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b → 0 ≤ totalProduction t := by
    intro a b ha hb hab
    filter_upwards [hproductionExpressionNonnegative a b ha hb hab] with t hprod
    intro htmem
    rw [hproductionDef]
    exact hprod htmem
  have hphysicalAC : ∀ a b : ℝ, a ∈ alive → b ∈ alive → a < b →
      AbsolutelyContinuousOnInterval
        (fun t => model.physicalEntropy (state t)) a b := by
    intro a b ha hb hab
    exact absolutely_continuous_of_hasDerivAt_continuousOn
      (fun t => model.physicalEntropy (state t)) physicalProduction a b hab
      hphysical (hphysicalContinuous a b ha hb hab)
  exact countable_layer_model_nonrecurrence_of_component_derivatives
    model state physicalProduction layerProduction derivativeBound
    hboundSummable hderivativeBound hphysical hlayers totalProduction hproductionDef
    alive hstrict hphysicalAC hproductionNonnegative t₁ t₂ ht₁ ht₂ ht


end Tomabechi.Theorem23
