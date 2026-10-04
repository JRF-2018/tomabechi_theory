import Tomabechi.Analysis.EntropyBalance
import Tomabechi.Dynamics.StageSwitching

/-!
# 定理15(I)：A6′型Vitali極限から一般化エントロピー収支へ

このモジュールは定理15の積分形を定理23の収支入口へ接続する。
物理エントロピーと認知層の端点部分和収支はA2/A5から有限段ごとに導き、A6′型
一様可積分性・a.e.収束で極限へ移す。A7交換式と符号条件は入力仮定として保持する。

原文監査：認知宇宙論§3.7のA6′(i)は各時刻での総和有限性、自由エネルギー論文の
別版では初期時刻での有限性と量化が異なる。主定理ではA6′(i)を軌道各時刻の総和
可能性として表現し、A6′(ii)の全有限部分集合族から列挙prefix列のUIを導く。
A7の物理・認知交換式自体は証明せず、独立仮定として用いる。
-/

namespace Tomabechi.Theorem15

open Filter
open scoped Topology

/-- A6′-type data on a fixed finite time measure: the enumerated finite
production sums are uniformly integrable and converge almost everywhere to
the full weighted layer rate. -/
structure A6PrimeIntervalData
    {Time : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time) (partialRate : ℕ → Time → ℝ)
    (totalRate : Time → ℝ) : Prop where
  measurable : ∀ n, MeasureTheory.AEStronglyMeasurable (partialRate n) μ
  uniformlyIntegrable : MeasureTheory.UniformIntegrable partialRate 1 μ
  aeConverges : ∀ᵐ t ∂μ,
    Tendsto (fun n => partialRate n t) atTop (𝓝 (totalRate t))

/-- A6′ quantifies uniform integrability over all finite layer subsets.
Restricting that family along any enumeration of finite prefixes preserves
uniform integrability. This packages the exact quantifier restriction needed
by the existing sequential Vitali theorem. -/
theorem uniformIntegrable_prefix_of_finiteFamily
    {Time Layer : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time)
    (finiteRate : Finset Layer → Time → ℝ)
    (prefixSet : ℕ → Finset Layer)
    (hfiniteUI : MeasureTheory.UniformIntegrable finiteRate 1 μ) :
    MeasureTheory.UniformIntegrable (fun n t => finiteRate (prefixSet n) t) 1 μ := by
  refine ⟨?_, ?_⟩
  · have hcriterion :=
    (MeasureTheory.unifIntegrable_iff (f := finiteRate)).mp hfiniteUI.1
    rw [MeasureTheory.unifIntegrable_iff]
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hcriterion ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n s hs
    exact hbound (prefixSet n) s hs
  · obtain ⟨C, hC⟩ := hfiniteUI.2
    refine ⟨C, fun n => ?_⟩
    simpa using hC (prefixSet n)

/-- Adding the fixed physical production rate to every finite cognitive
partial sum preserves UI. The MemLp premise for the physical rate follows
from the A5 absolute-continuity data together with integrability of its
derivative on the finite interval. -/
theorem uniformIntegrable_add_fixed_rate
    {Time Layer : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time)
    (cognitiveRate : Finset Layer → Time → ℝ)
    (physicalRate : Time → ℝ)
    (hUI : MeasureTheory.UniformIntegrable cognitiveRate 1 μ)
    (hphysical : MeasureTheory.MemLp physicalRate 1 μ) :
    MeasureTheory.UniformIntegrable
      (fun s t => physicalRate t + cognitiveRate s t) 1 μ := by
  have hphysicalConstant : MeasureTheory.UniformIntegrable
      (fun _ : Finset Layer => physicalRate) 1 μ :=
    MeasureTheory.uniformIntegrable_const (by norm_num) (by norm_num) hphysical
  refine ⟨?_, ?_⟩
  · have hsum := hphysicalConstant.unifIntegrable.add hUI.unifIntegrable
      (by norm_num)
    exact hsum.ae_eq fun s => Filter.Eventually.of_forall fun t => rfl
  · obtain ⟨C₁, hC₁⟩ := hphysicalConstant.2
    obtain ⟨C₂, hC₂⟩ := hUI.2
    refine ⟨C₁ + C₂, fun s => ?_⟩
    calc
      MeasureTheory.eLpNorm (physicalRate + cognitiveRate s) 1 μ ≤
          MeasureTheory.eLpNorm physicalRate 1 μ +
            MeasureTheory.eLpNorm (cognitiveRate s) 1 μ := by
              exact MeasureTheory.eLpNorm_add_le (by norm_num)
      _ ≤ ↑C₁ + ↑C₂ := add_le_add (hC₁ s) (hC₂ s)
      _ = ↑(C₁ + C₂) := by simp

/-- The arbitrary-finite-subset A6′ UI premise therefore supplies UI for any
enumerated sequence of cognitive prefixes after adjoining the physical rate. -/
theorem uniformIntegrable_enumerated_total_prefix_of_A6Prime
    {Time Layer : Type*} [MeasurableSpace Time] [DecidableEq Layer]
    (μ : MeasureTheory.Measure Time)
    (enumeration : ℕ ≃ Layer)
    (cognitiveRate : Finset Layer → Time → ℝ)
    (physicalRate : Time → ℝ)
    (prefixRate : ℕ → Time → ℝ)
    (hUI : MeasureTheory.UniformIntegrable cognitiveRate 1 μ)
    (hphysical : MeasureTheory.MemLp physicalRate 1 μ)
    (hprefix : ∀ n t,
      prefixRate n t =
        cognitiveRate (Finset.image enumeration (Finset.range n)) t) :
    MeasureTheory.UniformIntegrable
      (fun n t => physicalRate t + prefixRate n t) 1 μ := by
  have htotalFamily := uniformIntegrable_add_fixed_rate μ cognitiveRate
    physicalRate hUI hphysical
  have hprefixFamily := uniformIntegrable_prefix_of_finiteFamily μ
    (fun s t => physicalRate t + cognitiveRate s t)
    (fun n => Finset.image enumeration (Finset.range n)) htotalFamily
  exact hprefixFamily.ae_eq fun n => Filter.Eventually.of_forall fun t => by
    simpa [hprefix n t]

/-- Reindexing the first `n` terms of an enumeration is exactly summation over
its image finite set. -/
theorem sum_fin_enumeration_eq_sum_image
    {Layer : Type*} [DecidableEq Layer]
    (enumeration : ℕ ≃ Layer) (f : Layer → ℝ) (n : ℕ) :
    (∑ i : Fin n, f (enumeration i.val)) =
      ∑ a ∈ Finset.image enumeration (Finset.range n), f a := by
  classical
  apply Finset.sum_bij (fun i _ => enumeration i.val)
  · intro i hi
    exact Finset.mem_image.mpr
      ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩
  · intro i hi j hj heq
    exact Fin.ext (enumeration.injective heq)
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, hia⟩
    subst a
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
  · intro i hi
    rfl

/-- Pointwise summability of the layer entropy terms gives endpoint
convergence of their enumerated finite sums. This is the trajectory-local
form of A6′(i), so it does not require summability at states off the orbit. -/
theorem enumerated_tsum_partial_tendsto_of_summable
    {Layer : Type*} (enumeration : ℕ ≃ Layer) (f : Layer → ℝ)
    (hsummable : Summable f) :
    Tendsto (fun n => ∑ i : Fin n, f (enumeration i.val)) atTop
      (𝓝 (∑' layer, f layer)) := by
  have hnat : Summable (fun n => f (enumeration n)) :=
    hsummable.comp_injective enumeration.injective
  have htsum : (∑' layer, f layer) = ∑' n, f (enumeration n) := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      Equiv.tsum_eq enumeration.symm (fun n => f (enumeration n))
  convert hnat.hasSum.tendsto_sum_nat using 1
  · ext n
    exact Fin.sum_univ_eq_sum_range (fun k => f (enumeration k)) n
  · exact congrArg 𝓝 htsum

/-- Trajectory-local, end-to-end form of Theorem 15(I). It encodes A2/A5 as
absolute continuity, A6′(i) as summability along each trajectory time and
A6′(ii) as uniform integrability over *all* finite layer subsets plus a.e.
prefix convergence, and A7 as the exchange equation with nonnegative
integrable production (integrability follows from Vitali). No global
summability away from the trajectory is required. -/
theorem theorem15_trajectory_integral_balance
    {State Layer : Type*} [Countable Layer] [DecidableEq Layer]
    (enumeration : ℕ ≃ Layer)
    (physicalEntropy : State → ℝ)
    (layerEntropy : Layer → State → ℝ)
    (layerWeight : Layer → ℝ)
    (hweight : ∀ layer, 0 < layerWeight layer)
    (_hlayerNonnegative : ∀ layer z, 0 ≤ layerEntropy layer z)
    (state : ℝ → State) (a b : ℝ) (hab : a ≤ b)
    (hA2 : ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => layerEntropy layer (state t)) a b)
    (hA5 : AbsolutelyContinuousOnInterval
      (fun t => physicalEntropy (state t)) a b)
    (hA6finiteA : Summable (fun layer =>
      layerWeight layer * layerEntropy layer (state a)))
    (hA6finiteB : Summable (fun layer =>
      layerWeight layer * layerEntropy layer (state b)))
    (hA6UI : MeasureTheory.UniformIntegrable
      (fun s t => ∑ layer ∈ s,
        layerWeight layer * deriv (fun u => layerEntropy layer (state u)) t)
      1 (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hA6ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Tendsto
        (fun n => ∑ i : Fin n,
          layerWeight (enumeration i.val) *
            deriv (fun u => layerEntropy (enumeration i.val) (state u)) t)
        atTop (𝓝 (∑' layer,
          layerWeight layer * deriv (fun u => layerEntropy layer (state u)) t)))
    (totalProduction : ℝ → ℝ)
    (hA7 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      deriv (fun u => physicalEntropy (state u)) t =
        -(∑' layer, layerWeight layer *
          deriv (fun u => layerEntropy layer (state u)) t) +
          totalProduction t)
    (hA7nonnegative : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      totalProduction) :
    (physicalEntropy (state b) +
        ∑' layer, layerWeight layer * layerEntropy layer (state b)) -
      (physicalEntropy (state a) +
        ∑' layer, layerWeight layer * layerEntropy layer (state a)) =
        ∫ t in a..b, totalProduction t ∧
      0 ≤ ∫ t in a..b, totalProduction t := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  let physicalRate : ℝ → ℝ := fun t =>
    deriv (fun u => physicalEntropy (state u)) t
  let layerRate : Layer → ℝ → ℝ := fun layer t =>
    deriv (fun u => layerEntropy layer (state u)) t
  let partialCognitiveRate : ℕ → ℝ → ℝ := fun n t =>
    ∑ i : Fin n, layerWeight (enumeration i.val) *
      layerRate (enumeration i.val) t
  let totalCognitiveRate : ℝ → ℝ := fun t =>
    ∑' layer, layerWeight layer * layerRate layer t
  let partialRate : ℕ → ℝ → ℝ := fun n t =>
    physicalRate t + partialCognitiveRate n t
  let partialEntropy : ℕ → ℝ → ℝ := fun n t =>
    physicalEntropy (state t) +
      ∑ i : Fin n, layerWeight (enumeration i.val) *
        layerEntropy (enumeration i.val) (state t)
  let totalEntropy : ℝ → ℝ := fun t =>
    physicalEntropy (state t) +
      ∑' layer, layerWeight layer * layerEntropy layer (state t)
  have hphysicalInt : IntervalIntegrable physicalRate
      MeasureTheory.volume a b := by
    exact hA5.intervalIntegrable_deriv
  have hlayersInt : ∀ layer, IntervalIntegrable (layerRate layer)
      MeasureTheory.volume a b := fun layer => (hA2 layer).intervalIntegrable_deriv
  have hphysicalMemLp : MeasureTheory.MemLp physicalRate 1 μ := by
    rw [MeasureTheory.memLp_one_iff_integrable]
    change MeasureTheory.Integrable physicalRate μ
    exact hphysicalInt.def'
  have htotalUI : MeasureTheory.UniformIntegrable partialRate 1 μ := by
    have hpref := uniformIntegrable_enumerated_total_prefix_of_A6Prime μ
      enumeration
      (fun s t => ∑ layer ∈ s,
        layerWeight layer * layerRate layer t)
      physicalRate partialCognitiveRate hA6UI hphysicalMemLp
    have hprefix : ∀ n t,
        partialCognitiveRate n t =
          (fun s => ∑ layer ∈ s,
            layerWeight layer * layerRate layer t)
            (Finset.image enumeration (Finset.range n)) := by
      intro n t
      exact sum_fin_enumeration_eq_sum_image enumeration
        (fun layer => layerWeight layer * layerRate layer t) n
    simpa [partialRate] using hpref (hprefix := hprefix)
  have htotalRateTendsto : ∀ᵐ t ∂μ,
      Tendsto (fun n => partialRate n t) atTop
        (𝓝 (totalProduction t)) := by
    filter_upwards [hA6ae, hA7] with t hconv hswap
    have hcancel : physicalRate t + totalCognitiveRate t =
        totalProduction t := by
      change deriv (fun u => physicalEntropy (state u)) t +
          (∑' layer, layerWeight layer *
            deriv (fun u => layerEntropy layer (state u)) t) = _
      rw [hswap]
      ring
    rw [← hcancel]
    exact tendsto_const_nhds.add (by simpa [partialCognitiveRate, layerRate]
      using hconv)
  have hstart : Tendsto (fun n => partialEntropy n a) atTop
      (𝓝 (totalEntropy a)) := by
    have hsum := enumerated_tsum_partial_tendsto_of_summable enumeration
      (fun layer => layerWeight layer * layerEntropy layer (state a))
      hA6finiteA
    have hsum' := hsum.const_add (physicalEntropy (state a))
    simpa [partialEntropy, totalEntropy] using hsum'
  have hend : Tendsto (fun n => partialEntropy n b) atTop
      (𝓝 (totalEntropy b)) := by
    have hsum := enumerated_tsum_partial_tendsto_of_summable enumeration
      (fun layer => layerWeight layer * layerEntropy layer (state b))
      hA6finiteB
    have hsum' := hsum.const_add (physicalEntropy (state b))
    simpa [partialEntropy, totalEntropy] using hsum'
  have hpartialBalance : ∀ n,
      partialEntropy n b - partialEntropy n a =
        ∫ t, partialRate n t ∂μ := by
    intro n
    let finiteModel : Tomabechi.Theorem23.GeneralizedEntropyModel State (Fin n) := {
      physicalEntropy := physicalEntropy
      layerEntropy := fun i => layerEntropy (enumeration i.val)
      layerWeight := fun i => layerWeight (enumeration i.val)
      layerWeight_pos := fun i => hweight (enumeration i.val)
      weightedLayerTerms_summable := fun z => Summable.of_finite }
    have hphysDeriv : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b →
          deriv (fun s => finiteModel.physicalEntropy (state s)) t =
            physicalRate t := by
      filter_upwards [Filter.Eventually.of_forall fun t => rfl] with t ht
      intro _
      exact ht
    have hlayerDeriv : ∀ i, ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIcc a b →
          deriv (fun s => finiteModel.layerEntropy i (state s)) t =
            layerRate (enumeration i.val) t := by
      intro i
      filter_upwards [Filter.Eventually.of_forall fun t => rfl] with t ht
      intro _
      exact ht
    have hfinite :=
      Tomabechi.Theorem23.finite_layer_entropy_balance_of_component_derivatives
        finiteModel state physicalRate (fun i => layerRate (enumeration i.val)) a b
        hA5 hphysDeriv (fun i => hA2 (enumeration i.val)) hlayerDeriv
        hphysicalInt (fun i => hlayersInt (enumeration i.val))
    calc
      partialEntropy n b - partialEntropy n a =
          finiteModel.totalEntropy (state b) - finiteModel.totalEntropy (state a) := by
            simp [partialEntropy, finiteModel,
              Tomabechi.Theorem23.GeneralizedEntropyModel.totalEntropy]
      _ = ∫ t in a..b,
          Tomabechi.Theorem23.finiteGeneralizedEntropyProduction
            finiteModel.layerWeight physicalRate
            (fun i => layerRate (enumeration i.val)) t := hfinite
      _ = ∫ t in a..b, partialRate n t := by
        simp [partialRate, partialCognitiveRate,
          Tomabechi.Theorem23.finiteGeneralizedEntropyProduction,
          physicalRate, layerRate, finiteModel]
      _ = ∫ t, partialRate n t ∂μ := by
        rw [← Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
          (partialRate n) a b hab]
  have hbalance := Tomabechi.Theorem23.countable_layer_entropy_balance_of_uniformIntegrable
    μ partialEntropy totalEntropy partialRate totalProduction a b
    htotalUI.aestronglyMeasurable htotalUI htotalRateTendsto
    hstart hend hpartialBalance
  refine ⟨?_, ?_⟩
  · calc
      totalEntropy b - totalEntropy a = ∫ t, totalProduction t ∂μ := hbalance
      _ = ∫ t in a..b, totalProduction t := by
        symm
        exact Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
          totalProduction a b hab
  · rw [Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
      totalProduction a b hab]
    exact MeasureTheory.integral_nonneg_of_ae hA7nonnegative

/-- Finite-layer form of Theorem 15(I). The finite partial-sum limit is
immediate, and A2/A5 component balances plus the finite A7 exchange equation
give the same generalized entropy production balance. This complements the
enumerated countably-infinite theorem above. -/
theorem theorem15_finite_layer_integral_balance
    {State Layer : Type*} [Fintype Layer]
    (physicalEntropy : State → ℝ)
    (layerEntropy : Layer → State → ℝ)
    (layerWeight : Layer → ℝ)
    (hweight : ∀ layer, 0 < layerWeight layer)
    (_hlayerNonnegative : ∀ layer z, 0 ≤ layerEntropy layer z)
    (state : ℝ → State) (a b : ℝ) (hab : a ≤ b)
    (hA2 : ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => layerEntropy layer (state t)) a b)
    (hA5 : AbsolutelyContinuousOnInterval
      (fun t => physicalEntropy (state t)) a b)
    (totalProduction : ℝ → ℝ)
    (hA7 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      deriv (fun u => physicalEntropy (state u)) t =
        -(∑ layer, layerWeight layer *
          deriv (fun u => layerEntropy layer (state u)) t) +
          totalProduction t)
    (hA7nonnegative : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      totalProduction) :
    (physicalEntropy (state b) +
        ∑ layer, layerWeight layer * layerEntropy layer (state b)) -
      (physicalEntropy (state a) +
        ∑ layer, layerWeight layer * layerEntropy layer (state a)) =
        ∫ t in a..b, totalProduction t ∧
      0 ≤ ∫ t in a..b, totalProduction t := by
  let finiteModel : Tomabechi.Theorem23.GeneralizedEntropyModel State Layer := {
    physicalEntropy := physicalEntropy
    layerEntropy := layerEntropy
    layerWeight := layerWeight
    layerWeight_pos := hweight
    weightedLayerTerms_summable := fun _ => Summable.of_finite }
  let physicalRate : ℝ → ℝ := fun t =>
    deriv (fun u => physicalEntropy (state u)) t
  let layerRate : Layer → ℝ → ℝ := fun layer t =>
    deriv (fun u => layerEntropy layer (state u)) t
  have hphysicalDeriv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => finiteModel.physicalEntropy (state s)) t =
          physicalRate t := by
    filter_upwards [Filter.Eventually.of_forall fun t => rfl] with t ht
    intro _
    exact ht
  have hlayersDeriv : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => finiteModel.layerEntropy layer (state s)) t =
          layerRate layer t := by
    intro layer
    filter_upwards [Filter.Eventually.of_forall fun t => rfl] with t ht
    intro _
    exact ht
  have hfinite :=
    Tomabechi.Theorem23.finite_layer_entropy_balance_of_component_derivatives
      finiteModel state physicalRate layerRate a b hA5 hphysicalDeriv hA2
      hlayersDeriv hA5.intervalIntegrable_deriv
      (fun layer => (hA2 layer).intervalIntegrable_deriv)
  have hproductionEq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Tomabechi.Theorem23.finiteGeneralizedEntropyProduction layerWeight
        physicalRate layerRate t = totalProduction t := by
    filter_upwards [hA7] with t ht
    dsimp [Tomabechi.Theorem23.finiteGeneralizedEntropyProduction,
      physicalRate, layerRate]
    rw [ht]
    ring
  have hproductionIntegral :
      (∫ t in a..b,
        Tomabechi.Theorem23.finiteGeneralizedEntropyProduction
          layerWeight physicalRate layerRate t) =
        ∫ t in a..b, totalProduction t := by
    apply intervalIntegral.integral_congr_ae
    exact (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).1 hproductionEq
  have hbalance :
      (physicalEntropy (state b) +
        ∑ layer, layerWeight layer * layerEntropy layer (state b)) -
      (physicalEntropy (state a) +
        ∑ layer, layerWeight layer * layerEntropy layer (state a)) =
        ∫ t in a..b, totalProduction t := by
    calc
      _ = finiteModel.totalEntropy (state b) -
          finiteModel.totalEntropy (state a) := by
            simp [finiteModel, Tomabechi.Theorem23.GeneralizedEntropyModel.totalEntropy]
      _ = ∫ t in a..b,
          Tomabechi.Theorem23.finiteGeneralizedEntropyProduction
            layerWeight physicalRate layerRate t := hfinite
      _ = ∫ t in a..b, totalProduction t := hproductionIntegral
  refine ⟨hbalance, ?_⟩
  rw [Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
    totalProduction a b hab]
  exact MeasureTheory.integral_nonneg_of_ae hA7nonnegative

/-- The A7 exchange identity turns convergence of the finite cognitive-rate
prefixes into convergence of the finite generalized production rates. The
exchange equation remains an explicit almost-everywhere premise, as in the
source theorem. -/
theorem generalized_rate_tendsto_of_A7
    {Time : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time)
    (physicalProduction : Time → ℝ)
    (partialCognitiveRate : ℕ → Time → ℝ)
    (cognitiveRate totalProduction : Time → ℝ)
    (hA6converges : ∀ᵐ t ∂μ,
      Tendsto (fun n => partialCognitiveRate n t) atTop
        (𝓝 (cognitiveRate t)))
    (hA7 : ∀ᵐ t ∂μ,
      physicalProduction t = -cognitiveRate t + totalProduction t) :
    ∀ᵐ t ∂μ,
      Tendsto (fun n => physicalProduction t + partialCognitiveRate n t)
        atTop (𝓝 (totalProduction t)) := by
  filter_upwards [hA6converges, hA7] with t hconv hswap
  have hcancel : physicalProduction t + cognitiveRate t = totalProduction t := by
    rw [hswap]
    ring
  rw [← hcancel]
  exact tendsto_const_nhds.add hconv

/-- If every finite-layer truncation obeys its integrated balance, then A6′'s
Vitali condition yields the full generalized entropy balance. This is the
generic integral-form bridge used by Theorem 23. The end-to-end trajectory
theorem above derives the finite balances from A2/A5 and supplies the A6′/A7
rate convergence and prefix UI premises. -/
theorem generalized_entropy_balance_of_A6Prime
    {Time : Type*} [MeasurableSpace Time]
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (partialEntropy : ℕ → ℝ → ℝ) (totalEntropy : ℝ → ℝ)
    (partialRate : ℕ → Time → ℝ) (totalRate : Time → ℝ)
    (a b : ℝ)
    (hA6 : A6PrimeIntervalData μ partialRate totalRate)
    (hstart : Tendsto (fun n => partialEntropy n a) atTop
      (𝓝 (totalEntropy a)))
    (hend : Tendsto (fun n => partialEntropy n b) atTop
      (𝓝 (totalEntropy b)))
    (hpartialBalance : ∀ n,
      partialEntropy n b - partialEntropy n a =
        ∫ t, partialRate n t ∂μ) :
    totalEntropy b - totalEntropy a = ∫ t, totalRate t ∂μ := by
  exact Tomabechi.Theorem23.countable_layer_entropy_balance_of_uniformIntegrable
    μ partialEntropy totalEntropy partialRate totalRate a b
    hA6.measurable hA6.uniformlyIntegrable hA6.aeConverges
    hstart hend hpartialBalance

/-- Model-specific version: pointwise absolute convergence of the weighted
layer entropy series supplies the endpoint limits, while the finite
truncation balances and A6′ data supply the interval balance. -/
theorem model_generalized_entropy_balance_of_A6Prime
    {State Layer Time : Type*} [Countable Layer] [MeasurableSpace Time]
    (model : Tomabechi.Theorem23.GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (μ : MeasureTheory.Measure Time) [MeasureTheory.IsFiniteMeasure μ]
    (partialRate : ℕ → Time → ℝ) (totalRate : Time → ℝ)
    (a b : ℝ)
    (hA6 : A6PrimeIntervalData μ partialRate totalRate)
    (hpartialBalance : ∀ n,
      Tomabechi.Theorem23.enumeratedPartialTotalEntropy
          model enumeration state n b -
        Tomabechi.Theorem23.enumeratedPartialTotalEntropy
          model enumeration state n a = ∫ t, partialRate n t ∂μ) :
    model.totalEntropy (state b) - model.totalEntropy (state a) =
      ∫ t, totalRate t ∂μ := by
  exact Tomabechi.Theorem23.enumerated_countable_layer_entropy_balance_of_uniformIntegrable
    model enumeration state μ partialRate totalRate a b
    hA6.measurable hA6.uniformlyIntegrable hA6.aeConverges hpartialBalance

/-- Theorem 15(I) on a finite interval, from componentwise A2/A5 regularity,
the arbitrary-finite-subset A6′ hypotheses, and the A7 exchange equation.
Finite balances are generated from component derivatives; A6′ UI is first
restricted from all finite subsets to enumeration prefixes; A7 identifies
their a.e. rate limit with the physical total production. -/
theorem theorem15_integral_balance_of_A2_A5_A6Prime_A7
    {State Layer : Type*} [Countable Layer] [DecidableEq Layer]
    (model : Tomabechi.Theorem23.GeneralizedEntropyModel State Layer)
    (enumeration : ℕ ≃ Layer) (state : ℝ → State)
    (a b : ℝ) (hab : a ≤ b)
    (physicalProduction : ℝ → ℝ)
    (layerProduction : Layer → ℝ → ℝ)
    (totalProduction : ℝ → ℝ)
    (hphysicalAC : AbsolutelyContinuousOnInterval
      (fun t => model.physicalEntropy (state t)) a b)
    (hphysicalDeriv : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.physicalEntropy (state s)) t =
          physicalProduction t)
    (hlayersAC : ∀ layer,
      AbsolutelyContinuousOnInterval
        (fun t => model.layerEntropy layer (state t)) a b)
    (hlayersDeriv : ∀ layer, ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIcc a b →
        deriv (fun s => model.layerEntropy layer (state s)) t =
          layerProduction layer t)
    (hA6UI : MeasureTheory.UniformIntegrable
      (fun s t => ∑ layer ∈ s,
        model.layerWeight layer * layerProduction layer t) 1
      (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hA6ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      Tendsto
        (fun n => ∑ i : Fin n,
          model.layerWeight (enumeration i.val) *
            layerProduction (enumeration i.val) t)
        atTop (𝓝 (∑' layer,
          model.layerWeight layer * layerProduction layer t)))
    (hA7 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
      physicalProduction t =
        -(∑' layer, model.layerWeight layer * layerProduction layer t) +
          totalProduction t)
    (hA7nonnegative : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      totalProduction) :
    model.totalEntropy (state b) - model.totalEntropy (state a) =
        ∫ t in a..b, totalProduction t ∧
      0 ≤ ∫ t in a..b, totalProduction t := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  have hphysicalDerivRestrict :
      deriv (fun s => model.physicalEntropy (state s)) =ᵐ[μ]
        physicalProduction := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hphysicalDeriv] with t ht
    intro htIoc
    exact ht (Set.uIoc_subset_uIcc htIoc)
  have hphysicalInt : IntervalIntegrable physicalProduction
      MeasureTheory.volume a b :=
    hphysicalAC.intervalIntegrable_deriv.congr_ae hphysicalDerivRestrict
  have hlayersInt : ∀ layer, IntervalIntegrable (layerProduction layer)
      MeasureTheory.volume a b := by
    intro layer
    have hlayerDerivRestrict :
        deriv (fun s => model.layerEntropy layer (state s)) =ᵐ[μ]
          layerProduction layer := by
      apply (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
      filter_upwards [hlayersDeriv layer] with t ht
      intro htIoc
      exact ht (Set.uIoc_subset_uIcc htIoc)
    exact (hlayersAC layer).intervalIntegrable_deriv.congr_ae
      hlayerDerivRestrict
  have hphysicalMemLp : MeasureTheory.MemLp physicalProduction 1 μ := by
    rw [MeasureTheory.memLp_one_iff_integrable]
    change MeasureTheory.Integrable physicalProduction μ
    exact hphysicalInt.def'
  have hA6totalUI : MeasureTheory.UniformIntegrable
      (fun n t => physicalProduction t +
        ∑ i : Fin n, model.layerWeight (enumeration i.val) *
          layerProduction (enumeration i.val) t) 1 μ := by
    apply uniformIntegrable_enumerated_total_prefix_of_A6Prime μ
      enumeration
      (fun s t => ∑ layer ∈ s,
        model.layerWeight layer * layerProduction layer t)
      physicalProduction
      (fun n t => ∑ i : Fin n,
        model.layerWeight (enumeration i.val) *
          layerProduction (enumeration i.val) t)
      hA6UI hphysicalMemLp
    intro n t
    exact sum_fin_enumeration_eq_sum_image enumeration
      (fun layer => model.layerWeight layer * layerProduction layer t) n
  have hA6rate := generalized_rate_tendsto_of_A7 μ physicalProduction
    (fun n t => ∑ i : Fin n,
      model.layerWeight (enumeration i.val) *
        layerProduction (enumeration i.val) t)
    (fun t => ∑' layer,
      model.layerWeight layer * layerProduction layer t)
    totalProduction hA6ae hA7
  have hA6data : A6PrimeIntervalData μ
      (fun n t => physicalProduction t +
        ∑ i : Fin n, model.layerWeight (enumeration i.val) *
          layerProduction (enumeration i.val) t)
      totalProduction := by
    exact ⟨hA6totalUI.aestronglyMeasurable, hA6totalUI, hA6rate⟩
  have hpartialBalance : ∀ n,
      Tomabechi.Theorem23.enumeratedPartialTotalEntropy
          model enumeration state n b -
        Tomabechi.Theorem23.enumeratedPartialTotalEntropy
          model enumeration state n a =
        ∫ t,
          (physicalProduction t +
            ∑ i : Fin n, model.layerWeight (enumeration i.val) *
              layerProduction (enumeration i.val) t) ∂μ := by
    intro n
    calc
      _ = ∫ t in a..b,
          Tomabechi.Theorem23.enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n t :=
        Tomabechi.Theorem23.enumerated_partial_entropy_balance_of_component_derivatives
        model enumeration state physicalProduction layerProduction n a b
        hphysicalAC hphysicalDeriv hlayersAC hlayersDeriv hphysicalInt hlayersInt
      _ = ∫ t,
          Tomabechi.Theorem23.enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n t ∂μ := by
        rw [← Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
          (Tomabechi.Theorem23.enumeratedPartialTotalProduction model enumeration
            physicalProduction layerProduction n) a b hab]
      _ = ∫ t,
          (physicalProduction t +
            ∑ i : Fin n, model.layerWeight (enumeration i.val) *
              layerProduction (enumeration i.val) t) ∂μ := by
        rfl
  have hbalance := model_generalized_entropy_balance_of_A6Prime
    model enumeration state μ
    (fun n t => physicalProduction t +
      ∑ i : Fin n, model.layerWeight (enumeration i.val) *
        layerProduction (enumeration i.val) t)
    totalProduction a b hA6data hpartialBalance
  refine ⟨?_, ?_⟩
  · calc
      model.totalEntropy (state b) - model.totalEntropy (state a) =
          ∫ t, totalProduction t ∂μ := hbalance
      _ = ∫ t in a..b, totalProduction t := by
        symm
        exact Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
          totalProduction a b hab
  · rw [Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc
      totalProduction a b hab]
    exact MeasureTheory.integral_nonneg_of_ae hA7nonnegative

end Tomabechi.Theorem15
