import Theorem1

/-!
# 定理4：苫米地臨場感加重

臨場感 `P` と価値符号 `Q` による実効ポテンシャル `V₀ - κPQ` を定義し、
その正部分残差を持つ臨場感加重TCZスライスへの条件付き指数収束を示す。
下降条件・距離誤差境界は制御系から導出せず、原文の補題0条件として入力する。
-/

namespace Tomabechi.Theorem4

open MeasureTheory
open Filter
open scoped Topology

/-- 原文の臨場感加重実効ポテンシャル `Ṽ = V₀ - κPQ`。 -/
def effectivePotential (V₀ P Q κ : ℝ) : ℝ := V₀ - κ * P * Q

/-- 定理4の零残差 `[Ṽ - θP]₊`。 -/
def residual4 (V₀ P Q κ θP : ℝ) : ℝ :=
  Tomabechi.Theorem1.residual1 (effectivePotential V₀ P Q κ) θP

/-- `V₀ ≥ 0`, `P ∈ [0,1]`, `Q ∈ [-1,1]`, `κ > 0` なら原文の下限 `Ṽ ≥ -κ`。 -/
theorem effectivePotential_lower_bound
    (V₀ P Q κ : ℝ) (hV₀ : 0 ≤ V₀) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (_hQ0 : -1 ≤ Q) (hQ1 : Q ≤ 1) (hκ : 0 < κ) :
    -κ ≤ effectivePotential V₀ P Q κ := by
  unfold effectivePotential
  nlinarith [mul_nonneg (le_of_lt hκ) (show 1 - P * Q ≥ 0 by nlinarith)]

/-- 原文の `ΩP(t) = {x ∈ K | Ṽ(x,t) ≤ θP}`。基礎 `V₀` のTCZとは異なる。 -/
def weightedTCZ {X : Type*} (K : Set X) (V₀ P Q : X → ℝ → ℝ)
    (κ θP t : ℝ) : Set X :=
  {x | x ∈ K ∧ effectivePotential (V₀ x t) (P x t) (Q x t) κ ≤ θP}

/-- 定理4の条件付き定量結論。実効残差の絶対連続性、指数散逸、
臨場感加重TCZスライスへの誤差境界を仮定し、距離の指数評価を得る。
反復ホライズン最適性だけからこれらの条件が出るとは主張しない。 -/
theorem weighted_tcz_exponential_decay
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ P Q : X → ℝ → ℝ)
    (κ θP c C t₀ t : ℝ)
    (hTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t,
      (weightedTCZ K V₀ P Q κ θP s).Nonempty)
    (hresidual_ac : AbsolutelyContinuousOnInterval
      (fun s => residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
        (Q (trajectory s) s) κ θP) t₀ t)
    (hdecay_ae : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (fun r => residual4 (V₀ (trajectory r) r) (P (trajectory r) r)
        (Q (trajectory r) r) κ θP) s ≤
      -2 * c * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
        (Q (trajectory s) s) κ θP)
    (herror : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (weightedTCZ K V₀ P Q κ θP s)) ^ 2 ≤
        C * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t) :
    Metric.infDist (trajectory t) (weightedTCZ K V₀ P Q κ θP t) ≤
      Real.sqrt (C * residual4 (V₀ (trajectory t₀) t₀)
        (P (trajectory t₀) t₀) (Q (trajectory t₀) t₀) κ θP) *
        Real.exp (-c * (t - t₀)) := by
  exact Tomabechi.Theorem1.individual_tcz_distance_decay_of_ac_ae_derivative
    trajectory (weightedTCZ K V₀ P Q κ θP)
    (fun s => residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
      (Q (trajectory s) s) κ θP)
    c C t₀ t hc hC ht hTCZ_nonempty hresidual_ac
    (fun s _ => show 0 ≤ residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
      (Q (trajectory s) s) κ θP from by
        simp [residual4, Tomabechi.Theorem1.residual1]) hdecay_ae herror

/-- 区間ごとの定理4の指数距離評価を全ての有限終端時刻へ適用し、臨場感加重TCZへの
距離の極限も得る。各有限区間の残差正則性・下降・距離誤差を要求し、定理4の定量結論
からそのまま極限へ進む。 -/
theorem weighted_tcz_distance_tendsto_zero
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (K : Set X) (V₀ P Q : X → ℝ → ℝ)
    (κ θP c C t₀ : ℝ)
    (hTCZ_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (weightedTCZ K V₀ P Q κ θP s).Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual4 (V₀ (trajectory r) r) (P (trajectory r) r)
          (Q (trajectory r) r) κ θP) s ≤
        -2 * c * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (trajectory s) (weightedTCZ K V₀ P Q κ θP s)) ^ 2 ≤
        C * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP)
    (hc : 0 < c) (hC : 0 < C) :
    Filter.Tendsto (fun t => Metric.infDist (trajectory t)
      (weightedTCZ K V₀ P Q κ θP t)) atTop (𝓝 0) := by
  let distance : ℝ → ℝ := fun t => Metric.infDist (trajectory t)
    (weightedTCZ K V₀ P Q κ θP t)
  have hbound : ∀ T, t₀ ≤ T →
      distance T ≤ Real.sqrt (C * residual4 (V₀ (trajectory t₀) t₀)
        (P (trajectory t₀) t₀) (Q (trajectory t₀) t₀) κ θP) *
        Real.exp (-c * (T - t₀)) := by
    intro T hT
    exact weighted_tcz_exponential_decay trajectory K V₀ P Q κ θP c C
      t₀ T (hTCZ_nonempty T hT) (hresidual_ac T hT) (hdecay_ae T hT)
      (herror T hT) hc hC hT
  have hnonneg : ∀ t, 0 ≤ distance t := fun t => Metric.infDist_nonneg
  exact Tomabechi.Theorem1.tendsto_zero_of_exponential_majorant distance
    (Real.sqrt (C * residual4 (V₀ (trajectory t₀) t₀)
      (P (trajectory t₀) t₀) (Q (trajectory t₀) t₀) κ θP)) c t₀
    hbound hnonneg hc

/-- Theorem 4 with the closed-loop reachable closure constructed from the
selected policy's time-indexed reachable sets. The policy dynamics supply the
reachable-set witnesses; descent and the weighted error bound remain explicit
inputs and are not inferred from finite-horizon optimality.
日本語要約：閉到達集合内の加重TCZの非空性から指数距離評価と極限を得る。
同じ時刻の実到達点が閾値以下になることは要求しない。 -/
theorem weighted_reachable_tcz_distance_tendsto_zero
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (reachableAt : ℝ → Set X)
    (V₀ P Q : X → ℝ → ℝ) (κ θP c C t₀ : ℝ)
    (htrajectory_reachable : ∀ t, t₀ ≤ t → trajectory t ∈ reachableAt t)
    (hreachable_tcz_nonempty : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
        V₀ P Q κ θP s).Nonempty)
    (hresidual_ac : ∀ T, t₀ ≤ T →
      AbsolutelyContinuousOnInterval
        (fun s => residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP) t₀ T)
    (hdecay_ae : ∀ T, t₀ ≤ T →
      ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
        deriv (fun r => residual4 (V₀ (trajectory r) r) (P (trajectory r) r)
          (Q (trajectory r) r) κ θP) s ≤
        -2 * c * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP)
    (herror : ∀ T, t₀ ≤ T → ∀ s ∈ Set.Icc t₀ T,
      (Metric.infDist (trajectory s)
        (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          V₀ P Q κ θP s)) ^ 2 ≤
        C * residual4 (V₀ (trajectory s) s) (P (trajectory s) s)
          (Q (trajectory s) s) κ θP)
    (ht₀ : 0 ≤ t₀) (hc : 0 < c) (hC : 0 < C) :
    (∀ t, t₀ ≤ t →
      trajectory t ∈ Tomabechi.Theorem1.closedLoopReachableSet reachableAt) ∧
      (∀ t, t₀ ≤ t → Metric.infDist (trajectory t)
        (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          V₀ P Q κ θP t) ≤
          Real.sqrt (C * residual4 (V₀ (trajectory t₀) t₀)
            (P (trajectory t₀) t₀) (Q (trajectory t₀) t₀) κ θP) *
            Real.exp (-c * (t - t₀))) ∧
      Filter.Tendsto (fun t => Metric.infDist (trajectory t)
        (weightedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt)
          V₀ P Q κ θP t)) atTop (𝓝 0) := by
  have hcore := Tomabechi.Theorem1.theorem1_reachable_tcz_distance_tendsto_zero
    trajectory reachableAt
    (fun x t => effectivePotential (V₀ x t) (P x t) (Q x t) κ) θP c C t₀
    htrajectory_reachable hreachable_tcz_nonempty hresidual_ac ?_ ?_ ht₀ hc hC
  · exact hcore
  · intro T hT
    filter_upwards [hdecay_ae T hT] with s hs
    simpa [residual4] using hs
  · intro T hT s hs
    simpa [weightedTCZ, effectivePotential, residual4] using herror T hT s hs

/-- Qを固定したP偏微分。PとQが同時に変化する経路の全微分とは区別する。 -/
theorem effectivePotential_hasDerivAt_P
    (V₀ Q κ P : ℝ) :
    HasDerivAt (fun p : ℝ => effectivePotential V₀ p Q κ) (-κ * Q) P := by
  convert (hasDerivAt_const P V₀).sub
    ((hasDerivAt_id P).const_mul (κ * Q)) using 1
  · funext p
    simp [effectivePotential]
    ring
  · ring

/-- `Q` の符号ごとの臨場感効果。 -/
theorem effectivePotential_P_monotonicity
    (V₀ Q κ P₁ P₂ : ℝ) (hκ : 0 < κ) (hP : P₁ ≤ P₂) :
    (Q ≥ 0 → effectivePotential V₀ P₂ Q κ ≤ effectivePotential V₀ P₁ Q κ) ∧
    (Q ≤ 0 → effectivePotential V₀ P₁ Q κ ≤ effectivePotential V₀ P₂ Q κ) := by
  constructor
  · intro hQ
    unfold effectivePotential
    nlinarith [mul_nonneg (le_of_lt hκ) (mul_nonneg (sub_nonneg.mpr hP) hQ)]
  · intro hQ
    unfold effectivePotential
    nlinarith [mul_nonneg (le_of_lt hκ)
      (mul_nonneg (sub_nonneg.mpr hP) (neg_nonneg.mpr hQ))]

end Tomabechi.Theorem4

#print axioms Tomabechi.Theorem4.weighted_tcz_exponential_decay
#print axioms Tomabechi.Theorem4.weighted_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem4.weighted_reachable_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem4.effectivePotential_hasDerivAt_P
