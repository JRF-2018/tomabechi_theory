import Tomabechi.Consistency.ConsistencyR123_NativeNondegenerate

/-!
# 定理4の値域条件と sup／Euclid 距離の比較

* **定理4の値域（M6.1）：** `P = exp(−F) ∈ (0,1]`、`Q = 1 ∈ [−1,1]`、`κ = 1` で
  `Ṽ = V₀ − κPQ ≥ −κ`（実際は `Ṽ ≥ 0`）。
* **定理1–4と20の距離の統一：** 1–4 は状態空間 `AgentState`（ℝ² の sup 距離）で、
  20 は同じ状態の Euclid 座標（`c1EuclideanCoordinates`）の距離で誤差を述べていた。
  ℝ² では `‖·‖_∞ ≤ ‖·‖₂ ≤ √2 ‖·‖_∞` なので、集合への距離は
  `infDist_sup ≤ infDist_Euclid ≤ √2 · infDist_sup`。1–4 の二乗誤差境界を Euclid 距離で
  述べ直すと定数が 2 倍になる（`SharedNormUnification`）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Theorem1 Tomabechi.Theorem4
open Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Examples.Theorem2

/-! ## 定理4の値域 -/

theorem commonBasePresenceP_mem (x : AgentState) (t : ℝ) :
    commonBasePresenceP x t ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  have := consensusPresence_potential_nonneg x 0
  linarith

theorem commonBasePresenceQ_mem (x : AgentState) (t : ℝ) :
    commonBasePresenceQ x t ∈ Set.Icc (-1 : ℝ) 1 := by
  simp [commonBasePresenceQ]

/-- `κ = 1` で `Ṽ = V₀ − κ P Q ≥ −κ`（実際は 0 以上）。 -/
theorem commonBase_tildeV_ge (x : AgentState) (t : ℝ) :
    -(1 : ℝ) ≤ commonBaseV0 x t - 1 * commonBasePresenceP x t * commonBasePresenceQ x t := by
  have hP := commonBasePresenceP_mem x t
  have hV := commonBaseV0_positive x t
  simp only [commonBasePresenceQ, mul_one]
  nlinarith [hP.2]

/-! ## sup 距離と Euclid 距離の比較 -/

theorem c1EuclideanCoordinates_symm_eq (y : AgentState) :
    c1EuclideanCoordinates.symm y = (WithLp.toLp 2 y : C1EuclideanAgentState) :=
  (ContinuousLinearEquiv.symm_apply_eq _).mpr (c1EuclideanCoordinates_toLp y).symm

theorem dist_sup_le_dist_euclid (y a : AgentState) :
    dist y a ≤ dist (WithLp.toLp 2 y : C1EuclideanAgentState) (WithLp.toLp 2 a) := by
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  rw [PiLp.dist_eq_of_L2]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun j : Fin 2 => dist (y j) (a j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem dist_euclid_le_sqrt_two_mul_dist_sup (y a : AgentState) :
    dist (WithLp.toLp 2 y : C1EuclideanAgentState) (WithLp.toLp 2 a) ≤
      Real.sqrt 2 * dist y a := by
  rw [PiLp.dist_eq_of_L2, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num), Fin.sum_univ_two]
  have h0 : dist (y 0) (a 0) ^ 2 ≤ dist y a ^ 2 :=
    pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist y a 0) 2
  have h1 : dist (y 1) (a 1) ^ 2 ≤ dist y a ^ 2 :=
    pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist y a 1) 2
  linarith

/-- 集合への距離：`infDist_sup ≤ infDist_Euclid ≤ √2 · infDist_sup`。 -/
theorem infDist_euclid_le (A : Set AgentState) (y : AgentState) :
    Metric.infDist (WithLp.toLp 2 y : C1EuclideanAgentState)
        ((fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState)) '' A) ≤
      Real.sqrt 2 * Metric.infDist y A := by
  by_cases hA : A.Nonempty
  · have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
    have : Metric.infDist (WithLp.toLp 2 y : C1EuclideanAgentState)
        ((fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState)) '' A) / Real.sqrt 2 ≤
        Metric.infDist y A := by
      rw [Metric.le_infDist hA]
      intro a ha
      rw [div_le_iff₀ hs, mul_comm]
      exact (Metric.infDist_le_dist_of_mem
        (Set.mem_image_of_mem (fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState))
          ha)).trans
        (dist_euclid_le_sqrt_two_mul_dist_sup y a)
    rw [div_le_iff₀ hs, mul_comm] at this
    exact this
  · rw [Set.not_nonempty_iff_eq_empty.mp hA]
    simp

theorem infDist_sup_le (A : Set AgentState) (y : AgentState) :
    Metric.infDist y A ≤ Metric.infDist (WithLp.toLp 2 y : C1EuclideanAgentState)
        ((fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState)) '' A) := by
  by_cases hA : A.Nonempty
  · rw [Metric.le_infDist (hA.image _)]
    rintro _ ⟨a, ha, rfl⟩
    exact (Metric.infDist_le_dist_of_mem ha).trans (dist_sup_le_dist_euclid y a)
  · rw [Set.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- 二乗誤差境界を Euclid 距離で述べ直すと定数が 2 倍になる。 -/
theorem euclid_sq_error_of_sup (A : Set AgentState) (y : AgentState) (B : ℝ)
    (h : Metric.infDist y A ^ 2 ≤ B) :
    Metric.infDist (c1EuclideanCoordinates.symm y) (c1EuclideanCoordinates.symm '' A) ^ 2 ≤
      2 * B := by
  have himg : c1EuclideanCoordinates.symm '' A =
      (fun a : AgentState => (WithLp.toLp 2 a : C1EuclideanAgentState)) '' A := by
    ext z; simp [c1EuclideanCoordinates_symm_eq]
  rw [himg, c1EuclideanCoordinates_symm_eq]
  have h1 := infDist_euclid_le A y
  have h2 := pow_le_pow_left₀ Metric.infDist_nonneg h1 2
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at h2
  linarith

/-- 1–4 の誤差境界を、定理20と同じ Euclid 座標の距離で述べた版（定数 2 倍）。 -/
structure SharedNormUnification (N : SharedModelSignature) : Prop where
  error1 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist (c1EuclideanCoordinates.symm y)
        (c1EuclideanCoordinates.symm '' N.theorem1PointTarget x t₀ t) ^ 2 ≤
      2 * residual1 (N.base.V0 y t) 1
  error2 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist (c1EuclideanCoordinates.symm y)
        (c1EuclideanCoordinates.symm '' N.theorem2PointTarget x t₀ t) ^ 2 ≤
      2 * DA.potential y t
  error3 : ∀ x ∈ box, x 0 + x 1 = 0 → ∀ t₀ ≥ 0,
    ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist (c1EuclideanCoordinates.symm y)
        (c1EuclideanCoordinates.symm '' N.theorem3PointTarget x t₀ t) ^ 2 ≤
      2 * c1Theorem3StatePhi3 y t
  error4 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist (c1EuclideanCoordinates.symm y)
        (c1EuclideanCoordinates.symm '' N.theorem4PointTarget x t₀ t) ^ 2 ≤
      2 * residual4 (N.base.V0 y t) (commonBasePresenceP y t) (commonBasePresenceQ y t) 1 0

theorem SharedPointDomainInputs.normUnification {N : SharedModelSignature}
    (h : SharedPointDomainInputs N) : SharedNormUnification N where
  error1 := fun x hx t₀ ht₀ y hy t => euclid_sq_error_of_sup _ _ _ (h.error1 x hx t₀ ht₀ y hy t)
  error2 := fun x hx t₀ ht₀ y hy t => euclid_sq_error_of_sup _ _ _ (h.error2 x hx t₀ ht₀ y hy t)
  error3 := fun x hx hm t₀ ht₀ y hy t =>
    euclid_sq_error_of_sup _ _ _ (h.error3 x hx hm t₀ ht₀ y hy t)
  error4 := fun x hx t₀ ht₀ y hy t => euclid_sq_error_of_sup _ _ _ (h.error4 x hx t₀ ht₀ y hy t)

theorem sharedModel_normUnification : SharedNormUnification sharedModel :=
  sharedModel_pointDomainInputs.normUnification

#print axioms commonBase_tildeV_ge
#print axioms infDist_euclid_le
#print axioms sharedModel_normUnification
end Tomabechi.Consistency.R123
