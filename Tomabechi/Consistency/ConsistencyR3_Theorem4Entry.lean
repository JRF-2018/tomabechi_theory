import Tomabechi.Consistency.ConsistencyR3_CommonBase

/-!
# 共通基礎評価の定理4一般入口

基礎評価は定理1と同じ `1+F`、臨場感は `exp(-F)` である。
一点初期状態の閉到達Kに対し、実効残差のAC・微分散逸・誤差境界を供給し、
一般定理4を適用する。箱内の二主体rate-3具体モデルに限る。
-/

noncomputable section
namespace Tomabechi.Consistency.R3
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Theorem1 Tomabechi.Theorem4
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.R2

/-- 共有実効残差の明示式。箱内軌道に沿うFの率6減衰を代入する。 -/
def sharedT4Explicit (F t₀ t : ℝ) : ℝ :=
  1 + F * Real.exp (-6 * (t - t₀)) -
    Real.exp (-(F * Real.exp (-6 * (t - t₀))))

/-- 一般入口へ渡す、実際の共有評価から読んだ残差。 -/
def sharedT4Residual (x : AgentState) (t₀ t : ℝ) : ℝ :=
  residual4 (commonBaseV0 (consensusOptimalFlow.flow t₀ x t) t)
    (commonBasePresenceP (consensusOptimalFlow.flow t₀ x t) t)
    (commonBasePresenceQ (consensusOptimalFlow.flow t₀ x t) t) 1 0

/-- 閾値0の共有実効評価は非負なので、正部分を取っても値は変わらない。 -/
theorem sharedT4Residual_eq_effective (x : AgentState) (t₀ t : ℝ) :
    sharedT4Residual x t₀ t =
      commonBaseTheorem4Effective (consensusOptimalFlow.flow t₀ x t) t := by
  have hnonneg : 0 ≤ commonBaseTheorem4Effective (consensusOptimalFlow.flow t₀ x t) t :=
    le_trans (consensusPresence_potential_nonneg _ 0) (commonBaseTheorem4_bounds _ t).1
  change max (commonBaseTheorem4Effective (consensusOptimalFlow.flow t₀ x t) t - 0) 0 = _
  simp only [sub_zero, max_eq_left hnonneg]

/-- 同じrate-3軌道上の基礎残差Fの厳密な時間表示。 -/
theorem sharedBasePotential_rate3 (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    DA.potential (consensusOptimalFlow.flow t₀ x t) 0 =
      DA.potential x 0 * Real.exp (-6 * (t - t₀)) := by
  have hybox := consensusOptimalFlow_forward_invariant x hx t₀ t ht
  rw [sharedPotential_eq_coupling _ hybox 0, consensusOptimalFlow_gap,
    mul_pow, ← Real.exp_nat_mul, sharedPotential_eq_coupling x hx 0]
  ring

theorem sharedT4Residual_eq_explicit (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    sharedT4Residual x t₀ t = sharedT4Explicit (DA.potential x 0) t₀ t := by
  rw [sharedT4Residual_eq_effective, commonBaseTheorem4Effective_formula,
    sharedBasePotential_rate3 x hx t₀ t ht]
  rfl

/-- 明示残差へ連鎖律を適用する。 -/
theorem sharedT4Explicit_hasDerivAt (F t₀ t : ℝ) :
    HasDerivAt (sharedT4Explicit F t₀)
      (-6 * (F * Real.exp (-6 * (t - t₀))) *
        (1 + Real.exp (-(F * Real.exp (-6 * (t - t₀)))))) t := by
  have hlin : HasDerivAt (fun u : ℝ => -6 * (u - t₀)) (-6) t := by
    simpa using ((hasDerivAt_id t).sub_const t₀).const_mul (-6)
  have hexp := (Real.hasDerivAt_exp (-6 * (t - t₀))).comp t hlin
  have hF : HasDerivAt (fun u => F * Real.exp (-6 * (u - t₀)))
      (-6 * (F * Real.exp (-6 * (t - t₀)))) t := by
    convert hexp.const_mul F using 1
    · rfl
    · ring
  have h := ((hasDerivAt_const t (1 : ℝ)).add hF).sub hF.neg.exp
  convert h using 1
  · rfl
  · dsimp
    ring

/-- 全有限前向き区間で実残差はAC。閉区間上の一致で明示式から移す。 -/
theorem sharedT4Residual_ac (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) (hT : t₀ ≤ T) :
    AbsolutelyContinuousOnInterval (sharedT4Residual x t₀) t₀ T := by
  have hcd : ContDiff ℝ 1 (sharedT4Explicit (DA.potential x 0) t₀) := by
    unfold sharedT4Explicit
    fun_prop
  apply hcd.contDiffOn.absolutelyContinuousOnInterval.congr
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  exact (sharedT4Residual_eq_explicit x hx t₀ t ht.1).symm

/-- 一般入口のa.e.散逸。開始点だけは零測度集合として除く。
単なる値の減衰から微分不等式を推測していない。 -/
theorem sharedT4Residual_decay_ae (x : AgentState) (hx : x ∈ box)
    (t₀ T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc t₀ T),
      deriv (sharedT4Residual x t₀) t ≤ -3 * sharedT4Residual x t₀ t := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (measure_singleton t₀ : volume ({t₀} : Set ℝ) = 0)] with t hne ht
  have hlt : t₀ < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using hne)
  have hnear : sharedT4Residual x t₀ =ᶠ[𝓝 t] sharedT4Explicit (DA.potential x 0) t₀ := by
    filter_upwards [Ioi_mem_nhds hlt] with u hu
    exact sharedT4Residual_eq_explicit x hx t₀ u hu.le
  have hderiv := (sharedT4Explicit_hasDerivAt (DA.potential x 0) t₀ t).congr_of_eventuallyEq hnear
  rw [hderiv.deriv, sharedT4Residual_eq_effective]
  rw [← sharedBasePotential_rate3 x hx t₀ t ht.1]
  exact commonBaseTheorem4_rate3_dissipation_rhs_bound _ t

/-- 共通基礎評価の閾値0目標を一点K内で選ぶ。 -/
def sharedT4PointTarget (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  weightedTCZ (pointReachableClosure x t₀)
    commonBaseV0 commonBasePresenceP commonBasePresenceQ 1 0 t

/-- 新評価の一点目標は同じ一点Kの共有TCZと一致する。 -/
theorem sharedT4PointTarget_eq (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) :
    sharedT4PointTarget x t₀ t = pointSharedTCZ x t₀ t := by
  ext y
  have hK := pointReachableClosure_subset_box x hx t₀
  have heq := Set.ext_iff.mp (commonBaseTheorem4_weightedTCZ_eq_shared t) y
  change (y ∈ pointReachableClosure x t₀ ∧
    effectivePotential (commonBaseV0 y t) (commonBasePresenceP y t)
      (commonBasePresenceQ y t) 1 ≤ 0) ↔
    (y ∈ pointReachableClosure x t₀ ∧ y ∈ DA.sharedTCZ box t)
  constructor
  · rintro ⟨hy, hv⟩
    exact ⟨hy, heq.mp ⟨hK hy, hv⟩⟩
  · rintro ⟨hy, hv⟩
    exact ⟨hy, (heq.mpr hv).2⟩

/-- 同じ一点初期目標への全前向き時刻の誤差境界。
集合包含による逆向き距離評価を使わず、合意点までの距離から証明する。 -/
theorem sharedT4PointTarget_error (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    (Metric.infDist (consensusOptimalFlow.flow t₀ x t) (sharedT4PointTarget x t₀ t)) ^ 2 ≤
      1 * sharedT4Residual x t₀ t := by
  rw [sharedT4PointTarget_eq x hx, pointSharedTCZ_eq_singleton x hx t₀ t ht₀,
    Metric.infDist_singleton, sharedT4Residual_eq_effective, one_mul]
  have hdist := consensusOptimalFlow_dist_agreementPoint_le x t₀ t
  have hsq : dist (consensusOptimalFlow.flow t₀ x t) (agreementPoint x) ^ 2 ≤
      (halfDifference x) ^ 2 * Real.exp (-6 * (t - t₀)) := by
    have hh := sq_le_sq₀ (dist_nonneg : 0 ≤ dist
      (consensusOptimalFlow.flow t₀ x t) (agreementPoint x)) (by positivity :
        0 ≤ |halfDifference x| * Real.exp (-3 * (t - t₀)))
    have h := hh.mpr hdist
    simpa only [mul_pow, sq_abs, ← Real.exp_nat_mul, Nat.cast_ofNat,
      show (2 : ℝ) * (-3 * (t - t₀)) = -6 * (t - t₀) by ring] using h
  have hF : DA.potential x 0 = 8 * (halfDifference x) ^ 2 := by
    rw [sharedPotential_eq_coupling x hx 0]
    dsimp [γ, halfDifference]
    ring
  have hbound := (commonBaseTheorem4_bounds (consensusOptimalFlow.flow t₀ x t) t).1
  rw [sharedBasePotential_rate3 x hx t₀ t ht, hF] at hbound
  nlinarith [sq_nonneg (halfDifference x), Real.exp_pos (-6 * (t - t₀))]

/-- 定理4の一般入口を共有V₀・一点初期集合で実際に適用する。
距離評価と極限の両方を得る。率は散逸から得る3/2。 -/
theorem sharedBase_theorem4_point_entry (x : AgentState) (hx : x ∈ box)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∀ t, t₀ ≤ t → consensusOptimalFlow.flow t₀ x t ∈ pointReachableClosure x t₀) ∧
    (∀ t, t₀ ≤ t →
      Metric.infDist (consensusOptimalFlow.flow t₀ x t) (sharedT4PointTarget x t₀ t) ≤
        Real.sqrt (sharedT4Residual x t₀ t₀) * Real.exp (-(3 / 2 : ℝ) * (t - t₀))) ∧
    Tendsto (fun t => Metric.infDist (consensusOptimalFlow.flow t₀ x t)
      (sharedT4PointTarget x t₀ t)) atTop (𝓝 0) := by
  simpa only [one_mul, sharedT4PointTarget, pointReachableClosure, sharedT4Residual] using
    (weighted_reachable_tcz_distance_tendsto_zero
    (consensusOptimalFlow.flow t₀ x)
    (policyFlowReachableAt consensusOptimalFlow {x} t₀)
    commonBaseV0 commonBasePresenceP commonBasePresenceQ 1 0 (3 / 2) 1 t₀
    (fun t ht => mem_policyFlowReachableAt_of_flow consensusOptimalFlow {x}
      t₀ t x (Set.mem_singleton x) ht)
    (fun T hT t ht => by
      change (sharedT4PointTarget x t₀ t).Nonempty
      rw [sharedT4PointTarget_eq x hx, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]
      exact Set.singleton_nonempty _)
    (fun T hT => sharedT4Residual_ac x hx t₀ T hT)
    (fun T _ => by
      have h := sharedT4Residual_decay_ae x hx t₀ T
      norm_num at h ⊢
      exact h)
    (fun T hT t ht => sharedT4PointTarget_error x hx t₀ t ht₀ ht.1)
    ht₀ (by norm_num) (by norm_num))

#print axioms sharedBase_theorem4_point_entry
end Tomabechi.Consistency.R3
