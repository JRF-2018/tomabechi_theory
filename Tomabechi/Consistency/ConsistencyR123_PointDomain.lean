import Tomabechi.Consistency.ConsistencyR123_FullExperimentRecovery

/-!
# 一点Kの全状態に対する原文誤差境界

選んだ軌道上だけでなく、Kの全状態と全評価時刻で1/2/3/4の誤差を証明する。
同じNのflowでの任意の再始動に対する前向き不変性も保持する。
定理3は零平均初期点のKに限る。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Theorem1 Tomabechi.Theorem4
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.R1 Tomabechi.Consistency.R2 Tomabechi.Consistency.R3
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge

/-- K線分上では初期平均が保存される。零平均スライスも同じK全体で保つ。 -/
theorem pointK_mean (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀) :
    meanState y = meanState x := by
  rw [pointReachableClosure_eq_orbitSegment x t₀ ht₀] at hy
  rcases hy with ⟨r, hr, rfl⟩
  simp [segmentPoint, meanState]

/-- 線分内の任意点の合意点への距離二乗は、その点の共有残差以下。 -/
theorem pointK_error2 (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ pointReachableClosure x t₀) (t : ℝ) :
    dist y (agreementPoint x) ^ 2 ≤ DA.potential y t := by
  have hm := pointK_mean x t₀ ht₀ hy
  have hybox := pointReachableClosure_subset_box x hx t₀ hy
  have hd : dist y (agreementPoint x) ≤ |halfDifference y| := by
    apply (dist_pi_le_iff (abs_nonneg _)).2
    intro i
    fin_cases i
    · rw [Real.dist_eq]
      change |y 0 - meanState x| ≤ _
      rw [← hm, show y 0 - meanState y = halfDifference y by dsimp [meanState, halfDifference]; ring]
    · rw [Real.dist_eq]
      change |y 1 - meanState x| ≤ _
      rw [← hm, show y 1 - meanState y = -halfDifference y by dsimp [meanState, halfDifference]; ring,
        abs_neg]
  have hs := (sq_le_sq₀ dist_nonneg (abs_nonneg _)).2 hd
  rw [sq_abs] at hs
  rw [sharedPotential_eq_coupling y hybox t]
  dsimp [halfDifference, γ] at *
  nlinarith [sq_nonneg (y 0 - y 1)]

/-- 同じNの実一点Kを具体線分へ同定する保存式。 -/
theorem SharedKernelInputs.pointK {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (t₀ : ℝ) :
    (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
  rw [h.preservation.point_reachable, h.preservation.point_flow,
    N.legacy.c1.selectedFlow_eq_rate3]
  rfl

theorem SharedKernelInputs.pointTarget2 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) :
    N.theorem2PointTarget x t₀ t = {agreementPoint x} := by
  dsimp [SharedModelSignature.theorem2PointTarget]
  rw [h.pointK]
  have heq : DA.sharedTCZ (pointReachableClosure x t₀) t = pointSharedTCZ x t₀ t := by
    ext y
    constructor
    · rintro ⟨hy, hp⟩
      exact ⟨hy, pointReachableClosure_subset_box x hx t₀ hy, hp⟩
    · rintro ⟨hy, _, hp⟩
      exact ⟨hy, hp⟩
  rw [heq, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]

/-- 一点Kの全状態での原文定理2誤差。時刻tを軌道時刻に固定しない。 -/
theorem SharedKernelInputs.pointDomain_error2 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ (N.pointAdapter x t₀).reachable) (t : ℝ) :
    Metric.infDist y (N.theorem2PointTarget x t₀ t) ^ 2 ≤ DA.potential y t := by
  rw [h.pointTarget2 x hx t₀ ht₀ t, Metric.infDist_singleton]
  exact pointK_error2 x hx t₀ ht₀ (by simpa only [h.pointK] using hy) t

/-- 同じKの全状態での定理1誤差。基礎評価はN.baseそのもの。 -/
theorem SharedKernelInputs.pointDomain_error1 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ (N.pointAdapter x t₀).reachable) (t : ℝ) :
    Metric.infDist y (N.theorem1PointTarget x t₀ t) ^ 2 ≤ residual1 (N.base.V0 y t) 1 := by
  rw [sharedBase_pointTargets, sharedBase_residual]
  exact h.pointDomain_error2 x hx t₀ ht₀ hy t

/-- 共有実効評価の零集合は同じKの共有TCZ。全K点で定理4誤差を得る。 -/
theorem SharedKernelInputs.pointDomain_error4 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : AgentState} (hy : y ∈ (N.pointAdapter x t₀).reachable) (t : ℝ) :
    Metric.infDist y (N.theorem4PointTarget x t₀ t) ^ 2 ≤
      residual4 (N.base.V0 y t) (commonBasePresenceP y t) (commonBasePresenceQ y t) 1 0 := by
  have hV : N.base.V0 = commonBaseV0 := by
    funext z s
    exact N.base.V0_eq_shared z s
  have hZ : N.theorem4PointTarget x t₀ t = N.theorem2PointTarget x t₀ t := by
    rw [h.pointTarget2 x hx t₀ ht₀ t]
    dsimp [SharedModelSignature.theorem4PointTarget]
    rw [h.pointK, hV]
    change sharedT4PointTarget x t₀ t = _
    rw [sharedT4PointTarget_eq x hx, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]
  rw [hZ]
  apply (h.pointDomain_error2 x hx t₀ ht₀ hy t).trans
  rw [hV]
  have htime : DA.potential y t = DA.potential y 0 := by rfl
  have heff := (commonBaseTheorem4_bounds y t).1
  change DA.potential y t ≤ max (commonBaseTheorem4Effective y t - 0) 0
  rw [htime, sub_zero]
  exact heff.trans (le_max_left _ _)

/-- 零平均K全体で、完全Φ₃の目標と共有TCZの目標が一致する。 -/
theorem SharedKernelInputs.pointTarget3 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (t : ℝ) :
    N.theorem3PointTarget x t₀ t = N.theorem2PointTarget x t₀ t := by
  rw [h.pointTarget2 x hx t₀ ht₀ t]
  dsimp [SharedModelSignature.theorem3PointTarget]
  rw [h.pointK]
  change pointTheorem3Target x t₀ t = _
  rw [pointTheorem3Target_eq_singleton x hx hmean t₀ t ht₀]
  congr 1
  ext i
  fin_cases i <;> simp [agreementPoint, meanState, c1Theorem3Zero] <;> linarith

/-- 完全Φ₃を使った全K点の誤差。Φ₂だけを完全残差と呼ばない。 -/
theorem SharedKernelInputs.pointDomain_error3 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) (t : ℝ) :
    Metric.infDist y (N.theorem3PointTarget x t₀ t) ^ 2 ≤ c1Theorem3StatePhi3 y t := by
  rw [h.pointTarget3 x hx hmean t₀ ht₀ t]
  apply (h.pointDomain_error2 x hx t₀ ht₀ hy t).trans
  change DA.potential y t ≤ DA.potential y t + _
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by norm_num [c1Theorem3Weight])
    (Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System i _)

/-- K内の全点で、一点制限目標距離と全域象徴目標距離が一致する。 -/
theorem SharedKernelInputs.pointDomain_distance20 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : C1EuclideanAgentState) (hx : x ∈ c1EuclideanBox) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : C1EuclideanAgentState}
    (hy : y ∈ c1EuclideanCoordinates.symm ''
      (N.pointAdapter (c1EuclideanCoordinates x) t₀).reachable) :
    Metric.infDist y (N.theorem20PointTarget x t₀) = Metric.infDist y c1EuclideanSymbolTarget := by
  have hm : meanState (c1EuclideanCoordinates y) = meanState (c1EuclideanCoordinates x) := by
    rcases hy with ⟨z, hz, rfl⟩
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact pointK_mean _ t₀ ht₀ (by simpa only [h.pointK] using hz)
  have ha : sharedT20Agreement y = sharedT20Agreement x := by
    apply c1EuclideanCoordinates.injective
    simp only [sharedT20Agreement, ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun m : ℝ => ![m, m]) hm
  rw [h.theorem20PointTarget_eq, sharedT20PointTarget_eq_singleton x hx t₀ ht₀,
    Metric.infDist_singleton, sharedT20_globalTarget_infDist, ha]

/-- 同じ一点K全体で、原文20の全域誤差定数をそのまま使用できる。 -/
theorem SharedKernelInputs.pointDomain_error20 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : C1EuclideanAgentState) (hx : x ∈ c1EuclideanBox) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    {y : C1EuclideanAgentState}
    (hy : y ∈ c1EuclideanCoordinates.symm ''
      (N.pointAdapter (c1EuclideanCoordinates x) t₀).reachable) :
    Metric.infDist y (N.theorem20PointTarget x t₀) ≤ 2 * Real.sqrt (sharedT20D y) := by
  rw [h.pointDomain_distance20 x hx t₀ ht₀ hy]
  exact h.theorem20Inputs.error y

/-- 同じNの一点Kは、任意の内部状態・任意再始動時刻で前向き不変。 -/
theorem SharedKernelInputs.pointDomain_invariant {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) {s t : ℝ} (ht : s ≤ t) :
    (N.pointAdapter x t₀).flow.flow s y t ∈ (N.pointAdapter x t₀).reachable := by
  rw [h.pointK] at hy ⊢
  rw [h.preservation.point_flow, N.legacy.c1.selectedFlow_eq_rate3]
  exact pointReachableClosure_forward_invariant x t₀ ht₀ hy ht

/-- 全一点adapterのflowは同じ保存された選択flowである。
初期集合と到達Kを変えても、再始動の動力学を別のflowへ置き換えない。 -/
theorem SharedKernelInputs.pointFlow_same {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x y : AgentState) (t₀ s : ℝ) :
    (N.pointAdapter y s).flow = (N.pointAdapter x t₀).flow := by
  rw [h.preservation.point_flow, h.preservation.point_flow]

/-- K内部の任意点・非負再始動時刻の全有限区間で定理2のACと率6散逸。 -/
theorem SharedKernelInputs.pointDomain_restart2 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) (s T : ℝ) (hs : 0 ≤ s) (hT : s ≤ T) :
    AbsolutelyContinuousOnInterval (fun r => DA.potential
      ((N.pointAdapter x t₀).flow.flow s y r) r) s T ∧
    (∀ᵐ r ∂volume.restrict (Set.Icc s T),
      deriv (fun v => DA.potential ((N.pointAdapter x t₀).flow.flow s y v) v) r ≤
        -2 * 3 * DA.potential ((N.pointAdapter x t₀).flow.flow s y r) r) := by
  have hybox : y ∈ box := pointReachableClosure_subset_box x hx t₀ (by
    simpa only [h.pointK] using hy)
  have hi := h.theorem2Inputs y hybox s hs
  have hp : N.theorem2PointPotential y s =
      (fun r => DA.potential ((N.pointAdapter x t₀).flow.flow s y r) r) := by
    funext r
    dsimp [SharedModelSignature.theorem2PointPotential]
    rw [h.pointFlow_same x y t₀ s]
  simpa only [hp]
    using And.intro (hi.potential_ac T hT) (hi.decay_ae T hT)

/-- 同じ共有基礎評価を使う定理1のAC・率6散逸も全K内部再始動で成立。 -/
theorem SharedKernelInputs.pointDomain_restart1 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) (s T : ℝ) (hs : 0 ≤ s) (hT : s ≤ T) :
    AbsolutelyContinuousOnInterval (fun r => residual1
      (N.base.V0 ((N.pointAdapter x t₀).flow.flow s y r) r) 1) s T ∧
    (∀ᵐ r ∂volume.restrict (Set.Icc s T),
      deriv (fun v => residual1 (N.base.V0 ((N.pointAdapter x t₀).flow.flow s y v) v) 1) r ≤
        -2 * 3 * residual1 (N.base.V0 ((N.pointAdapter x t₀).flow.flow s y r) r) 1) := by
  simpa only [sharedBase_residual] using h.pointDomain_restart2 x hx t₀ hy s T hs hT

/-- 零平均Kの任意点から、完全Φ₃のAC・散逸条件を再始動する。 -/
theorem SharedKernelInputs.pointDomain_restart3 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (hmean : x 0 + x 1 = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) (s T : ℝ) (hs : 0 ≤ s) (hT : s ≤ T) :
    AbsolutelyContinuousOnInterval (fun r => c1Theorem3StatePhi3
      ((N.pointAdapter x t₀).flow.flow s y r) r) s T ∧
    (∀ᵐ r ∂volume.restrict (Set.Icc s T),
      deriv (fun v => c1Theorem3StatePhi3 ((N.pointAdapter x t₀).flow.flow s y v) v) r ≤
        -2 * 3 * c1Theorem3StatePhi3 ((N.pointAdapter x t₀).flow.flow s y r) r) := by
  have hyK : y ∈ pointReachableClosure x t₀ := by simpa only [h.pointK] using hy
  have hm := pointK_mean x t₀ ht₀ hyK
  have hymean : y 0 + y 1 = 0 := by dsimp [meanState] at hm; linarith
  have hi := h.theorem3Inputs y (pointReachableClosure_subset_box x hx t₀ hyK) hymean s hs
  have hp : N.theorem3PointPotential y s =
      (fun r => c1Theorem3StatePhi3 ((N.pointAdapter x t₀).flow.flow s y r) r) := by
    funext r
    dsimp [SharedModelSignature.theorem3PointPotential]
    rw [h.pointFlow_same x y t₀ s]
    rfl
  simpa only [hp]
    using And.intro (hi.potential_ac T hT) (hi.decay_ae T hT)

/-- 同じ実効評価の定理4も、K内部の任意点から率3の残差散逸で再始動する。 -/
theorem SharedKernelInputs.pointDomain_restart4 {N : SharedModelSignature} (h : SharedKernelInputs N)
    (x : AgentState) (hx : x ∈ box) (t₀ : ℝ) {y : AgentState}
    (hy : y ∈ (N.pointAdapter x t₀).reachable) (s T : ℝ) (hs : 0 ≤ s) (hT : s ≤ T) :
    let R := fun r =>
      let z := (N.pointAdapter x t₀).flow.flow s y r
      residual4 (N.base.V0 z r) (commonBasePresenceP z r) (commonBasePresenceQ z r) 1 0
    AbsolutelyContinuousOnInterval R s T ∧
      (∀ᵐ r ∂volume.restrict (Set.Icc s T), deriv R r ≤ -2 * (3 / 2 : ℝ) * R r) := by
  have hybox : y ∈ box := pointReachableClosure_subset_box x hx t₀ (by
    simpa only [h.pointK] using hy)
  have hi := h.theorem4Inputs y hybox s hs
  have hp : N.theorem4PointResidual y s =
      (fun r =>
        let z := (N.pointAdapter x t₀).flow.flow s y r
        residual4 (N.base.V0 z r) (commonBasePresenceP z r) (commonBasePresenceQ z r) 1 0) := by
    funext r
    dsimp [SharedModelSignature.theorem4PointResidual]
    rw [h.pointFlow_same x y t₀ s]
  simpa only [hp]
    using And.intro (hi.residual_ac T hT) (hi.decay_ae T hT)

/-- 全K点の誤差と不変性を同じ署名の受入に追加する。
再始動解析条件は同じ受入のSharedKernelInputsから上の一般量化補題で得る。 -/
structure SharedPointDomainInputs (N : SharedModelSignature) : Prop extends SharedFullExperimentInputs N where
  closed : ∀ x t₀, IsClosed (N.pointAdapter x t₀).reachable
  invariant : ∀ x t₀, 0 ≤ t₀ → ∀ y ∈ (N.pointAdapter x t₀).reachable,
    ∀ s t, s ≤ t → (N.pointAdapter x t₀).flow.flow s y t ∈ (N.pointAdapter x t₀).reachable
  error2 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist y (N.theorem2PointTarget x t₀ t) ^ 2 ≤ DA.potential y t
  error1 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist y (N.theorem1PointTarget x t₀ t) ^ 2 ≤ residual1 (N.base.V0 y t) 1
  error3 : ∀ x ∈ box, x 0 + x 1 = 0 → ∀ t₀ ≥ 0,
    ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist y (N.theorem3PointTarget x t₀ t) ^ 2 ≤ c1Theorem3StatePhi3 y t
  error4 : ∀ x ∈ box, ∀ t₀ ≥ 0, ∀ y ∈ (N.pointAdapter x t₀).reachable, ∀ t,
    Metric.infDist y (N.theorem4PointTarget x t₀ t) ^ 2 ≤
      residual4 (N.base.V0 y t) (commonBasePresenceP y t) (commonBasePresenceQ y t) 1 0
  error20 : ∀ x ∈ c1EuclideanBox, ∀ t₀ ≥ 0,
    ∀ y ∈ c1EuclideanCoordinates.symm '' (N.pointAdapter (c1EuclideanCoordinates x) t₀).reachable,
    Metric.infDist y (N.theorem20PointTarget x t₀) ≤ 2 * Real.sqrt (sharedT20D y)

theorem sharedModel_pointDomainInputs : SharedPointDomainInputs sharedModel := by
  refine ⟨sharedModel_fullExperimentInputs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t₀
    rw [sharedModel_kernelInputs.preservation.point_reachable]
    exact isClosed_closure
  · intro x t₀ ht₀ y hy s t ht
    exact sharedModel_kernelInputs.pointDomain_invariant x t₀ ht₀ hy ht
  · exact sharedModel_kernelInputs.pointDomain_error2
  · exact sharedModel_kernelInputs.pointDomain_error1
  · exact sharedModel_kernelInputs.pointDomain_error3
  · exact sharedModel_kernelInputs.pointDomain_error4
  · exact sharedModel_kernelInputs.pointDomain_error20

theorem shared_point_domain_model_exists : ∃ N : SharedModelSignature, SharedPointDomainInputs N :=
  ⟨sharedModel, sharedModel_pointDomainInputs⟩

#print axioms SharedKernelInputs.pointDomain_error2
#print axioms SharedKernelInputs.pointDomain_error3
#print axioms SharedKernelInputs.pointDomain_error4
#print axioms SharedKernelInputs.pointDomain_distance20
#print axioms SharedKernelInputs.pointDomain_error20
#print axioms SharedKernelInputs.pointDomain_invariant
#print axioms SharedKernelInputs.pointDomain_restart2
#print axioms SharedKernelInputs.pointDomain_restart1
#print axioms SharedKernelInputs.pointDomain_restart3
#print axioms SharedKernelInputs.pointDomain_restart4
#print axioms shared_point_domain_model_exists
end Tomabechi.Consistency.R123
