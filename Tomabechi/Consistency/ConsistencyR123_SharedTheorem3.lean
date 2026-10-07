import Tomabechi.Consistency.ConsistencyR123_SharedTheorem1

/-!
# 一点K上の完全Φ₃と全主体の表象距離

同じNの実軌道を定理3の状態付き一般入口へ渡す。
この二主体モデルでは零平均初期状態を要求する。非零平均状態まで量化しない。
共有残差Φ₂だけで目標を代用せず、Φ₃の零集合を使用する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Theorem1 Tomabechi.Theorem3
open Tomabechi.Examples.Theorem2
open Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge

local instance (i : Fin 2) : PseudoMetricSpace (c1Theorem3System.State i) := by
  change PseudoMetricSpace ℝ
  infer_instance

local instance : NormedAddCommGroup (∀ i, c1Theorem3System.State i) := by
  change NormedAddCommGroup AgentState
  infer_instance

local instance : NormedSpace ℝ (∀ i, c1Theorem3System.State i) := by
  change NormedSpace ℝ AgentState
  infer_instance

def SharedModelSignature.theorem3PointTarget (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : Set AgentState :=
  c1Theorem3System.stateTCZ (N.pointAdapter x t₀).reachable
    DA.potential c1Theorem3Weight t

def SharedModelSignature.theorem3PointPotential (N : SharedModelSignature)
    (x : AgentState) (t₀ t : ℝ) : ℝ :=
  c1Theorem3System.statePotential DA.potential c1Theorem3Weight
    ((N.pointAdapter x t₀).flow.flow t₀ x t) t

/-- 一点到達集合上の完全Φ₃に対する、一般定理3の全解析前件。 -/
structure SharedTheorem3PointInputs (N : SharedModelSignature)
    (x : AgentState) (t₀ : ℝ) : Prop where
  reachable : (N.pointAdapter x t₀).reachable = closedLoopReachableSet
    (policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
  target_nonempty : ∀ t, (N.theorem3PointTarget x t₀ t).Nonempty
  shared_nonneg : ∀ t, 0 ≤ DA.potential ((N.pointAdapter x t₀).flow.flow t₀ x t) t
  potential_ac : ∀ T, t₀ ≤ T → AbsolutelyContinuousOnInterval
    (N.theorem3PointPotential x t₀) t₀ T
  decay_ae : ∀ T, t₀ ≤ T → ∀ᵐ t ∂volume.restrict (Set.Icc t₀ T),
    deriv (N.theorem3PointPotential x t₀) t ≤
      -2 * 3 * N.theorem3PointPotential x t₀ t
  error : ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
      (N.theorem3PointTarget x t₀ t) ^ 2 ≤ N.theorem3PointPotential x t₀ t

/-- 零平均スライスに限り、完全Φ₃の目標非空性と解析前件を構成する。 -/
theorem SharedKernelInputs.theorem3Inputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : AgentState) (hx : x ∈ box)
    (hmean : x 0 + x 1 = 0) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    SharedTheorem3PointInputs N x t₀ := by
  have hF : (N.pointAdapter x t₀).flow = consensusOptimalFlow :=
    (h.preservation.point_flow x t₀).trans N.legacy.c1.selectedFlow_eq_rate3
  have hK : (N.pointAdapter x t₀).reachable = pointReachableClosure x t₀ := by
    rw [h.preservation.point_reachable, hF]
    rfl
  have hP : N.theorem3PointPotential x t₀ = c1Theorem3Potential x t₀ := by
    funext t
    dsimp [SharedModelSignature.theorem3PointPotential]
    rw [hF]
    rfl
  have hZ : ∀ t, N.theorem3PointTarget x t₀ t = {c1Theorem3Zero} := by
    intro t
    dsimp [SharedModelSignature.theorem3PointTarget]
    rw [hK]
    change pointTheorem3Target x t₀ t = _
    exact pointTheorem3Target_eq_singleton x hx hmean t₀ t ht₀
  have h2 := h.theorem2Inputs x hx t₀ ht₀
  have hZ2 : ∀ t, N.theorem2PointTarget x t₀ t = {c1Theorem3Zero} := by
    intro t
    rw [← sharedBase_pointTargets]
    dsimp [SharedModelSignature.theorem1PointTarget]
    rw [hK]
    have hV : N.base.V0 = consensusV0 := by
      funext y s
      exact N.base.V0_eq_shared y s
    rw [hV]
    change pointTheorem1Target x t₀ t = _
    have heq : pointTheorem1Target x t₀ t = pointSharedTCZ x t₀ t := by
      ext y
      have hn := consensusPresence_potential_nonneg y 0
      have htime : DA.potential y 0 = DA.potential y t := by rfl
      simp only [pointTheorem1Target, pointSharedTCZ, consensusV0,
        Tomabechi.Theorem2.StatePairResidualSystem.sharedTCZ, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hy, hv⟩
        exact ⟨hy, pointReachableClosure_subset_box x hx t₀ hy, by linarith⟩
      · rintro ⟨hy, _, hp⟩
        exact ⟨hy, by linarith⟩
    rw [heq, pointSharedTCZ_eq_singleton x hx t₀ t ht₀]
    congr 1
    ext i
    fin_cases i <;> simp [agreementPoint, meanState, c1Theorem3Zero] <;> linarith
  refine ⟨h.preservation.point_reachable x t₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hZ]
    exact Set.singleton_nonempty _
  · intro t
    exact consensusPresence_potential_nonneg _ t
  · rw [hP]
    exact c1Theorem3Potential_ac x hx hmean t₀
  · intro T hT
    rw [hP]
    by_cases heq : T = t₀
    · subst T
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (by simp : volume (Set.Icc t₀ t₀) = 0)] with t ht hmem
      exact False.elim (ht hmem)
    · exact c1Theorem3Potential_decay_ae x hx hmean t₀ T
        (lt_of_le_of_ne hT (Ne.symm heq))
  · intro t ht
    have herr := h2.error t ht
    rw [hZ2] at herr
    rw [hZ]
    apply herr.trans
    change DA.potential _ t ≤ DA.potential _ t + _
    apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by norm_num [c1Theorem3Weight])
      (AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System i _)

/-- 全主体についての率3表象距離とその極限を、状態TCZ距離とともに保持する。 -/
structure SharedTheorem3PointConclusion (N : SharedModelSignature)
    (x : AgentState) (t₀ : ℝ) : Prop where
  reachable : ∀ t, t₀ ≤ t → (N.pointAdapter x t₀).flow.flow t₀ x t ∈
    (N.pointAdapter x t₀).reachable
  state_bound : ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t) (N.theorem3PointTarget x t₀ t) ≤
    Real.sqrt (N.theorem3PointPotential x t₀ t₀) * Real.exp (-3 * (t - t₀))
  agent_bound : ∀ i t, t₀ ≤ t →
    euclideanCoordinateNorm (c1Theorem3System.ι (c1Theorem3System.abstraction i
      ((N.pointAdapter x t₀).flow.flow t₀ x t i)) - c1Theorem3System.ι c1Theorem3System.lub) ≤
    Real.sqrt (N.theorem3PointPotential x t₀ t₀ / c1Theorem3Weight i) *
      Real.exp (-3 * (t - t₀))
  state_limit : Tendsto (fun t => Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
    (N.theorem3PointTarget x t₀ t)) atTop (𝓝 0)
  agent_limit : ∀ i, Tendsto (fun t => euclideanCoordinateNorm
    (c1Theorem3System.ι (c1Theorem3System.abstraction i
      ((N.pointAdapter x t₀).flow.flow t₀ x t i)) - c1Theorem3System.ι c1Theorem3System.lub))
    atTop (𝓝 0)

set_option backward.isDefEq.respectTransparency false in
/-- Nの実flow・一点到達集合・完全Φ₃を一般定理3へ直接渡す。 -/
theorem SharedTheorem3PointInputs.conclusion {N : SharedModelSignature}
    {x : AgentState} {t₀ : ℝ} (h : SharedTheorem3PointInputs N x t₀)
    (ht₀ : 0 ≤ t₀) : SharedTheorem3PointConclusion N x t₀ := by
  have hcore := fun i : Fin 2 => c1Theorem3System.theorem3_reachable_state_tcz_quantitative_conclusion
    (show ℝ → Set AgentState from policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
    (fun j t => (N.pointAdapter x t₀).flow.flow t₀ x t j)
    DA.potential c1Theorem3Weight i 3 1 t₀
    (by norm_num [c1Theorem3Weight]) (by norm_num) (by norm_num) ht₀
    (fun t ht => mem_policyFlowReachableAt_of_flow (N.pointAdapter x t₀).flow {x}
      t₀ t x (Set.mem_singleton _) ht)
    (fun t ht => h.shared_nonneg t)
    (fun t ht j => mul_nonneg (by norm_num [c1Theorem3Weight])
      (AbstractSharedSystem.abstractResidual_nonneg c1Theorem3System j _))
    (fun t ht => by rw [← h.reachable]; exact h.target_nonempty t)
    h.potential_ac h.decay_ae
    (fun t ht => by rw [← h.reachable, one_mul]; exact h.error t ht)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← h.reachable] using (hcore 0).1
  · intro t ht
    simpa only [← h.reachable, one_mul, SharedModelSignature.theorem3PointTarget,
      SharedModelSignature.theorem3PointPotential] using ((hcore 0).2.1 t ht).1
  · intro i t ht
    exact ((hcore i).2.1 t ht).2
  · simpa only [← h.reachable, SharedModelSignature.theorem3PointTarget] using (hcore 0).2.2.1
  · intro i
    exact (hcore i).2.2.2

/-- 既存全stage/SCM入力と、全箱点の1/2・零平均箱点の3を一つのNへ集約する。 -/
structure SharedPointInputs (N : SharedModelSignature) : Prop extends SharedStageInputs N where
  theorem2 : ∀ x ∈ box, ∀ t₀ ≥ 0, SharedTheorem2PointInputs N x t₀
  theorem3 : ∀ x ∈ box, x 0 + x 1 = 0 → ∀ t₀ ≥ 0, SharedTheorem3PointInputs N x t₀

theorem sharedModel_pointInputs : SharedPointInputs sharedModel := by
  exact {
    toSharedStageInputs := {
      toSharedSCMAndExperimentInputs := sharedModel_scmAndExperimentInputs
      information := ⟨sharedModel_stageInformationInputs⟩
      switching := sharedModel_stageSwitchInputs
      path := sharedModel_stagePathCouplings }
    theorem2 := sharedModel_kernelInputs.theorem2Inputs
    theorem3 := sharedModel_kernelInputs.theorem3Inputs }

theorem shared_point_model_exists : ∃ N : SharedModelSignature, SharedPointInputs N :=
  ⟨sharedModel, sharedModel_pointInputs⟩

#print axioms SharedKernelInputs.theorem3Inputs
#print axioms SharedTheorem3PointInputs.conclusion
#print axioms shared_point_model_exists
end Tomabechi.Consistency.R123
