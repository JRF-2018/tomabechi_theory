import Tomabechi.Consistency.ConsistencyR123_SharedEntropy

/-!
# 共有署名を読む解析入口の受入条件

旧局所入力の受入、共通束24/26データの保存、同じ観測からの15→23入力、
同じSCMの25入力、一点初期O24を一つの署名に接続する。
この型は既に構成した入口の束であり、定理4/20共有評価の残る解析条件や
全原文共有条件の最終監査を完了したという意味ではない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Consistency.R2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Examples.Theorem2
open Tomabechi.Theorem24_26 Tomabechi.Theorem16_25

/-- 各条件はNの実データを読む。未監査の一般入口を完了条件から除く型ではない。 -/
structure SharedKernelInputs (N : SharedModelSignature) : Prop where
  original : OriginalPremises N.legacy
  additional : AdditionalConditions N.legacy
  nondegenerate : Nondegenerate N.legacy
  preservation : SharedDataPreservation N
  entropy : SharedEntropyInputs N
  scm_output_noninterference : ∀ d a h s,
    ∀ᵐ u ∂N.scm.model.scm.exogenousLaw.toMeasure,
      N.scm.model.scm.outputEquation d a h u s =
        N.scm.model.scm.outputEquation d a h u
          (N.scm.model.scm.candidateVariable d a u)
  scm_candidate_positive : ∀ d s a,
    Theorem25GlobalHistorySCM.candidateHasPositiveMass N.scm.model.scm.toIndexed d a s
  point_tcz : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → ∀ t,
    (N.pointAdapter x t₀).TCZ t = {agreementPoint x}
  point_distance : ∀ x ∈ box, ∀ t₀, 0 ≤ t₀ → ∀ t, t₀ ≤ t →
    Metric.infDist ((N.pointAdapter x t₀).flow.flow t₀ x t)
      ((N.pointAdapter x t₀).TCZ t) ≤
      Real.sqrt (DA.potential x t₀) * Real.exp (-3 * (t - t₀))

/-- 新署名の24一般入口を全真部分点に適用する。
別の固定24-dataの結論を使わず、N.dataの入力recordを渡す。 -/
theorem SharedKernelInputs.theorem24 {N : SharedModelSignature} (_h : SharedKernelInputs N) :
    ∀ a (ha : a < (⊤ : CommonConcept)) (x : fullCommonLayerState a) (T : ℝ), 0 ≤ T →
      0 < N.data.optimalValue a x T ∧
        ¬ FeedbackPZS (N.data.admissible a) (fun _ => futureLebesgueMeasure T)
          (fun π y t s => N.data.runningCost a π (N.data.trajectory a π y t s) s) x T :=
  theorem24_lower_conclusions_from_nonnegativeTimeData N.data

/-- 同じNのSCMへ定理25の測度付き一般入口を適用する。 -/
theorem SharedKernelInputs.theorem25 {N : SharedModelSignature} (h : SharedKernelInputs N) :
    ∀ d a, ¬ (Theorem25ProbabilityCausalModel.toCausalModel
      N.scm.model.scm.toIndexed.toProbabilityCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    N.scm
  intro d a history s
  filter_upwards [h.scm_output_noninterference d a history s] with u hu
  exact hu.symm

/-- Nの同じ24-data/26-dynamicsを一般入口へ渡す。
全真部分層の正価値、頂点PZS分類、速度付き距離/評価、最適値極限、
零評価目標同値と不変性を、全非負初期対についてまとめて得る。 -/
theorem SharedKernelInputs.theorem24_26 {N : SharedModelSignature} (_h : SharedKernelInputs N) :
    ∀ (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ),
      0 ≤ T → x ∈ N.dynamics.alive →
      (∀ a (ha : a < (⊤ : CommonConcept)) (y : fullCommonLayerState a),
        0 < N.data.optimalValue a y T ∧
          ¬ FeedbackPZS (N.data.admissible a) (fun _ => futureLebesgueMeasure T)
            (fun π z t s => N.data.runningCost a π (N.data.trajectory a π z t s) s) y T) ∧
      (FeedbackPZS (N.data.admissible ⊤) futureLebesgueMeasure
        (fun π y t s => N.data.runningCost ⊤ π (N.data.trajectory ⊤ π y t s) s) x T ↔
        x ∈ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T) ∧
      (∀ s ≥ T,
        N.dynamics.W (N.data.trajectory ⊤ N.dynamics.feedback x T s) s ≤
            N.dynamics.W x T * Real.exp (-N.dynamics.rate * (s - T)) ∧
          Metric.infDist (N.data.trajectory ⊤ N.dynamics.feedback x T s)
            (theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) s) ≤
            Real.sqrt (N.dynamics.W x T / N.dynamics.c₁) *
              Real.exp (-(N.dynamics.rate / 2) * (s - T))) ∧
      Filter.Tendsto
        (fun s => N.data.optimalValue ⊤ (N.data.trajectory ⊤ N.dynamics.feedback x T s) s)
        Filter.atTop (nhds 0) ∧
      (∀ s ≥ T, N.dynamics.W (N.data.trajectory ⊤ N.dynamics.feedback x T s) s = 0 ↔
        N.data.trajectory ⊤ N.dynamics.feedback x T s ∈
          theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) s) ∧
      (∀ s ≥ T,
        x ∈ theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) T →
        N.data.trajectory ⊤ N.dynamics.feedback x T s ∈
          theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue ⊤) s) :=
  theorem24_to26_from_nonnegativeTimeData N.data N.dynamics

/-- 同じNの完全状態pathへ15→23の一般入口を適用する。 -/
theorem SharedKernelInputs.theorem15_23 {N : SharedModelSignature} (h : SharedKernelInputs N) :
    ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ici 0 → t₂ ∈ Set.Ici 0 → t₁ < t₂ →
      N.completePath t₂ ≠ N.completePath t₁ := h.entropy.nonrecurrence

private theorem runningCost_cast
    {I : Type*} {State Policy : I → Type*}
    (f : ∀ i, Policy i → State i → ℝ → ℝ)
    {i j : I} (heq : j = i) (π : Policy i) (x : State i) (t : ℝ) :
    f j (cast (congrArg Policy heq.symm) π)
      (cast (congrArg State heq.symm) x) t = f i π x t := by
  cases heq
  rfl

/-- Nの有限層24費用とNに一度だけ格納した基礎評価の一致。
箱内状態と同じ有限層で述べ、頂点への数値baselineの一致を要求しない。 -/
theorem SharedKernelInputs.finite_cost_eq_base {N : SharedModelSignature}
    (h : SharedKernelInputs N) (n : ℕ)
    (π : C1GainSignal)
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    N.data.runningCost (layerAddressEmbedding (n : WithTop ℕ))
      (cast (congrArg C6LayeredPolicy
        (fullCommonLayerIndex_layerAddress (n : WithTop ℕ)).symm) π)
      (cast (congrArg C6LayeredState
        (fullCommonLayerIndex_layerAddress (n : WithTop ℕ)).symm) x) t = N.base.V0 x t := by
  rw [h.preservation.runningCost]
  rw [runningCost_cast N.legacy.data.runningCost
    (fullCommonLayerIndex_layerAddress (n : WithTop ℕ)) π x t]
  exact (h.additional.finite_c1_cost n π x hx t).trans
    (N.base.theorem1_matches x hx t).symm

/-- 外部モデル前提なしで、現在接続した解析入口を同じ署名に供給する。 -/
theorem sharedModel_kernelInputs : SharedKernelInputs sharedModel := by
  refine {
    original := commonModel_originalPremises
    additional := commonModel_additionalConditions
    nondegenerate := commonModel_nondegenerate
    preservation := sharedModel_preservation
    entropy := sharedModel_entropyInputs
    scm_output_noninterference := ?_
    scm_candidate_positive := commonConceptMeasuredC3Model_candidate_positive
    point_tcz := ?_
    point_distance := fun x hx t₀ ht₀ t ht =>
      pointOptimalConsensusO24_distance x hx t₀ t ht₀ ht }
  · intro d a h s
    filter_upwards with u
    change commonConceptMeasuredC3Model.model.scm.outputEquation d a h u s =
      commonConceptMeasuredC3Model.model.scm.outputEquation d a h u
        (commonConceptMeasuredC3Model.model.scm.candidateVariable d a u)
    rw [commonConceptSCM_output_eq_history, commonConceptSCM_output_eq_history]
  · intro x hx t₀ ht₀ t
    exact pointOptimalTCZ_eq_singleton x hx t₀ t ht₀

/-- 共有データと接続済み解析入力の同時存在。
FullOriginalPremisesの最終認定は残る原文条件の照合後に行う。 -/
theorem shared_kernel_model_exists : ∃ N : SharedModelSignature, SharedKernelInputs N :=
  ⟨sharedModel, sharedModel_kernelInputs⟩

#print axioms shared_kernel_model_exists
#print axioms SharedKernelInputs.theorem24
#print axioms SharedKernelInputs.theorem25
#print axioms SharedKernelInputs.theorem24_26
#print axioms SharedKernelInputs.theorem15_23
#print axioms SharedKernelInputs.finite_cost_eq_base
end Tomabechi.Consistency.R123
