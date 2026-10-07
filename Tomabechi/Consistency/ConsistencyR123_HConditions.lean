import Tomabechi.Consistency.ConsistencyR123_Final

/-!
# 追加の明示条件 H-flow/H-sum/H-stage/H-info を名前付きの条件として述べる

`ExplicitAdditionalConditions N` は、共有保存式と具体contextの採用等式からなる。
追加の明示条件 H-flow・H-sum・H-stage・H-info は、これまで証拠つきデータの型
（`C1OptimalConsensusAdapter`・`SharedEntropyInputs`・`MeanFieldStageInput` など）の中に
埋め込まれていて、名前で取り出せなかった。ここではそれぞれを共有署名Nのfieldについての
命題として書き下し、最終受入型 `SharedPointDomainInputs N` を満たす任意のNで成り立つことを
示す（具体証人への代入ではない）。

範囲：ここで述べるのは、このモデルで用いた形の H 条件である。H-stage は全段の平均場入力の
条件、H-sum は全alive区間の有限部分和の一様可積分性・a.e.収束・端点総和可能性、
H-flow は一点初期集合の同じ選択flow・再始動・到達集合と頂点軌道の再始動、
H-info は出力の型 `Bool` が標準Borel空間であることに限る。
定理3の状態写像と、ノルム・Borel構造の一致（H-flowの残りの部分）は、ここでは述べない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2 Tomabechi.Consistency.R1
open Tomabechi.Consistency.ConsistencyC1Consensus

/-- H-flow：一点初期集合の同じ選択flowが軌道と到達集合を生成し、再始動が軌道の続きと一致する。
頂点の閉ループ軌道も非負開始時刻で再始動と整合する。 -/
structure ExplicitHFlow (N : SharedModelSignature) : Prop where
  same_selected_flow : ∀ x t₀, (N.pointAdapter x t₀).flow = N.legacy.c1.selectedFlow
  point_initial : ∀ x t₀, (N.pointAdapter x t₀).initialSet = {x}
  reachable_from_flow : ∀ x t₀, (N.pointAdapter x t₀).reachable =
    Tomabechi.Theorem1.closedLoopReachableSet
      (Tomabechi.Theorem1.policyFlowReachableAt (N.pointAdapter x t₀).flow {x} t₀)
  flow_initial : ∀ x t₀ s y, (N.pointAdapter x t₀).flow.flow s y s = y
  flow_restart : ∀ x t₀ a y s t, a ≤ s → s ≤ t →
    (N.pointAdapter x t₀).flow.flow a y t =
      (N.pointAdapter x t₀).flow.flow s ((N.pointAdapter x t₀).flow.flow a y s) t
  reachable_invariant : ∀ x t₀, 0 ≤ t₀ → ∀ y ∈ (N.pointAdapter x t₀).reachable,
    ∀ s t, s ≤ t → (N.pointAdapter x t₀).flow.flow s y t ∈ (N.pointAdapter x t₀).reachable
  top_restart : ∀ y a s t, 0 ≤ a → a ≤ s → s ≤ t →
    N.topPath (N.topPath y a s) s t = N.topPath y a t

/-- H-sum：全alive区間で、正層の有限部分和の一様可積分性、列挙の部分和のa.e.収束、
端点での総和可能性。全時刻での総和可能性は要求しない。 -/
structure ExplicitHSum (N : SharedModelSignature) : Prop where
  endpoint_summable : ∀ a b : ℝ, 0 ≤ a → a < b →
    Summable (fun p => N.positiveWeight p * N.positiveObservation p (N.completePath a)) ∧
    Summable (fun p => N.positiveWeight p * N.positiveObservation p (N.completePath b))
  all_finite_ui : ∀ a b : ℝ, 0 ≤ a → a < b →
    UniformIntegrable (fun (s : Finset PositiveLayer) t => ∑ p ∈ s,
      N.positiveWeight p * deriv (fun u => N.positiveObservation p (N.completePath u)) t)
      1 (volume.restrict (Set.uIoc a b))
  prefix_tendsto : ∀ a b : ℝ, 0 ≤ a → a < b →
    ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun k => ∑ i : Fin k,
        N.positiveWeight (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val) *
          deriv (fun u => N.positiveObservation
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val)
            (N.completePath u)) t) atTop
        (𝓝 (∑' p, N.positiveWeight p *
          deriv (fun u => N.positiveObservation p (N.completePath u)) t))

/-- H-stage：全段で、平均場の全点積分表示、中心と台のLUBの表象、閉球上の背景・平均場のC²性、
移動度のC¹性・対称性・一様強制性、勾配表現、初期点を含む部分準位の閉包が開球内にあること、
初期値で決まる部分準位の等式。 -/
structure ExplicitHStage (N : SharedModelSignature) : Prop where
  meanField_integral : ∀ n x,
    (N.stages n).meanField x = (N.stages n).averagePresentation.integralValue x
  center_lub : ∀ n, (N.stages n).center =
    (N.stages n).averagePresentation.centerRepresentation
      (N.stages n).averagePresentation.supportLub
  background_c2 : ∀ n, ∀ x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ContDiffAt ℝ 2 (N.stages n).background x
  meanField_c2 : ∀ n, ∀ x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ContDiffAt ℝ 2 (N.stages n).meanField x
  background_gradient : ∀ n x,
    innerSL ℝ ((N.stages n).backgroundGradient x) = fderiv ℝ (N.stages n).background x
  meanField_gradient : ∀ n x,
    innerSL ℝ ((N.stages n).meanFieldGradient x) = fderiv ℝ (N.stages n).meanField x
  mobility_c1 : ∀ n, ∀ x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ContDiffAt ℝ 1 (N.stages n).mobility x
  mobility_symmetric : ∀ n, ∀ x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ∀ v w, inner ℝ ((N.stages n).mobility x v) w = inner ℝ v ((N.stages n).mobility x w)
  mobility_coercive : ∀ n, ∀ x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius,
    ∀ w, (N.stages n).gamma * ‖w‖ ^ 2 ≤ inner ℝ ((N.stages n).mobility x w) w
  initial_mem : ∀ n, (N.stages n).initial ∈ (N.stages n).sublevel
  sublevel_barrier : ∀ n,
    closure (N.stages n).sublevel ⊆ Metric.ball (N.stages n).center (N.stages n).radius
  sublevel_eq : ∀ n, (N.stages n).sublevel =
    {x | x ∈ Metric.closedBall (N.stages n).center (N.stages n).radius ∧
      (N.stages n).background x - (N.stages n).gain * (N.stages n).presenceGain *
          (N.stages n).meanField x ≤
        (N.stages n).background (N.stages n).initial - (N.stages n).gain *
          (N.stages n).presenceGain * (N.stages n).meanField (N.stages n).initial}

/-- H-info：情報実験と定理21の行為出力の型 `Bool` は標準Borel空間である。 -/
structure ExplicitHInfo : Prop where
  output_standardBorel : Nonempty (StandardBorelSpace Bool)

/-- 追加の明示条件Hの四つをまとめたもの。 -/
structure ExplicitHConditions (N : SharedModelSignature) : Prop where
  flow : ExplicitHFlow N
  sum : ExplicitHSum N
  stage : ExplicitHStage N
  info : ExplicitHInfo

/-- 最終受入型を満たす任意のNで、H条件が名前付きで成り立つ。 -/
theorem SharedPointDomainInputs.explicitHConditions {N : SharedModelSignature}
    (h : SharedPointDomainInputs N) : ExplicitHConditions N := by
  have hk : SharedKernelInputs N :=
    h.toSharedFullExperimentInputs.toSharedPointInputs.toSharedStageInputs.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs
  have h27 : SharedR3And27Inputs N :=
    h.toSharedFullExperimentInputs.toSharedPointInputs.toSharedStageInputs.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs
  have hp := hk.preservation
  have he := hk.entropy
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine {
      same_selected_flow := hp.point_flow
      point_initial := hp.point_initial
      reachable_from_flow := hp.point_reachable
      flow_initial := fun x t₀ s y => (N.pointAdapter x t₀).flow.initial s y
      flow_restart := fun x t₀ a y s t has hst =>
        (N.pointAdapter x t₀).flow.restart a y s t has hst
      reachable_invariant := h.invariant
      top_restart := ?_ }
    intro y a s t ha has hst
    exact (h27.top27 y 0 le_rfl).restart y a s t ha has hst
  · exact ⟨he.endpoint_summable, he.all_finite_ui, he.prefix_tendsto⟩
  · exact {
      meanField_integral := fun n => (N.stages n).meanField_eq_integral
      center_lub := fun n => (N.stages n).center_eq_supportLub_representation
      background_c2 := fun n => (N.stages n).background_c2_at
      meanField_c2 := fun n => (N.stages n).meanField_c2_at
      background_gradient := fun n => (N.stages n).background_gradient_representation
      meanField_gradient := fun n => (N.stages n).meanField_gradient_representation
      mobility_c1 := fun n => (N.stages n).mobility_c1
      mobility_symmetric := fun n => (N.stages n).mobility_symmetric
      mobility_coercive := fun n => (N.stages n).mobility_coercive
      initial_mem := fun n => (N.stages n).initial_mem
      sublevel_barrier := fun n => (N.stages n).sublevel_barrier
      sublevel_eq := fun n => (N.stages n).sublevel_eq }
  · exact ⟨⟨inferInstance⟩⟩

/-- 最終存在宣言に、H条件を名前付きで加えた版。外部のモデル前提を含まない。 -/
theorem final_consistency_with_explicit_H_conditions :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        ExplicitHConditions N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_fullOriginalPremises.inputs.explicitHConditions⟩

#print axioms SharedPointDomainInputs.explicitHConditions
#print axioms final_consistency_with_explicit_H_conditions
end Tomabechi.Consistency.R123
