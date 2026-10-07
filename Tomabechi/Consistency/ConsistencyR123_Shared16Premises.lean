import Tomabechi.Consistency.ConsistencyR123_Theorem4Ranges

/-!
# 定理16の存在節・表象節・縮小節の前件を述語の field に

以前は定理16の**結論**（`Theorem16EntryClause`：一意固定点・表象の固定・関係・幾何収束）を
受入型に入れた。しかし結論を出すための**前件**（M7.1–M7.6）は、具体定理
`theorem16_intervalGradientFlowC4_generalEntryConnection` の内側にだけあり、述語の外（W）にあった。
ここでは前件そのものを field として並べる。

* 層系（M7.1–M7.4）：各層の担体は**層別 TCZ**で、非空・コンパクト・凸。
  射影は担体上で連続アフィン、合成則・恒等、整合点；フィードバックは射影と可換で連続；
  添字は上向き有向で最大元なし。
* 表象節（M7.5）：表象空間はコンパクト Hausdorff、関係は閉、表象写像は連続・
  表象関係を満たし、表象側の写像は連続で逆極限の写像と同変；二履歴の固定点は異なる。
* 縮小節（M7.6）：履歴別逆極限は SC 距離で完備、層別フィードバックが誘導する写像は率 `exp(-1) < 1`
  の縮小。

**範囲：** 対象は具体の C4 系（`[0,1]` 対角逆系、`ℕ` 添字）。任意の層系・任意の自己表象に対する一般の前件ではない。
各 field の型は既存の層系・adapter の field の型そのもの（`type_of%`）なので、書き写しによる弱化はない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C4 Tomabechi.Theorem16_25

structure Shared16Premises (N : SharedModelSignature) : Prop where
  /-- M7.1：各層・各履歴の担体（層別 TCZ）は非空コンパクト凸。 -/
  layer_nonempty : ∀ (h : Bool) (i : ℕ), (N.layerTCZ h i).Nonempty
  layer_compact : ∀ (h : Bool) (i : ℕ), IsCompact (N.layerTCZ h i)
  layer_convex : ∀ (h : Bool) (i : ℕ), Convex ℝ (N.layerTCZ h i)
  /-- M7.3：射影は担体上で連続アフィン、合成則・恒等、担体を担体へ送る。 -/
  project_maps : type_of% theorem16_intervalGradientFlowLayerSystem.projectMaps
  project_affine : type_of% theorem16_intervalGradientFlowLayerSystem.projectAffineOnCarrier
  project_refl : type_of% theorem16_intervalGradientFlowLayerSystem.projectRefl
  project_comp : type_of% theorem16_intervalGradientFlowLayerSystem.projectComp
  project_continuous : type_of% theorem16_intervalGradientFlowLayerSystem.projectContinuousOn
  /-- M7.2：添字は上向き有向で最大元なし。 -/
  no_maximum : type_of% theorem16_intervalGradientFlowLayerSystem.noMax
  /-- M7.4：層別フィードバックは射影と可換で連続。 -/
  feedback_commutes : type_of% theorem16_intervalGradientFlowLayerSystem.feedbackCommutes
  feedback_continuous : type_of% theorem16_intervalGradientFlowLayerSystem.feedbackContinuous
  /-- M7.5（表象節）：表象空間はコンパクト Hausdorff、関係は閉、表象写像は連続、
  表象関係を満たし、表象側の写像は連続で逆極限の写像と同変。 -/
  rep_compact_t2 : CompactSpace (Set.Icc (0 : ℝ) 1) ∧ T2Space (Set.Icc (0 : ℝ) 1)
  rep_relation_closed : ∀ h, IsClosed (theorem16_intervalGradientFlowC4SelfRepresentation h).relation
  rep_continuous : ∀ h, Continuous (theorem16_intervalGradientFlowC4SelfRepresentation h).represent
  rep_represents : ∀ h s, ((theorem16_intervalGradientFlowC4SelfRepresentation h).represent s, s) ∈
    (theorem16_intervalGradientFlowC4SelfRepresentation h).relation
  rep_map_continuous : ∀ h, Continuous (theorem16_intervalGradientFlowC4RepresentedMap h)
  rep_equivariant : type_of% theorem16_intervalGradientFlowC4_equivariant
  /-- 25-A(1)：二履歴の固定点は異なる（共通周囲空間内）。 -/
  history_sensitive :
    (theorem16_intervalGradientFlowC4Points.fixedPoint false).1 ≠
      (theorem16_intervalGradientFlowC4Points.fixedPoint true).1
  /-- M7.6（縮小節）：SC 距離で完備、率 `exp(-1)` の縮小。 -/
  complete : type_of% c6C4FlowTCZAdapter.inverse_limit_complete
  contracting : type_of% c6C4FlowTCZAdapter.inverse_limit_feedback_contracting

theorem SharedModelSignature.shared16Premises {N : SharedModelSignature}
    (hp : SharedDataPreservation N) (hA : AdditionalConditions N.legacy) :
    Shared16Premises N where
  layer_nonempty := fun h i => by
    rw [SharedModelSignature.layerTCZ_eq_carrier hp hA]; exact ⟨0, by simp⟩
  layer_compact := fun h i => by
    rw [SharedModelSignature.layerTCZ_eq_carrier hp hA]; exact isCompact_Icc
  layer_convex := fun h i => by
    rw [SharedModelSignature.layerTCZ_eq_carrier hp hA]; exact convex_Icc 0 1
  project_maps := theorem16_intervalGradientFlowLayerSystem.projectMaps
  project_affine := theorem16_intervalGradientFlowLayerSystem.projectAffineOnCarrier
  project_refl := theorem16_intervalGradientFlowLayerSystem.projectRefl
  project_comp := theorem16_intervalGradientFlowLayerSystem.projectComp
  project_continuous := theorem16_intervalGradientFlowLayerSystem.projectContinuousOn
  no_maximum := theorem16_intervalGradientFlowLayerSystem.noMax
  feedback_commutes := theorem16_intervalGradientFlowLayerSystem.feedbackCommutes
  feedback_continuous := theorem16_intervalGradientFlowLayerSystem.feedbackContinuous
  rep_compact_t2 := ⟨inferInstance, inferInstance⟩
  rep_relation_closed := fun h => (theorem16_intervalGradientFlowC4SelfRepresentation h).relation_closed
  rep_continuous := fun h => (theorem16_intervalGradientFlowC4SelfRepresentation h).represent_continuous
  rep_represents := fun h s => (theorem16_intervalGradientFlowC4SelfRepresentation h).represents s
  rep_map_continuous := fun h => theorem16_intervalGradientFlowLayerSystem.feedbackContinuous h 0
  rep_equivariant := theorem16_intervalGradientFlowC4_equivariant
  history_sensitive := theorem16_intervalGradientFlowC4_generatedFixedPoints_separate
  complete := c6C4FlowTCZAdapter.inverse_limit_complete
  contracting := c6C4FlowTCZAdapter.inverse_limit_feedback_contracting

theorem sharedModel_shared16Premises : Shared16Premises sharedModel :=
  SharedModelSignature.shared16Premises sharedModel_preservation
    sharedModel_explicitAdditionalConditions.legacy

theorem final_consistency_v2_with_16premises :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N := by
  obtain ⟨N, h1, h2, h3, h4, h5, h6, h7⟩ := final_consistency_v2_with_theorem4_ranges
  exact ⟨N, h1, h2, h3, h4, h5, h6, h7,
    N.shared16Premises h1.base.inputs.toSharedFullExperimentInputs.toSharedPointInputs.toSharedStageInputs.toSharedSCMAndExperimentInputs.toSharedR3And27Inputs.toSharedR3Inputs.toSharedKernelInputs.preservation
      h2.base.legacy⟩

#print axioms SharedModelSignature.shared16Premises
#print axioms final_consistency_v2_with_16premises
end Tomabechi.Consistency.R123
