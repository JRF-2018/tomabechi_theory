import Tomabechi.Consistency.ConsistencyR123_NoClockCoordinate

/-!
# 状態の距離・制御の位相は原文のノルム／Borel 構造と一致する（H-flow″）

H-flow″ の前半（状態の距離）は距離の統一で、1・3・4 の誤差境界と結論を定理20と同じ Euclid 距離で
述べ直して閉じた。ここでは後半、**状態と制御の位相・Borel 構造**が原文のノルム／Borel
構造と一致することを述語にする。

* **有限層の状態：** `AgentState = Fin 2 → ℝ`（sup 距離・積 σ 代数）と Euclid 表示 `EuclideanSpace ℝ (Fin 2)`
  はどちらも Borel 空間で、座標写像 `c1EuclideanCoordinates` は同相かつ可測同値。
  同じ ℝ² の二つのノルムが同じ位相・同じ Borel 構造を与える。
* **頂点の状態：** `fullCommonLayerState ⊤` の可測構造は、E2 の距離を引き戻した距離の Borel 構造で、
  E2 への等長な可測同値がある。非負時刻つきの状態空間も Borel 空間。
* **制御：** 有限層の制御は ℝ 値の可測（標準 Borel 構造）有界ゲイン信号 `C1GainSignal`
  （値は `[0,3]`）。頂点の制御空間は E2（ノルム位相と Borel 構造）で、頂点の方策族は
  非負時刻上の Borel マルコフフィードバックと同値（`N.dynamics.policyEquiv`）。

**範囲：** 位相・Borel 構造の一致の記述であり、制御集合の位相（たとえばゲイン信号の空間に位相を
入れたときの連続性）は課していない（原文の制御は可測性だけが使われる）。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem24_26

structure SharedBorelStructure (N : SharedModelSignature) : Prop where
  state_borel : BorelSpace AgentState ∧ BorelSpace C1EuclideanAgentState
  state_chart_homeo : Continuous c1EuclideanCoordinates ∧ Continuous c1EuclideanCoordinates.symm
  state_chart_measurable : Measurable c1EuclideanCoordinates ∧
    Measurable c1EuclideanCoordinates.symm
  top_state_borel : BorelSpace (fullCommonLayerState (⊤ : CommonConcept))
  top_state_chart : ∃ e : fullCommonLayerState (⊤ : CommonConcept) ≃ᵐ C6LayeredState (⊤ : WithTop ℕ),
    (⇑e = fullCommonTopStateEquiv) ∧ Isometry e
  top_time_state_borel : BorelSpace (Set.Ici (0 : ℝ) × fullCommonLayerState (⊤ : CommonConcept))
  real_borel : BorelSpace ℝ
  finite_control : ∀ u : C1GainSignal, Measurable u.1 ∧ ∀ t, 0 ≤ u.1 t ∧ u.1 t ≤ 3
  top_control_borel : BorelSpace Tomabechi.Examples.Theorem27Op.E2
  top_policy_class : Nonempty (fullCommonLayerPolicy (⊤ : CommonConcept) ≃
    NonnegativeTimeBorelMarkovFeedback (fullCommonLayerState (⊤ : CommonConcept))
      Tomabechi.Examples.Theorem27Op.E2)

theorem SharedModelSignature.sharedBorelStructure (N : SharedModelSignature) :
    SharedBorelStructure N where
  state_borel := ⟨inferInstance, inferInstance⟩
  state_chart_homeo := ⟨c1EuclideanCoordinates.continuous, c1EuclideanCoordinates.symm.continuous⟩
  state_chart_measurable :=
    ⟨c1EuclideanCoordinates.continuous.measurable, c1EuclideanCoordinates.symm.continuous.measurable⟩
  top_state_borel := inferInstance
  top_state_chart := ⟨fullCommonTopStateMeasurableEquiv, rfl, fullCommonTopStateEquiv_isometry⟩
  top_time_state_borel := inferInstance
  real_borel := inferInstance
  finite_control := fun u => ⟨u.2.1, u.2.2⟩
  top_control_borel := inferInstance
  top_policy_class := ⟨N.dynamics.policyEquiv⟩

theorem sharedModel_borelStructure : SharedBorelStructure sharedModel :=
  sharedModel.sharedBorelStructure

theorem final_consistency_v2_with_borel_structure :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity, sharedModel_noClockCoordinate,
    sharedModel_borelStructure⟩

#print axioms SharedModelSignature.sharedBorelStructure
#print axioms final_consistency_v2_with_borel_structure
end Tomabechi.Consistency.R123
