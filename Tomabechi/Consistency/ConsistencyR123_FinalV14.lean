import Tomabechi.Consistency.ConsistencyR123_FinalV13

/-!
# 最終存在宣言 v14：三つの小補完を収録する

独立の監査で示された三つの小補完を、受入型へ入れる。
v13 の宣言・型・結論は変更しない。

* 現行評価 `commonV0X` の定理1–4（`FullOriginalPremisesCurrent` の `RestartLemma0`）の
  K 全点の二乗誤差を、定理20と同じ Euclid 距離へ移す（定数 C=2）。これで現行版でも
  定理1–4 と 20 の距離が一つのノルムに揃う（追加条件 H-flow″）。
* 担体全体の自己表象で、Self が到達和集合から TCZ を**ちょうど**返す（包含ではなく等号）。
  この証人の時間独立な評価 `ball16` についての等号で、時変評価一般の法則ではない。
* 容量の問題×方策の joint は、担体全体の自己過程を含む実験の情報周辺にも一致する。
  自己過程を含む joint 全体の旧新等号は要求しない。
-/

noncomputable section
open MeasureTheory
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Consistency.ConsistencyC1 Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1Theorem3Bridge Tomabechi.Consistency.R2
open Tomabechi.Consistency.R3

/-- `RestartLemma0` の K 全点の sup 距離の二乗誤差（係数1）を、Euclid 距離（係数2）へ移す。 -/
theorem RestartLemma0.euclid_error_all_K
    {D : AgentState → Prop} {Φ : AgentState → ℝ → ℝ}
    {Tgt : AgentState → ℝ → ℝ → Set AgentState} {rate : ℝ}
    (h : RestartLemma0 D Φ Tgt rate)
    (x : AgentState) (hx : D x) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (y : AgentState) (hy : y ∈ pointReachableClosure x t₀) (t : ℝ) :
    Metric.infDist (c1EuclideanCoordinates.symm y)
      (c1EuclideanCoordinates.symm '' Tgt x t₀ t) ^ 2 ≤ 2 * Φ y t := by
  apply euclid_sq_error_of_sup
  simpa using h.error_all_K x hx t₀ ht₀ y hy t

/-- Euclid 距離での K 全点の二乗誤差（`RestartLemma0` の誤差部分の Euclid 版）。 -/
def EuclidAllKError (D : AgentState → Prop) (Φ : AgentState → ℝ → ℝ)
    (Tgt : AgentState → ℝ → ℝ → Set AgentState) : Prop :=
  ∀ x, D x → ∀ t₀, 0 ≤ t₀ → ∀ y ∈ pointReachableClosure x t₀, ∀ t,
    Metric.infDist (c1EuclideanCoordinates.symm y)
      (c1EuclideanCoordinates.symm '' Tgt x t₀ t) ^ 2 ≤ 2 * Φ y t

theorem RestartLemma0.euclidAllKError
    {D : AgentState → Prop} {Φ : AgentState → ℝ → ℝ}
    {Tgt : AgentState → ℝ → ℝ → Set AgentState} {rate : ℝ}
    (h : RestartLemma0 D Φ Tgt rate) : EuclidAllKError D Φ Tgt :=
  fun x hx t₀ ht₀ y hy t => h.euclid_error_all_K x hx t₀ ht₀ y hy t

/-- 担体全体の自己表象で、Self は到達和集合から TCZ をちょうど返す。 -/
theorem sharedModel_full_self_eq (h : Bool) (i : ℕ) :
    (sharedModel.selfRepFull h).Self i
      {y | ∃ τ : ℝ, 0 ≤ τ ∧ y ∈ velReach onePointStart τ} =
      (sharedModel.selfRepFull h).TCZ i := by
  ext y
  constructor
  · rintro ⟨τ, hτ, _, hΩ⟩
    change y ∈ ball16 h
    rwa [SharedModelSignature.layerOmega_eq sharedModel_preservation
      sharedModel_explicitAdditionalConditions.legacy] at hΩ
  · intro hy
    change y ∈ ball16 h at hy
    have hc : y ∈ sharedModel.canonicalLayerTCZ h i := by
      rw [SharedModelSignature.canonicalLayerTCZ_eq sharedModel_preservation
        sharedModel_explicitAdditionalConditions.legacy]
      exact hy
    obtain ⟨τ, hτ, hr, hΩ⟩ := hc
    exact ⟨τ, hτ, ⟨τ, hτ, hr⟩, hΩ⟩

section
local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 容量の問題×方策の joint は、担体全体の自己過程を含む実験の情報周辺にも一致する。 -/
theorem sharedModel_policy_joint_full (d H : Bool) {a : CommonConcept}
    (q : CapProblemPolicy a) :
    sharedModel.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 =
      (sharedModel.fullExperimentLawFull q.2.1 d H q.1.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2).map
        (fun z => (z.1.2.1, z.1.2.2.1,
          fullActionEncode q.1.1.1 (q.2.1 q.1.1.1 z.1.2.2.2))) := by
  rw [capPolicy_eq_the_one q.2]
  rw [sharedModel_preservation.fullExperimentFull_information]
  simpa only [capPolicy_eq_the_one q.2] using
    sharedModel_policyCapacityInputs.joint_information d H q

/-- 三つの小補完を N についての受入型として束ねる。 -/
structure SharedP21Supplements (N : SharedModelSignature) : Prop where
  /-- 現行の定理1–4：K 全点の二乗誤差を定理20と同じ Euclid 距離で（C=2）。 -/
  euclid1 : EuclidAllKError (fun _ => True) phi1X target1X
  euclid2 : EuclidAllKError (fun x => x ∈ domainX3) DX.potential target2X
  euclid3 : EuclidAllKError domain3 phi3X target3X
  euclid4 : EuclidAllKError (fun _ => True) phi4X target4X
  /-- 担体全体の Self は到達和集合から TCZ をちょうど返す。 -/
  full_self_eq : ∀ (h : Bool) (i : ℕ),
    (N.selfRepFull h).Self i {y | ∃ τ : ℝ, 0 ≤ τ ∧ y ∈ velReach onePointStart τ} =
      (N.selfRepFull h).TCZ i
  /-- 容量 joint と、担体全体の自己過程を含む実験の情報周辺の一致。 -/
  policy_joint_full : ∀ (d H : Bool) {a : CommonConcept} (q : CapProblemPolicy a),
    N.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 =
      (N.fullExperimentLawFull q.2.1 d H q.1.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2).map
        (fun z => (z.1.2.1, z.1.2.2.1,
          fullActionEncode q.1.1.1 (q.2.1 q.1.1.1 z.1.2.2.2)))

theorem sharedModel_p21Supplements : SharedP21Supplements sharedModel where
  euclid1 := sharedModel_fullOriginalPremisesCurrent.lemma0_theorem1.euclidAllKError
  euclid2 := sharedModel_fullOriginalPremisesCurrent.lemma0_theorem2.euclidAllKError
  euclid3 := sharedModel_fullOriginalPremisesCurrent.lemma0_theorem3.euclidAllKError
  euclid4 := sharedModel_fullOriginalPremisesCurrent.lemma0_theorem4.euclidAllKError
  full_self_eq := sharedModel_full_self_eq
  policy_joint_full := fun d H _ q => sharedModel_policy_joint_full d H q

end

/-- v14：v13 に小補完（現行1–4の Euclid 全K誤差、Self の等号、容量 joint の情報周辺）を
同じ `N` で加える。報告範囲は v13 と同じ（層別の独立生成系の読み）。 -/
theorem final_consistency_v14 : ∃ (N : SharedModelSignature) (sig : LayerControlSignature),
    SharedFinalConsistencyV13 N sig ∧ SharedP21Supplements N :=
  ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistencyV13,
    sharedModel_p21Supplements⟩

#print axioms sharedModel_p21Supplements
#print axioms final_consistency_v14
end Tomabechi.Consistency.R123
