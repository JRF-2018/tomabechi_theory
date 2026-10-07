import Tomabechi.Consistency.ConsistencyR123_CommonDomainX

/-!
# 定理19の容量を固定した主体・履歴で

原文 §8 は主体 `i` と履歴 `h` を**固定**して、`ℱ_i(α) = sup_{問題, 許容方策} I(G;Y^π|X)` を定義する。
従来の `SharedModelSignature.sharedCapacity`は、問題族 `CapProblem a` が主体・履歴・初期状態・
時刻のすべてを動かす上限で、固定した `(i,h)` の容量ではなかった。

ここでは `(d, H)` を**外側の引数**にする。

* **問題：** 層 `c ≼ a`、その層の初期状態 `x`、開始時刻 `T`、時刻 `t`（`CapProblemFixed a`）。
  生成 joint は `N.fullExperimentLaw`（実軌道・実費用を含む、固定した `d, H`）を、入力・ゴール・
  実方策から再符号化した行為へ押し出したもの。評価値はその直接CMI。許容問題は `T ≥ 0`。
* **許容方策族（層 `c` ごとに有限族 `{decode c false, decode c true}`）：** 情報実験で既に実現した二つの
  decoder を使う。方策の相違は実制御の相違（`fullInformationDecoder` が区別される、再符号化で `false/true` に戻る）、
  両方が同じ N.data の許容方策で、`true` は最適方策。実験の軌道・費用は同じ N.data から作られる。
* **容量：** `fixedCapacity N d H a := dependentLayerCapacity …`（定理19の依存型容量）。
  包含埋込みで全対の joint と評価値を保つ。有限・非空・単調・端点・正規化。
  固定しない従来の `sharedCapacity` と一致する（この証人では joint が主体・履歴によらない）。
* **主体・履歴の対応：** 固定した `(d,H)` の実験の自己過程周辺は `N.selfProcess d a` のベースライン joint。

**範囲：** 方策族は、情報実験で実現した二つの decoder に限る（原文は方策族を固定していない）。ゴールは `Bool` 一つ。
容量が主体・履歴によらないのはこの証人の性質であり、一般の N では成り立つと主張しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 層 c の実験データ（主体・履歴を除く）：初期状態・開始時刻・時刻。 -/
abbrev FixedExperiment (c : CommonConcept) := fullCommonLayerState c × ℝ × ℝ

/-- 固定した主体・履歴の問題族：a 以下の層 c と、その層の実験データ。 -/
abbrev CapProblemFixed (a : CommonConcept) :=
  Σ c : {c : CommonConcept // c ≤ a}, FixedExperiment c.1

def capacityAdmissibleFixed (a : CommonConcept) : Set (CapProblemFixed a) :=
  {p | 0 ≤ p.2.2.1}

/-- 固定した `(d,H)` の問題を、`d,H` を動かす問題族の一要素として見る。 -/
def toPooled (d H : Bool) {a : CommonConcept} (p : CapProblemFixed a) : CapProblem a :=
  ⟨p.1, (d, H, p.2.1, p.2.2.1, p.2.2.2)⟩

def SharedModelSignature.capacityScoreFixed (N : SharedModelSignature) (d H : Bool)
    (a : CommonConcept) (p : CapProblemFixed a) : ℝ :=
  N.capacityScore a (toPooled d H p)

/-- 固定した主体 d・履歴 H の容量 `ℱ_{d,H}(a)`（定理19の依存型容量）。 -/
def SharedModelSignature.fixedCapacity (N : SharedModelSignature) (d H : Bool)
    (a : CommonConcept) : ℝ :=
  Tomabechi.Theorem19.dependentLayerCapacity CapProblemFixed capacityAdmissibleFixed
    (N.capacityScoreFixed d H) a

/-- 層の包含による問題の埋込み。 -/
def capacityEmbeddingFixed {a b : CommonConcept} (hab : a ≤ b) (p : CapProblemFixed a) :
    CapProblemFixed b :=
  ⟨⟨p.1.1, p.1.2.trans hab⟩, p.2⟩

theorem capacityEmbeddingFixed_injective {a b : CommonConcept} (hab : a ≤ b) :
    Function.Injective (capacityEmbeddingFixed hab) := by
  rintro ⟨⟨c, hc⟩, e⟩ ⟨⟨c', hc'⟩, e'⟩ h
  simp only [capacityEmbeddingFixed, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have : c = c' := congrArg Subtype.val h1
  subst this
  simpa using h2

theorem capacityAdmissibleFixed_nonempty (a : CommonConcept) :
    (capacityAdmissibleFixed a).Nonempty := by
  obtain ⟨x⟩ := capacityState_nonempty (⊥ : CommonConcept)
  exact ⟨⟨⟨⊥, bot_le⟩, (x, 0, 0)⟩, le_refl (0 : ℝ)⟩

theorem SharedDataPreservation.capacityScoreFixed_eq {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) (a : CommonConcept) (p : CapProblemFixed a) :
    N.capacityScoreFixed d H a p = if p.1.1 = ⊥ then 0 else Real.log 2 :=
  h.capacityScore_eq a (toPooled d H p)

theorem SharedDataPreservation.capacityScoreFixed_bounded {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) (a : CommonConcept) :
    BddAbove (N.capacityScoreFixed d H a '' capacityAdmissibleFixed a) :=
  ⟨Real.log 2, by
    rintro _ ⟨p, _, rfl⟩
    exact h.capacityScore_le_log_two a (toPooled d H p)⟩

theorem SharedDataPreservation.fixedCapacity_monotone {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) : Monotone (N.fixedCapacity d H) := by
  intro a b hab
  exact Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    CapProblemFixed capacityAdmissibleFixed (N.capacityScoreFixed d H)
    capacityAdmissibleFixed_nonempty (h.capacityScoreFixed_bounded d H)
    (fun {_ _} hab => capacityEmbeddingFixed hab)
    (fun {_ _} hab => capacityEmbeddingFixed_injective hab)
    (fun {_ _} hab {_} hp => hp)
    (fun {_ _} hab {_} hp => rfl) a b hab

theorem SharedDataPreservation.fixedCapacity_bottom {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) : N.fixedCapacity d H ⊥ = 0 := by
  unfold SharedModelSignature.fixedCapacity Tomabechi.Theorem19.dependentLayerCapacity
  have himg : N.capacityScoreFixed d H ⊥ '' capacityAdmissibleFixed ⊥ = {0} := by
    ext r
    constructor
    · rintro ⟨p, _, rfl⟩
      have hc : p.1.1 = ⊥ := le_bot_iff.mp p.1.2
      rw [h.capacityScoreFixed_eq, if_pos hc]; rfl
    · intro hr
      obtain ⟨q, hq⟩ := capacityAdmissibleFixed_nonempty (⊥ : CommonConcept)
      refine ⟨q, hq, ?_⟩
      have hc : q.1.1 = ⊥ := le_bot_iff.mp q.1.2
      rw [h.capacityScoreFixed_eq, if_pos hc]; exact (Set.mem_singleton_iff.mp hr).symm
  rw [himg]; simp

theorem SharedDataPreservation.fixedCapacity_top {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) : N.fixedCapacity d H ⊤ = Real.log 2 := by
  unfold SharedModelSignature.fixedCapacity Tomabechi.Theorem19.dependentLayerCapacity
  obtain ⟨x⟩ := capacityState_nonempty (⊤ : CommonConcept)
  let p : CapProblemFixed ⊤ := ⟨⟨⊤, le_refl _⟩, (x, 0, 0)⟩
  have hp : p ∈ capacityAdmissibleFixed ⊤ := le_refl (0 : ℝ)
  have hscore : N.capacityScoreFixed d H ⊤ p = Real.log 2 := by
    rw [h.capacityScoreFixed_eq, if_neg (by simp [p])]
  apply le_antisymm
  · exact csSup_le ((capacityAdmissibleFixed_nonempty ⊤).image _)
      (by rintro _ ⟨q, _, rfl⟩; exact h.capacityScore_le_log_two ⊤ (toPooled d H q))
  · rw [← hscore]
    exact le_csSup (h.capacityScoreFixed_bounded d H ⊤) ⟨p, hp, rfl⟩

/-- 固定した `(d,H)` の容量は、従来の（主体・履歴を動かす）`sharedCapacity` と、全点で一致する。 -/
theorem SharedDataPreservation.fixedCapacity_eq_shared {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H : Bool) (a : CommonConcept) :
    N.fixedCapacity d H a = N.sharedCapacity a := by
  unfold SharedModelSignature.fixedCapacity SharedModelSignature.sharedCapacity
    Tomabechi.Theorem19.dependentLayerCapacity
  congr 1
  ext r
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨toPooled d H p, hp, rfl⟩
  · rintro ⟨⟨c, e⟩, hp, rfl⟩
    refine ⟨⟨c, (e.2.2.1, e.2.2.2.1, e.2.2.2.2)⟩, hp, ?_⟩
    show N.capacityScore a _ = N.capacityScore a _
    rw [h.capacityScore_eq, h.capacityScore_eq]
    rfl

/-- 固定した `(d,H)` の容量の受入型：問題族・許容方策族・生成 joint・保存単射・容量を原文の量化で。 -/
structure SharedFixedCapacityInputs (N : SharedModelSignature) : Prop where
  /-- 各固定 `(d,H)` で、問題族は非空・上界つき。 -/
  nonempty : ∀ (d H : Bool) (a : CommonConcept), (capacityAdmissibleFixed a).Nonempty
  bounded : ∀ (d H : Bool) (a : CommonConcept),
    BddAbove (N.capacityScoreFixed d H a '' capacityAdmissibleFixed a)
  /-- 各問題の joint は、固定した `(d,H)` の実験 joint の押し出しで、確率測度・KL 有限。 -/
  joint_from_experiment : ∀ (d H : Bool) {c : CommonConcept} (x : fullCommonLayerState c) (T t : ℝ),
    N.capacityJoint (d, H, x, T, t) =
      (N.fullExperimentLaw fullInformationDecoder d H c x T t).map
        (fun z => (z.1.2.1, z.1.2.2.1, fullActionEncode c (fullInformationDecoder c z.1.2.2.2)))
  joint_probability : ∀ (d H : Bool) {c : CommonConcept} (x : fullCommonLayerState c) (T t : ℝ),
    IsProbabilityMeasure (N.capacityJoint (d, H, x, T, t))
  kl_finite : ∀ (d H : Bool) {c : CommonConcept} (x : fullCommonLayerState c) (T t : ℝ),
    haveI := joint_probability d H x T t
    InformationTheory.klDiv
        (Tomabechi.Theorem19_22.directActionGoalJoint (N.capacityJoint (d, H, x, T, t)))
        (Tomabechi.Theorem19_22.directCMIReference (N.capacityJoint (d, H, x, T, t))) ≠ ⊤
  /-- 許容方策族：各層 c の有限族 `{decode c false, decode c true}`。 -/
  policy_admissible : ∀ (c : CommonConcept) (g : Bool) (x : fullCommonLayerState c) (T : ℝ),
    0 ≤ T → N.data.admissible c (fullInformationDecoder c g) x T
  policy_true_optimal : ∀ (c : CommonConcept) (x : fullCommonLayerState c) (T : ℝ),
    fullInformationDecoder c true = N.data.optimalPolicy c x T
  /-- 方策の相違は実制御の相違で、再符号化で `false/true` に戻る。 -/
  policy_distinct : ∀ c : CommonConcept,
    fullInformationDecoder c false ≠ fullInformationDecoder c true
  policy_action_code : ∀ (c : CommonConcept) (g : Bool),
    fullActionEncode c (fullInformationDecoder c g) = g
  /-- 実験の状態・費用は、同じ N.data の実軌道・実走行費。 -/
  experiment_state_cost : ∀ (d H : Bool) (c : CommonConcept) (x : fullCommonLayerState c)
    (T t : ℝ),
    (N.fullExperimentLaw fullInformationDecoder d H c x T t).map (fun z => z.2.2) =
      (N.fullExperimentInputLaw c).map (fun w =>
        let π := fullInformationDecoder c w.2.2.2
        let y := N.data.trajectory c π x T t
        (y, N.data.runningCost c π y t))
  /-- 固定した `(d,H)` の実験の自己過程周辺は、25 の `N.selfProcess d a` のベースライン joint。 -/
  experiment_self_process : ∀ (d H : Bool) (c : CommonConcept) (x : fullCommonLayerState c)
    (T t : ℝ),
    (N.fullExperimentLaw fullInformationDecoder d H c x T t).map (fun z => z.2.1) =
      (N.selfProcess d c).exogenousLaw.toMeasure.map ((N.selfProcess d c).baselineEquation H)
  /-- 層の包含による埋込み（単射・許容性・評価値を保存）。 -/
  embedding : ∀ (d H : Bool), ∃ ι : ∀ {a b : CommonConcept}, a ≤ b → CapProblemFixed a → CapProblemFixed b,
    (∀ {a b} (hab : a ≤ b), Function.Injective (ι hab)) ∧
    (∀ {a b} (hab : a ≤ b) {p}, p ∈ capacityAdmissibleFixed a → ι hab p ∈ capacityAdmissibleFixed b) ∧
    (∀ {a b} (hab : a ≤ b) {p}, p ∈ capacityAdmissibleFixed a →
      N.capacityScoreFixed d H b (ι hab p) = N.capacityScoreFixed d H a p)
  /-- 容量：有限（≤ log 2）・非負・単調・端点・正規化。 -/
  capacity_le_log_two : ∀ (d H : Bool) (a : CommonConcept), N.fixedCapacity d H a ≤ Real.log 2
  capacity_nonneg : ∀ (d H : Bool) (a : CommonConcept), 0 ≤ N.fixedCapacity d H a
  monotone : ∀ d H : Bool, Monotone (N.fixedCapacity d H)
  bottom_zero : ∀ d H : Bool, N.fixedCapacity d H ⊥ = 0
  top_positive : ∀ d H : Bool, 0 < N.fixedCapacity d H ⊤
  normalization : ∀ d H : Bool,
    Tomabechi.Theorem19.endpointNormalization (N.fixedCapacity d H ⊥) (N.fixedCapacity d H ⊤)
        (N.fixedCapacity d H ⊥) = 0 ∧
    Tomabechi.Theorem19.endpointNormalization (N.fixedCapacity d H ⊥) (N.fixedCapacity d H ⊤)
        (N.fixedCapacity d H ⊤) = 1
  /-- 従来の `sharedCapacity`（主体・履歴を動かす）と一致する（この証人の性質）。 -/
  agrees_with_shared : ∀ (d H : Bool) (a : CommonConcept), N.fixedCapacity d H a = N.sharedCapacity a

theorem sharedModel_fixedCapacityInputs : SharedFixedCapacityInputs sharedModel := by
  have h := sharedModel_preservation
  have hfe := sharedModel_fullExperimentInputs
  refine
    { nonempty := fun _ _ a => capacityAdmissibleFixed_nonempty a
      bounded := fun d H a => h.capacityScoreFixed_bounded d H a
      joint_from_experiment := fun d H c x T t => rfl
      joint_probability := fun d H c x T t => h.capacityJoint_isProbability _
      kl_finite := fun d H c x T t => h.capacityProblem_kl_finite _
      policy_admissible := fun c g x T hT => hfe.decoder_admissible c g x T hT
      policy_true_optimal := fun c x T => hfe.decoder_optimal c x T
      policy_distinct := fun c => hfe.decoder_distinct c
      policy_action_code := fun c g => fullInformationDecoder_action_code c g
      experiment_state_cost := fun d H c x T t =>
        SharedModelSignature.fullExperiment_stateCost sharedModel fullInformationDecoder d H c x T t
      experiment_self_process := fun d H c x T t =>
        h.fullExperiment_selfProcess fullInformationDecoder d H c x T t
      embedding := fun d H => ⟨fun {_ _} hab => capacityEmbeddingFixed hab,
        fun {_ _} hab => capacityEmbeddingFixed_injective hab,
        fun {_ _} hab {_} hp => hp, fun {_ _} hab {_} hp => rfl⟩
      capacity_le_log_two := fun d H a => ?_
      capacity_nonneg := fun d H a => ?_
      monotone := fun d H => h.fixedCapacity_monotone d H
      bottom_zero := fun d H => h.fixedCapacity_bottom d H
      top_positive := fun d H => by rw [h.fixedCapacity_top]; exact Real.log_pos (by norm_num)
      normalization := fun d H => ?_
      agrees_with_shared := fun d H a => h.fixedCapacity_eq_shared d H a }
  · rw [h.fixedCapacity_eq_shared]
    exact h.sharedCapacityInputs.capacity_le_log_two a
  · rw [h.fixedCapacity_eq_shared]
    exact h.sharedCapacityInputs.capacity_nonneg a
  · apply Tomabechi.Theorem19.endpointNormalization_values
    rw [h.fixedCapacity_bottom, h.fixedCapacity_top]; exact Real.log_pos (by norm_num)

/-- v9：v8 に、固定した主体・履歴の定理19容量を加えた存在宣言。 -/
theorem final_consistency_v9 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N ∧ MortalityOnN N ∧
        MortalityPresence25B ∧ Shared16CanonicalInputs N ∧ Shared25CanonicalSelf N ∧
        SharedSubjectIdentityCanonical N ∧ SharedCommonDomainX N ∧ SharedFixedCapacityInputs N :=
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
    sharedModel_borelStructure, sharedModel_genealogyMortality, sharedModel_shared16OnePointInputs,
    sharedModel_theorem21V0, sharedModel_shared25OnePointSelf,
    SharedModelSignature.sharedTheorem21V0Common sharedModel_theorem21V0
      sharedModel_stageSwitchInputs,
    sharedModel_mortalityOnN, mortalityPresence25B,
    sharedModel_shared16CanonicalInputs, sharedModel_shared25CanonicalSelf,
    sharedModel_subjectIdentityCanonical, sharedModel_commonDomainX,
    sharedModel_fixedCapacityInputs⟩

#print axioms SharedDataPreservation.fixedCapacity_eq_shared
#print axioms final_consistency_v9
#print axioms sharedModel_fixedCapacityInputs

end Tomabechi.Consistency.R123
