import Tomabechi.Consistency.ConsistencyR123_Final
import Tomabechi.Information.MeasureCMICapacity

/-!
# 定理19の容量を共通束 𝕃 全域へ

原文 §8 は、各抽象度 α ∈ 𝕃 で問題族が非空で、容量 ℱ(α) が有限、
α ≼ β なら評価値を保つ単射 ι_{αβ} があるとして ℱ が単調になると述べる。
従来は容量が C3 の `WithTop ℕ` 層の上だけにあり、共通束 `CommonConcept` 全体では
定理19の容量入口を適用していなかった。ここでは同じ `SharedModelSignature N` の
全共通束点の実験 joint `N.fullExperimentLaw` から容量を構成する。

* 点 α での問題族 `CapProblem a` は、α 以下の各層 c ≼ α での実験
  （主体 d・履歴 H・初期状態 x・開始時刻 T・時刻 t）の全体。
  すなわち「より低い抽象度の問題は高い抽象度の問題族にも含まれる」とする
  モデル化であり、これが埋込み ι の定義である（恒等的な包含）。
* 問題の joint は `N.fullExperimentLaw`（実軌道・実費用を含む）を、
  情報の三成分（入力・ゴール・実方策から再符号化した行為）へ押し出したもの。
  各問題の評価値は、その joint の直接CMI（`directActionGoalJoint` と
  `directCMIReference` の KL 発散）。
* 容量 ℱ(α) は `Theorem19.dependentLayerCapacity` そのもの。

証明するのは、`SharedDataPreservation N` を満たす N（かつ物理層・上位層の
情報 law が C3 のものと一致する、すなわち `sharedModel`）について、
各点で非空・有限KL・上界 log 2・単調・端点（ℱ(⊥)=0, ℱ(⊤)>0）・正規化が成り立つこと。
定理16と主体の同一性（原文 M8.1）、他の主体・他のゴール型への一般化は主張しない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 情報 joint（入力・ゴール・行為）から直接CMIの評価値を読む。
確率測度でない場合は 0（実際には使わない）。 -/
def capacityScoreLaw (J : Measure (Unit × Bool × Bool)) : ℝ :=
  open Classical in
  if h : IsProbabilityMeasure J then
    (haveI := h
    (InformationTheory.klDiv (Tomabechi.Theorem19_22.directActionGoalJoint J)
      (Tomabechi.Theorem19_22.directCMIReference J)).toReal)
  else 0

/-- 層 c の実験データ。主体・履歴・初期状態・開始時刻・時刻。 -/
abbrev CapExperiment (c : CommonConcept) :=
  Bool × Bool × fullCommonLayerState c × ℝ × ℝ

/-- 点 a の問題族。a 以下の層 c と、その層の実験データ。 -/
abbrev CapProblem (a : CommonConcept) :=
  Σ c : {c : CommonConcept // c ≤ a}, CapExperiment c.1

/-- 実験 joint を情報の三成分へ押し出した joint。 -/
def SharedModelSignature.capacityJoint (N : SharedModelSignature) {c : CommonConcept}
    (e : CapExperiment c) : Measure (Unit × Bool × Bool) :=
  (N.fullExperimentLaw fullInformationDecoder e.1 e.2.1 c e.2.2.1 e.2.2.2.1 e.2.2.2.2).map
    (fun z => (z.1.2.1, z.1.2.2.1, fullActionEncode c (fullInformationDecoder c z.1.2.2.2)))

/-- 許容問題：開始時刻が非負（復号方策の許容性の条件）。 -/
def capacityAdmissible (a : CommonConcept) : Set (CapProblem a) :=
  {p | 0 ≤ p.2.2.2.2.1}

/-- 問題の評価値。 -/
def SharedModelSignature.capacityScore (N : SharedModelSignature) (a : CommonConcept)
    (p : CapProblem a) : ℝ :=
  capacityScoreLaw (N.capacityJoint p.2)

/-- 点 a の容量 ℱ(a)（定理19の依存型容量）。 -/
def SharedModelSignature.sharedCapacity (N : SharedModelSignature) (a : CommonConcept) : ℝ :=
  Tomabechi.Theorem19.dependentLayerCapacity CapProblem capacityAdmissible
    N.capacityScore a


/-! ## 各問題の joint と評価値 -/

/-- 全点・全実験で、押し出した joint は N.informationLaw そのもの。 -/
theorem SharedDataPreservation.capacityJoint_eq {N : SharedModelSignature}
    (h : SharedDataPreservation N) {c : CommonConcept} (e : CapExperiment c) :
    N.capacityJoint e = N.informationLaw c :=
  h.fullExperiment_actualActionInformation e.1 e.2.1 c e.2.2.1 e.2.2.2.1 e.2.2.2.2

theorem SharedDataPreservation.informationLaw_bot {N : SharedModelSignature}
    (h : SharedDataPreservation N) :
    N.informationLaw ⊥ = Tomabechi.Consistency.C3.physicalLayerLaw.joint := by
  rw [h.information, commonConceptInformationIndex_bottom]
  exact h.legacy_couplings.physical_information

theorem SharedDataPreservation.informationLaw_of_ne_bot {N : SharedModelSignature}
    (h : SharedDataPreservation N) {c : CommonConcept} (hc : c ≠ ⊥) :
    N.informationLaw c = Tomabechi.Consistency.C3.upperJoint := by
  rw [h.information]
  have hpos := commonConceptInformationIndex_positive_of_ne_bottom hc
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hk]
  exact h.legacy_couplings.stage_information k

theorem capacityScoreLaw_physical :
    capacityScoreLaw Tomabechi.Consistency.C3.physicalLayerLaw.joint = 0 := by
  have hp := Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
  unfold capacityScoreLaw
  rw [dif_pos hp]
  exact Tomabechi.Consistency.C3.physicalCMIPair_score_zero

theorem capacityScoreLaw_upper :
    capacityScoreLaw Tomabechi.Consistency.C3.upperJoint = Real.log 2 := by
  have hp := Tomabechi.Consistency.C3.upperJoint_isProbability
  unfold capacityScoreLaw
  rw [dif_pos hp]
  exact Tomabechi.Consistency.C3.upperCMIPair_score_log_two

theorem capacityKL_physical_finite :
    haveI := Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
    InformationTheory.klDiv
      (Tomabechi.Theorem19_22.directActionGoalJoint
        Tomabechi.Consistency.C3.physicalLayerLaw.joint)
      (Tomabechi.Theorem19_22.directCMIReference
        Tomabechi.Consistency.C3.physicalLayerLaw.joint) ≠ ⊤ :=
  Tomabechi.Consistency.C3.physicalCMIPair_kl_finite

theorem capacityKL_upper_finite :
    haveI := Tomabechi.Consistency.C3.upperJoint_isProbability
    InformationTheory.klDiv
      (Tomabechi.Theorem19_22.directActionGoalJoint Tomabechi.Consistency.C3.upperJoint)
      (Tomabechi.Theorem19_22.directCMIReference Tomabechi.Consistency.C3.upperJoint) ≠ ⊤ :=
  Tomabechi.Consistency.C3.upperCMIPair_kl_finite

/-- 問題の評価値：底の層の問題は 0、それ以外は log 2。 -/
theorem SharedDataPreservation.capacityScore_eq {N : SharedModelSignature}
    (h : SharedDataPreservation N) (a : CommonConcept) (p : CapProblem a) :
    N.capacityScore a p = if p.1.1 = ⊥ then 0 else Real.log 2 := by
  unfold SharedModelSignature.capacityScore
  rw [h.capacityJoint_eq]
  by_cases hc : p.1.1 = ⊥
  · rw [if_pos hc, hc, h.informationLaw_bot]; exact capacityScoreLaw_physical
  · rw [if_neg hc, h.informationLaw_of_ne_bot hc]; exact capacityScoreLaw_upper

theorem SharedDataPreservation.capacityJoint_isProbability {N : SharedModelSignature}
    (h : SharedDataPreservation N) {c : CommonConcept} (e : CapExperiment c) :
    IsProbabilityMeasure (N.capacityJoint e) := by
  rw [h.capacityJoint_eq]; exact h.fullInformation_probability c

/-- 各問題の KL は有限（原文 §8 の「容量が有限」の前提）。 -/
theorem SharedDataPreservation.capacityProblem_kl_finite {N : SharedModelSignature}
    (h : SharedDataPreservation N) {c : CommonConcept} (e : CapExperiment c) :
    haveI := h.capacityJoint_isProbability e
    InformationTheory.klDiv
        (Tomabechi.Theorem19_22.directActionGoalJoint (N.capacityJoint e))
        (Tomabechi.Theorem19_22.directCMIReference (N.capacityJoint e)) ≠ ⊤ := by
  have key : ∀ (J : Measure (Unit × Bool × Bool)) [IsProbabilityMeasure J],
      (J = Tomabechi.Consistency.C3.physicalLayerLaw.joint ∨
        J = Tomabechi.Consistency.C3.upperJoint) →
      InformationTheory.klDiv (Tomabechi.Theorem19_22.directActionGoalJoint J)
        (Tomabechi.Theorem19_22.directCMIReference J) ≠ ⊤ := by
    intro J _ hJ
    rcases hJ with rfl | rfl
    · exact capacityKL_physical_finite
    · exact capacityKL_upper_finite
  haveI := h.capacityJoint_isProbability e
  apply key
  rw [h.capacityJoint_eq]
  by_cases hc : c = ⊥
  · exact Or.inl (by rw [hc, h.informationLaw_bot])
  · exact Or.inr (h.informationLaw_of_ne_bot hc)


/-! ## 容量の性質：非空・上界・単調・端点・正規化 -/

/-- 各層の状態型は非空（有限層は二座標実数、頂点は動径ベクトル状態）。 -/
theorem capacityState_nonempty (c : CommonConcept) : Nonempty (fullCommonLayerState c) := by
  unfold fullCommonLayerState
  generalize fullCommonLayerIndex c = i
  induction i using WithTop.recTopCoe with
  | top => exact ⟨(Tomabechi.Examples.Theorem27Op.e0 : Tomabechi.Examples.Theorem27Op.E2)⟩
  | coe _ => exact ⟨fun _ => 0⟩

/-- 層の包含 a ≼ b による問題の埋込み ι_{ab}：層 c ≼ a の問題を同じ問題として b の族へ移す。 -/
def capacityEmbedding {a b : CommonConcept} (hab : a ≤ b) (p : CapProblem a) : CapProblem b :=
  ⟨⟨p.1.1, p.1.2.trans hab⟩, p.2⟩

theorem capacityEmbedding_injective {a b : CommonConcept} (hab : a ≤ b) :
    Function.Injective (capacityEmbedding hab) := by
  rintro ⟨⟨c, hc⟩, e⟩ ⟨⟨c', hc'⟩, e'⟩ h
  simp only [capacityEmbedding, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have : c = c' := congrArg Subtype.val h1
  subst this
  simpa using h2

theorem capacityEmbedding_mapsTo {a b : CommonConcept} (hab : a ≤ b) {p : CapProblem a}
    (hp : p ∈ capacityAdmissible a) : capacityEmbedding hab p ∈ capacityAdmissible b := hp

theorem capacityEmbedding_score {N : SharedModelSignature} {a b : CommonConcept} (hab : a ≤ b)
    {p : CapProblem a} (_ : p ∈ capacityAdmissible a) :
    N.capacityScore b (capacityEmbedding hab p) = N.capacityScore a p := rfl

theorem capacityAdmissible_nonempty (a : CommonConcept) : (capacityAdmissible a).Nonempty := by
  obtain ⟨x⟩ := capacityState_nonempty (⊥ : CommonConcept)
  exact ⟨⟨⟨⊥, bot_le⟩, (false, false, x, 0, 0)⟩, le_refl (0 : ℝ)⟩

theorem SharedDataPreservation.capacityScore_le_log_two {N : SharedModelSignature}
    (h : SharedDataPreservation N) (a : CommonConcept) (p : CapProblem a) :
    N.capacityScore a p ≤ Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [h.capacityScore_eq]
  split_ifs <;> linarith

theorem SharedDataPreservation.capacityScore_bounded {N : SharedModelSignature}
    (h : SharedDataPreservation N) (a : CommonConcept) :
    BddAbove (N.capacityScore a '' capacityAdmissible a) :=
  ⟨Real.log 2, by rintro _ ⟨p, _, rfl⟩; exact h.capacityScore_le_log_two a p⟩

/-- ℱ は全共通束点で単調。定理19の埋込み入口を共通束全域に適用した結果。 -/
theorem SharedDataPreservation.sharedCapacity_monotone {N : SharedModelSignature}
    (h : SharedDataPreservation N) : Monotone N.sharedCapacity := by
  intro a b hab
  exact Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding
    CapProblem capacityAdmissible N.capacityScore capacityAdmissible_nonempty
    h.capacityScore_bounded (fun {_ _} hab => capacityEmbedding hab)
    (fun {_ _} hab => capacityEmbedding_injective hab)
    (fun {_ _} hab {_} hp => capacityEmbedding_mapsTo hab hp)
    (fun {_ _} hab {_} hp => capacityEmbedding_score hab hp) a b hab

theorem SharedDataPreservation.sharedCapacity_bottom {N : SharedModelSignature}
    (h : SharedDataPreservation N) : N.sharedCapacity ⊥ = 0 := by
  unfold SharedModelSignature.sharedCapacity Tomabechi.Theorem19.dependentLayerCapacity
  have himg : N.capacityScore ⊥ '' capacityAdmissible ⊥ = {0} := by
    ext r
    constructor
    · rintro ⟨p, _, rfl⟩
      have hc : p.1.1 = ⊥ := le_bot_iff.mp p.1.2
      rw [h.capacityScore_eq, if_pos hc]; rfl
    · intro hr
      obtain ⟨q, hq⟩ := capacityAdmissible_nonempty (⊥ : CommonConcept)
      refine ⟨q, hq, ?_⟩
      have hc : q.1.1 = ⊥ := le_bot_iff.mp q.1.2
      rw [h.capacityScore_eq, if_pos hc]; exact (Set.mem_singleton_iff.mp hr).symm
  rw [himg]; simp

theorem SharedDataPreservation.sharedCapacity_top {N : SharedModelSignature}
    (h : SharedDataPreservation N) : N.sharedCapacity ⊤ = Real.log 2 := by
  unfold SharedModelSignature.sharedCapacity Tomabechi.Theorem19.dependentLayerCapacity
  obtain ⟨x⟩ := capacityState_nonempty (⊤ : CommonConcept)
  let p : CapProblem ⊤ := ⟨⟨⊤, le_refl _⟩, (false, false, x, 0, 0)⟩
  have hp : p ∈ capacityAdmissible ⊤ := le_refl (0 : ℝ)
  have hscore : N.capacityScore ⊤ p = Real.log 2 := by
    rw [h.capacityScore_eq, if_neg (by simp [p])]
  apply le_antisymm
  · exact csSup_le ((capacityAdmissible_nonempty ⊤).image _)
      (by rintro _ ⟨q, _, rfl⟩; exact h.capacityScore_le_log_two ⊤ q)
  · rw [← hscore]
    exact le_csSup (h.capacityScore_bounded ⊤) ⟨p, hp, rfl⟩

/-- 共通束全域の定理19容量の受入型：非空・各問題のKL有限・容量有限（上界 log 2）・
埋込みの存在・単調・端点・正規化。 -/
structure SharedCapacityInputs (N : SharedModelSignature) : Prop where
  nonempty : ∀ a, (capacityAdmissible a).Nonempty
  probability : ∀ {c : CommonConcept} (e : CapExperiment c), IsProbabilityMeasure (N.capacityJoint e)
  kl_finite : ∀ {c : CommonConcept} (e : CapExperiment c),
    haveI := probability e
    InformationTheory.klDiv
        (Tomabechi.Theorem19_22.directActionGoalJoint (N.capacityJoint e))
        (Tomabechi.Theorem19_22.directCMIReference (N.capacityJoint e)) ≠ ⊤
  bounded : ∀ a, BddAbove (N.capacityScore a '' capacityAdmissible a)
  capacity_le_log_two : ∀ a, N.sharedCapacity a ≤ Real.log 2
  capacity_nonneg : ∀ a, 0 ≤ N.sharedCapacity a
  embedding : ∃ ι : ∀ {a b : CommonConcept}, a ≤ b → CapProblem a → CapProblem b,
    (∀ {a b} (hab : a ≤ b), Function.Injective (ι hab)) ∧
    (∀ {a b} (hab : a ≤ b) {p}, p ∈ capacityAdmissible a → ι hab p ∈ capacityAdmissible b) ∧
    (∀ {a b} (hab : a ≤ b) {p}, p ∈ capacityAdmissible a →
      N.capacityScore b (ι hab p) = N.capacityScore a p)
  monotone : Monotone N.sharedCapacity
  bottom_zero : N.sharedCapacity ⊥ = 0
  top_positive : 0 < N.sharedCapacity ⊤
  normalization :
    Tomabechi.Theorem19.endpointNormalization (N.sharedCapacity ⊥) (N.sharedCapacity ⊤)
        (N.sharedCapacity ⊥) = 0 ∧
    Tomabechi.Theorem19.endpointNormalization (N.sharedCapacity ⊥) (N.sharedCapacity ⊤)
        (N.sharedCapacity ⊤) = 1

theorem SharedDataPreservation.sharedCapacityInputs {N : SharedModelSignature}
    (h : SharedDataPreservation N) : SharedCapacityInputs N where
  nonempty := capacityAdmissible_nonempty
  probability := fun e => h.capacityJoint_isProbability e
  kl_finite := fun e => h.capacityProblem_kl_finite e
  bounded := h.capacityScore_bounded
  capacity_le_log_two := fun a => by
    unfold SharedModelSignature.sharedCapacity Tomabechi.Theorem19.dependentLayerCapacity
    exact csSup_le ((capacityAdmissible_nonempty a).image _)
      (by rintro _ ⟨q, _, rfl⟩; exact h.capacityScore_le_log_two a q)
  capacity_nonneg := fun a => by
    have := h.sharedCapacity_monotone (bot_le : (⊥ : CommonConcept) ≤ a)
    rwa [h.sharedCapacity_bottom] at this
  embedding := ⟨fun {_ _} hab => capacityEmbedding hab,
    fun {_ _} hab => capacityEmbedding_injective hab,
    fun {_ _} hab {_} hp => capacityEmbedding_mapsTo hab hp,
    fun {_ _} hab {_} hp => capacityEmbedding_score hab hp⟩
  monotone := h.sharedCapacity_monotone
  bottom_zero := h.sharedCapacity_bottom
  top_positive := by
    rw [h.sharedCapacity_top]; exact Real.log_pos (by norm_num)
  normalization := by
    apply Tomabechi.Theorem19.endpointNormalization_values
    rw [h.sharedCapacity_bottom, h.sharedCapacity_top]; exact Real.log_pos (by norm_num)

/-- 同じ `sharedModel` で全共通束点の定理19容量入力が成り立つ。 -/
theorem sharedModel_capacityInputs : SharedCapacityInputs sharedModel :=
  sharedModel_preservation.sharedCapacityInputs

/-- 原文前提・明示追加条件・非退化性に、共通束全域の容量入力を加えた存在宣言。 -/
theorem final_consistency_with_shared_capacity :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        SharedCapacityInputs N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_capacityInputs⟩

#print axioms SharedDataPreservation.sharedCapacity_monotone
#print axioms SharedDataPreservation.sharedCapacity_bottom
#print axioms SharedDataPreservation.sharedCapacity_top
#print axioms sharedModel_capacityInputs
#print axioms final_consistency_with_shared_capacity
end Tomabechi.Consistency.R123
