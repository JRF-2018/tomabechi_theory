import Tomabechi.Consistency.ConsistencyR123_CurrentPremises

/-!
# 定理19の容量を「問題 × 方策」の上限として

原文 §8 は `ℱ_i(α) = sup_{(d,π) ∈ 𝔠_{i,α}} I(G_d; Y_d^π | X_d)` と、**問題 `d` と方策 `π` の組**の上限を取る。
`fixedCapacity`の問題は方策の添字を持たず、固定した一つの `fullInformationDecoder` に委譲していた。
`decode c false`／`decode c true` は、その一つの decoder が出す**二つの実制御方策**であって、二つのゴール条件付き
写像ではない。

ここでは方策族を型に入れる。

* **方策族 `Pol`：** 一つのゴール条件付き decoder `fullInformationDecoder`（物理層以外ではゴール `Bool` から実制御方策への
  写像）の**一元集合**（`CapPolicy := {δ // δ = fullInformationDecoder}`）。
* **問題×方策：** `CapProblemPolicy a := CapProblemFixed a × CapPolicy`。評価値 `policyScore` は、**その方策 δ から**
  実験 joint（`fullExperimentLaw δ`）を作り、情報三成分へ押し出した joint の直接CMIである（固定 decoder への
  委譲ではなく、方策から joint を生成する）。
* **容量：** `fixedPolicyCapacity := dependentLayerCapacity CapProblemPolicy …`。`fixedCapacity`・`sharedCapacity` と一致。
  方策の許容性（`N.data.admissible`）は許容集合の条件に入れる。包含埋込みは問題・方策を保ち、評価値を保つ。

**範囲：** 原文は方策族 `Pol` の大きさを要求しない。ここでは**一元の方策族**という読みで、現行容量が原文の
「問題×方策の上限」の一例になることを証明した。native の全方策に対する上限が現行容量に一致するとは
**主張しない**（全方策版は未実施）。非退化性は、上層で decoder がゴールの差を実制御の差へ写して `log 2` を達成すること。
-/

open MeasureTheory

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 方策族 `Pol`：一つのゴール条件付き decoder の一元集合。 -/
def capPolicySet : Set SharedInformationDecoder := {fullInformationDecoder}

abbrev CapPolicy := {δ : SharedInformationDecoder // δ ∈ capPolicySet}

def capPolicyTheOne : CapPolicy := ⟨fullInformationDecoder, rfl⟩

theorem capPolicy_eq_the_one (π : CapPolicy) : π.1 = fullInformationDecoder := π.2

/-- 問題 × 方策。 -/
abbrev CapProblemPolicy (a : CommonConcept) := CapProblemFixed a × CapPolicy

/-- decoder `δ` の実方策が全層・全ゴールで許容的（開始時刻 `T ≥ 0`）。 -/
def PolicyAdmissible (N : SharedModelSignature) (δ : SharedInformationDecoder) : Prop :=
  ∀ (c : CommonConcept) (g : Bool) (x : fullCommonLayerState c) (T : ℝ), 0 ≤ T →
    N.data.admissible c (δ c g) x T

/-- 許容な問題×方策：開始時刻が非負、方策が許容的。 -/
def capacityAdmissiblePolicy (N : SharedModelSignature) (a : CommonConcept) :
    Set (CapProblemPolicy a) :=
  {q | q.1 ∈ capacityAdmissibleFixed a ∧ PolicyAdmissible N q.2.1}

/-- 方策 `δ` から生成した情報 joint（入力・ゴール・行為）。 -/
def SharedModelSignature.policyJoint (N : SharedModelSignature) (d H : Bool)
    (δ : SharedInformationDecoder) {c : CommonConcept} (x : fullCommonLayerState c) (T t : ℝ) :
    Measure (Unit × Bool × Bool) :=
  (N.fullExperimentLaw δ d H c x T t).map
    (fun z => (z.1.2.1, z.1.2.2.1, fullActionEncode c (δ c z.1.2.2.2)))

/-- 問題×方策の評価値：その方策から生成した joint の直接CMI。 -/
def SharedModelSignature.policyScore (N : SharedModelSignature) (d H : Bool) (a : CommonConcept)
    (q : CapProblemPolicy a) : ℝ :=
  capacityScoreLaw (N.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2)

/-- 固定した `(d,H)` の、問題×方策の上限としての容量。 -/
def SharedModelSignature.fixedPolicyCapacity (N : SharedModelSignature) (d H : Bool)
    (a : CommonConcept) : ℝ :=
  Tomabechi.Theorem19.dependentLayerCapacity CapProblemPolicy (capacityAdmissiblePolicy N)
    (N.policyScore d H) a

/-- 包含による問題×方策の埋込み（問題は層の埋込み、方策は保つ）。 -/
def capacityEmbeddingPolicy {a b : CommonConcept} (hab : a ≤ b) (q : CapProblemPolicy a) :
    CapProblemPolicy b :=
  (capacityEmbeddingFixed hab q.1, q.2)

theorem capacityEmbeddingPolicy_injective {a b : CommonConcept} (hab : a ≤ b) :
    Function.Injective (capacityEmbeddingPolicy hab) := by
  rintro ⟨p, π⟩ ⟨p', π'⟩ h
  simp only [capacityEmbeddingPolicy, Prod.mk.injEq] at h
  rw [capacityEmbeddingFixed_injective hab h.1, h.2]

/-- 方策が一元なので、方策から生成した joint は固定 decoder の `capacityJoint`。 -/
theorem policyJoint_the_one (N : SharedModelSignature) (d H : Bool) {c : CommonConcept}
    (x : fullCommonLayerState c) (T t : ℝ) :
    N.policyJoint d H fullInformationDecoder x T t = N.capacityJoint (d, H, x, T, t) := rfl

theorem policyScore_eq_fixed (N : SharedModelSignature) (d H : Bool) (a : CommonConcept)
    (q : CapProblemPolicy a) : N.policyScore d H a q = N.capacityScoreFixed d H a q.1 := by
  obtain ⟨p, π, hπ⟩ := q
  have : π = fullInformationDecoder := hπ
  subst this
  rfl

theorem capacityAdmissiblePolicy_nonempty {N : SharedModelSignature}
    (hN : PolicyAdmissible N fullInformationDecoder) (a : CommonConcept) :
    (capacityAdmissiblePolicy N a).Nonempty := by
  obtain ⟨p, hp⟩ := capacityAdmissibleFixed_nonempty a
  exact ⟨(p, capPolicyTheOne), hp, hN⟩

/-- 一元の方策族の上で、問題×方策の上限は `fixedCapacity` に一致する。 -/
theorem fixedPolicyCapacity_eq_fixed {N : SharedModelSignature}
    (hN : PolicyAdmissible N fullInformationDecoder) (d H : Bool) (a : CommonConcept) :
    N.fixedPolicyCapacity d H a = N.fixedCapacity d H a := by
  unfold SharedModelSignature.fixedPolicyCapacity SharedModelSignature.fixedCapacity
    Tomabechi.Theorem19.dependentLayerCapacity
  congr 1
  ext r
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, hq.1, (policyScore_eq_fixed N d H a q).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p, capPolicyTheOne), ⟨hp, hN⟩, policyScore_eq_fixed N d H a _⟩

/-- 問題×方策の容量の受入型。 -/
structure SharedPolicyCapacityInputs (N : SharedModelSignature) : Prop where
  policy_the_one : ∀ π : CapPolicy, π.1 = fullInformationDecoder
  policy_admissible : ∀ π : CapPolicy, PolicyAdmissible N π.1
  /-- 二つの値は二つの実制御方策（ゴール条件付き写像は一つ）で、再符号化で戻る。 -/
  policy_values_distinct : ∀ c : CommonConcept,
    fullInformationDecoder c false ≠ fullInformationDecoder c true
  policy_action_code : ∀ (c : CommonConcept) (g : Bool),
    fullActionEncode c (fullInformationDecoder c g) = g
  nonempty : ∀ a : CommonConcept, (capacityAdmissiblePolicy N a).Nonempty
  /-- 各問題×方策の joint は、その方策の実験 joint の押し出しで、情報法則そのもの。 -/
  joint_from_policy : ∀ (d H : Bool) {a : CommonConcept} (q : CapProblemPolicy a),
    N.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 =
      (N.fullExperimentLaw q.2.1 d H q.1.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2).map
        (fun z => (z.1.2.1, z.1.2.2.1, fullActionEncode q.1.1.1 (q.2.1 q.1.1.1 z.1.2.2.2)))
  joint_information : ∀ (d H : Bool) {a : CommonConcept} (q : CapProblemPolicy a),
    N.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 = N.informationLaw q.1.1.1
  score_eq_fixed : ∀ (d H : Bool) (a : CommonConcept) (q : CapProblemPolicy a),
    N.policyScore d H a q = N.capacityScoreFixed d H a q.1
  capacity_eq_fixed : ∀ d H a, N.fixedPolicyCapacity d H a = N.fixedCapacity d H a
  capacity_eq_shared : ∀ d H a, N.fixedPolicyCapacity d H a = N.sharedCapacity a
  capacity_le_log_two : ∀ d H a, N.fixedPolicyCapacity d H a ≤ Real.log 2
  capacity_nonneg : ∀ d H a, 0 ≤ N.fixedPolicyCapacity d H a
  monotone : ∀ d H, Monotone (N.fixedPolicyCapacity d H)
  bottom_zero : ∀ d H, N.fixedPolicyCapacity d H ⊥ = 0
  top_log_two : ∀ d H, N.fixedPolicyCapacity d H ⊤ = Real.log 2
  /-- 包含埋込みは問題×方策を保ち、単射・許容性・評価値を保存。 -/
  embedding_injective : ∀ {a b : CommonConcept} (hab : a ≤ b),
    Function.Injective (capacityEmbeddingPolicy hab)
  embedding_admissible : ∀ {a b : CommonConcept} (hab : a ≤ b) {q : CapProblemPolicy a},
    q ∈ capacityAdmissiblePolicy N a → capacityEmbeddingPolicy hab q ∈ capacityAdmissiblePolicy N b
  embedding_score : ∀ (d H : Bool) {a b : CommonConcept} (hab : a ≤ b) (q : CapProblemPolicy a),
    N.policyScore d H b (capacityEmbeddingPolicy hab q) = N.policyScore d H a q

theorem sharedModel_policyCapacityInputs : SharedPolicyCapacityInputs sharedModel := by
  have h := sharedModel_preservation
  have hfe := sharedModel_fullExperimentInputs
  have hN : PolicyAdmissible sharedModel fullInformationDecoder :=
    fun c g x T hT => hfe.decoder_admissible c g x T hT
  have hcap := sharedModel_fixedCapacityInputs
  refine
    { policy_the_one := capPolicy_eq_the_one
      policy_admissible := fun π => by rw [capPolicy_eq_the_one π]; exact hN
      policy_values_distinct := fun c => hfe.decoder_distinct c
      policy_action_code := fun c g => fullInformationDecoder_action_code c g
      nonempty := fun a => capacityAdmissiblePolicy_nonempty hN a
      joint_from_policy := fun d H c q => rfl
      joint_information := fun d H c q => ?_
      score_eq_fixed := fun d H a q => policyScore_eq_fixed sharedModel d H a q
      capacity_eq_fixed := fun d H a => fixedPolicyCapacity_eq_fixed hN d H a
      capacity_eq_shared := fun d H a => ?_
      capacity_le_log_two := fun d H a => ?_
      capacity_nonneg := fun d H a => ?_
      monotone := fun d H a b hab => ?_
      bottom_zero := fun d H => ?_
      top_log_two := fun d H => ?_
      embedding_injective := fun {_ _} hab => capacityEmbeddingPolicy_injective hab
      embedding_admissible := fun {_ _} hab {_} hq => hq
      embedding_score := fun d H {_ _} hab q => rfl }
  · have hq := capPolicy_eq_the_one q.2
    have e : sharedModel.policyJoint d H q.2.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 =
        sharedModel.capacityJoint (d, H, q.1.2.1, q.1.2.2.1, q.1.2.2.2) := by
      rw [hq]; rfl
    rw [e]; exact h.capacityJoint_eq _
  · rw [fixedPolicyCapacity_eq_fixed hN, h.fixedCapacity_eq_shared]
  · rw [fixedPolicyCapacity_eq_fixed hN]; exact hcap.capacity_le_log_two d H a
  · rw [fixedPolicyCapacity_eq_fixed hN]; exact hcap.capacity_nonneg d H a
  · rw [fixedPolicyCapacity_eq_fixed hN, fixedPolicyCapacity_eq_fixed hN]
    exact hcap.monotone d H hab
  · rw [fixedPolicyCapacity_eq_fixed hN]; exact hcap.bottom_zero d H
  · rw [fixedPolicyCapacity_eq_fixed hN, h.fixedCapacity_top]

/-- 現行評価の前件・全正典担体の自己過程・問題×方策の容量を同じ `N` で。 -/
theorem final_consistency_with_policy_capacity :
    ∃ N sig, SharedFinalConsistency N ∧ LayerControlSound N sig ∧ Shared25FullSelf N ∧
      FullOriginalPremisesCurrent N ∧ SharedPolicyCapacityInputs N :=
  ⟨sharedModel, velocityLayerControlSignature, sharedModel_finalConsistency,
    sharedModel_layerControlSound, sharedModel_shared25FullSelf,
    sharedModel_fullOriginalPremisesCurrent, sharedModel_policyCapacityInputs⟩

#print axioms fixedPolicyCapacity_eq_fixed
#print axioms sharedModel_policyCapacityInputs
#print axioms final_consistency_with_policy_capacity

end Tomabechi.Consistency.R123
