import Tomabechi.Consistency.ConsistencyR123_SharedStageSwitch

/-!
# 同じNの平均場段階と直接KL情報量

MeanFieldStageInputの全解析前件と同じ平均場の支持/枝/LUB対応を使う。
情報jointは同じN.informationLawの段住所に同定し、21の四結論を保持する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C3 Tomabechi.Consistency.C6
open Tomabechi.Theorem21 Tomabechi.Theorem22 Tomabechi.Theorem19_22

/-- 同じ共通束の真部分住所を支持とする情報枝。 -/
def sharedStageBranch (n : ℕ) : Theorem21BranchContext CommonConcept where
  branch := {sharedStageU n}
  symbolSupport := {sharedStageU n}
  support_nonempty := Set.singleton_nonempty _
  top_not_in_branch := by
    simp only [Set.mem_singleton_iff]
    exact (ne_of_lt (sharedStageU_below_top n)).symm
  support_lub := by simp only [csSup_singleton]; exact isLUB_singleton
  address_in_branch := by simp

/-- Nの実平均場presentationと同じ共通束枝を結ぶ全前件。 -/
structure SharedStageInformationInputs (N : SharedModelSignature) where
  joint : ∀ n, N.informationLaw (N.stageAddress n) = upperJoint
  branchRepresentation : ∀ n, (N.stages n).averagePresentation.Atom → CommonConcept
  faithful : ∀ n, Function.Injective (branchRepresentation n)
  monotone : ∀ n a b, (N.stages n).averagePresentation.atomOrder.le a b →
    branchRepresentation n a ≤ branchRepresentation n b
  branch : ∀ n, (sharedStageBranch n).branch =
    branchRepresentation n '' (N.stages n).averagePresentation.sourceLayer
  support : ∀ n, (sharedStageBranch n).symbolSupport =
    branchRepresentation n '' (N.stages n).averagePresentation.measureSupport
  top : ∀ n, branchRepresentation n (N.stages n).averagePresentation.abstractTop = ⊤
  lub : ∀ n, branchRepresentation n (N.stages n).averagePresentation.supportLub =
    sSup (sharedStageBranch n).symbolSupport

/-- N.stagesの解析前件と支持前件を21の一般入口に直接渡す。 -/
def SharedStageInformationInputs.theorem21 {N : SharedModelSignature}
    (h : SharedStageInformationInputs N) (n : ℕ) :=
  And.intro (h.joint n) (meanField_stage_theorem21_four_conclusions_directKL
    (N.stages n) (sharedStageBranch n)
    (Measure.dirac ()) inputMass inputAction (fun _ => sharedStageU n)
    inputAction_measurable
    (by filter_upwards with x; intro g hg; exact Set.mem_singleton _)
    (by filter_upwards with x; exact inputMass_nonneg x)
    (by filter_upwards with x; exact inputMass_sum x)
    (by filter_upwards with x; exact inputAction_injective x)
    inputMass_measurable inputEntropy_pos
    (h.branchRepresentation n) (h.faithful n) (h.monotone n)
    (h.branch n) (h.support n) (h.top n) (h.lub n))

/-- 同じ段列へ22の全谷・指数軌道一般入口を適用する。 -/
def SharedModelSignature.theorem22 (N : SharedModelSignature) :=
  all_mean_field_stages_have_global_valley_orbits N.stages

/-- 共通束上の忠実な旧原子埋込みが具体平均場の枝対応を満たす。 -/
def sharedModel_stageInformationInputs : SharedStageInformationInputs sharedModel := by
  refine {
    joint := ?_
    branchRepresentation := fun _ => layerAddressEmbedding
    faithful := fun _ => layerAddressEmbedding.injective
    monotone := fun _ _ _ h => layerAddressEmbedding.monotone h
    branch := ?_
    support := ?_
    top := fun _ => layerAddress_top
    lub := ?_ }
  · intro n
    rw [sharedModel_preservation.stage_information]
    exact commonModel_additionalConditions.stage_information n
  · intro n
    change {sharedStageU n} = layerAddressEmbedding '' {((n + 1 : ℕ) : Atom)}
    simp [sharedStageU, layerU]
  · intro n
    change {sharedStageU n} = layerAddressEmbedding '' {((n + 1 : ℕ) : Atom)}
    simp [sharedStageU, layerU]
  · intro n
    change layerAddressEmbedding ((n + 1 : ℕ) : Atom) = sSup {sharedStageU n}
    simp [sharedStageU, layerU]

/-- 同じNの段住所情報lawを読む直接KL型CMI。 -/
def SharedStageInformationInputs.cmiScore {N : SharedModelSignature}
    (h : SharedStageInformationInputs N) (n : ℕ) : ℝ :=
  letI : IsProbabilityMeasure (N.informationLaw (N.stageAddress n)) := by
    rw [h.joint n]
    exact upperJoint_isProbability
  (InformationTheory.klDiv
    (directActionGoalJoint (N.informationLaw (N.stageAddress n)))
    (directCMIReference (N.informationLaw (N.stageAddress n)))).toReal

/-- 21の第4結論は別lawのスコアではなくN自身のjointで成立する。 -/
theorem SharedStageInformationInputs.cmiScore_eq_entropy {N : SharedModelSignature}
    (h : SharedStageInformationInputs N) (n : ℕ) :
    h.cmiScore n = conditionalGoalEntropy (Measure.dirac ()) inputMass ∧ 0 < h.cmiScore n := by
  rcases (h.theorem21 n).2 with ⟨w, hmin, hshift, horbit, hinfo⟩
  have hscore : h.cmiScore n = finiteGoalActionGeneratedJoint_directCMIScore
      (Measure.dirac ()) inputMass inputMass_measurable
      (by filter_upwards with x; exact inputMass_nonneg x)
      (by filter_upwards with x; exact inputMass_sum x) inputAction inputAction_measurable
      (finiteGoal_nonempty_of_conditionalGoalEntropy_pos (Measure.dirac ()) inputMass inputEntropy_pos) := by
    unfold SharedStageInformationInputs.cmiScore
    simp only [h.joint n]
    rfl
  exact ⟨hscore.trans hinfo.1, hscore.symm ▸ hinfo.2.1⟩

#print axioms SharedStageInformationInputs.cmiScore_eq_entropy

#print axioms SharedStageInformationInputs.theorem21
#print axioms SharedModelSignature.theorem22
#print axioms sharedModel_stageInformationInputs
end Tomabechi.Consistency.R123
