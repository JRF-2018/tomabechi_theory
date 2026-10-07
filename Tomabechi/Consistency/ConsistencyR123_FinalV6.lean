import Tomabechi.Consistency.ConsistencyR123_SelfProcessOnePoint
import Tomabechi.Consistency.ConsistencyR123_MortalityOnN

/-!
# 最終存在宣言 v6：一点版の受入型と 25-C5 の N 上の実例をまとめる

`final_consistency_v5`（`ConsistencyR123_SelfProcessOnePoint`）と
`final_consistency_v5_mortality`（`ConsistencyR123_MortalityOnN`）は、別々のモジュールで
v4 に違う受入型を足していた。ここで両方を一つの `sharedModel` で同時に主張する。

あわせて、25-C5 の時刻依存の profile `profileT` が、条件25-B の現前支持の条件
（非空・上向き閉・⊤ を含む、最高層は非個体化マーカー）を全時刻で保つことを示す。
死後に物理層の座標が ∂ になっても、25-B は崩れない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.R1

/-- 時刻依存の profile の現前支持。 -/
def supportT (h d : Bool) (t : ℝ) : Set CommonConcept := {α | profileT h d t α ≠ none}

/-- 25-B を時刻依存の profile で：全時刻・全主体で、現前支持は非空・上向き閉・⊤ を含み、
⊤ の座標は非個体化マーカー `some ()`。 -/
structure MortalityPresence25B : Prop where
  nonempty : ∀ h d t, (supportT h d t).Nonempty
  upward_closed : ∀ h d t α β, α ∈ supportT h d t → α ≤ β → β ∈ supportT h d t
  top_mem : ∀ h d t, (⊤ : CommonConcept) ∈ supportT h d t
  top_marker : ∀ h d t, profileT h d t ⊤ = some ()

theorem bot_ne_top_commonConcept : (⊥ : CommonConcept) ≠ ⊤ := by
  intro h
  have := congrFun h 0
  simp at this

theorem mortalityPresence25B : MortalityPresence25B := by
  have htop : ∀ h d t, profileT h d t ⊤ = some () := by
    intro h d t
    simp [profileT, (bot_ne_top_commonConcept).symm]
  refine ⟨fun h d t => ⟨⊤, by simp [supportT, htop]⟩, ?_, fun h d t => by simp [supportT, htop], htop⟩
  intro h d t α β hα hαβ
  simp only [supportT, Set.mem_ofPred_eq, profileT, ne_eq] at hα ⊢
  by_cases hβ : β = ⊥
  · subst hβ
    have hα0 : α = ⊥ := le_bot_iff.mp hαβ
    subst hα0
    exact hα
  · simp [hβ]

/-- 一点版の受入型（一点版 16 担体を TCZ にもつ 25 の自己過程、共通束上の 21 の V₀ 実例）と、
25-C5 の N 上の実例・その 25-B を、一つのNで同時に主張する。 -/
theorem final_consistency_v6 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        Shared25OnePointSelf N ∧ SharedTheorem21V0Common N ∧ MortalityOnN N ∧
        MortalityPresence25B :=
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
    sharedModel_mortalityOnN, mortalityPresence25B⟩

#print axioms mortalityPresence25B
#print axioms final_consistency_v6
end Tomabechi.Consistency.R123
