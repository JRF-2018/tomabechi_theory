import Tomabechi.Consistency.ConsistencyR123_BorelStructure

/-!
# 25-C4（父母子）と 25-C5（死後の上位履歴層の表象）を N に接続した拡張

原文 §14 の (25.C4)・(25.C5) は「簡約した生物学的系譜モデルでは」「完全履歴が過去の身体的存在の
因果履歴を保持する本モデルでは」と書くモデル例で、定理25の結論の前提ではない。N の主体は `Bool`
の二つで、出生・死亡を持たないので、N だけでは 𝔇born=∅ で空虚に成立していた。

ここでは N を**変えずに**、系譜と死亡の補助データを加えた拡張 `GenealogyMortalityExtension N` を作る。
N 自身の述語（v2 の全受入型）は N の field だけを読むので、拡張を加えても
そのまま保たれる（`final_consistency_v2_with_genealogy_mortality`）。

* **人物：** 六人の系譜例 `Person`（祖父 0・父 1・母 2・子 3・叔母 4・祖母 5）。
  N の二主体は `embed : Bool → Person`（false ↦ 父、true ↦ 子）で人物に埋め込む。
* **(25.C4)：** `GenealogyC4`（逆役割、𝔇born={子} 非空で父母がいる）。さらに N の関係辺が、
  埋め込んだ父・子の間に実在する（`edge_realizes_genealogy`）。
* **(25.C5)：** 祖父は時刻 1、祖母は時刻 2 に死亡し、他は死なない（`deathTime`）。
  `AliveRealization0 d t := t < τ_d`。死亡時刻以降は `AliveRealization0 = 0`、かつ
  `0 ≺ α_hist ≺ ⊤` の層 `diagonalLayer 1` で、表象（presence の profile）は境界 `∂ = none` でない。
  人物の profile は N の profile と同じ形で、N の二主体では N の profile と一致する（`profile_agree`）。

**範囲：** 死亡時刻・人物の profile は補助データとして**構成したモデルの選択**であり、N の力学から
導かれたものではない（N の軌道は ℬ_alive の中に留まり、N 自身には死亡がない）。
(25.C4)/(25.C5) を N の SCM・自己過程の保存式へ組み込んだのではなく、N を変えない拡張である。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1 Tomabechi.Examples.Theorem25

/-- N の二主体の人物への埋め込み：false ↦ 父(1)、true ↦ 子(3)。 -/
def embedPerson (b : Bool) : Person := if b then 3 else 1

/-- 死亡時刻：祖父(0)は 1、祖母(5)は 2、他は死なない。 -/
def deathTime (d : Person) : WithTop ℝ :=
  if d = 0 then ((1 : ℝ) : WithTop ℝ) else if d = 5 then ((2 : ℝ) : WithTop ℝ) else ⊤

/-- 物理層における生きた自己制御過程の直接実装の有無。 -/
def AliveRealization0 (d : Person) (t : ℝ) : Prop := (t : WithTop ℝ) < deathTime d

/-- 人物・履歴・層の表象（presence の profile と同じ形。`none` が境界 ∂ に当たる）。 -/
def personProfile (_h : Bool) (_d : Person) (_α : CommonConcept) : Option Unit := some ()

structure GenealogyMortalityExtension (N : SharedModelSignature) : Prop where
  c4 : GenealogyC4 ({3} : Set Person) (Set.univ : Set Bool)
    (fun _ f c => FatherOf f c) (fun _ m c => MotherOf m c)
    (fun _ c f => HasFather c f) (fun _ c m => HasMotherExample c m)
  born_nonempty : ({3} : Set Person).Nonempty
  c5 : ∀ (h : Bool) (d : Person) (t : ℝ), deathTime d ≤ (t : WithTop ℝ) →
    ¬ AliveRealization0 d t ∧
      ∃ α : CommonConcept, ⊥ < α ∧ α < ⊤ ∧ personProfile h d α ≠ none
  some_death : ∃ (d : Person) (t : ℝ), deathTime d ≤ (t : WithTop ℝ)
  profile_agree : ∀ (h b : Bool) (α : CommonConcept),
    personProfile h (embedPerson b) α = N.scm.model.presenceAndRelations.profile h b α
  edge_realizes_genealogy : ∀ h : Bool,
    FatherOf (embedPerson false) (embedPerson true) ∧
      ∃ (a b : CommonConcept) (r : Bool),
        N.scm.model.presenceAndRelations.relationEdge h false a r true b

theorem sharedModel_genealogyMortality : GenealogyMortalityExtension sharedModel where
  c4 := ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ c hc => by
    obtain rfl := Set.mem_singleton_iff.mp hc
    exact child_has_father_and_mother⟩
  born_nonempty := genealogyC4_example_born_nonempty
  c5 := fun h d t hd => by
    refine ⟨fun hlt => absurd hlt (not_lt.mpr hd), diagonalLayer 1, ?_, diagonalLayer_lt_top 1, by
      simp [personProfile]⟩
    have h01 : diagonalLayer 0 < diagonalLayer 1 := diagonalLayer_strictMono (by norm_num)
    have h0 : diagonalLayer 0 = ⊥ := layerAddress_zero_eq_bottom
    rwa [h0] at h01
  some_death := ⟨0, 1, by simp [deathTime]⟩
  profile_agree := fun h b α => rfl
  edge_realizes_genealogy := fun h => ⟨by simp [FatherOf, embedPerson], ⊥, ⊥, h, by decide, by simp⟩

theorem final_consistency_v2_with_genealogy_mortality :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N :=
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
    sharedModel_borelStructure, sharedModel_genealogyMortality⟩

#print axioms sharedModel_genealogyMortality
#print axioms final_consistency_v2_with_genealogy_mortality
end Tomabechi.Consistency.R123
