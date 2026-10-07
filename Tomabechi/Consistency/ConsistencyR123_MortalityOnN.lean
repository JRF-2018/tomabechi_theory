import Tomabechi.Consistency.ConsistencyR123_Theorem21V0Instance

/-!
# 25-C5 を N の主体に寄せる

以前の 25-C5 の実例は、死ぬ人物（祖父・祖母）が N の主体に埋め込まれておらず、profile も定数
だった。ここでは **N の主体 `false` に死亡時刻 1 を与え**（`true` は死なない）、時刻依存の profile
`profileT` を拡張側に持たせる。

* 物理層 `⊥` の profile は死亡時刻以降 `none`（境界 `∂`）、それ以前は N の profile と同じ。
* 上位層（`⊥` 以外）の profile は全時刻で N の profile のまま（死後も表象が残る）。
* `AliveRealization0 d t ↔ 物理層の profile が ∂ でない`（`t < τ_d`）。
* (25.C5)：`t ≥ τ_d ⇒ AliveRealization0 = 0 ∧ 物理層の profile = ∂ ∧ ∃ α_hist, 0 ≺ α_hist ≺ ⊤ ∧ 表象 ≠ ∂`。

N の SCM・自己過程・保存式は変更しない（N の profile は全時刻で一定で、拡張側が時刻依存の読み替えを
持つ）。**範囲：** 死亡時刻は構成したモデルの選択で、N の力学（軌道は ℬ_alive に留まる）から導いたものではない。
N の presence 構造そのものを時刻依存にしたのではない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.R1

/-- N の主体 `false` は時刻 1 に死亡、`true` は死なない。 -/
def deathTimeN : Bool → WithTop ℝ
  | false => ((1 : ℝ) : WithTop ℝ)
  | true => ⊤

/-- 物理層における生きた自己制御過程の直接実装の有無。 -/
def AliveRealization0N (d : Bool) (t : ℝ) : Prop := (t : WithTop ℝ) < deathTimeN d

open Classical in
/-- 時刻依存の profile：物理層 `⊥` は死亡時刻以降 `none`（境界 ∂）、他は常に `some ()`。 -/
def profileT (_h : Bool) (d : Bool) (t : ℝ) (α : CommonConcept) : Option Unit :=
  if α = ⊥ ∧ deathTimeN d ≤ (t : WithTop ℝ) then none else some ()

structure MortalityOnN (N : SharedModelSignature) : Prop where
  /-- 生きた実装があることは、物理層の profile が境界でないことと同値。 -/
  alive_iff_physical : ∀ (h d : Bool) (t : ℝ),
    AliveRealization0N d t ↔ profileT h d t ⊥ ≠ none
  /-- 死亡前は、全層で N の profile と一致する。 -/
  pre_death_agree : ∀ (h d : Bool) (t : ℝ) (α : CommonConcept),
    (t : WithTop ℝ) < deathTimeN d →
      profileT h d t α = N.scm.model.presenceAndRelations.profile h d α
  /-- 上位層（⊥ 以外）では、全時刻で N の profile と一致する。 -/
  upper_agree : ∀ (h d : Bool) (t : ℝ) (α : CommonConcept), α ≠ ⊥ →
    profileT h d t α = N.scm.model.presenceAndRelations.profile h d α
  /-- (25.C5)：死亡時刻以降は、物理層の実装は 0 で profile は境界、かつ `0 ≺ α_hist ≺ ⊤` の層で
  N の profile による表象が境界でない形で残る。 -/
  c5 : ∀ (h d : Bool) (t : ℝ), deathTimeN d ≤ (t : WithTop ℝ) →
    ¬ AliveRealization0N d t ∧ profileT h d t ⊥ = none ∧
      ∃ α : CommonConcept, ⊥ < α ∧ α < ⊤ ∧ profileT h d t α ≠ none ∧
        profileT h d t α = N.scm.model.presenceAndRelations.profile h d α
  /-- 死亡が実際に起きる主体と時刻がある（空虚でない）。 -/
  some_death : ∃ (d : Bool) (t : ℝ), deathTimeN d ≤ (t : WithTop ℝ)
  /-- 死なない主体もある（死亡が全主体の自明な性質ではない）。 -/
  some_survivor : ∃ d : Bool, ∀ t : ℝ, AliveRealization0N d t

theorem sharedModel_mortalityOnN : MortalityOnN sharedModel where
  alive_iff_physical := fun h d t => by
    cases d <;> simp [AliveRealization0N, deathTimeN, profileT]
  pre_death_agree := fun h d t α hlt => by
    have : ¬ (deathTimeN d ≤ (t : WithTop ℝ)) := not_le.mpr hlt
    simp [profileT, this]
    rfl
  upper_agree := fun h d t α hα => by
    simp [profileT, hα]
    rfl
  c5 := fun h d t hd => by
    refine ⟨fun hlt => absurd hlt (not_lt.mpr hd), ?_, diagonalLayer 1, ?_,
      diagonalLayer_lt_top 1, ?_, ?_⟩
    · simp [profileT, hd]
    · have h01 : diagonalLayer 0 < diagonalLayer 1 := diagonalLayer_strictMono (by norm_num)
      have h0 : diagonalLayer 0 = ⊥ := layerAddress_zero_eq_bottom
      rwa [h0] at h01
    · have hne : diagonalLayer 1 ≠ ⊥ := by
        intro hb
        have h01 : diagonalLayer 0 < diagonalLayer 1 := diagonalLayer_strictMono (by norm_num)
        have h0 : diagonalLayer 0 = ⊥ := layerAddress_zero_eq_bottom
        rw [h0, hb] at h01
        exact lt_irrefl _ h01
      simp [profileT, hne]
    · have hne : diagonalLayer 1 ≠ ⊥ := by
        intro hb
        have h01 : diagonalLayer 0 < diagonalLayer 1 := diagonalLayer_strictMono (by norm_num)
        have h0 : diagonalLayer 0 = ⊥ := layerAddress_zero_eq_bottom
        rw [h0, hb] at h01
        exact lt_irrefl _ h01
      simp [profileT, hne]
      rfl
  some_death := ⟨false, 1, by simp [deathTimeN]⟩
  some_survivor := ⟨true, fun t => by simp [AliveRealization0N, deathTimeN]⟩

theorem final_consistency_v5_mortality :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N ∧ SharedBorelStructure N ∧
        GenealogyMortalityExtension N ∧ Shared16OnePointInputs N ∧ SharedTheorem21V0 N ∧
        MortalityOnN N :=
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
    sharedModel_theorem21V0, sharedModel_mortalityOnN⟩

#print axioms sharedModel_mortalityOnN
#print axioms final_consistency_v5_mortality
end Tomabechi.Consistency.R123
