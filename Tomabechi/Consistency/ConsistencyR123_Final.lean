import Tomabechi.Consistency.ConsistencyR123_Nondegenerate

/-!
# §14 最終存在宣言：共有署名Nの原文前提・明示追加条件・非退化性

共通完備束 `CommonConcept` を添字とする `SharedModelSignature N` について、

* `FullOriginalPremises N`：原文の全層解析入力（旧署名の `OriginalPremises`）と、
  同じNの実データを一般入口へ渡す全入力（15→23、21/22/23-B、24→26、25、27、
  一点初期状態Kからの1/2/3/4/20・全域誤差・再始動、全CommonConcept点の情報実験）
* `ExplicitAdditionalConditions N`：旧署名の `AdditionalConditions`、共有保存式
  `SharedDataPreservation N`、および層添字埋込みが順序・頂を保つこと
* `SharedNondegenerate N`：Nの実fieldを読むN1–N7

を同時に満たすNが外部モデル前提なしに存在することを述べる。
これは追加条件を許容した一つの非退化共有モデルの存在であり、原文の前提だけから
定理が従うこと、全モデルで成立することは主張しない。頂点では二値作用の符号が
時刻0・参照状態の観測であること、定理3が零平均箱点に限ること、20の二次式拡張が箱内に限ること、
一点Kは各箱初期点からの閉到達集合であることなどの量化範囲は各入力型に従う。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

/-- 原文の全入口前提。旧署名の原文入力と、同じNの全一般入口入力。 -/
structure FullOriginalPremises (N : SharedModelSignature) : Prop where
  legacy : OriginalPremises N.legacy
  inputs : SharedPointDomainInputs N

/-- 明示的な追加条件。旧署名の追加条件、共有保存式、共通束への層添字の順序・頂保存。 -/
structure ExplicitAdditionalConditions (N : SharedModelSignature) : Prop where
  legacy : AdditionalConditions N.legacy
  preservation : SharedDataPreservation N
  layer_order : ∀ a b : WithTop ℕ,
    layerAddressEmbedding a ≤ layerAddressEmbedding b ↔ a ≤ b
  layer_top : layerAddressEmbedding (⊤ : WithTop ℕ) = ⊤

/-- 原文前提・明示追加条件・非退化性の同時充足。 -/
structure FinalConsistency (N : SharedModelSignature) : Prop where
  original : FullOriginalPremises N
  additional : ExplicitAdditionalConditions N
  nondegenerate : SharedNondegenerate N

theorem sharedModel_fullOriginalPremises : FullOriginalPremises sharedModel :=
  ⟨commonModel_originalPremises, sharedModel_pointDomainInputs⟩

theorem sharedModel_explicitAdditionalConditions : ExplicitAdditionalConditions sharedModel :=
  ⟨commonModel_additionalConditions, sharedModel_preservation,
    fun _ _ => layerAddressEmbedding.le_iff_le, layerAddress_top⟩

/-- 最終存在宣言。外部のモデル前提を含まない。 -/
theorem final_consistency_model_exists :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate⟩

/-- 同じ内容を一つのrecordとして述べた版。 -/
theorem final_consistency_record : ∃ N : SharedModelSignature, FinalConsistency N :=
  ⟨sharedModel, ⟨sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate⟩⟩

#print axioms final_consistency_model_exists
#print axioms final_consistency_record
end Tomabechi.Consistency.R123
