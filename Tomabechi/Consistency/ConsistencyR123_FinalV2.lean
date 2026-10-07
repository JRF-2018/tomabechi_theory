import Tomabechi.Consistency.ConsistencyR123_ReadingClosures
import Tomabechi.Consistency.ConsistencyR123_HConditions

/-!
# 最終存在宣言 v2（先行する受入型をまとめる）

旧 `final_consistency_model_exists` は残し、新しい受入型を足した別の宣言を置く。

* `FullOriginalPremisesV2`：旧 `FullOriginalPremises` ＋ 定理19の容量を 𝕃 全域で
  （`SharedCapacityInputs`）＋ 定理16の担体と層別 TCZ の同定・存在表象縮小節
  （`Shared16LayerTCZInputs`）＋ 定理1–4 の誤差を定理20と同じ Euclid 距離で
  （`SharedNormUnification`）。
* `ExplicitAdditionalConditionsV2`：旧 `ExplicitAdditionalConditions` ＋ 名前つきの
  H-info/H-flow/H-sum/H-stage（`ExplicitHConditions`）＋ 定理16の層添字（`Shared16Indexing`）
  ＋ 基礎評価の領域 X := box（`SharedBaseDomain`）。
* `SharedNondegenerateV2`：旧 `SharedNondegenerate` ＋ N 自身の量で読む
  `SharedNativeNondegenerate`。

**範囲：** これは Lean で定義した述語についての存在証明である。原文の読みの判断
（定理21の V₀、定理26の完全状態、19と16の主体の同一性、定理25-C4/C5 のモデル例）は
非公開の対応表に記録した。他AIによる読み合わせは未実施。
-/

noncomputable section
namespace Tomabechi.Consistency.R123

structure FullOriginalPremisesV2 (N : SharedModelSignature) : Prop where
  base : FullOriginalPremises N
  capacity : SharedCapacityInputs N
  layerTCZ : Shared16LayerTCZInputs N
  norm : SharedNormUnification N

structure ExplicitAdditionalConditionsV2 (N : SharedModelSignature) : Prop where
  base : ExplicitAdditionalConditions N
  hConditions : ExplicitHConditions N
  indexing16 : Shared16Indexing N
  baseDomain : SharedBaseDomain N

structure SharedNondegenerateV2 (N : SharedModelSignature) : Prop where
  base : SharedNondegenerate N
  native : SharedNativeNondegenerate N

/-- 最終存在宣言 v2。外部のモデル前提を含まない。 -/
theorem final_consistency_model_exists_v2 :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩⟩

#print axioms final_consistency_model_exists_v2
end Tomabechi.Consistency.R123
