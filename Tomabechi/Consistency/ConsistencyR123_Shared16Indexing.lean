import Tomabechi.Consistency.ConsistencyR123_SharedCapacity

/-!
# 定理16の層添字を共通束へ

原文 §2.3 は、定理16の抽象度の族 𝔄16 を 𝕃∖{⊤} の部分集合で、上向き有向かつ最大元を
持たないものとする。従来、定理16の系は旧署名の `ℕ` 添字だけを読み、共通束への
埋込みを課す field がなかった（非退化性 N2 は別物の `N.stageAddress` を読んでいた）。

ここでは定理16の層 `i : ℕ` を共通束の対角層 `diagonalLayer i` へ割り当て
（`index16`）、次を同じ `SharedModelSignature N` について示す。

* `index16` は狭義単調で、すべて頂点 ⊤ より真に下にある（𝔄16 ⊂ 𝕃∖{⊤}）。
* 𝔄16 は上向き有向で、最大元を持たない。
* 21–23 の段アドレスとの関係は `N.stageAddress n = index16 (n+1)`（段 n は 16 の層 n+1。
  添字が 1 ずれる。同一視はしない）。旧有限層の埋込み `layerAddressEmbedding i` とは
  `index16 i` が一致する。

定理16の担体（K_{i,α}(h) の中身）と層別 TCZ との同定は別の課題であり、ここでは
添字の順序構造だけを扱う。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1

/-- 定理16の層 i の共通束での住所。 -/
def index16 (i : ℕ) : CommonConcept := diagonalLayer i

theorem index16_eq_layerAddressEmbedding (i : ℕ) :
    index16 i = layerAddressEmbedding (i : WithTop ℕ) := rfl

/-- 𝔄16 の添字構造：𝕃∖{⊤} 内、狭義単調、上向き有向、最大元なし。 -/
structure Shared16Indexing (N : SharedModelSignature) : Prop where
  strictMono : StrictMono index16
  lt_top : ∀ i, index16 i < (⊤ : CommonConcept)
  directed : ∀ i j : ℕ, ∃ k : ℕ, index16 i ≤ index16 k ∧ index16 j ≤ index16 k
  no_maximum : ∀ i : ℕ, ∃ j : ℕ, index16 i < index16 j
  /-- 21–23 の段 n は 16 の層 n+1（添字は 1 ずれる）。 -/
  stage_shift : ∀ n : ℕ, N.stageAddress n = index16 (n + 1)
  /-- 旧有限層の共通束埋込みと一致する。 -/
  legacy_embedding : ∀ i : ℕ, index16 i = layerAddressEmbedding (i : WithTop ℕ)
  /-- 𝔄16 の上限は束の頂点（有限層は頂点に達しない）。 -/
  isLUB_top : IsLUB (Set.range index16) (⊤ : CommonConcept)

theorem SharedDataPreservation.shared16Indexing {N : SharedModelSignature}
    (h : SharedDataPreservation N) : Shared16Indexing N where
  strictMono := diagonalLayer_strictMono
  lt_top := diagonalLayer_lt_top
  directed := diagonalLayer_pair_has_upper
  no_maximum := exists_diagonalLayer_strictly_above
  stage_shift := fun n => by
    rw [h.stageAddress]
    simp [commonConceptPositiveEntropyAddress, index16, layerAddressEmbedding]
    rfl
  legacy_embedding := index16_eq_layerAddressEmbedding
  isLUB_top := diagonalLayer_range_isLUB_top

/-- 非退化性 N2 と同じ形（頂点より下・有向・最大元なし）を `index16` で述べ直したもの。
`N.stageAddress` 版の `inverse_indices` は残している。 -/
theorem Shared16Indexing.inverse_indices16 {N : SharedModelSignature} (h : Shared16Indexing N) :
    (∃ n : ℕ, index16 n ≠ (⊤ : CommonConcept)) ∧
      (∀ m n : ℕ, ∃ k : ℕ, index16 m ≤ index16 k ∧ index16 n ≤ index16 k) ∧
      (∀ n : ℕ, ∃ m : ℕ, index16 n < index16 m) :=
  ⟨⟨0, (h.lt_top 0).ne⟩, h.directed, h.no_maximum⟩

theorem sharedModel_shared16Indexing : Shared16Indexing sharedModel :=
  sharedModel_preservation.shared16Indexing

/-- 容量入力に、定理16の添字入力を加えた存在宣言。 -/
theorem final_consistency_with_capacity_and_16indexing :
    ∃ N : SharedModelSignature,
      FullOriginalPremises N ∧ ExplicitAdditionalConditions N ∧ SharedNondegenerate N ∧
        SharedCapacityInputs N ∧ Shared16Indexing N :=
  ⟨sharedModel, sharedModel_fullOriginalPremises, sharedModel_explicitAdditionalConditions,
    sharedModel_nondegenerate, sharedModel_capacityInputs, sharedModel_shared16Indexing⟩

#print axioms SharedDataPreservation.shared16Indexing
#print axioms final_consistency_with_capacity_and_16indexing
end Tomabechi.Consistency.R123
