import Tomabechi.Consistency.ConsistencyR123_SubjectIdentity

/-!
# 完全状態に時計座標を加えていないこと（M12.1）

原文 §12（定理23）は、完全状態 `z=(x₀,(x_α)_{α>0},e)` に「𝒮 を一価にするため必要な環境・記憶・
履歴変数は含めるが、**時計座標そのものを追加して非再帰結論を自明化しない**」と書き、
総エントロピー `𝒮(z) = Ŝ_phys(z) + Σ_α w_α Ĥ_α(z)` を**時間非依存の一価状態汎関数**とする。

モデルの完全状態は `CompleteState = ℝ × ℝ`（認知座標 q・物理座標 p）。物理座標は
エントロピー収支 `p' + q'² = p + q² + E`（`E` は生成）で動き、時刻 `A` では動かない。
このことを次の形で証明する（`SharedNoClockCoordinate`）。

1. **時間非依存の汎関数：** `totalEntropy N z := Ŝ_phys z + Σ w_α Ĥ_α z` は完全状態だけの関数
   （時刻の引数を持たない）で、完全路 `z(t)` の上で `𝒮(z(t)) = 1 + 3t`（生成 Π=3 による）。
2. **増分は生成で決まる：** 一歩の `(p+q²)` の増分は経過時間 `A` によらず生成 `E` に等しい
   （`E = 0` なら、どれだけ時間が経っても `p+q²` は変わらない）。
3. **状態は時刻で決まらない：** 同じ経過時間 `A` でも、生成 `E=0` と `E=1` では異なる完全状態に着く。
   物理座標は時計ではない。

**範囲：** 時計座標の不在を「状態が時刻の関数でない」ことで形式化した。完全路の上では
`𝒮(z(t)) = 1+3t` なので、`𝒮` を通せば時刻は読み出せる（これは定理23の結論そのもので、
座標として時計を足したわけではない）。「𝒮 を一価にする変数が足りている」ことは、
`𝒮` が `CompleteState` 上の関数として定義されていること（型）で担保する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open Tomabechi.Consistency.C6 Tomabechi.Consistency.C2

/-- 総エントロピー汎関数：完全状態だけの関数。 -/
def SharedModelSignature.totalEntropy (N : SharedModelSignature) (z : CompleteState) : ℝ :=
  N.legacy.physicalObservation z + ∑' n, N.legacy.weight n * N.legacy.layerObservation n z

structure SharedNoClockCoordinate (N : SharedModelSignature) : Prop where
  /-- 完全状態は認知座標と物理座標の二つ（時刻の座標を持たない）。 -/
  state_space : CompleteState = (ℝ × ℝ)
  /-- 完全路の上で `𝒮(z(t)) = 1 + 3t`。 -/
  path_value : ∀ t : ℝ, N.totalEntropy (N.legacy.completePath t) = 1 + 3 * t
  /-- `p+q²` の増分は経過時間 A によらず生成 E に等しい。 -/
  increment_is_production : ∀ (c A E : ℝ) (z : CompleteState),
    (physicalCoordinate (N.legacy.step c A E z) +
        cognitiveCoordinate (N.legacy.step c A E z) ^ 2) -
      (physicalCoordinate z + cognitiveCoordinate z ^ 2) = E
  /-- 生成 0 なら、時間が経っても `p+q²` は変わらない。 -/
  zero_production_conserved : ∀ (c A : ℝ) (z : CompleteState),
    physicalCoordinate (N.legacy.step c A 0 z) + cognitiveCoordinate (N.legacy.step c A 0 z) ^ 2 =
      physicalCoordinate z + cognitiveCoordinate z ^ 2
  /-- 同じ経過時間でも、生成が違えば着く完全状態は異なる（状態は時刻の関数でない）。 -/
  same_elapsed_time_different_states : ∀ (c A : ℝ) (z : CompleteState),
    N.legacy.step c A 0 z ≠ N.legacy.step c A 1 z

theorem SharedDataPreservation.noClockCoordinate {N : SharedModelSignature}
    (h : SharedDataPreservation N) : SharedNoClockCoordinate N := by
  have hc := h.legacy_couplings
  have hinc : ∀ (c A E : ℝ) (z : CompleteState),
      (physicalCoordinate (N.legacy.step c A E z) +
          cognitiveCoordinate (N.legacy.step c A E z) ^ 2) -
        (physicalCoordinate z + cognitiveCoordinate z ^ 2) = E := by
    intro c A E z
    have := hc.core_entropy c A E z
    rw [hc.physical_observation] at this
    simp only [physicalEntropy] at this
    linarith
  refine ⟨rfl, ?_, hinc, ?_, ?_⟩
  · intro t
    exact hc.entropy_observation t
  · intro c A z
    have := hinc c A 0 z
    linarith
  · intro c A z heq
    have h0 := hinc c A 0 z
    have h1 := hinc c A 1 z
    rw [heq] at h0
    linarith

theorem sharedModel_noClockCoordinate : SharedNoClockCoordinate sharedModel :=
  sharedModel_preservation.noClockCoordinate

theorem final_consistency_v2_with_no_clock :
    ∃ N : SharedModelSignature,
      FullOriginalPremisesV2 N ∧ ExplicitAdditionalConditionsV2 N ∧ SharedNondegenerateV2 N ∧
        SharedBaseBackground21 N ∧ SharedTopCompleteReading N ∧
        SharedNormUnificationConclusions N ∧ SharedTheorem4Ranges N ∧ Shared16Premises N ∧
        SharedSubjectIdentity N ∧ SharedNoClockCoordinate N :=
  ⟨sharedModel,
    ⟨sharedModel_fullOriginalPremises, sharedModel_capacityInputs,
      sharedModel_shared16LayerTCZInputs, sharedModel_normUnification⟩,
    ⟨sharedModel_explicitAdditionalConditions,
      sharedModel_pointDomainInputs.explicitHConditions,
      sharedModel_shared16Indexing, sharedModel_baseDomain⟩,
    ⟨sharedModel_nondegenerate, sharedModel_nativeNondegenerate⟩,
    sharedModel_baseBackground21, sharedModel.sharedTopCompleteReading,
    sharedModel_normUnificationConclusions, sharedModel_theorem4Ranges,
    sharedModel_shared16Premises, sharedModel_subjectIdentity, sharedModel_noClockCoordinate⟩

#print axioms SharedDataPreservation.noClockCoordinate
#print axioms final_consistency_v2_with_no_clock
end Tomabechi.Consistency.R123
