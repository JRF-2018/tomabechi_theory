import Tomabechi.Consistency.ConsistencyR123_FullDecoder

/-!
# 全域実験と有限旧住所実験の厳密な回収

全域実験はnative状態型を保存する。有限旧住所では、同じ住所の型castだけで
以前の状態・費用・自己過程・標本を含むjoint全体へ戻る。
非埋込み点と頂点の実験を有限旧住所の実験に読み替えない。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Consistency.ConsistencyC1Consensus

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

private theorem stateCast_measurable {i j : CommonLayer} (h : i = j) :
    @Measurable (C6LayeredState i) (C6LayeredState j)
      (sharedLayerStateMeasurable i) (sharedLayerStateMeasurable j)
      (cast (congrArg C6LayeredState h)) := by
  cases h
  exact measurable_id

/-- 有限住所の状態型cast。その他の観測はすべてそのまま保持する。 -/
def fullExperimentFiniteRecovery (k : ℕ)
    (z : FullExperimentObservation (layerAddressEmbedding (k : WithTop ℕ))) :
    SharedExperimentObservation :=
  (z.1, (z.2.1,
    (cast (congrArg C6LayeredState (fullCommonLayerIndex_layerAddress k)) z.2.2.1, z.2.2.2)))

theorem fullExperimentFiniteRecovery_measurable (k : ℕ) :
    Measurable (fullExperimentFiniteRecovery k) := by
  have hc := stateCast_measurable (fullCommonLayerIndex_layerAddress k)
  exact measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((hc.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

/-- 同じ入力標本ごとに、全域実験が従来の有限実験の全観測へ戻る。 -/
theorem SharedFullExperimentInputs.finiteObservation {N : SharedModelSignature}
    (h : SharedFullExperimentInputs N) (d H : Bool) (k : ℕ) (x : AgentState)
    (T t : ℝ) (w : C6ExperimentInput) :
    fullExperimentFiniteRecovery k
      (N.fullExperimentObservation fullInformationDecoder d H
        (layerAddressEmbedding (k : WithTop ℕ))
        (cast (congrArg C6LayeredState (fullCommonLayerIndex_layerAddress k).symm) x) T t w) =
      N.experimentObservation d H k x T t w := by
  dsimp [fullExperimentFiniteRecovery, SharedModelSignature.fullExperimentObservation,
    SharedModelSignature.experimentObservation]
  rw [h.decoder_finite]
  rfl

/-- 標本・自己過程・情報・状態・費用のjoint全体の回収。
周辺lawだけの一致で代替しない。 -/
theorem SharedFullExperimentInputs.finiteLaw {N : SharedModelSignature}
    (h : SharedFullExperimentInputs N) (d H : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    (N.fullExperimentLaw fullInformationDecoder d H
      (layerAddressEmbedding (k : WithTop ℕ))
      (cast (congrArg C6LayeredState (fullCommonLayerIndex_layerAddress k).symm) x) T t).map
        (fullExperimentFiniteRecovery k) = N.experimentLaw d H k x T t := by
  rw [SharedModelSignature.fullExperimentLaw,
    Measure.map_map (fullExperimentFiniteRecovery_measurable k) (measurable_of_finite _)]
  unfold SharedModelSignature.experimentLaw
  congr 1
  funext w
  exact h.finiteObservation d H k x T t w

/-- さらにΓ制限観測を行えば、旧署名の全実験jointを回収する。 -/
theorem SharedFullExperimentInputs.legacyFiniteLaw {N : SharedModelSignature}
    (h : SharedFullExperimentInputs N) (d H : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    ((N.fullExperimentLaw fullInformationDecoder d H
      (layerAddressEmbedding (k : WithTop ℕ))
      (cast (congrArg C6LayeredState (fullCommonLayerIndex_layerAddress k).symm) x) T t).map
        (fullExperimentFiniteRecovery k)).map sharedExperimentRecovery =
      N.legacy.experimentLaw d H k x T t := by
  rw [h.finiteLaw]
  exact h.toSharedPointInputs.toSharedStageInputs.toSharedSCMAndExperimentInputs.experiment_joint
    d H k x T t

#print axioms SharedFullExperimentInputs.finiteLaw
#print axioms SharedFullExperimentInputs.legacyFiniteLaw
end Tomabechi.Consistency.R123
