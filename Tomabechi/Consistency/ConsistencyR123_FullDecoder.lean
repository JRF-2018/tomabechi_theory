import Tomabechi.Consistency.ConsistencyR123_FullExperiment

/-!
# 全共通束点の許容情報方策族

有限層では元のゲイン0/3、頂点では元の可測動径ゲイン0/1/2を使用する。
二方策は各層の許容族の部分族であり、元の全方策族を置き換えない。
同じN.dataでの許容性・true方策の最適性を全初期状態・非負開始時刻で要求する。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory
open Tomabechi.Consistency.C6 Tomabechi.Consistency.R1
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Examples.Theorem27 Tomabechi.Examples.Theorem27Op
open Tomabechi.Examples.Theorem26_27ControlClasses

local instance (a : CommonConcept) : MeasurableSpace (fullCommonLayerState a) :=
  sharedLayerStateMeasurable (fullCommonLayerIndex a)

/-- 頂点で使う定数零動径ゲイン。生命方向の成分は元の方策に保つ。 -/
def fullDecoderZeroGain : BoundedMeasurableGainSignal :=
  ⟨fun _ => 0, measurable_const, by intro t; norm_num⟩

def fullLayerDecoder : (a : CommonLayer) → Bool → C6LayeredPolicy a
  | none, g => if g then vectorMaximalPolicy else measurableGainVectorPolicy fullDecoderZeroGain
  | some _, g => c6InformationPolicy g

def fullInformationDecoder : SharedInformationDecoder :=
  fun a => fullLayerDecoder (fullCommonLayerIndex a)

/-- 実方策族の中の二方策は全層で区別される。 -/
theorem fullLayerDecoder_distinct (a : CommonLayer) :
    fullLayerDecoder a false ≠ fullLayerDecoder a true := by
  cases a with
  | some k => exact c6InformationPolicy_distinct
  | none =>
    intro heq
    have he := congrArg (fun π : VectorSourcePolicy true => π.action (⟨0, by norm_num⟩, e0) 0) heq
    norm_num [fullLayerDecoder, vectorMaximalPolicy, measurableGainVectorPolicy,
      fullDecoderZeroGain, maximalMeasurableGain, e0] at he

/-- true情報行為は実Dの最適方策。全共通束点・全初期状態・全開始時刻。 -/
theorem fullInformationDecoder_optimal (a : CommonConcept)
    (x : fullCommonLayerState a) (T : ℝ) :
    fullInformationDecoder a true = sharedModel.data.optimalPolicy a x T := by
  have hf : ∀ i (y : C6LayeredState i) s,
      fullLayerDecoder i true = c6LayeredNonnegativeTimeData.optimalPolicy i y s := by
    intro i y s
    cases i <;> rfl
  exact hf (fullCommonLayerIndex a) x T

/-- false方策も同じ実Dの許容方策族に属する。 -/
theorem fullInformationDecoder_false_admissible (a : CommonConcept)
    (x : fullCommonLayerState a) (T : ℝ) :
    sharedModel.data.admissible a (fullInformationDecoder a false) x T := by
  have hf : ∀ i (y : C6LayeredState i) s,
      c6LayeredNonnegativeTimeData.admissible i (fullLayerDecoder i false) y s := by
    intro i y s
    cases i with
    | some k => trivial
    | none => exact ⟨fullDecoderZeroGain, fun _ => rfl⟩
  exact hf (fullCommonLayerIndex a) x T

/-- 方策を同じ二値行為へ戻す符号化。全方策上に定義し、復号像上で左逆を証明する。 -/
def fullInformationEncode (a : CommonConcept) (π : fullCommonLayerPolicy a) : Bool := by
  classical
  exact decide (π = fullInformationDecoder a true)

theorem fullInformationDecoder_code (a : CommonConcept) (g : Bool) :
    fullInformationEncode a (fullInformationDecoder a g) = g := by
  cases g
  · simp only [fullInformationEncode, fullInformationDecoder,
      fullLayerDecoder_distinct, decide_false]
  · simp [fullInformationEncode]

/-- 実制御の観測による符号化。有限層は時刻0のゲイン、頂点は時刻0・
参照状態e₀での動径作用を読む。任意の初期状態で作用が区別されるとは主張しない。 -/
def fullLayerActionEncode : (a : CommonLayer) → C6LayeredPolicy a → Bool
  | some _, π => c6EncodeRate3AsSCMAction (π.1 0)
  | none, π => by
    classical
    exact decide (π.action (⟨0, by norm_num⟩, e0) 0 = -(1 / 2 : ℝ))

def fullActionEncode (a : CommonConcept) (π : fullCommonLayerPolicy a) : Bool :=
  fullLayerActionEncode (fullCommonLayerIndex a) π

theorem fullLayerDecoder_action_code (a : CommonLayer) (g : Bool) :
    fullLayerActionEncode a (fullLayerDecoder a g) = g := by
  cases a with
  | some k => exact c6InformationPolicy_code g 0
  | none =>
    cases g <;> norm_num [fullLayerActionEncode, fullLayerDecoder, vectorMaximalPolicy,
      measurableGainVectorPolicy, fullDecoderZeroGain, maximalMeasurableGain, e0, e1]

theorem fullInformationDecoder_action_code (a : CommonConcept) (g : Bool) :
    fullActionEncode a (fullInformationDecoder a g) = g :=
  fullLayerDecoder_action_code (fullCommonLayerIndex a) g

private theorem decoder_cast {i j : CommonLayer} (h : i = j) (g : Bool) :
    fullLayerDecoder i g =
      cast (congrArg C6LayeredPolicy h.symm) (fullLayerDecoder j g) := by
  cases h
  rfl

/-- 全有限旧住所では、実復号方策がNの元の情報方策へ厳密に戻る。 -/
theorem fullInformationDecoder_finite (k : ℕ) (g : Bool) :
    fullInformationDecoder (layerAddressEmbedding (k : WithTop ℕ)) g =
      cast (congrArg C6LayeredPolicy (fullCommonLayerIndex_layerAddress k).symm)
        (sharedModel.legacy.informationPolicy g) := by
  exact decoder_cast (fullCommonLayerIndex_layerAddress k) g

/-- 全点の情報jointは実方策を復号・再符号化しても変わらない。 -/
theorem SharedDataPreservation.fullExperiment_actualPolicyInformation {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H a x T t) :
    (N.fullExperimentLaw fullInformationDecoder d H a x T t).map
      (fun z => (z.1.2.1, z.1.2.2.1,
        fullInformationEncode a (fullInformationDecoder a z.1.2.2.2))) = N.informationLaw a := by
  simpa only [fullInformationDecoder_code] using
    h.fullExperiment_information fullInformationDecoder d H a x T t

/-- 指定の参照状態で実入力を観測・再符号化した情報jointも同じlawである。 -/
theorem SharedDataPreservation.fullExperiment_actualActionInformation {N : SharedModelSignature}
    (h : SharedDataPreservation N) (d H a x T t) :
    (N.fullExperimentLaw fullInformationDecoder d H a x T t).map
      (fun z => (z.1.2.1, z.1.2.2.1,
        fullActionEncode a (fullInformationDecoder a z.1.2.2.2))) = N.informationLaw a := by
  simpa only [fullInformationDecoder_action_code] using
    h.fullExperiment_information fullInformationDecoder d H a x T t

/-- 全実験の復号族について、同じN.dataの許容性・最適性を必須にする。 -/
structure SharedFullExperimentInputs (N : SharedModelSignature) : Prop extends SharedPointInputs N where
  decoder_optimal : ∀ a x T,
    fullInformationDecoder a true = N.data.optimalPolicy a x T
  decoder_admissible : ∀ a g x T, 0 ≤ T →
    N.data.admissible a (fullInformationDecoder a g) x T
  decoder_distinct : ∀ a, fullInformationDecoder a false ≠ fullInformationDecoder a true
  decoder_finite : ∀ (k : ℕ) (g : Bool),
    fullInformationDecoder (layerAddressEmbedding (k : WithTop ℕ)) g =
      cast (congrArg C6LayeredPolicy (fullCommonLayerIndex_layerAddress k).symm)
        (N.legacy.informationPolicy g)

/-- 許容・最適・非退化の復号族と、既存全入力を同じ署名で構成する。 -/
theorem sharedModel_fullExperimentInputs : SharedFullExperimentInputs sharedModel := by
  refine ⟨sharedModel_pointInputs, fullInformationDecoder_optimal, ?_, ?_,
    fullInformationDecoder_finite⟩
  · intro a g x T hT
    cases g
    · exact fullInformationDecoder_false_admissible a x T
    · rw [fullInformationDecoder_optimal]
      exact sharedModel.data.optimal_policy_admissible a x T hT
  · intro a
    exact fullLayerDecoder_distinct (fullCommonLayerIndex a)

theorem shared_full_experiment_model_exists :
    ∃ N : SharedModelSignature, SharedFullExperimentInputs N :=
  ⟨sharedModel, sharedModel_fullExperimentInputs⟩

#print axioms fullInformationDecoder_optimal
#print axioms fullInformationDecoder_false_admissible
#print axioms SharedDataPreservation.fullExperiment_actualPolicyInformation
#print axioms SharedDataPreservation.fullExperiment_actualActionInformation
#print axioms shared_full_experiment_model_exists
end Tomabechi.Consistency.R123
