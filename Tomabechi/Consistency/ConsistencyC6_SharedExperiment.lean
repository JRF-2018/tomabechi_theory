import Tomabechi.Consistency.ConsistencyC6_FullLayerSCM

/-!
# C6：同じ主体・層・制御を観測する情報／自己過程の実験法則

SCMの外生標本と情報標本は異なる役割を保った積空間に置く。
主体dと履歴hをcontextで固定し、情報の行為ラベルは実際の許容ゲインへ復号する。
候補を主体ラベルに使わず、情報行為を履歴出力Y⁺と同一視しない。
物理層の零情報lawを保持し、正層で元のC3上位jointを使う。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Theorem16_25
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open MeasureTheory

/-- 情報の二値行為を実際の許容ゲイン0/3へ復号する。
この二方策は許容族の部分族であり、族全体を二値へ狭めない。 -/
def c6InformationPolicy (g : Bool) : C1GainSignal :=
  if g then c1MaxGainSignal else c1ZeroGainSignal

theorem c6InformationPolicy_code (g : Bool) (t : ℝ) :
    c6EncodeRate3AsSCMAction ((c6InformationPolicy g).1 t) = g := by
  cases g <;> norm_num [c6InformationPolicy, c6EncodeRate3AsSCMAction,
    c1MaxGainSignal, c1ZeroGainSignal]

theorem c6InformationPolicy_distinct :
    c6InformationPolicy false ≠ c6InformationPolicy true := by
  simpa [c6InformationPolicy] using c1_two_distinct_admissible_gains

/-- 底層の零情報lawと正層の元C3上位law。 -/
def c6LayerInformationLaw (k : ℕ) : Measure (Unit × Bool × Bool) :=
  if k = 0 then Tomabechi.Consistency.C3.physicalLayerLaw.joint
  else Tomabechi.Consistency.C3.upperJoint

theorem c6LayerInformationLaw_probability (k : ℕ) :
    IsProbabilityMeasure (c6LayerInformationLaw k) := by
  unfold c6LayerInformationLaw
  split
  · exact Tomabechi.Consistency.C3.physicalLayerLaw.joint_isProbabilityMeasure
  · exact Tomabechi.Consistency.C3.upperJoint_isProbability

theorem c6LayerInformationLaw_stage (n : ℕ) :
    c6LayerInformationLaw (n + 1) = Tomabechi.Consistency.C3.upperJoint := by
  simp [c6LayerInformationLaw]

abbrev C6ExperimentInput := (Bool × Bool) × (Unit × Bool × Bool)

/-- 完全な外生lawと元情報jointを保持する共通実験の標本law。 -/
def c6ExperimentInputLaw (k : ℕ) : Measure C6ExperimentInput :=
  c6FullLayerMeasuredC3Model.model.scm.exogenousLaw.toMeasure.prod (c6LayerInformationLaw k)

theorem c6ExperimentInputLaw_probability (k : ℕ) : IsProbabilityMeasure (c6ExperimentInputLaw k) := by
  letI := c6LayerInformationLaw_probability k
  unfold c6ExperimentInputLaw
  infer_instance

theorem c6ExperimentInputLaw_scm (k : ℕ) :
    (c6ExperimentInputLaw k).map Prod.fst =
      c6FullLayerMeasuredC3Model.model.scm.exogenousLaw.toMeasure := by
  letI := c6LayerInformationLaw_probability k
  rw [c6ExperimentInputLaw, Measure.map_fst_prod]
  simp

theorem c6ExperimentInputLaw_information (k : ℕ) :
    (c6ExperimentInputLaw k).map Prod.snd = c6LayerInformationLaw k := by
  rw [c6ExperimentInputLaw, Measure.map_snd_prod]
  simp

/-- 同じ情報行為が共通Dの実軌道を生成する。 -/
def c6ExperimentState (k : ℕ) (x : AgentState) (T t : ℝ)
    (w : C6ExperimentInput) : AgentState :=
  c6CommonLayerData.trajectory (some k) (c6InformationPolicy w.2.2.2) x T t

abbrev C6ExperimentObservation := C6ExperimentInput ×
  (((C6FullLayerGamma × C6TypedSelfRepresentation) × Bool) × (AgentState × ℝ))

/-- 同じcontextの型付き自己過程、情報行為による状態、同じDの走行費を同時に観測する。
元標本も保持するので、主体/候補/行為を別の役割へ取り替えていないことを検査できる。 -/
def c6ExperimentObservation (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ)
    (w : C6ExperimentInput) : C6ExperimentObservation :=
  (w, ((c6FullLayerTypedSelfProcess d (some k)).baselineEquation h w.1,
    (c6ExperimentState k x T t w,
     c6CommonLayerData.runningCost (some k) (c6InformationPolicy w.2.2.2)
       (c6ExperimentState k x T t w) t)))

def c6ExperimentLaw (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    Measure C6ExperimentObservation :=
  (c6ExperimentInputLaw k).map (c6ExperimentObservation d h k x T t)

theorem c6ExperimentLaw_probability (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    IsProbabilityMeasure (c6ExperimentLaw d h k x T t) := by
  letI := c6ExperimentInputLaw_probability k
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).mpr inferInstance

/-- 情報の元jointを、制御状態/自己過程を付加した法則から厳密に回収する。 -/
theorem c6ExperimentLaw_information (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    (c6ExperimentLaw d h k x T t).map (fun z => z.1.2) = c6LayerInformationLaw k := by
  rw [c6ExperimentLaw, Measure.map_map
    (show Measurable (fun z : C6ExperimentObservation => z.1.2) from
      measurable_snd.comp measurable_fst)
    (measurable_of_finite _)]
  exact c6ExperimentInputLaw_information k

/-- 自己過程の同じbaseline jointを、情報/制御状態付き法則から厳密に回収する。 -/
theorem c6ExperimentLaw_selfProcess (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    (c6ExperimentLaw d h k x T t).map (fun z => z.2.1) =
      ((c6FullLayerTypedSelfProcess d (some k)).exogenousLaw.toMeasure).map
        ((c6FullLayerTypedSelfProcess d (some k)).baselineEquation h) := by
  rw [c6ExperimentLaw, Measure.map_map
    (show Measurable (fun z : C6ExperimentObservation => z.2.1) from
      measurable_fst.comp measurable_snd)
    (measurable_of_finite _)]
  change (c6ExperimentInputLaw k).map
    (((c6FullLayerTypedSelfProcess d (some k)).baselineEquation h) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
    c6ExperimentInputLaw_scm]
  rfl

/-- 実験の主体dは同じFin 2主体座標へ復号される。情報goalで主体を置換しない。 -/
theorem c6Experiment_subject_coordinate (d : Bool) (k : ℕ) (x : AgentState) (T t : ℝ)
    (w : C6ExperimentInput) :
    c6FiniteSubjectStateView (c6ExperimentState k x T t w) d =
      controlledConsensusState x T (c6InformationPolicy w.2.2.2) t
        (c6FiniteSubjectEquiv.symm d) := by
  simpa [c6ExperimentState, c6CommonLayerData, c6LayeredNonnegativeTimeData,
    c6LayeredTrajectory] using c6FiniteSubjectStateView_preserves_coordinate
      (c6ExperimentState k x T t w) (c6FiniteSubjectEquiv.symm d)

/-- 費用は同じ実制御状態の層別二次評価。lawから独立した定数費用を付加していない。 -/
theorem c6Experiment_cost (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ)
    (w : C6ExperimentInput) :
    (c6ExperimentObservation d h k x T t w).2.2.2 =
      1 + 8 * (halfDifference (c6ExperimentState k x T t w)) ^ 2 := rfl

/-- 情報行為を実入力へ復号し再符号化したjointも、元の情報jointと完全に一致する。
数値スコアの一致だけで制御の意味対応を済ませない。 -/
theorem c6ExperimentLaw_actualPolicyInformation (d h : Bool) (k : ℕ) (x : AgentState) (T t : ℝ) :
    (c6ExperimentLaw d h k x T t).map
      (fun z => (z.1.2.1, z.1.2.2.1,
        c6EncodeRate3AsSCMAction ((c6InformationPolicy z.1.2.2.2).1 t))) =
      c6LayerInformationLaw k := by
  calc
    _ = (c6ExperimentLaw d h k x T t).map (fun z => z.1.2) := by
      congr 1
      funext z
      rw [c6InformationPolicy_code]
    _ = _ := c6ExperimentLaw_information d h k x T t

/-- 情報行為trueは、同じ有限層Dの実最適方策を指定する。 -/
theorem c6InformationPolicy_optimal (k : ℕ) (x : AgentState) (t : ℝ) :
    c6InformationPolicy true = c6CommonLayerData.optimalPolicy (some k) x t := rfl

/-- 候補介入にも同じ情報行為・制御状態・費用観測を用いる。 -/
def c6ExperimentIntervenedObservation (d h s : Bool) (k : ℕ) (x : AgentState) (T t : ℝ)
    (w : C6ExperimentInput) : C6ExperimentObservation :=
  (w, ((c6FullLayerTypedSelfProcess d (some k)).intervenedEquation h s w.1,
    (c6ExperimentState k x T t w,
     c6CommonLayerData.runningCost (some k) (c6InformationPolicy w.2.2.2)
       (c6ExperimentState k x T t w) t)))

/-- 候補と情報行為は異なる役割であり、候補介入後も同じ全jointを観測する。
元SCMの候補非干渉からpointwise一致するこの具体モデルの結論。 -/
theorem c6Experiment_intervention_invariance (d h s : Bool) (k : ℕ)
    (x : AgentState) (T t : ℝ) :
    (c6ExperimentInputLaw k).map (c6ExperimentIntervenedObservation d h s k x T t) =
      c6ExperimentLaw d h k x T t := rfl

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6ExperimentLaw_selfProcess
#print axioms Tomabechi.Consistency.C6.c6ExperimentLaw_information
#print axioms Tomabechi.Consistency.C6.c6ExperimentLaw_actualPolicyInformation
#print axioms Tomabechi.Consistency.C6.c6Experiment_intervention_invariance
