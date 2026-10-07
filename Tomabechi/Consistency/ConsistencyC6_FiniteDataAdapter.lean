import Tomabechi.Consistency.ConsistencyC6_CommonLayerData

/-!
# C6: 正層からC1有限層データへの実接続

既存の `C6CommonLayerAdapter` は層束の順序対応を扱い、時間発展データは扱わない。
このmoduleではC2の正層アドレスを、共通層DのC1有限層へ結び、状態・全制御族・軌道・
評価・重みがその層でどう対応するかを一つのadapterに記録する。
-/

noncomputable section

namespace Tomabechi.Consistency.C6

open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem24_26
open MeasureTheory

/-- 二主体C1の `Fin 2` 添字と25-SCMのBool主体ラベルを結ぶ全単射。 -/
def c6FiniteSubjectEquiv : Fin 2 ≃ Bool where
  toFun i := decide (i.val = 1)
  invFun
    | false => 0
    | true => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro d
    cases d <;> rfl

/-- C1の二主体状態を、25-SCMと同じBoolラベルで読み直す。 -/
def c6FiniteSubjectStateView (x : AgentState) : Bool → ℝ :=
  fun d => x (c6FiniteSubjectEquiv.symm d)

/-- C1のrate 3だけをSCMのtrue行為ラベルで表す局所コード。
これは全実数のゲインとBoolとの同一視ではなく、選択された最大ゲイン値の符号化である。 -/
def c6EncodeRate3AsSCMAction (r : ℝ) : Bool := decide (r = 3)

/-- Boolラベルへ写して戻すと、各C1主体の値を保つ。 -/
theorem c6FiniteSubjectStateView_preserves_coordinate
    (x : AgentState) (i : Fin 2) :
    c6FiniteSubjectStateView x (c6FiniteSubjectEquiv i) = x i := by
  simp [c6FiniteSubjectStateView]

/-- 二主体状態の等しさは、対応するBool主体ごとの観測値の等しさと同値。 -/
theorem c6FiniteSubjectStateView_injective :
    Function.Injective c6FiniteSubjectStateView := by
  intro x y h
  funext i
  have hi := congrFun h (c6FiniteSubjectEquiv i)
  simpa [c6FiniteSubjectStateView] using hi

abbrev C6C1C4Observation :=
  C6C1ObservedState ×
    ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
      (Bool × C6C5ControlledState × ℝ))

/-- 同じ外生入力から得るC1主体座標と25-SCMの(Γ,Y⁺)を一緒に読む射影。
第1成分はC1の実数状態、第2成分はSCMの離散状態・出力なので、型を潰して同一視しない。 -/
def c6C1SubjectSCMObservationView (d : Bool) (z : C6C1C4Observation) :
    ℝ × (Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) :=
  (c6FiniteSubjectStateView z.1.1 d, z.2.1)

theorem c6C1SubjectSCMObservationView_measurable (d : Bool) :
    Measurable (c6C1SubjectSCMObservationView d) := by
  unfold c6C1SubjectSCMObservationView c6FiniteSubjectStateView
  fun_prop

abbrev c6SharedHistorySCM :=
  (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm

/-- C1主体値、C3の元情報joint、および同じC3値を文脈として使う25-SCM構造式を
一つの観測に載せた空間。 -/
abbrev C6C1C3SCMJointObservation :=
  ((ℝ × (Unit × (Bool × Bool))) ×
    (Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool))

/-- C3 goalをC1主体ラベルとして読み、C3 action/goalをそれぞれSCM action/candidateに
渡す。外生点は既存C3/C4共通lawのC4入力から取り出す。 -/
noncomputable def c6C1C3SCMJointLaw
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure C6C1C3SCMJointObservation :=
  c6C3C4CommonInputLaw.map (fun p =>
    ((c6FiniteSubjectStateView
        (c6CommonLayerData.trajectory (entropyLayerAddress n)
          c1MaxGainSignal x t₀ t) p.2.2.1,
      p.2),
      (c6SharedHistorySCM.stateEquation p.2.2.1 p.2.2.2
          (c6SharedHistorySCM.globalHistory p.1.1.2) p.1.1.2,
        c6SharedHistorySCM.outputEquation p.2.2.1 p.2.2.2
          (c6SharedHistorySCM.globalHistory p.1.1.2) p.1.1.2 p.2.2.1)))

/-- C1/C3/SCM同時観測は確率法則であり、情報jointは完全に保存される。 -/
theorem c6C1C3SCMJointLaw_isProbability
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure (c6C1C3SCMJointLaw n x t₀ t T τ) := by
  rw [c6C1C3SCMJointLaw, MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C3C4CommonInputLaw_isProbability
  · fun_prop

/-- 同時観測lawをC3入力tupleへ射影すると、元の上位情報joint lawそのものに戻る。 -/
theorem c6C1C3SCMJointLaw_informationMarginal
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3SCMJointLaw n x t₀ t T τ).map (fun z => z.1.2) =
      Tomabechi.Consistency.C3.upperJoint := by
  rw [c6C1C3SCMJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (measurable_of_finite _)]
  change c6C3C4CommonInputLaw.map Prod.snd =
    Tomabechi.Consistency.C3.upperJoint
  exact c6C3C4CommonInputLaw_c3_marginal

/-- joint law内のSCM出力は、同じC4入力からの大域履歴に等しい。
従ってS5の履歴出力をC3 goal/actionとの同時観測上でも保つ。 -/
theorem c6C1C3SCMJointLaw_output_eq_C4HistoryLaw
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3SCMJointLaw n x t₀ t T τ).map (fun z => z.2.2) =
      c6C3C4CommonInputLaw.map (fun p => c6SharedHistorySCM.globalHistory p.1.1.2) := by
  rw [c6C1C3SCMJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (measurable_of_finite _)]
  apply MeasureTheory.Measure.map_congr
  filter_upwards with p
  change c6SharedHistorySCM.outputEquation p.2.2.1 p.2.2.2
    (c6SharedHistorySCM.globalHistory p.1.1.2) p.1.1.2 p.2.2.1 = _
  rw [Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_output_eq_history]

/-- 正層C1状態を、元のC3情報jointおよび共有SCM構造式へ載せるS7部分証人。 -/
structure C6FiniteSubjectInformationAdapter
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) where
  law : MeasureTheory.Measure C6C1C3SCMJointObservation
  law_is_joint_observation : law = c6C1C3SCMJointLaw n x t₀ t T τ
  probability : MeasureTheory.IsProbabilityMeasure law
  c3_information_marginal :
    law.map (fun z => z.1.2) = Tomabechi.Consistency.C3.upperJoint
  c4_history_output_marginal :
    law.map (fun z => z.2.2) =
      c6C3C4CommonInputLaw.map (fun p => c6SharedHistorySCM.globalHistory p.1.1.2)

/-- C1/C3/SCM同時観測lawの具体adapter。 -/
noncomputable def c6FiniteSubjectInformationAdapter
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) :
    C6FiniteSubjectInformationAdapter n x t₀ t T τ where
  law := c6C1C3SCMJointLaw n x t₀ t T τ
  law_is_joint_observation := rfl
  probability := c6C1C3SCMJointLaw_isProbability n x t₀ t T τ
  c3_information_marginal := c6C1C3SCMJointLaw_informationMarginal n x t₀ t T τ
  c4_history_output_marginal := c6C1C3SCMJointLaw_output_eq_C4HistoryLaw n x t₀ t T τ

/-- C1のBool符号化主体座標と25-SCMの(Γ,Y⁺)は、同じ外生標本上のjoint lawで観測できる。
law右辺は実際の25-C3 SCMの構造式から作り、単なる独立productで置き換えない。 -/
theorem c6C1SubjectSCM_jointLaw
    (x : AgentState) (t₀ t T τ : ℝ) (d a s : Bool) :
    (((c6SharedHistorySCM.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map
        (c6C1C4JointObservation x t₀ t T τ)).map
          (c6C1SubjectSCMObservationView d) =
      c6SharedHistorySCM.exogenousLaw.toMeasure.map (fun u =>
          (c6FiniteSubjectStateView
              (Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow
                t₀ x t) d,
            (c6SharedHistorySCM.stateEquation d a
                (c6SharedHistorySCM.globalHistory u) u,
              c6SharedHistorySCM.outputEquation d a
                (c6SharedHistorySCM.globalHistory u) u s))) := by
  have h := c6C1C4JointObservationLaw_eq_actualSCMLaw x t₀ t T τ d a s
  have hm := congrArg
    (fun ν : Measure C6C1C4Observation => ν.map (c6C1SubjectSCMObservationView d)) h
  calc
    _ = _ := hm
    _ = _ := by
      rw [MeasureTheory.Measure.map_map
        (c6C1SubjectSCMObservationView_measurable d)
        (by fun_prop)]
      rfl

/-- 正層nは、原文の正整数添字n+1を持つ共通層に置かれる。 -/
theorem c6FiniteData_positiveLayer_address (n : PositiveLayer) :
    entropyLayerAddress n = (some (originalPositiveIndex n) : CommonLayer) := rfl

/-- 正層nの共通データ状態は、そのままC1の二主体状態である。 -/
theorem c6FiniteData_positiveLayer_state (n : PositiveLayer) :
    C6LayeredState (entropyLayerAddress n) = AgentState := rfl

/-- 正層nの許容方策型はC1の全可測有界ゲイン族である。 -/
theorem c6FiniteData_positiveLayer_policy (n : PositiveLayer) :
    C6LayeredPolicy (entropyLayerAddress n) = C1GainSignal := rfl

/-- C1全制御族について、正層nのデータ軌道はC1制御軌道そのもの。 -/
theorem c6FiniteData_positiveLayer_trajectory
    (n : PositiveLayer) (u : C1GainSignal) (x : AgentState) (T s : ℝ) :
    c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s =
      controlledConsensusState x T u s := rfl

/-- C1のrate-3選択flowは、正層Dに最大ゲイン方策を入れたtrajectoryそのもの。 -/
theorem c6FiniteData_positiveLayer_selectedFlow
    (n : PositiveLayer) (x : AgentState) (T s : ℝ) :
    c6CommonLayerData.trajectory (entropyLayerAddress n)
        c1MaxGainSignal x T s =
      Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow
        T x s := by
  change controlledConsensusState x T c1MaxGainSignal s =
    Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow T x s
  rw [Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow_eq_rate3]
  ext i
  fin_cases i <;>
    simp [controlledConsensusState, consensusOptimalFlow, c1ControlledOrbit,
      c1MaxGain_accumulation, meanState, halfDifference]

/-- O24の型付きEgoは、各正層Dに置いた最適方策の値と一致する。
実数値のゲインを保ち、SCMのBool行為型への同一視は行わない。 -/
theorem c6FiniteData_o24Ego_eq_maxGain
    (n : PositiveLayer) (t₀ : ℝ) (x : AgentState) (t : ℝ) :
    (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t =
      3 := by
  rfl

/-- O24が選ぶrate 3を、上記の限定コードでSCM行為trueへ送る。 -/
theorem c6FiniteData_o24Ego_actionCode
    (n : PositiveLayer) (t₀ : ℝ) (x : AgentState) (t : ℝ) :
    c6EncodeRate3AsSCMAction
      ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t) =
        true := by
  rw [c6FiniteData_o24Ego_eq_maxGain n t₀ x t]
  simp [c6EncodeRate3AsSCMAction]

/-- O24のflowを、同じ正層Dの最適方策signalで駆動するtrajectoryとして表す。 -/
theorem c6FiniteData_o24Flow_eq_layerOptimalPolicyTrajectory
    (n : PositiveLayer) (t₀ : ℝ) (x : AgentState) (t : ℝ) :
    (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).flow.flow t₀ x t =
      c6CommonLayerData.trajectory (entropyLayerAddress n)
        (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t₀ t := by
  simpa [Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter,
    c6CommonLayerData, c6LayeredNonnegativeTimeData, c6LayeredOptimalPolicy,
    entropyLayerAddress, originalPositiveIndex,
    Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow_eq_rate3] using
      (c6FiniteData_positiveLayer_selectedFlow n x t₀ t).symm

/-- O24/C1からC2保存平均状態を経由した同じ軌道は、正層DのC1 trajectoryと
C5の実ベクトルtrajectoryへ同時に射影される。 -/
theorem c6FiniteData_C1C5_flow_crosswalk
    (n : PositiveLayer) (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) :
    let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
    completeStateToC1 (meanState x) bridge.c2CompleteState =
        c6CommonLayerData.trajectory (entropyLayerAddress n)
          c1MaxGainSignal x t₀ t ∧
      disagreementStateTo27 bridge.c2CompleteState =
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          (disagreementStateTo27 (c1ToCompleteState x)) 0 (3 * (t - t₀)) := by
  let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
  refine ⟨?_, bridge.c5Flow_preserved⟩
  exact bridge.c1Flow_preserved.trans
    (c6FiniteData_positiveLayer_selectedFlow n x t₀ t).symm

/-- 有限正層のbaseline付き費用は、同じC1→C2→C5軌道上のC5費用から
係数8/3とbaseline 1で復元できる。これは費用同一視ではなく原文二費用の正確な換算式。 -/
theorem c6FiniteData_C1C5_runningCost_baselineScale
    (n : PositiveLayer) (x : AgentState) (hx : x ∈ box)
    (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) :
    let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
    c6LayeredRunningCost (some (originalPositiveIndex n)) c1MaxGainSignal
        (controlledConsensusState x t₀ c1MaxGainSignal t) t =
      1 + (8 / 3 : ℝ) *
        Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          (disagreementStateTo27 bridge.c2CompleteState) t := by
  let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
  have hproj : completeStateToC1 (meanState x) bridge.c2CompleteState =
      controlledConsensusState x t₀ c1MaxGainSignal t := by
    exact bridge.c1Flow_preserved.trans
      ((c6FiniteData_positiveLayer_selectedFlow n x t₀ t).symm.trans
        (c6FiniteData_positiveLayer_trajectory n c1MaxGainSignal x t₀ t))
  have hcoordinate : halfDifference (controlledConsensusState x t₀ c1MaxGainSignal t) =
      1 - cognitiveCoordinate bridge.c2CompleteState := by
    rw [← hproj]
    simp [completeStateToC1, halfDifference, cognitiveCoordinate]
  calc
    _ = 1 + 8 * (halfDifference (controlledConsensusState x t₀ c1MaxGainSignal t)) ^ 2 := by
      rfl
    _ = 1 + (8 / 3 : ℝ) *
        Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          (disagreementStateTo27 bridge.c2CompleteState) t := by
      rw [bridge.c5RunningCost_preserved Tomabechi.Examples.Theorem27.vectorMaximalPolicy]
      rw [hcoordinate]
      ring

/-- O24 Selfが閾値内と判定する条件を、箱内では有限層Dの同じ走行費で表せる。 -/
theorem c6FiniteData_o24Self_layerCostThreshold
    (n : PositiveLayer) (t₀ t : ℝ) (x : AgentState) (hx : x ∈ box) :
    x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Self
        t (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ↔
      x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ∧
        c6CommonLayerData.runningCost (entropyLayerAddress n)
          (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t ≤ 1 := by
  change (x ∈ Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusReachable t₀ ∧
      consensusV0 x t ≤ 1) ↔
    x ∈ Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusReachable t₀ ∧
      c6LayeredRunningCost (some (originalPositiveIndex n))
        (c6LayeredOptimalPolicy (some (originalPositiveIndex n)) x t) x t ≤ 1
  rw [c6LayeredFiniteRunningCost_eq_C1V0 (originalPositiveIndex n)
    (c6LayeredOptimalPolicy (some (originalPositiveIndex n)) x t) x hx t]

/-- O24 TCZ membership is Self membership; its finite-layer cost view follows on box states. -/
theorem c6FiniteData_o24TCZ_layerCostThreshold
    (n : PositiveLayer) (t₀ t : ℝ) (x : AgentState) (hx : x ∈ box) :
    x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).TCZ t ↔
      x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ∧
        c6CommonLayerData.runningCost (entropyLayerAddress n)
          (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t ≤ 1 := by
  change x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Self t
    (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ↔ _
  exact c6FiniteData_o24Self_layerCostThreshold n t₀ t x hx

/-- 同一SCM joint lawのC1座標を、同じ正層Dのrate-3 trajectoryで読み替える。
有限層状態と(Γ,Y⁺)を実際の25-SCM外生標本上の一つのjoint lawに置く。 -/
theorem c6FiniteData_subjectSCM_jointLaw
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) (d a s : Bool) :
    (((c6SharedHistorySCM.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map
        (c6C1C4JointObservation x t₀ t T τ)).map
          (c6C1SubjectSCMObservationView d) =
      c6SharedHistorySCM.exogenousLaw.toMeasure.map (fun u =>
          (c6FiniteSubjectStateView
              (c6CommonLayerData.trajectory (entropyLayerAddress n)
                c1MaxGainSignal x t₀ t) d,
            (c6SharedHistorySCM.stateEquation d a
                (c6SharedHistorySCM.globalHistory u) u,
              c6SharedHistorySCM.outputEquation d a
                (c6SharedHistorySCM.globalHistory u) u s))) := by
  rw [c6C1SubjectSCM_jointLaw]
  apply MeasureTheory.Measure.map_congr
  filter_upwards with u
  congr 1
  · exact congrArg (fun y => c6FiniteSubjectStateView y d)
      (c6FiniteData_positiveLayer_selectedFlow n x t₀ t).symm

/-- 型付きO24 Egoのrateを局所Boolコードへ写した行為を使っても、同じ外生標本上の
C1主体座標と25-SCM (Γ,Y⁺) のjoint lawが得られる。コード値は前定理によりtrue。 -/
theorem c6FiniteData_o24Ego_subjectSCM_jointLaw
    (n : PositiveLayer) (x : AgentState) (t₀ t T τ : ℝ) (d s : Bool) :
    (((c6SharedHistorySCM.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d
        (c6EncodeRate3AsSCMAction
          ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t)) s)).map
        (c6C1C4JointObservation x t₀ t T τ)).map
          (c6C1SubjectSCMObservationView d) =
      c6SharedHistorySCM.exogenousLaw.toMeasure.map (fun u =>
          (c6FiniteSubjectStateView
              (c6CommonLayerData.trajectory (entropyLayerAddress n)
                c1MaxGainSignal x t₀ t) d,
            (c6SharedHistorySCM.stateEquation d
                (c6EncodeRate3AsSCMAction
                  ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t))
                (c6SharedHistorySCM.globalHistory u) u,
              c6SharedHistorySCM.outputEquation d
                (c6EncodeRate3AsSCMAction
                  ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t))
                (c6SharedHistorySCM.globalHistory u) u s))) := by
  exact c6FiniteData_subjectSCM_jointLaw n x t₀ t T τ d
    (c6EncodeRate3AsSCMAction
      ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t)) s

/-- A7 の stitched pathは、同じ制御信号を各正層Dの有限層へ入れた
実C1状態軌道を完全状態から復元したものと一致する。初期状態は費用最適性用boxの
外側だが、ここではC1軌道の代数的一致だけを主張する。 -/
theorem c6FiniteData_stitchedPath_identity
    (n : PositiveLayer) (t : ℝ) (ht : 0 ≤ t) :
    c6CommonLayerData.trajectory (entropyLayerAddress n)
        c3A7StitchedC1Gain ![(1 : ℝ), -1] 0 t =
      completeStateToC1 0 (c3A7StitchedTrajectory t) := by
  simpa [c6CommonLayerData, c6LayeredNonnegativeTimeData,
    c6LayeredTrajectory, entropyLayerAddress, originalPositiveIndex] using
    c3A7StitchedC1Gain_matches_twoAgent_flow t ht

/-- D上のstitched pathをC1座標から完全状態へ戻しても、C2認知座標は保存される。 -/
theorem c6FiniteData_stitchedPath_cognitive
    (n : PositiveLayer) (t : ℝ) (ht : 0 ≤ t) :
    cognitiveCoordinate
      (c1ToCompleteState
        (c6CommonLayerData.trajectory (entropyLayerAddress n)
          c3A7StitchedC1Gain ![(1 : ℝ), -1] 0 t)) =
      cognitiveCoordinate (c3A7StitchedTrajectory t) := by
  rw [c6FiniteData_stitchedPath_identity n t ht]
  simp [c1ToCompleteState, completeStateToC1, cognitiveCoordinate,
    meanState, halfDifference]
  ring

/-- 有限正層の実費用は、C1定理1の同じ状態評価を用いる。箱条件は元のC1評価の条件。 -/
theorem c6FiniteData_positiveLayer_runningCost
    (n : PositiveLayer) (u : C1GainSignal) (x : AgentState)
    (hx : x ∈ box) (t : ℝ) :
    c6CommonLayerData.runningCost (entropyLayerAddress n) u x t =
      consensusV0 x t := by
  exact c6LayeredFiniteRunningCost_eq_C1V0 (originalPositiveIndex n) u x hx t

/-- 率1での有限正層最適値は、C1最大ゲイン軌道の明示積分値である。 -/
theorem c6FiniteData_positiveLayer_optimalValue
    (n : PositiveLayer) (x : AgentState) (T : ℝ) :
    c6CommonLayerData.optimalValue (entropyLayerAddress n) x T =
      1 + 8 * (halfDifference x) ^ 2 / 7 := rfl

/-- 共通束上の正層重みは、C2原文の正層重みと一致する。 -/
theorem c6FiniteData_positiveLayer_weight (n : PositiveLayer) :
    commonEntropyWeight (entropyLayerAddress n) = layerWeight n :=
  (c6CommonLayerAdapter n).c1_common_weight_agrees n

/-- S0/S2用の有限正層adapter。これは正層アドレスだけでなく、同じ層に置いたC1の
状態型・全制御族・軌道・走行費・割引最適値・重みの対応を保持する。 -/
structure C6FiniteLayerDataAdapter (n : PositiveLayer) where
  address : entropyLayerAddress n = (some (originalPositiveIndex n) : CommonLayer)
  state_type : C6LayeredState (entropyLayerAddress n) = AgentState
  policy_type : C6LayeredPolicy (entropyLayerAddress n) = C1GainSignal
  trajectory : ∀ (u : C1GainSignal) (x : AgentState) (T s : ℝ),
    c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s =
      controlledConsensusState x T u s
  selected_flow : ∀ (x : AgentState) (T s : ℝ),
    c6CommonLayerData.trajectory (entropyLayerAddress n)
        c1MaxGainSignal x T s =
      Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow
        T x s
  o24_ego_max_gain : ∀ (t₀ : ℝ) (x : AgentState) (t : ℝ),
    (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t = 3
  o24_ego_action_code : ∀ (t₀ : ℝ) (x : AgentState) (t : ℝ),
    c6EncodeRate3AsSCMAction
      ((Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Ego x t) = true
  o24_flow_layer_policy : ∀ (t₀ : ℝ) (x : AgentState) (t : ℝ),
    (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).flow.flow t₀ x t =
      c6CommonLayerData.trajectory (entropyLayerAddress n)
        (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t₀ t
  o24_self_layer_cost : ∀ (t₀ t : ℝ) (x : AgentState) (hx : x ∈ box),
    (x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).Self t
      (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ↔
    x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ∧
      c6CommonLayerData.runningCost (entropyLayerAddress n)
        (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t ≤ 1)
  o24_tcz_layer_cost : ∀ (t₀ t : ℝ) (x : AgentState) (hx : x ∈ box),
    (x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).TCZ t ↔
    x ∈ (Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀).reachable ∧
      c6CommonLayerData.runningCost (entropyLayerAddress n)
        (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x t) x t ≤ 1)
  subject_equiv : Fin 2 ≃ Bool
  subject_coordinate : ∀ (u : C1GainSignal) (x : AgentState) (T s : ℝ)
      (i : Fin 2),
    c6FiniteSubjectStateView
      (c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s)
      (subject_equiv i) =
        controlledConsensusState x T u s i
  subject_information_law : ∀ (x : AgentState) (t₀ t T τ : ℝ),
    C6FiniteSubjectInformationAdapter n x t₀ t T τ
  running_cost : ∀ (u : C1GainSignal) (x : AgentState), x ∈ box → ∀ t : ℝ,
    c6CommonLayerData.runningCost (entropyLayerAddress n) u x t = consensusV0 x t
  layer_potential : ∀ (u : C1GainSignal) (x : AgentState), x ∈ box → ∀ t : ℝ,
    c6CommonLayerData.runningCost (entropyLayerAddress n) u x t =
      1 + 16 * centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation (originalPositiveIndex n))
        (recenterEntropyState 1
          (Tomabechi.Consistency.C3.representation (originalPositiveIndex n))
          (c1ToCompleteState x))
  trajectory_layer_potential : ∀ (u : C1GainSignal) (x : AgentState),
    x ∈ box → ∀ (T s : ℝ), T ≤ s →
      c6CommonLayerData.runningCost (entropyLayerAddress n) u
          (c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s) s =
        1 + 16 * centeredQuadraticPotential
          (Tomabechi.Consistency.C3.representation (originalPositiveIndex n))
          (recenterEntropyState 1
            (Tomabechi.Consistency.C3.representation (originalPositiveIndex n))
            (c1ToCompleteState
              (c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s)))
  optimal_value : ∀ (x : AgentState) (T : ℝ),
    c6CommonLayerData.optimalValue (entropyLayerAddress n) x T =
      1 + 8 * (halfDifference x) ^ 2 / 7
  optimal_policy : ∀ (x : AgentState) (T : ℝ),
    c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x T = c1MaxGainSignal
  optimal_cost_integrable : ∀ (x : AgentState) (T : ℝ),
    Integrable
      (fun s => theorem26DiscountWeight c6CommonLayerData.rho T s *
        c6CommonLayerData.runningCost (entropyLayerAddress n)
          (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x T)
          (c6CommonLayerData.trajectory (entropyLayerAddress n)
            (c6CommonLayerData.optimalPolicy (entropyLayerAddress n) x T) x T s) s)
      (futureLebesgueMeasure T)
  optimal_value_minimal : ∀ (x : AgentState) (T : ℝ) (u : C1GainSignal),
    ENNReal.ofReal (c6CommonLayerData.optimalValue (entropyLayerAddress n) x T) ≤
      ∫⁻ s, ENNReal.ofReal
        (theorem26DiscountWeight c6CommonLayerData.rho T s *
          c6CommonLayerData.runningCost (entropyLayerAddress n) u
            (c6CommonLayerData.trajectory (entropyLayerAddress n) u x T s) s)
        ∂futureLebesgueMeasure T
  c1_c2_c5_flow_crosswalk : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t),
    let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
    completeStateToC1 (meanState x) bridge.c2CompleteState =
        c6CommonLayerData.trajectory (entropyLayerAddress n)
          c1MaxGainSignal x t₀ t ∧
      disagreementStateTo27 bridge.c2CompleteState =
        Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          (disagreementStateTo27 (c1ToCompleteState x)) 0 (3 * (t - t₀))
  c1_c2_c5_cost_baseline_scale : ∀ (x : AgentState) (hx : x ∈ box)
      (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t),
    let bridge := Tomabechi.Consistency.C6.c6C1C5Adapter x hx t₀ t ht₀ htt
    c6LayeredRunningCost (some (originalPositiveIndex n)) c1MaxGainSignal
        (controlledConsensusState x t₀ c1MaxGainSignal t) t =
      1 + (8 / 3 : ℝ) *
        Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          (disagreementStateTo27 bridge.c2CompleteState) t
  weight : commonEntropyWeight (entropyLayerAddress n) = layerWeight n

/-- 各正層のadapterは、既存の順序・重み対応と実際のC1有限層Dから構成できる。 -/
theorem c6FiniteLayerDataAdapter_exists (n : PositiveLayer) :
    Nonempty (C6FiniteLayerDataAdapter n) := by
  refine ⟨{
    address := c6FiniteData_positiveLayer_address n
    state_type := c6FiniteData_positiveLayer_state n
    policy_type := c6FiniteData_positiveLayer_policy n
    trajectory := c6FiniteData_positiveLayer_trajectory n
    selected_flow := c6FiniteData_positiveLayer_selectedFlow n
    o24_ego_max_gain := c6FiniteData_o24Ego_eq_maxGain n
    o24_ego_action_code := c6FiniteData_o24Ego_actionCode n
    o24_flow_layer_policy := c6FiniteData_o24Flow_eq_layerOptimalPolicyTrajectory n
    o24_self_layer_cost := c6FiniteData_o24Self_layerCostThreshold n
    o24_tcz_layer_cost := c6FiniteData_o24TCZ_layerCostThreshold n
    subject_equiv := c6FiniteSubjectEquiv
    subject_coordinate := by intro u x T s i; exact c6FiniteSubjectStateView_preserves_coordinate _ i
    subject_information_law := c6FiniteSubjectInformationAdapter n
    running_cost := ?_
    layer_potential := ?_
    trajectory_layer_potential := ?_
    optimal_value := c6FiniteData_positiveLayer_optimalValue n
    optimal_policy := by intro x T; rfl
    optimal_cost_integrable := ?_
    optimal_value_minimal := ?_
    c1_c2_c5_flow_crosswalk := c6FiniteData_C1C5_flow_crosswalk n
    c1_c2_c5_cost_baseline_scale := c6FiniteData_C1C5_runningCost_baselineScale n
    weight := c6FiniteData_positiveLayer_weight n }⟩
  · intro u x hx t
    exact c6FiniteData_positiveLayer_runningCost n u x hx t
  · intro u x hx t
    exact c6LayeredFiniteRunningCost_eq_layerPotential
      (originalPositiveIndex n) u x hx t
  · intro u x hx T s hTs
    exact c6LayeredTrajectory_runningCost_eq_layerPotential
      (originalPositiveIndex n) u x hx T s hTs
  · intro x T
    simpa [c6CommonLayerData, c6LayeredNonnegativeTimeData,
      c6LayeredOptimalPolicy, c6LayeredRunningCost, c6LayeredTrajectory,
      entropyLayerAddress, originalPositiveIndex] using
      c1FiniteLayer_optimalCost_integrable x T
  · intro x T u
    simpa [c6CommonLayerData, c6LayeredNonnegativeTimeData,
      c6LayeredOptimalValue, c6LayeredRunningCost, c6LayeredTrajectory,
      theorem26DiscountWeight, entropyLayerAddress, originalPositiveIndex] using
      c1FiniteLayer_optimalValue_minimal x T u

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c6FiniteLayerDataAdapter_exists
