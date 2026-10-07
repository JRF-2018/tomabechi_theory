import Tomabechi.Consistency.ConsistencyC6_Integration

/-!
# C6のC1接続を進めるための座標保存補題

既存のエントロピーから半径を作る射影は軌道を保存するが、C1の合意目標を
C5の零価値集合へ送らない。ここでは半径を不一致 `1-q` とする別の射影を
構成し、軌道・走行費・価値・零集合を保存する。C1の保存平均も状態に保持する。
全許容方策・割引費用・履歴法則を統合するC6全体の証人ではない。
-/

namespace Tomabechi.Consistency.C6

open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1CommonModel
open Filter

/-- 半径を認知的不一致、位相をC2の物理・認知観測から作る射影。
物理エントロピーを走行費に加算せず、零不一致状態を零価値目標へ写す。 -/
noncomputable def disagreementStateTo27
    (z : CompleteState) : Tomabechi.Examples.Theorem27Op.E2 :=
  (1 - cognitiveCoordinate z) • Tomabechi.Examples.Theorem27Op.e0 +
    ((3 / 2 : ℝ) * entropyObservedElapsed z) •
      Tomabechi.Examples.Theorem27Op.e1

theorem disagreementStateTo27_radial (z : CompleteState) :
    disagreementStateTo27 z 0 = 1 - cognitiveCoordinate z := by
  simp [disagreementStateTo27,
    Tomabechi.Examples.Theorem27Op.e0_apply0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]

theorem disagreementStateTo27_phase (z : CompleteState) :
    disagreementStateTo27 z 1 = (3 / 2 : ℝ) * entropyObservedElapsed z := by
  simp [disagreementStateTo27,
    Tomabechi.Examples.Theorem27Op.e0_apply1,
    Tomabechi.Examples.Theorem27Op.e1_apply1]

/-- C5の任意の二次元初期値を持ち上げる代数的右逆。
aliveや物理観測の追加領域条件は、この等式から自動的には従わない。 -/
noncomputable def vectorStateToCompleteState
    (x : Tomabechi.Examples.Theorem27Op.E2) : CompleteState :=
  (1 - x 0, (2 / 3 : ℝ) * x 1 - (1 - x 0) ^ 2)

theorem disagreementStateTo27_right_inverse
    (x : Tomabechi.Examples.Theorem27Op.E2) :
    disagreementStateTo27 (vectorStateToCompleteState x) = x := by
  ext i
  fin_cases i
  · change disagreementStateTo27 (vectorStateToCompleteState x) 0 = x 0
    rw [disagreementStateTo27_radial]
    simp [vectorStateToCompleteState, cognitiveCoordinate]
  · change disagreementStateTo27 (vectorStateToCompleteState x) 1 = x 1
    rw [disagreementStateTo27_phase]
    simp [vectorStateToCompleteState, entropyObservedElapsed,
      cognitiveCoordinate, physicalCoordinate]
    ring

theorem disagreementStateTo27_surjective :
    Function.Surjective disagreementStateTo27 := by
  intro x
  exact ⟨vectorStateToCompleteState x, disagreementStateTo27_right_inverse x⟩

/-- 旧エントロピー射影は半径が常に正なので、零価値集合の保存には使えない。 -/
theorem entropyStateTo27_radial_pos (z : CompleteState) :
    0 < entropyStateTo27 z 0 := by
  simpa [entropyStateTo27,
    Tomabechi.Examples.Theorem27Op.e0_apply0,
    Tomabechi.Examples.Theorem27Op.e1_apply0] using
    Real.exp_pos (-entropyObservedElapsed z)

/-- エントロピー半径射影の像はC5の零価値目標と交わらない。
軌道保存だけを根拠に、この射影を零目標保存adapterとして使うことはできない。 -/
theorem entropyStateTo27_not_mem_zeroValueTarget (z : CompleteState) (t : ℝ) :
    entropyStateTo27 z ∉
      Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) t := by
  rw [Tomabechi.Examples.Theorem27.vectorSourceTarget_eq_ring,
    Tomabechi.Examples.Theorem27Op.ringE_eq]
  exact ne_of_gt (entropyStateTo27_radial_pos z)

/-- 認知的不一致が零の状態では二つのC5射影は必ず異なる。
これは射影の過剰同定の反証であり、C6全体のモデル存在を反証するものではない。 -/
theorem entropyStateTo27_ne_disagreement_of_cognitive_eq_one
    (z : CompleteState) (hq : cognitiveCoordinate z = 1) :
    entropyStateTo27 z ≠ disagreementStateTo27 z := by
  intro heq
  have hradial := congrArg (fun x : Tomabechi.Examples.Theorem27Op.E2 => x 0) heq
  rw [disagreementStateTo27_radial, hq] at hradial
  have hpos := entropyStateTo27_radial_pos z
  linarith

/-- 新しい射影も全初期完全状態からC5の同じ最適ベクトル流を保存する。 -/
theorem disagreementStateTo27_preserves_flow (z : CompleteState) (t : ℝ) :
    disagreementStateTo27 (completeEntropyFlow z t) =
      Tomabechi.Examples.Theorem27Op.flowE (disagreementStateTo27 z) 0 t := by
  ext i
  fin_cases i
  · change disagreementStateTo27 (completeEntropyFlow z t) 0 =
      Tomabechi.Examples.Theorem27Op.flowE (disagreementStateTo27 z) 0 t 0
    rw [disagreementStateTo27_radial, Tomabechi.Examples.Theorem27Op.flowE_0,
      disagreementStateTo27_radial, cognitiveCoordinate_completeEntropyFlow]
    simp [Tomabechi.Theorem24_26_Model.flow]
  · change disagreementStateTo27 (completeEntropyFlow z t) 1 =
      Tomabechi.Examples.Theorem27Op.flowE (disagreementStateTo27 z) 0 t 1
    rw [disagreementStateTo27_phase, Tomabechi.Examples.Theorem27Op.flowE_1,
      disagreementStateTo27_phase, entropyObservedElapsed_completeEntropyFlow]
    simp [Tomabechi.Examples.Theorem27Op.omg]
    ring

theorem disagreementStateTo27_preserves_data_trajectory
    (z : CompleteState) (t : ℝ) (ht : 0 ≤ t) :
    disagreementStateTo27 (completeEntropyFlow z t) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        (disagreementStateTo27 z) 0 t := by
  rw [Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE
    (disagreementStateTo27 z) 0 t (by norm_num) ht]
  exact disagreementStateTo27_preserves_flow z t

/-- C1の選択flowをrate-3の経過時間でC2完全状態へ移し、さらに
零目標・走行費を保つC5半径射影から同じC5データ軌道を回収する。 -/
theorem c1CompleteFlow_disagreement_matches_theorem27_data
    (x : AgentState) (t₀ t : ℝ) (htt : t₀ ≤ t) :
    disagreementStateTo27
        (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        (disagreementStateTo27 (c1ToCompleteState x)) 0 (3 * (t - t₀)) := by
  apply disagreementStateTo27_preserves_data_trajectory
  positivity

/-- C5走行費は射影後も全方策で同じ二乗不一致の3倍。 -/
theorem disagreementStateTo27_runningCost
    (z : CompleteState) (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (disagreementStateTo27 z) t =
      3 * (1 - cognitiveCoordinate z) ^ 2 := by
  change 3 * (disagreementStateTo27 z 0) ^ 2 = _
  rw [disagreementStateTo27_radial]

theorem disagreementStateTo27_optimalValue (z : CompleteState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 z) t =
      (1 - cognitiveCoordinate z) ^ 2 := by
  change (disagreementStateTo27 z 0) ^ 2 = _
  rw [disagreementStateTo27_radial]

/-- 零不一致とC5の最高層零価値目標の所属が同値になる。 -/
theorem disagreementStateTo27_target_iff (z : CompleteState) (t : ℝ) :
    disagreementStateTo27 z ∈
        Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) t ↔
      cognitiveCoordinate z = 1 := by
  rw [Tomabechi.Examples.Theorem27.vectorSourceTarget_eq_ring,
    Tomabechi.Examples.Theorem27Op.ringE_eq]
  change disagreementStateTo27 z 0 = 0 ↔ _
  rw [disagreementStateTo27_radial]
  constructor <;> intro h <;> linarith

theorem c1ToCompleteState_disagreement (x : AgentState) :
    1 - cognitiveCoordinate (c1ToCompleteState x) = halfDifference x := by
  simp [c1ToCompleteState, cognitiveCoordinate]

theorem c1ToCompleteState_value_preserved (x : AgentState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c1ToCompleteState x)) t =
      (halfDifference x) ^ 2 := by
  rw [disagreementStateTo27_optimalValue, c1ToCompleteState_disagreement]

/-- C1定理1の残差は、箱上でC5最適価値の8倍。基礎評価のbaselineは別に保持する。 -/
theorem c1ToCompleteState_residual_preserved
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    Tomabechi.Theorem1.residual1 (consensusV0 x t) 1 =
      8 * Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c1ToCompleteState x)) t := by
  rw [consensusV0_residual_eq_potential x hx t,
    sharedPotential_eq_coupling x hx t, c1ToCompleteState_value_preserved]
  simp [Tomabechi.Examples.Theorem2.γ, halfDifference]
  ring

/-- 箱内では、C1の実際の到達TCZとC5の零価値目標の所属を同じ射影で結ぶ。
二つの層の基礎評価自体が等しいという主張ではない。 -/
theorem c1ToCompleteState_target_preserved
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀) :
    x ∈ consensusOptimalTheorem1Target t₀ t ↔
      disagreementStateTo27 (c1ToCompleteState x) ∈
        Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) t := by
  have hpot : Tomabechi.Examples.Theorem2.DA.potential x t =
      8 * Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c1ToCompleteState x)) t := by
    rw [← consensusV0_residual_eq_potential x hx t]
    exact c1ToCompleteState_residual_preserved x hx t
  rw [consensusOptimalTheorem1Target_eq_shared t₀ t ht₀]
  change (x ∈ box ∧ Tomabechi.Examples.Theorem2.DA.potential x t = 0) ↔ _
  rw [hpot]
  simp [hx, Tomabechi.Theorem24_26.theorem26ZeroValueTarget]

/-- C1箱初期値について、元のrate-3 flow、C2完全状態、C5実制御データ、
定理1残差と定理1/26の到達零目標を、一つの保存adapterへ束ねる。 -/
structure C6C1C5Adapter
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) where
  c2CompleteState : CompleteState
  c5UpperControl : Tomabechi.Consistency.C6.C6C4C5UpperControlAdapter
    (disagreementStateTo27 (c1ToCompleteState x))
  c1Flow_preserved :
    completeStateToC1 (meanState x) c2CompleteState =
      c1Witness.selectedFlow.flow t₀ x t
  c5Flow_preserved :
    disagreementStateTo27 c2CompleteState =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        (disagreementStateTo27 (c1ToCompleteState x)) 0 (3 * (t - t₀))
  c5RunningCost_preserved : ∀ π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true,
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (disagreementStateTo27 c2CompleteState) t =
      3 * (1 - cognitiveCoordinate c2CompleteState) ^ 2
  c5OptimalValue_preserved :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 c2CompleteState) t =
      (1 - cognitiveCoordinate c2CompleteState) ^ 2
  theorem1Residual_preserved :
    Tomabechi.Theorem1.residual1 (consensusV0 x t) 1 =
      8 * Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c1ToCompleteState x)) t
  theorem1Target_preserved :
    x ∈ consensusOptimalTheorem1Target t₀ t ↔
      disagreementStateTo27 (c1ToCompleteState x) ∈
        Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) t

/-- C1→C2→C5保存を各箱状態・各許容開始時刻で具体的に構成する。 -/
noncomputable def c6C1C5Adapter
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) : C6C1C5Adapter x hx t₀ t ht₀ htt where
  c2CompleteState := completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))
  c5UpperControl := c6C4C5UpperControlAdapter (disagreementStateTo27 (c1ToCompleteState x))
  c1Flow_preserved := by
    exact c1CompleteFlow_matches_witness x t₀ t
  c5Flow_preserved := c1CompleteFlow_disagreement_matches_theorem27_data x t₀ t htt
  c5RunningCost_preserved := by
    intro π
    exact disagreementStateTo27_runningCost
      (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) π t
  c5OptimalValue_preserved := disagreementStateTo27_optimalValue
    (completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))) t
  theorem1Residual_preserved := c1ToCompleteState_residual_preserved x hx t
  theorem1Target_preserved := c1ToCompleteState_target_preserved x hx t₀ t ht₀

/-- C1射影に適合させた上層adapterと、C4のtrue履歴に対応する上層adapterは、
初期状態が異なっても同じC5 feedback 方策を使う。S6で共有する方策の同定。 -/
theorem c6C1C5_policy_eq_C4_upper
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) :
    (c6C1C5Adapter x hx t₀ t ht₀ htt).c5UpperControl.policy =
      (c6C4C5ControlAdapter true).policy := by
  rfl

/-- 共有feedbackは、C1から来る上層状態でもC4上層adapterの状態でも、
それぞれのC5費用データの最適方策である。 -/
theorem c6C1C5_sharedPolicy_optimal_at_both_states
    (x : AgentState) (hx : x ∈ box) (t₀ t T : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) :
    (c6C1C5Adapter x hx t₀ t ht₀ htt).c5UpperControl.policy =
        Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy true
          (c6C1C5Adapter x hx t₀ t ht₀ htt).c5UpperControl.state T ∧
      (c6C4C5ControlAdapter true).policy =
        Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy true
          (c6C4C5ControlAdapter true).state T := by
  exact ⟨(c6C1C5Adapter x hx t₀ t ht₀ htt).c5UpperControl.policy_is_data_optimum T,
    (c6C4C5ControlAdapter true).policy_is_data_optimum T⟩

/-- C1の保存平均を完全状態の一成分として保持する。 -/
abbrev MeanCompleteState := ℝ × CompleteState

noncomputable def c1MeanCompleteInitial (x : AgentState) : MeanCompleteState :=
  (meanState x, c1ToCompleteState x)

def meanCompleteC1Projection (z : MeanCompleteState) : AgentState :=
  completeStateToC1 z.1 z.2

/-- 基準経過時間sで動く完全状態流。C1側ではs=3(t-t₀)を使う。 -/
noncomputable def meanCompleteFlow (z : MeanCompleteState) (s : ℝ) : MeanCompleteState :=
  (z.1, completeEntropyFlow z.2 s)

theorem meanCompleteFlow_initial (z : MeanCompleteState) :
    meanCompleteFlow z 0 = z := by
  simp [meanCompleteFlow, completeEntropyFlow_initial]

theorem meanCompleteFlow_semigroup (z : MeanCompleteState) (s t : ℝ) :
    meanCompleteFlow (meanCompleteFlow z s) t = meanCompleteFlow z (s + t) := by
  simp [meanCompleteFlow, completeEntropyFlow_semigroup]

/-- 状態に格納した平均から射影するので、初期値を外部引数に残さずflowを保存する。 -/
theorem meanCompleteC1Projection_preserves_witness_flow
    (x : AgentState) (t₀ t : ℝ) :
    meanCompleteC1Projection
        (meanCompleteFlow (c1MeanCompleteInitial x) (3 * (t - t₀))) =
      c1Witness.selectedFlow.flow t₀ x t := by
  exact c1CompleteFlow_matches_witness x t₀ t

/-- 同じ時刻に観測するC1状態と、それを持ち上げたC2完全状態。 -/
abbrev C6C1ObservedState := AgentState × CompleteState

noncomputable def c6C1ObservedStateAt
    (x : AgentState) (t₀ t : ℝ) : C6C1ObservedState :=
  (c1Witness.selectedFlow.flow t₀ x t,
    completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀)))

/-- C1/C2状態と、C4介入から得るSCM観測・C5制御評価を一つに束ねる。 -/
noncomputable def c6C1C4JointObservation
    (x : AgentState) (t₀ t T τ : ℝ)
    (i : C4C5SCMInput) :
    C6C1ObservedState ×
      ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
        (Bool × C6C5ControlledState × ℝ)) :=
  (c6C1ObservedStateAt x t₀ t,
    c4C6IntervenedJointControlOutcome T τ i)

/-- 任意のC1初期状態とC4介入contextについて、C1流/C2完全状態と
C4 `(Γ,Y⁺)`/C5制御・実費用を、同じC4外生確率空間上の一つのlawで結合できる。
C4 comparison-input経由の共有SCM観測と、無作為化25-C3モデルの実観測は一致する。 -/
theorem c6C1C4JointObservationLaw_eq_actualSCMLaw
    (x : AgentState) (t₀ t T τ : ℝ) (d a s : Bool) :
    (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map
        (c6C1C4JointObservation x t₀ t T τ) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (c6C1ObservedStateAt x t₀ t,
            (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
                d a
                ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
                u,
              (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
                d a
                ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
                u s),
            c6C4C5JointControlOutcome T τ
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)))) := by
  rw [MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  dsimp [c6C1C4JointObservation, c4C6IntervenedJointControlOutcome,
    c4C6StateOutputFromInput]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact (c4RandomizedIntervenedOutput_eq_c6Output_allContexts d a s u).symm
    · rfl

/-- C1/C2状態・C4 joint・C5実費用のlawは、候補値を外生入力から無作為に選ぶ
25-C3モデルそのもののSCM lawとも一致する。 -/
theorem c6C1C4JointObservationLaw_eq_randomizedActualSCMLaw
    (x : AgentState) (t₀ t T τ : ℝ) :
    c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (c6C1ObservedStateAt x t₀ t,
            (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
                false false
                ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
                u,
              (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
                false false
                ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
                u
                ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.candidateVariable
                  false false u)),
            c6C4C5JointControlOutcome T τ
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)))) := by
  rw [c4RandomizedInputLaw, MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact (c4RandomizedActualOutput_eq_c6Output u).symm
    · rfl

/-- C1箱端の最大不一致から、元C3 H-stage列の各中心へ実際に到達する時刻。
段n≥1では開始後の時刻が非負である。 -/
noncomputable def c1TimeAtC3StageCenter (n : ℕ) : ℝ :=
  Real.log (((n : ℝ) + 2) / 4) / 3

theorem c1TimeAtC3StageCenter_strictMono : StrictMono c1TimeAtC3StageCenter := by
  intro m n hmn
  unfold c1TimeAtC3StageCenter
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).2
  apply Real.log_lt_log (by positivity)
  have hcast : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  linarith

theorem c1TimeAtC3StageCenter_tendsto_atTop :
    Tendsto c1TimeAtC3StageCenter atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hadd := tendsto_atTop_add_const_right atTop (2 : ℝ) hcast
  have harg : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / 4) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      hadd.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  unfold c1TimeAtC3StageCenter
  exact (Real.tendsto_log_atTop.comp harg).atTop_div_const
    (by norm_num : (0 : ℝ) < 3)

theorem c1TimeAtC3StageCenter_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ c1TimeAtC3StageCenter n := by
  unfold c1TimeAtC3StageCenter
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg1 : 1 ≤ ((n : ℝ) + 2) / 4 := by nlinarith
  have hlog : 0 ≤ Real.log (((n : ℝ) + 2) / 4) := Real.log_nonneg harg1
  positivity

/-- n≥2なら、C1/C2の認知座標はC3元H-stage列のn段目中心表象に一致する。
有限段表象 `(k/(k+1))` を単なる束ラベルでなく、同じ指数流の実軌道上で実現する。 -/
theorem c1ExtremeCompleteFlow_reaches_C3_hStage_center
    (n : ℕ) (hn : 2 ≤ n) :
    Tomabechi.Consistency.C2.cognitiveCoordinate
        (completeEntropyFlow
          (c1ToCompleteState ![(1 / 4 : ℝ), -(1 / 4 : ℝ)])
          (3 * c1TimeAtC3StageCenter n)) =
      Tomabechi.Consistency.C3.representation
        (commonStageAddress (n + 1)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg : 0 < ((n : ℝ) + 2) / 4 := by positivity
  have hexp : Real.exp (-(3 * c1TimeAtC3StageCenter n)) =
      4 / ((n : ℝ) + 2) := by
    rw [c1TimeAtC3StageCenter,
      show -(3 * (Real.log (((n : ℝ) + 2) / 4) / 3)) =
        -Real.log (((n : ℝ) + 2) / 4) by ring,
      Real.exp_neg, Real.exp_log harg]
    field_simp
  have hq : Tomabechi.Consistency.C2.cognitiveCoordinate
      (c1ToCompleteState ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]) = (3 / 4 : ℝ) := by
    simp [c1ToCompleteState, cognitiveCoordinate, halfDifference]
    norm_num
  rw [cognitiveCoordinate_completeEntropyFlow, hq, hexp]
  change 1 - (1 - (3 / 4 : ℝ)) * (4 / ((n : ℝ) + 2)) =
    ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)
  field_simp
  push_cast
  ring

/-- 上のC3中心到達はC2座標だけの式ではなく、C1の実際の選択流でも同じ時刻に成立する。 -/
theorem c1ExtremeFlow_reaches_C3_hStage_center
    (n : ℕ) (hn : 2 ≤ n) :
    1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c1TimeAtC3StageCenter n)) =
      Tomabechi.Consistency.C3.representation
        (commonStageAddress (n + 1)) := by
  let x : AgentState := ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
  let τ := c1TimeAtC3StageCenter n
  have hproject := c1CompleteFlow_matches_witness x 0 τ
  have hcoordinate : ∀ z : CompleteState,
      1 - halfDifference (completeStateToC1 (meanState x) z) =
        cognitiveCoordinate z := by
    intro z
    simp [completeStateToC1, halfDifference, cognitiveCoordinate]
  calc
    1 - halfDifference (c1Witness.selectedFlow.flow 0 x τ) =
        1 - halfDifference
          (completeStateToC1 (meanState x)
            (completeEntropyFlow (c1ToCompleteState x) (3 * (τ - 0)))) := by
          rw [← hproject]
    _ = Tomabechi.Consistency.C2.cognitiveCoordinate
        (completeEntropyFlow (c1ToCompleteState x) (3 * τ)) := by
          rw [hcoordinate]
          simp
    _ = Tomabechi.Consistency.C3.representation
        (commonStageAddress (n + 1)) := by
          simpa [x, τ] using c1ExtremeCompleteFlow_reaches_C3_hStage_center n hn

theorem c1ExtremeFlow_reaches_actual_C3_hStage_center
    (n : ℕ) (hn : 2 ≤ n) :
    1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c1TimeAtC3StageCenter n)) =
      (Tomabechi.Consistency.C3.hStageSequence n).center := by
  rw [c1ExtremeFlow_reaches_C3_hStage_center n hn,
    ← hStageSequence_center_is_commonStage_representation]

/-- C1の端点選択flowから作るC2完全状態を、C3中心へ達する時刻で読む。 -/
noncomputable def c1C2StateAtC3CenterSample (n : ℕ) : CompleteState :=
  completeEntropyFlow (c1ToCompleteState ![(1 / 4 : ℝ), -(1 / 4 : ℝ)])
    (3 * c1TimeAtC3StageCenter (n + 2))

/-- C1選択flow上で、対応するC3元H-stage中心は厳密に順次更新される。 -/
theorem c1ExtremeFlow_C3_stageCenters_strictly_advance
    (n : ℕ) (hn : 2 ≤ n) :
    1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c1TimeAtC3StageCenter n)) <
      1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c1TimeAtC3StageCenter (n + 1))) := by
  rw [c1ExtremeFlow_reaches_C3_hStage_center n hn,
    c1ExtremeFlow_reaches_C3_hStage_center (n + 1) (by omega)]
  change ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) <
    ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) + 1)
  have hn1 : 0 < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  have hn2 : 0 < ((n + 2 : ℕ) : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hn1 hn2]
  push_cast
  nlinarith

/-- C1の実際の最適流を、C3の元H-stage中心列へ写すサンプリングadapter。
時刻はC3の元stageTimeではなく、C1軌道が同じ中心に達する時刻である。
従ってこれはS7の中心列共有を満たすが、S1の同一時刻・同一制御法則接続を主張しない。 -/
structure C6C1C3CenterSamplingAdapter where
  sampleTime : ℕ → ℝ
  time_eq : ∀ n, sampleTime n = c1TimeAtC3StageCenter (n + 2)
  strictMono : StrictMono sampleTime
  nonnegative : ∀ n, 0 ≤ sampleTime n
  stageInformation : ∀ n,
    Tomabechi.Consistency.C6.C6C3InformationAdapter (n + 2)
  completeState : ℕ → CompleteState
  completeState_is_sampled_rate3_flow : ∀ n,
    completeState n = c1C2StateAtC3CenterSample n
  completeState_cognitive_is_stage_center : ∀ n,
    cognitiveCoordinate (completeState n) =
      (Tomabechi.Consistency.C3.hStageSequence (n + 2)).center
  completeState_entropy_production : ∀ n,
    Tomabechi.Consistency.C2.generalizedEntropy (completeState n) =
      Tomabechi.Consistency.C2.generalizedEntropy
        (c1ToCompleteState ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]) +
        3 * sampleTime n
  reaches_center : ∀ n,
    1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)] (sampleTime n)) =
      (Tomabechi.Consistency.C3.hStageSequence (n + 2)).center

/-- C1/C3の中心列接続を、存在時刻・軌道上の等式・厳密な時間順序とともに供給する。 -/
noncomputable def c6C1C3CenterSamplingAdapter : C6C1C3CenterSamplingAdapter where
  sampleTime n := c1TimeAtC3StageCenter (n + 2)
  time_eq _ := rfl
  strictMono := by
    intro m n hmn
    exact c1TimeAtC3StageCenter_strictMono (by omega)
  nonnegative n := c1TimeAtC3StageCenter_nonneg (n + 2) (by omega)
  stageInformation n := Tomabechi.Consistency.C6.c6C3InformationAdapter (n + 2)
  completeState := c1C2StateAtC3CenterSample
  completeState_is_sampled_rate3_flow _ := rfl
  completeState_cognitive_is_stage_center n := by
    rw [c1C2StateAtC3CenterSample,
      hStageSequence_center_is_commonStage_representation]
    simpa using c1ExtremeCompleteFlow_reaches_C3_hStage_center
      (n + 2) (by omega)
  completeState_entropy_production n := by
    simpa [c1C2StateAtC3CenterSample] using c1CompleteFlow_generalizedEntropy_exactProduction
      ![(1 / 4 : ℝ), -(1 / 4 : ℝ)] 0
      (c1TimeAtC3StageCenter (n + 2))
  reaches_center n := by
    simpa using c1ExtremeFlow_reaches_actual_C3_hStage_center (n + 2) (by omega)

/-- 中心サンプリングadapterは全段で実際のC3中心に到達する。 -/
theorem c6C1C3CenterSamplingAdapter_reaches (n : ℕ) :
    1 - halfDifference
        (c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c6C1C3CenterSamplingAdapter.sampleTime n)) =
      (Tomabechi.Consistency.C3.hStageSequence (n + 2)).center :=
  c6C1C3CenterSamplingAdapter.reaches_center n

/-- C1/C2がサンプルする有限C3層の中心では、C5上位価値は層間gapの二乗。
共通層添字n+2に対し値は `1/(n+4)^2` で、有限層では正である。 -/
theorem c6C1C3_sample_C5_value_eq_layerGap (n : ℕ) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState n)) t =
      (1 / ((n : ℝ) + 4)) ^ 2 := by
  have hrep : Tomabechi.Consistency.C3.representation
      (commonStageAddress (n + 3)) =
      ((n : ℝ) + 3) / ((n : ℝ) + 4) := by
    change Tomabechi.Consistency.C3.representation
      ((n + 3 : ℕ) : Tomabechi.Consistency.C3.Atom) = _
    simp [Tomabechi.Consistency.C3.representation]
    push_cast
    ring
  rw [disagreementStateTo27_optimalValue,
    c6C1C3CenterSamplingAdapter.completeState_cognitive_is_stage_center,
    hStageSequence_center_is_commonStage_representation]
  rw [hrep]
  field_simp
  <;> ring

theorem c6C1C3_sample_C5_value_pos (n : ℕ) (t : ℝ) :
    0 < Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState n)) t := by
  rw [c6C1C3_sample_C5_value_eq_layerGap]
  positivity

/-- 共通束上で上位を表す値1はC5の零価値集合へ写る。 -/
theorem c6CommonTop_value_zero (t : ℝ) :
    operationalLayerAddress true = (⊤ : CommonLayer) ∧
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      (disagreementStateTo27 (1, 0)) t = 0 := by
  constructor
  · exact operationalLayerAddress_top
  · rw [disagreementStateTo27_optimalValue]
    simp [cognitiveCoordinate]

/-- C1/C2の中心サンプルにおけるC5価値は、上位値0へ収束する。 -/
theorem c6C1C3_sample_C5_value_tendsto_zero (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
          (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState n)) t)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4))
      Filter.atTop (nhds 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 3) using 1
    funext n
    simp only [Function.comp_apply]
    push_cast
    ring
  have hsq := hinv.pow 2
  have heq : (fun n : ℕ =>
      Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState n)) t) =
      fun n : ℕ => (1 / ((n : ℝ) + 4)) ^ 2 := by
    funext n
    exact c6C1C3_sample_C5_value_eq_layerGap n t
  rw [heq]
  simpa using hsq

/-- C3元stageの累積開始時刻は、各stage durationが1以上なのでstage index以上。 -/
theorem c3StageTime_ge_nat (n : ℕ) :
    (n : ℝ) ≤ Tomabechi.Consistency.C3.stageTime n := by
  calc
    (n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ Finset.range n,
        Tomabechi.Consistency.C3.stageDuration k := by
      apply Finset.sum_le_sum
      intro k hk
      exact Tomabechi.Consistency.C3.stageDuration_lower_bound k

/-- 時刻そのものを共有してC1の箱内最大ゲイン流をC3元stage開始時刻へ置くと、
n≥1ではC1認知座標はC3 H-stage中心より厳密に大きい。従って両方の中心列を
同じ時刻・同じC1初期箱・同じrate-3流で点wise同定する案は成立しない。 -/
theorem c1BoxFlow_not_at_C3_center_at_original_stageTime
    (x : AgentState) (hx : x ∈ box) (n : ℕ) (hn : 1 ≤ n) :
    (1 - halfDifference
        (c1Witness.selectedFlow.flow 0 x
          (Tomabechi.Consistency.C3.stageTime n))) >
      (Tomabechi.Consistency.C3.hStageSequence n).center := by
  have hselected : c1Witness.selectedFlow.flow 0 x
      (Tomabechi.Consistency.C3.stageTime n) =
      consensusOptimalFlow.flow 0 x (Tomabechi.Consistency.C3.stageTime n) := by
    rw [c1Witness.selectedFlow_eq_rate3]
  have hcoord : 1 - halfDifference
      (consensusOptimalFlow.flow 0 x (Tomabechi.Consistency.C3.stageTime n)) =
      1 - halfDifference x * Real.exp
        (-3 * Tomabechi.Consistency.C3.stageTime n) := by
    unfold halfDifference
    rw [consensusOptimalFlow_gap]
    ring
  have hboxq := c1ToCompleteState_cognitive_mem x hx
  change (3 / 4 : ℝ) ≤ cognitiveCoordinate (c1ToCompleteState x) ∧
      cognitiveCoordinate (c1ToCompleteState x) ≤ 5 / 4 at hboxq
  have hd : halfDifference x ≤ (1 / 4 : ℝ) := by
    have hdis := c1ToCompleteState_disagreement x
    nlinarith
  have htime : (n : ℝ) ≤ Tomabechi.Consistency.C3.stageTime n :=
    c3StageTime_ge_nat n
  have harg : 0 < ((n : ℝ) + 2) / 4 := by positivity
  have hlarge : ((n : ℝ) + 2) / 4 <
      Real.exp (3 * Tomabechi.Consistency.C3.stageTime n) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    calc
      ((n : ℝ) + 2) / 4 < 3 * n + 1 := by nlinarith
      _ < Real.exp (3 * n) := Real.add_one_lt_exp (by positivity)
      _ ≤ Real.exp (3 * Tomabechi.Consistency.C3.stageTime n) :=
        Real.exp_le_exp.mpr (by nlinarith)
  have hdecay : Real.exp (-3 * Tomabechi.Consistency.C3.stageTime n) <
      4 / ((n : ℝ) + 2) := by
    rw [show -3 * Tomabechi.Consistency.C3.stageTime n =
      -(3 * Tomabechi.Consistency.C3.stageTime n) by ring, Real.exp_neg]
    have hinv : (Real.exp (3 * Tomabechi.Consistency.C3.stageTime n))⁻¹ <
        (((n : ℝ) + 2) / 4)⁻¹ :=
      (inv_lt_inv₀ (Real.exp_pos _) harg).2 hlarge
    calc
      (Real.exp (3 * Tomabechi.Consistency.C3.stageTime n))⁻¹ <
          (((n : ℝ) + 2) / 4)⁻¹ := hinv
      _ = 4 / ((n : ℝ) + 2) := by field_simp
  have hprod : halfDifference x *
      Real.exp (-3 * Tomabechi.Consistency.C3.stageTime n) <
      1 / ((n : ℝ) + 2) := by
    calc
      halfDifference x * Real.exp (-3 * Tomabechi.Consistency.C3.stageTime n) ≤
          (1 / 4 : ℝ) * Real.exp (-3 * Tomabechi.Consistency.C3.stageTime n) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      _ < (1 / 4 : ℝ) * (4 / ((n : ℝ) + 2)) :=
        mul_lt_mul_of_pos_left hdecay (by norm_num)
      _ = 1 / ((n : ℝ) + 2) := by field_simp
  rw [hselected, hcoord, Tomabechi.Consistency.C3.hStageSequence_center]
  change 1 - halfDifference x *
      Real.exp (-3 * Tomabechi.Consistency.C3.stageTime n) >
      ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)
  have hcenter : ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) =
      1 - 1 / ((n : ℝ) + 2) := by
    push_cast
    field_simp
    ring
  rw [hcenter]
  linarith

/-- C3/C4 common-input lawをC1/C2状態とC4/C5実joint-control outcomeへ
押し出した一つのC1–C5–C3結合law。C3とC4の元周辺は保たれる。 -/
noncomputable def c6C1C3C4JointLaw
    (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure
      ((C6C1ObservedState ×
          ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
            (Bool × C6C5ControlledState × ℝ))) ×
        (Unit × (Bool × Bool))) :=
  c6C3C4CommonInputLaw.map (fun w =>
    (c6C1C4JointObservation x t₀ t T τ w.1, w.2))

/-- C1/C2/C4/C5/C3を載せたpushforwardも確率lawである。 -/
theorem c6C1C3C4JointLaw_isProbability
    (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure (c6C1C3C4JointLaw x t₀ t T τ) := by
  rw [c6C1C3C4JointLaw, MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C3C4CommonInputLaw_isProbability
  · exact (by fun_prop)

/-- 合成lawからC3情報標本を観測しても、元C3 jointが周辺lawとして戻る。 -/
theorem c6C1C3C4JointLaw_c3_marginal
    (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4JointLaw x t₀ t T τ).map Prod.snd =
      Tomabechi.Consistency.C3.upperJoint := by
  rw [c6C1C3C4JointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : Prod.snd ∘ (fun w : C4C5SCMInput × (Unit × (Bool × Bool)) =>
      (c6C1C4JointObservation x t₀ t T τ w.1, w.2)) = Prod.snd := by
    funext w
    rfl
  rw [hcomp, c6C3C4CommonInputLaw_c3_marginal]

/-- 合成lawのC1/C2/C4/C5観測周辺は、C4入力law上の従来の結合観測law。 -/
theorem c6C1C3C4JointLaw_c1C4C5_marginal
    (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4JointLaw x t₀ t T τ).map Prod.fst =
      c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ) := by
  rw [c6C1C3C4JointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : Prod.fst ∘ (fun w : C4C5SCMInput × (Unit × (Bool × Bool)) =>
      (c6C1C4JointObservation x t₀ t T τ w.1, w.2)) =
        c6C1C4JointObservation x t₀ t T τ ∘ Prod.fst := by
    funext w
    rfl
  rw [hcomp, ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
    c6C3C4CommonInputLaw_c4_marginal]

/-- C1/C2、C4介入joint、C5状態/実費用、C3情報jointを
同じlawに置く統合の具体的な部分adapter。 -/
structure C6C1C3C4JointLawAdapter
    (x : AgentState) (t₀ t T τ : ℝ) where
  law : MeasureTheory.Measure
      ((C6C1ObservedState ×
          ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
            (Bool × C6C5ControlledState × ℝ))) ×
        (Unit × (Bool × Bool)))
  law_is_pushforward : law = c6C1C3C4JointLaw x t₀ t T τ
  probability : MeasureTheory.IsProbabilityMeasure law
  c1C4C5_marginal :
    law.map Prod.fst =
      c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ)
  c3_information_marginal :
    law.map Prod.snd = Tomabechi.Consistency.C3.upperJoint
  c3c4_source_adapter : C6C3C4CommonLawAdapter 0

/-- 既存のlaw保存接続を組み合わせたC1/C2/C3/C4/C5のcommon-law部分証人。 -/
noncomputable def c6C1C3C4JointLawAdapter
    (x : AgentState) (t₀ t T τ : ℝ) :
    C6C1C3C4JointLawAdapter x t₀ t T τ where
  law := c6C1C3C4JointLaw x t₀ t T τ
  law_is_pushforward := rfl
  probability := c6C1C3C4JointLaw_isProbability x t₀ t T τ
  c1C4C5_marginal := c6C1C3C4JointLaw_c1C4C5_marginal x t₀ t T τ
  c3_information_marginal := c6C1C3C4JointLaw_c3_marginal x t₀ t T τ
  c3c4_source_adapter := c6C3C4CommonLawAdapter 0

theorem c6C1C3C4JointLawAdapter_nonempty
    (x : AgentState) (t₀ t T τ : ℝ) :
    Nonempty (C6C1C3C4JointLawAdapter x t₀ t T τ) :=
  ⟨c6C1C3C4JointLawAdapter x t₀ t T τ⟩

end Tomabechi.Consistency.C6
