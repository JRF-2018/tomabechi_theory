import Tomabechi.Consistency.ConsistencyC6_C1Connections

/-!
# C6: 中心と累積ゲインを共有する制御流の核

C1・C3・C4・C5を、中心c、累積ゲインA、エントロピー増分Eを持つ一つの
状態更新則から取り出す。C1/C5は最適方策だけでなく元の全ゲイン族を保持する。
中心・許容族・基礎評価が異なるcontextを、同一の最適軌道へ強制的に同定しない。
この核は共有署名・全費用・全SCMの統合存在証人ではない。
-/

namespace Tomabechi.Consistency.C6

open Tomabechi.Consistency.C2
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Theorem2
open MeasureTheory
open Filter
open scoped Topology

/-- q'=g(c-q)、(y+q²)'=σ の累積ゲインA・収支増分Eに対する状態更新。
状態にはqと物理観測yを置き、独立時計は置かない。 -/
noncomputable def centeredGainEntropyStep (c A E : ℝ) (z : CompleteState) :
    CompleteState :=
  let q := c + (cognitiveCoordinate z - c) * Real.exp (-A)
  (q, entropyObservedElapsed z + E - q ^ 2)

theorem centeredGainEntropyStep_cognitive (c A E : ℝ) (z : CompleteState) :
    cognitiveCoordinate (centeredGainEntropyStep c A E z) =
      c + (cognitiveCoordinate z - c) * Real.exp (-A) := rfl

/-- 同じ観測から収支増分を回収する。 -/
theorem centeredGainEntropyStep_entropy (c A E : ℝ) (z : CompleteState) :
    entropyObservedElapsed (centeredGainEntropyStep c A E z) =
      entropyObservedElapsed z + E := by
  simp [centeredGainEntropyStep, entropyObservedElapsed, cognitiveCoordinate,
    physicalCoordinate]

/-- 共通核の中心からの二次評価。C3/C4の凍結谷・勾配流評価に対応する。 -/
noncomputable def centeredQuadraticPotential (c : ℝ) (z : CompleteState) : ℝ :=
  (cognitiveCoordinate z - c) ^ 2 / 2

/-- 中心からの二次評価は、累積ゲインAだけで `exp(-2A)` 倍される。
物理収支Eはこの評価に影響しない。 -/
theorem centeredQuadraticPotential_step (c A E : ℝ) (z : CompleteState) :
    centeredQuadraticPotential c (centeredGainEntropyStep c A E z) =
      centeredQuadraticPotential c z * Real.exp (-2 * A) := by
  rw [centeredQuadraticPotential, centeredQuadraticPotential,
    centeredGainEntropyStep_cognitive]
  rw [show (c + (cognitiveCoordinate z - c) * Real.exp (-A) - c) =
      (cognitiveCoordinate z - c) * Real.exp (-A) by ring]
  rw [show -2 * A = (-A) + (-A) by ring, Real.exp_add]
  ring

/-- C4の履歴別評価は、同じ認知座標上の共通二次評価そのもの。
これは評価関数の同定で、逆極限やTCZの集合同定は別の接続義務である。 -/
theorem centeredQuadraticPotential_eq_C4
    (h : Bool) (z : CompleteState) :
    centeredQuadraticPotential
        (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) z =
      Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h
        (cognitiveCoordinate z) := by
  rfl

/-- C4の実勾配流に沿う評価減衰を、共通核の二次評価減衰と同じ式で表す。 -/
theorem c4Potential_flow_decay (h : Bool) (x t : ℝ) :
    Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h
        (Tomabechi.Theorem16_25.theorem16_intervalGradientFlow h x t) =
      Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h x *
        Real.exp (-2 * t) := by
  simp only [Tomabechi.Theorem16_25.theorem16_intervalGradientPotential,
    Tomabechi.Theorem16_25.theorem16_intervalGradientFlow]
  rw [show -2 * t = (-t) + (-t) by ring, Real.exp_add]
  ring

/-- C3の元H-stageで使う実効二次谷評価も、同じ共有評価のpullbackである。
ここでは元の `hStageSequence` の段を保ち、別の谷列を作り直さない。 -/
theorem centeredQuadraticPotential_eq_C3_stage (n : ℕ) (z : CompleteState) :
    Tomabechi.Theorem22.stageEffectivePotential
        (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
        (cognitiveCoordinate z) =
      centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) z := by
  rw [Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec,
    Tomabechi.Consistency.C3.valleySequence_shape]
  simp [Tomabechi.Theorem22.stageEffectivePotential,
    Tomabechi.Examples.Theorem23B.quadraticStage,
    centeredQuadraticPotential, cognitiveCoordinate]
  ring

/-- C5上位走行費は共通核の二次評価の6倍。
係数を保持するので、C1/C5の異なる基礎評価を同一視しない。 -/
theorem c5RunningCost_eq_six_centeredPotential
    (z : CompleteState) (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (disagreementStateTo27 z) t =
      6 * centeredQuadraticPotential 1 z := by
  rw [disagreementStateTo27_runningCost]
  simp [centeredQuadraticPotential, cognitiveCoordinate]
  ring

/-- C5上位最適価値は共通核の二次評価の2倍である。 -/
theorem c5OptimalValue_eq_two_centeredPotential (z : CompleteState) (t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 z) t =
      2 * centeredQuadraticPotential 1 z := by
  rw [disagreementStateTo27_optimalValue]
  simp [centeredQuadraticPotential, cognitiveCoordinate]
  ring

/-- C1定理1の箱上評価は共通核二次評価の16倍にbaseline 1を加えたもの。
これにより共有する残差とcontext固有のbaselineを明示的に分ける。 -/
theorem c1V0_eq_baseline_add_centeredPotential
    (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    consensusV0 x t =
      1 + 16 * centeredQuadraticPotential 1 (c1ToCompleteState x) := by
  rw [consensusV0]
  rw [sharedPotential_eq_coupling x hx 0]
  simp [centeredQuadraticPotential, c1ToCompleteState, cognitiveCoordinate,
    halfDifference, Tomabechi.Examples.Theorem2.γ]
  ring

/-- C1定理1の基礎評価とC5上位走行費は、合意点ですら等しくない。
残差の係数付き対応を、同一contextの基礎費用そのものの一致と読み替えてはならない。 -/
theorem c1V0_ne_C5_runningCost_at_consensus
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true) (t : ℝ) :
    consensusV0 (0 : AgentState) t ≠
      Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (disagreementStateTo27 (c1ToCompleteState (0 : AgentState))) t := by
  have hx : (0 : AgentState) ∈ box := by simp [box]
  rw [c1V0_eq_baseline_add_centeredPotential (0 : AgentState) hx t,
    c5RunningCost_eq_six_centeredPotential]
  norm_num [centeredQuadraticPotential, c1ToCompleteState, cognitiveCoordinate,
    halfDifference]

/-- 中心cの認知座標を中心dへ平行移動し、物理観測を補正して総エントロピーを保つ。
C1の座標上の中心1を、共通束の頂点と無条件に同一視せずに移送するための写像。 -/
noncomputable def recenterEntropyState (c d : ℝ) (z : CompleteState) : CompleteState :=
  let q := cognitiveCoordinate z + d - c
  (q, entropyObservedElapsed z - q ^ 2)

/-- 再中心化は物理観測と認知二乗の総和を変えない。 -/
theorem recenterEntropyState_entropy (c d : ℝ) (z : CompleteState) :
    entropyObservedElapsed (recenterEntropyState c d z) = entropyObservedElapsed z := by
  simp [recenterEntropyState, entropyObservedElapsed, cognitiveCoordinate,
    physicalCoordinate]

/-- 再中心化は同じ累積ゲイン・同じ生成量の制御更新に可換する。 -/
theorem recenterEntropyState_step (c d A E : ℝ) (z : CompleteState) :
    recenterEntropyState c d (centeredGainEntropyStep c A E z) =
      centeredGainEntropyStep d A E (recenterEntropyState c d z) := by
  apply Prod.ext <;>
    simp [recenterEntropyState, centeredGainEntropyStep, entropyObservedElapsed,
      cognitiveCoordinate, physicalCoordinate] <;> ring

/-- 再中心化で同じ二次残差を保持する。baselineや閾値は変更しない。 -/
theorem recenterEntropyState_potential (c d : ℝ) (z : CompleteState) :
    centeredQuadraticPotential d (recenterEntropyState c d z) =
      centeredQuadraticPotential c z := by
  simp [centeredQuadraticPotential, recenterEntropyState, cognitiveCoordinate]
  ring

/-- 逆向きの再中心化で元の完全状態を復元する。 -/
theorem recenterEntropyState_inverse (c d : ℝ) (z : CompleteState) :
    recenterEntropyState d c (recenterEntropyState c d z) = z := by
  rcases z with ⟨q, y⟩
  apply Prod.ext <;>
    simp [recenterEntropyState, entropyObservedElapsed, cognitiveCoordinate,
      physicalCoordinate] <;> ring

/-- C1 の評価を有限層 `n` の中心へ移しても、正の基準値と係数を保つ。
これは有限層のC1側評価の保存式であり、C5頂点の走行費とは別のcontextに置く。 -/
theorem c1V0_eq_recentered_finite_layer_evaluation
    (n : ℕ) (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    consensusV0 x t =
      1 + 16 * centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (recenterEntropyState 1
          (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (c1ToCompleteState x)) := by
  rw [c1V0_eq_baseline_add_centeredPotential x hx t]
  rw [recenterEntropyState_potential]

/-- 再中心化後の有限層評価は、移した座標と有限層中心との差で表せる。 -/
theorem c1V0_eq_finite_layer_coordinate
    (n : ℕ) (x : AgentState) (hx : x ∈ box) (t : ℝ) :
    consensusV0 x t =
      1 + 8 * (cognitiveCoordinate
        (recenterEntropyState 1
          (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (c1ToCompleteState x)) -
        Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) ^ 2 := by
  rw [c1V0_eq_recentered_finite_layer_evaluation n x hx t]
  simp [centeredQuadraticPotential, recenterEntropyState, cognitiveCoordinate]
  ring

/-- 有限層でC1評価を走行費に使うとき、最大ゲインの割引被積分量は
すべての可測 `[0,3]` ゲイン競合以下となる。割引率は定理24/26の `rho=1`。 -/
theorem c1FiniteLayer_discounted_cost_minimal_pointwise
    (x : AgentState) (T s : ℝ) (u : C1GainSignal) (hs : T ≤ s) :
    Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference
          (controlledConsensusState x T c1MaxGainSignal s)) ^ 2) ≤
      Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (1 + 8 * (halfDifference
          (controlledConsensusState x T u s)) ^ 2) := by
  rw [controlledConsensusState_halfDifference,
    controlledConsensusState_halfDifference]
  have hsq :
      (c1ControlledOrbit (halfDifference x) T c1MaxGainSignal s) ^ 2 ≤
        (c1ControlledOrbit (halfDifference x) T u s) ^ 2 := by
    simpa [c1ControlledOrbit, c1MaxGain_accumulation] using
      (c1MaxGain_orbit_sq_le (halfDifference x) T s u hs)
  have hcost :
      1 + 8 * (c1ControlledOrbit (halfDifference x) T c1MaxGainSignal s) ^ 2 ≤
        1 + 8 * (c1ControlledOrbit (halfDifference x) T u s) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hcost (by
    rw [Tomabechi.Theorem24_26.theorem26DiscountWeight]
    exact (Real.exp_pos _).le)

theorem centeredGainEntropyStep_initial (c : ℝ) (z : CompleteState) :
    centeredGainEntropyStep c 0 0 z = z := by
  rcases z with ⟨q, y⟩
  simp [centeredGainEntropyStep, entropyObservedElapsed, cognitiveCoordinate,
    physicalCoordinate]

/-- 同じ凍結中心で累積ゲイン・収支が加法的なら、全状態更新も再始動する。
中心を変更する段間切替は別に端点一致を要求する。 -/
theorem centeredGainEntropyStep_add (c A B E F : ℝ) (z : CompleteState) :
    centeredGainEntropyStep c B F (centeredGainEntropyStep c A E z) =
      centeredGainEntropyStep c (A + B) (E + F) z := by
  apply Prod.ext
  · simp only [centeredGainEntropyStep, cognitiveCoordinate]
    rw [neg_add, Real.exp_add]
    ring
  · change entropyObservedElapsed (centeredGainEntropyStep c A E z) + F -
        (c + (cognitiveCoordinate (centeredGainEntropyStep c A E z) - c) *
          Real.exp (-B)) ^ 2 =
      entropyObservedElapsed z + (E + F) -
        (c + (cognitiveCoordinate z - c) * Real.exp (-(A + B))) ^ 2
    rw [centeredGainEntropyStep_entropy, centeredGainEntropyStep_cognitive,
      neg_add, Real.exp_add]
    ring

/-- 累積ゲインAの導関数がgなら、同じ状態則の認知座標は指定制御場を満たす。
可測ゲインのa.e.版にも、この補題を各微分可能点で適用できる。 -/
theorem centeredGainEntropyStep_cognitive_hasDerivAt
    (c : ℝ) (z : CompleteState) (A E : ℝ → ℝ) (t g : ℝ)
    (hA : HasDerivAt A g t) :
    HasDerivAt (fun s => cognitiveCoordinate (centeredGainEntropyStep c (A s) (E s) z))
      (g * (c - cognitiveCoordinate (centeredGainEntropyStep c (A t) (E t) z))) t := by
  have h := ((hA.neg.exp).const_mul (cognitiveCoordinate z - c)).const_add c
  convert h using 1
  · rfl
  · simp only [centeredGainEntropyStep_cognitive, Pi.neg_apply]
    ring

/-- 物理観測の微分は同じ認知微分と生成率σから定まる。
エントロピー収支を独立な時計座標で代用しない。 -/
theorem centeredGainEntropyStep_physical_hasDerivAt
    (c : ℝ) (z : CompleteState) (A E : ℝ → ℝ) (t g σ : ℝ)
    (hA : HasDerivAt A g t) (hE : HasDerivAt E σ t) :
    HasDerivAt (fun s => physicalCoordinate (centeredGainEntropyStep c (A s) (E s) z))
      (σ - 2 * cognitiveCoordinate (centeredGainEntropyStep c (A t) (E t) z) *
        (g * (c - cognitiveCoordinate (centeredGainEntropyStep c (A t) (E t) z)))) t := by
  have hq := centeredGainEntropyStep_cognitive_hasDerivAt c z A E t g hA
  have h := ((hasDerivAt_const t (entropyObservedElapsed z)).add hE).sub (hq.pow 2)
  convert h using 1
  · rfl
  · norm_num

/-- 中心c・実ゲインg・生成率σを引数に持つ共通制御場。 -/
def centeredGainEntropyField (c g σ : ℝ) (z : CompleteState) : CompleteState :=
  (g * (c - cognitiveCoordinate z),
    σ - 2 * cognitiveCoordinate z * (g * (c - cognitiveCoordinate z)))

/-- 状態更新は、この同じ制御場の微分方程式を満たす。 -/
theorem centeredGainEntropyStep_hasDerivAt
    (c : ℝ) (z : CompleteState) (A E : ℝ → ℝ) (t g σ : ℝ)
    (hA : HasDerivAt A g t) (hE : HasDerivAt E σ t) :
    HasDerivAt (fun s => centeredGainEntropyStep c (A s) (E s) z)
      (centeredGainEntropyField c g σ (centeredGainEntropyStep c (A t) (E t) z)) t := by
  convert (centeredGainEntropyStep_cognitive_hasDerivAt c z A E t g hA).prodMk
    (centeredGainEntropyStep_physical_hasDerivAt c z A E t g σ hA hE) using 1
  · funext s
    exact (Prod.eta _).symm
  · rfl

/-- 元のC2共通エントロピーflowは、この核のc=1、A=E=tの場合。 -/
theorem centeredGainEntropyStep_eq_completeEntropyFlow (z : CompleteState) (t : ℝ) :
    centeredGainEntropyStep 1 t t z = completeEntropyFlow z t := by
  apply Prod.ext <;>
    simp [centeredGainEntropyStep, completeEntropyFlow, cognitiveCoordinate] <;> ring

/-- C1の全許容ゲイン信号の実軌道を、同じ状態更新の射影から回収する。
最適ゲインだけの一致やC5へのゲイン族同一視には限定しない。 -/
theorem centeredGainEntropyStep_projects_all_C1_controls
    (x : AgentState) (u : C1GainSignal) (T t : ℝ) (E : ℝ) :
    completeStateToC1 (meanState x)
        (centeredGainEntropyStep 1 (c1AccumulatedGain u T t) E
          (c1ToCompleteState x)) =
      controlledConsensusState x T u t := by
  ext i
  fin_cases i <;>
    simp [completeStateToC1, centeredGainEntropyStep, c1ToCompleteState,
      cognitiveCoordinate, controlledConsensusState, c1ControlledOrbit]

/-- C1の任意ゲイン信号を共有核上で表す完全状態軌道。
平均は別の `MeanCompleteState` 成分に保存し、この状態では不一致座標を追う。 -/
noncomputable def c1CoreTrajectory (x : AgentState) (u : C1GainSignal)
    (T t : ℝ) : CompleteState :=
  centeredGainEntropyStep 1 (c1AccumulatedGain u T t) 0 (c1ToCompleteState x)

/-- C1の全許容ゲインについて、核軌道のC1射影が実二主体軌道そのもの。 -/
theorem c1CoreTrajectory_projects_controlledState
    (x : AgentState) (u : C1GainSignal) (T t : ℝ) :
    completeStateToC1 (meanState x) (c1CoreTrajectory x u T t) =
      controlledConsensusState x T u t := by
  exact centeredGainEntropyStep_projects_all_C1_controls x u T t 0

/-- C1の定理1被積分費用は、共有核の基準値1と二次評価16Pの和。
箱内条件を使って、原文の `DA.potential` を元の二主体状態から評価する。 -/
theorem c1CoreTrajectory_theorem1_runningCost
    (x : AgentState) (hx : x ∈ box) (u : C1GainSignal) (T t : ℝ)
    (ht : T ≤ t) :
    1 + Tomabechi.Examples.Theorem2.DA.potential
      (controlledConsensusState x T u t) t =
      1 + 16 * centeredQuadraticPotential 1 (c1CoreTrajectory x u T t) := by
  have hbox := controlledConsensusState_mem_box x hx T t u ht
  have hpot := Tomabechi.Consistency.ConsistencyC1Consensus.sharedPotential_eq_coupling
    (controlledConsensusState x T u t) hbox t
  rw [hpot]
  have hgap : controlledConsensusState x T u t 0 -
      controlledConsensusState x T u t 1 =
      2 * halfDifference (controlledConsensusState x T u t) := by
    simp [halfDifference]
    ring
  rw [hgap]
  have hcoordinate :
      cognitiveCoordinate (c1CoreTrajectory x u T t) - 1 =
        -halfDifference (controlledConsensusState x T u t) := by
    simp [c1CoreTrajectory, centeredGainEntropyStep, c1ToCompleteState,
      cognitiveCoordinate, controlledConsensusState, c1ControlledOrbit,
      halfDifference]
  rw [centeredQuadraticPotential, hcoordinate]
  norm_num [Tomabechi.Examples.Theorem2.γ]
  ring

/-- C1定理1の有限地平費用を、核評価とbaselineに分けて積分する表示。 -/
noncomputable def c1CoreTheorem1HorizonCost (x : AgentState) (u : C1GainSignal)
    (T H : ℝ) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal
      (1 + 16 * centeredQuadraticPotential 1 (c1CoreTrajectory x u T t))
    ∂volume.restrict (Set.Icc T (T + H))

/-- C1の実際の定理1費用積分は、共有核上の基準費用＋二次評価積分。 -/
theorem c1CoreTheorem1HorizonCost_eq_dataCost
    (x : AgentState) (hx : x ∈ box) (u : C1GainSignal) (T H : ℝ) :
    c1CoreTheorem1HorizonCost x u T H =
      consensusTheorem1HorizonCost x T H u := by
  unfold c1CoreTheorem1HorizonCost consensusTheorem1HorizonCost
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact congrArg ENNReal.ofReal
    (c1CoreTrajectory_theorem1_runningCost x hx u T t ht.1).symm

/-- C1の最大ゲインは、共有核の有限地平費用表示でも全許容ゲインに対し最小。 -/
theorem c1CoreTheorem1HorizonCost_optimal_minimal
    (x : AgentState) (hx : x ∈ box) (T H : ℝ) (hH : 0 < H) :
    ∀ u : C1GainSignal,
      c1CoreTheorem1HorizonCost x c1MaxGainSignal T H ≤
        c1CoreTheorem1HorizonCost x u T H := by
  intro u
  rw [c1CoreTheorem1HorizonCost_eq_dataCost x hx c1MaxGainSignal T H,
    c1CoreTheorem1HorizonCost_eq_dataCost x hx u T H]
  exact consensus_maxGain_attains_theorem1_horizon_argmin x hx T H hH u

/-- C1の元費用argminと、その同じ箱contextからC5へ写した実feedbackの最適性を
一つの保存adapterに束ねる。 -/
structure C6C1C5OptimalityAdapter
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) where
  state_cost_adapter : C6C1C5Adapter x hx t₀ t ht₀ htt
  /-- 保存平均を内部に持ち、現在時刻のC1二主体状態とC2完全状態を同じ状態から読む。 -/
  mean_complete_state : MeanCompleteState
  mean_complete_projects_to_c1 :
    meanCompleteC1Projection mean_complete_state =
      Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow
        t₀ x t
  mean_complete_c2_state : mean_complete_state.2 =
    completeEntropyFlow (c1ToCompleteState x) (3 * (t - t₀))
  mean_is_preserved : mean_complete_state.1 = meanState x
  /-- 原文O24で型を分けたSelf・Ego・TCZを保持するadapter。 -/
  o24_self_ego_tcz : Tomabechi.Consistency.ConsistencyC1O24.C1OptimalConsensusAdapter t₀
  /-- O24のflowはこの同じcontextのC1選択flow。 -/
  o24_flow_is_c1_selected : o24_self_ego_tcz.flow =
    Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow
  /-- O24の型付きTCZはC1定理1の選択flow到達目標に一致する。 -/
  o24_tcz_is_theorem1_target : ∀ s : ℝ, 0 ≤ t₀ →
    o24_self_ego_tcz.TCZ s = consensusOptimalTheorem1Target t₀ s
  /-- O24のTCZ所属を、同じ状態射影下のC5零価値目標所属として読む。 -/
  o24_tcz_preserves_c5_target : ∀ (y : AgentState) (hy : y ∈ box) (s : ℝ),
    y ∈ o24_self_ego_tcz.TCZ s ↔
      disagreementStateTo27 (c1ToCompleteState y) ∈
        Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) s
  /-- 定理1の実有限地平費用と、共有二次評価核上の費用の一致。 -/
  theorem1_cost_identity : ∀ (u : C1GainSignal) (T H : ℝ),
    c1CoreTheorem1HorizonCost x u T H =
      consensusTheorem1HorizonCost x T H u
  /-- 最大ゲインは元の定理1費用に対して全許容入力中で最小。 -/
  theorem1_argmin : ∀ (T H : ℝ), 0 < H → ∀ u : C1GainSignal,
    c1CoreTheorem1HorizonCost x c1MaxGainSignal T H ≤
      c1CoreTheorem1HorizonCost x u T H
  /-- 同じcontextからC5へ射影した方策は、C5の各有限地平でも実データ最適方策。 -/
  shared_c5_feedback_optimal : ∀ H : ℝ,
    state_cost_adapter.c5UpperControl.policy =
      Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy true
        state_cost_adapter.c5UpperControl.state H

/-- box内の全contextでC1定理1の全競合最小性とC5の実方策最適性を構成する。 -/
noncomputable def c6C1C5OptimalityAdapter
    (x : AgentState) (hx : x ∈ box) (t₀ t : ℝ)
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) :
    C6C1C5OptimalityAdapter x hx t₀ t ht₀ htt where
  state_cost_adapter := c6C1C5Adapter x hx t₀ t ht₀ htt
  mean_complete_state := meanCompleteFlow (c1MeanCompleteInitial x) (3 * (t - t₀))
  mean_complete_projects_to_c1 := by
    exact meanCompleteC1Projection_preserves_witness_flow x t₀ t
  mean_complete_c2_state := rfl
  mean_is_preserved := rfl
  o24_self_ego_tcz :=
    Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter t₀
  o24_flow_is_c1_selected := rfl
  o24_tcz_is_theorem1_target := by
    intro s hs
    calc
      _ = Tomabechi.Examples.Theorem2.DA.sharedTCZ box s :=
        Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ_eq_shared t₀ s hs
      _ = consensusOptimalTheorem1Target t₀ s :=
        (consensusOptimalTheorem1Target_eq_shared t₀ s hs).symm
  o24_tcz_preserves_c5_target := by
    intro y hy s
    change y ∈ Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ t₀ s ↔ _
    have htarget :
        Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ t₀ s =
          consensusOptimalTheorem1Target t₀ s := by
      calc
        _ = Tomabechi.Examples.Theorem2.DA.sharedTCZ box s :=
          Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ_eq_shared t₀ s ht₀
        _ = consensusOptimalTheorem1Target t₀ s :=
          (consensusOptimalTheorem1Target_eq_shared t₀ s ht₀).symm
    rw [htarget]
    exact c1ToCompleteState_target_preserved y hy t₀ s ht₀
  theorem1_cost_identity := fun u T H =>
    c1CoreTheorem1HorizonCost_eq_dataCost x hx u T H
  theorem1_argmin := fun T H hH u =>
    c1CoreTheorem1HorizonCost_optimal_minimal x hx T H hH u
  shared_c5_feedback_optimal := fun H =>
    (c6C1C5Adapter x hx t₀ t ht₀ htt).c5UpperControl.policy_is_data_optimum H

/-- 保存平均を状態内に保持した同じ更新則。 -/
noncomputable def meanCenteredGainEntropyStep (c A E : ℝ) (z : MeanCompleteState) :
    MeanCompleteState :=
  (z.1, centeredGainEntropyStep c A E z.2)

/-- C1全制御族の射影は、初期平均を外部引数にせず、現在の完全状態だけから読める。 -/
theorem meanCenteredGainEntropyStep_projects_all_C1_controls
    (x : AgentState) (u : C1GainSignal) (T t E : ℝ) :
    meanCompleteC1Projection
        (meanCenteredGainEntropyStep 1 (c1AccumulatedGain u T t) E
          (c1MeanCompleteInitial x)) = controlledConsensusState x T u t :=
  centeredGainEntropyStep_projects_all_C1_controls x u T t E

/-- C3の凍結二次軌道は、中心c・ゲイン1の同じ核から得る。 -/
theorem centeredGainEntropyStep_projects_quadraticFrozenOrbit
    (c x y T t E : ℝ) :
    cognitiveCoordinate (centeredGainEntropyStep c (t - T) E (x, y)) =
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit c x T t := rfl

/-- 元C3の谷証人が選ぶ軌道にも一致する。中心到達のサンプリングへ置き換えない。 -/
theorem centeredGainEntropyStep_projects_C3_witness
    (n : ℕ) (y t E : ℝ)
    (ht : (Tomabechi.Consistency.C3.valleySequence n).startTime ≤ t) :
    cognitiveCoordinate
        (centeredGainEntropyStep
          (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (t - (Tomabechi.Consistency.C3.valleySequence n).startTime) E
          ((Tomabechi.Consistency.C3.valleySequence n).initial, y)) =
      (Tomabechi.Theorem22.chooseStageValley
        (Tomabechi.Consistency.C3.valleySequence n)).orbit t := by
  rw [centeredGainEntropyStep_projects_quadraticFrozenOrbit]
  conv_rhs => rw [Tomabechi.Consistency.C3.valleySequence_shape n]
  exact Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit _ _ _ _ ht

/-- C3各段の完全状態拡張。物理観測座標yを保ち、累積観測増分Eには
`q(t)^2-q(start)^2` を入れるため、E−q²の変化が打ち消し合う。 -/
noncomputable def c3CoreStageTrajectory (n : ℕ) (y t : ℝ) : CompleteState :=
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let x₀ := (Tomabechi.Consistency.C3.valleySequence n).initial
  let t₀ := Tomabechi.Consistency.C3.stageTime n
  let q := Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit c x₀ t₀ t
  centeredGainEntropyStep c (t - t₀) (q ^ 2 - x₀ ^ 2) (x₀, y)

theorem c3CoreStageTrajectory_cognitive (n : ℕ) (y t : ℝ) :
    cognitiveCoordinate (c3CoreStageTrajectory n y t) =
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (Tomabechi.Consistency.C3.valleySequence n).initial
        (Tomabechi.Consistency.C3.stageTime n) t := by
  simp [c3CoreStageTrajectory, centeredGainEntropyStep,
    cognitiveCoordinate, Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]

theorem centeredGainEntropyStep_physical_preserved_by_quadraticIncrement
    (c A q₀ q y : ℝ)
    (hq : q = c + (q₀ - c) * Real.exp (-A)) :
    physicalCoordinate
        (centeredGainEntropyStep c A (q ^ 2 - q₀ ^ 2) (q₀, y)) = y := by
  rw [hq]
  simp [centeredGainEntropyStep, entropyObservedElapsed,
    cognitiveCoordinate, physicalCoordinate]

theorem c3CoreStageTrajectory_physical (n : ℕ) (y t : ℝ) :
    physicalCoordinate (c3CoreStageTrajectory n y t) = y := by
  simp only [c3CoreStageTrajectory]
  apply centeredGainEntropyStep_physical_preserved_by_quadraticIncrement
  simp [Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit,
    Tomabechi.Consistency.C3.stageTime]

/-- このC3拡張で観測される完全状態エントロピーは、段内では認知座標の二乗。 -/
theorem c3CoreStageTrajectory_entropyObserved (n : ℕ) (t : ℝ) :
    entropyObservedElapsed (c3CoreStageTrajectory n 0 t) =
      (cognitiveCoordinate (c3CoreStageTrajectory n 0 t)) ^ 2 := by
  unfold entropyObservedElapsed
  rw [c3CoreStageTrajectory_physical]
  simp [cognitiveCoordinate]

/-- 元C3各段は共有核の観測エントロピーを真に増加させる。増加は時刻カウンタではなく、
段の実軌道が初期点から中心へ動いた二乗差である。 -/
theorem c3CoreStage_entropy_increases (n : ℕ) :
    entropyObservedElapsed
        (c3CoreStageTrajectory n 0
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n)) >
      entropyObservedElapsed
        (c3CoreStageTrajectory n 0 (Tomabechi.Consistency.C3.stageTime n)) := by
  let a := (Tomabechi.Consistency.C3.valleySequence n).initial
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let e := Real.exp (-Tomabechi.Consistency.C3.stageDuration n)
  let q := cognitiveCoordinate
    (c3CoreStageTrajectory n 0
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n))
  have hinit : (Tomabechi.Consistency.C3.hStageSequence n).initial = a := by
    calc
      (Tomabechi.Consistency.C3.hStageSequence n).initial =
          ((Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec).initial := rfl
      _ = a := by
        dsimp [a]
        exact congrArg (fun s : Tomabechi.Theorem22.StageValleySpec ℝ => s.initial)
          (Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n)
  have hac : a < c := by
    rw [← hinit]
    simpa [c, Tomabechi.Consistency.C3.hStageSequence_center] using
      c6C3_stageInitial_strict_below_center n
  have hepos : 0 < e := Real.exp_pos _
  have helt : e < 1 := by
    dsimp [e]
    rw [Real.exp_lt_one_iff]
    linarith [Tomabechi.Consistency.C3.stageDuration_pos n]
  have ha0 : 0 ≤ a := by
    have h := Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n
    rw [← hinit]
    exact h.1
  have hqformula : q = c + (a - c) * e := by
    dsimp [q, a, c, e]
    rw [c3CoreStageTrajectory_cognitive,
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]
    have htime : Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n -
          Tomabechi.Consistency.C3.stageTime n =
        Tomabechi.Consistency.C3.stageDuration n := by ring
    rw [htime]
  have hqconv : q = (1 - e) * c + e * a := by
    rw [hqformula]
    ring
  have hqgt : a < q := by
    have hprod : 0 < (c - a) * (1 - e) :=
      mul_pos (by linarith) (by linarith)
    rw [hqconv]
    nlinarith
  have hq0 : 0 ≤ q := le_trans ha0 hqgt.le
  have hsum : 0 < q + a := by linarith
  have hsq : a ^ 2 < q ^ 2 := by
    have hp := mul_pos (show 0 < q - a by linarith) hsum
    nlinarith
  rw [c3CoreStageTrajectory_entropyObserved,
    c3CoreStageTrajectory_entropyObserved]
  simpa [q, c3CoreStageTrajectory_cognitive,
    Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit] using hsq

/-- 初期時刻では完全状態も正確に入力を再現する。 -/
theorem c3CoreStageTrajectory_initial (n : ℕ) (y : ℝ) :
    c3CoreStageTrajectory n y (Tomabechi.Consistency.C3.stageTime n) =
      ((Tomabechi.Consistency.C3.valleySequence n).initial, y) := by
  apply Prod.ext
  · simp [c3CoreStageTrajectory, centeredGainEntropyStep,
      cognitiveCoordinate, Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]
  · simp [c3CoreStageTrajectory, centeredGainEntropyStep,
      entropyObservedElapsed, cognitiveCoordinate, physicalCoordinate,
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit]

/-- 元のC3-H-stageを、共有状態核・同じ段時間・S7情報lawと同時に保持するadapter。
完全状態の第1座標が段階軌道、第2座標は核上に残る物理観測である。 -/
structure C6C3CoreStageAdapter (n : ℕ) where
  information : C6C3InformationAdapter n
  sourceStage : Tomabechi.Theorem22.StageValleySpec ℝ :=
    (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
  sourceStage_is_original :
    sourceStage = (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
  commonAddress : CommonLayer
  address_is_sourceLayer :
    commonAddress = entropyLayerAddress n
  startTime : ℝ
  startTime_is_stageStart :
    startTime = (Tomabechi.Consistency.C3.hStageSequence n).startTime
  duration : ℝ
  duration_positive : 0 < duration
  coreTrajectory : ℝ → CompleteState
  coreTrajectory_eq : ∀ t,
    coreTrajectory t = c3CoreStageTrajectory n 0 t
  physical_coordinate_preserved : ∀ t,
    physicalCoordinate (coreTrajectory t) = 0
  cognitive_projection_is_stage_orbit : ∀ t, startTime ≤ t →
    cognitiveCoordinate (coreTrajectory t) =
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
        Tomabechi.Consistency.C3.hStageSequence n).orbit t
  evaluation_is_original_stage_evaluation : ∀ t,
    Tomabechi.Theorem22.stageEffectivePotential sourceStage
        (cognitiveCoordinate (coreTrajectory t)) =
      centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (coreTrajectory t)
  observed_entropy_increases :
    entropyObservedElapsed (coreTrajectory (startTime + duration)) >
      entropyObservedElapsed (coreTrajectory startTime)
  endpoint_is_next_stage_initial :
    (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial =
      (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
        Tomabechi.Consistency.C3.hStageSequence n).orbit
          (startTime + duration)

/-- 全てのフィールドに元H-stage列と実情報adapterを代入した具体証人。 -/
noncomputable def c6C3CoreStageAdapter (n : ℕ) : C6C3CoreStageAdapter n :=
  { information := c6C3InformationAdapter n
    sourceStage := (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
    sourceStage_is_original := rfl
    commonAddress := entropyLayerAddress n
    address_is_sourceLayer := rfl
    startTime := Tomabechi.Consistency.C3.stageTime n
    startTime_is_stageStart := (Tomabechi.Consistency.C3.hStageSequence_start n).symm
    duration := Tomabechi.Consistency.C3.stageDuration n
    duration_positive := Tomabechi.Consistency.C3.stageDuration_pos n
    coreTrajectory := fun t => c3CoreStageTrajectory n 0 t
    coreTrajectory_eq := fun _ => rfl
    physical_coordinate_preserved := by
      intro t
      rw [c3CoreStageTrajectory_physical]
    cognitive_projection_is_stage_orbit := by
      intro t ht
      have hstart : (Tomabechi.Consistency.C3.valleySequence n).startTime =
          Tomabechi.Consistency.C3.stageTime n :=
        Tomabechi.Consistency.C3.hStageSequence_start n
      have ht' : (Tomabechi.Consistency.C3.valleySequence n).startTime ≤ t := by
        rw [hstart]
        exact ht
      have hshape : (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec =
          Tomabechi.Examples.Theorem23B.quadraticStage
            (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
            (Tomabechi.Consistency.C3.valleySequence n).initial
            (Tomabechi.Consistency.C3.valleySequence n).startTime := by
        rw [Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n,
          Tomabechi.Consistency.C3.valleySequence_shape n]
        simp [Tomabechi.Examples.Theorem23B.quadraticStage]
      have hchosen :
          (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
            Tomabechi.Consistency.C3.hStageSequence n).orbit t =
          (Tomabechi.Theorem22.chooseStageValley
            (Tomabechi.Examples.Theorem23B.quadraticStage
              (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
              (Tomabechi.Consistency.C3.valleySequence n).initial
              (Tomabechi.Consistency.C3.valleySequence n).startTime)).orbit t := by
        change (Tomabechi.Theorem22.chooseStageValley
          ((Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec)).orbit t = _
        rw [hshape]
      calc
        cognitiveCoordinate (c3CoreStageTrajectory n 0 t) =
            Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
              (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
              (Tomabechi.Consistency.C3.valleySequence n).initial
              (Tomabechi.Consistency.C3.stageTime n) t :=
          c3CoreStageTrajectory_cognitive n 0 t
        _ = (Tomabechi.Theorem22.chooseStageValley
              (Tomabechi.Examples.Theorem23B.quadraticStage
                (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
                (Tomabechi.Consistency.C3.valleySequence n).initial
                (Tomabechi.Consistency.C3.valleySequence n).startTime)).orbit t := by
          rw [hstart]
          exact Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit
            _ _ _ _ ht
        _ = (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys
              Tomabechi.Consistency.C3.hStageSequence n).orbit t := hchosen.symm
    evaluation_is_original_stage_evaluation := by
      intro t
      exact centeredQuadraticPotential_eq_C3_stage n
        (c3CoreStageTrajectory n 0 t)
    observed_entropy_increases := by
      exact c3CoreStage_entropy_increases n
    endpoint_is_next_stage_initial := by
      simpa [Tomabechi.Consistency.C3.hStageSequence_start,
        Tomabechi.Consistency.C3.stageTime_recurrence] using
        Tomabechi.Consistency.C3.hStageSequence_transition n
  }

theorem c6C3CoreStageAdapter_nonempty (n : ℕ) :
    Nonempty (C6C3CoreStageAdapter n) := ⟨c6C3CoreStageAdapter n⟩

/-- C3段の終端は、認知座標だけでなく物理座標を含む完全状態のまま次段初期点へ渡る。 -/
theorem c6C3CoreStageAdapter_endpoint_completeState (n : ℕ) :
    (c6C3CoreStageAdapter n).coreTrajectory
        ((c6C3CoreStageAdapter n).startTime +
          (c6C3CoreStageAdapter n).duration) =
      ((Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial, 0) := by
  let A := c6C3CoreStageAdapter n
  apply Prod.ext
  · have htime : A.startTime ≤ A.startTime + A.duration :=
      le_add_of_nonneg_right A.duration_positive.le
    have hq := A.cognitive_projection_is_stage_orbit
      (A.startTime + A.duration) htime
    change cognitiveCoordinate (A.coreTrajectory (A.startTime + A.duration)) = _
    rw [hq, A.endpoint_is_next_stage_initial]
  · have hy := A.physical_coordinate_preserved (A.startTime + A.duration)
    change physicalCoordinate (A.coreTrajectory (A.startTime + A.duration)) = _
    rw [hy]

/-- 隣り合うadapterの端点と次段初期値は、物理座標を含めて同じ完全状態である。 -/
theorem c6C3CoreStageAdapter_restart (n : ℕ) :
    (c6C3CoreStageAdapter n).coreTrajectory
        ((c6C3CoreStageAdapter n).startTime +
          (c6C3CoreStageAdapter n).duration) =
      c3CoreStageTrajectory (n + 1) 0
        (Tomabechi.Consistency.C3.stageTime (n + 1)) := by
  rw [c6C3CoreStageAdapter_endpoint_completeState]
  have hinitial :
      (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial =
        (Tomabechi.Consistency.C3.valleySequence (n + 1)).initial := by
    have h := congrArg (fun s : Tomabechi.Theorem22.StageValleySpec ℝ => s.initial)
      (Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec (n + 1))
    exact h
  rw [hinitial, c3CoreStageTrajectory_initial]

/-- C4の全履歴・全初期値の勾配流も、同じ核の中心パラメータから得る。 -/
theorem centeredGainEntropyStep_projects_C4_history_flow
    (h : Bool) (x y t E : ℝ) :
    cognitiveCoordinate
        (centeredGainEntropyStep
          (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) t E (x, y)) =
      Tomabechi.Theorem16_25.theorem16_intervalGradientFlow h x t := rfl

/-- C5の全有界可測ゲインのベクトル軌道を、零目標保存射影で回収する。
半径だけでなく位相も一致し、C5の元時刻T,tを維持する。 -/
theorem centeredGainEntropyStep_projects_all_C5_gains
    (z : CompleteState)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (T t : ℝ) :
    disagreementStateTo27
        (centeredGainEntropyStep 1
          ((1 / 2) * (t - T) +
            Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain k T t)
          (t - T) z) =
      Tomabechi.Examples.Theorem27.measurableGainVectorOrbit
        (disagreementStateTo27 z 0) (disagreementStateTo27 z 1) T t k := by
  ext i
  fin_cases i
  · change disagreementStateTo27 _ 0 = _
    rw [disagreementStateTo27_radial, centeredGainEntropyStep_cognitive]
    simp [Tomabechi.Examples.Theorem27.measurableGainVectorOrbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit,
      disagreementStateTo27_radial,
      Tomabechi.Examples.Theorem27Op.e0_apply0,
      Tomabechi.Examples.Theorem27Op.e1_apply0]
    ring
  · change disagreementStateTo27 _ 1 = _
    rw [disagreementStateTo27_phase, centeredGainEntropyStep_entropy]
    simp [Tomabechi.Examples.Theorem27.measurableGainVectorOrbit,
      disagreementStateTo27_phase,
      Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1]
    ring

/-- C5の実際の費用データが定めるtrajectoryへ、全方策・全初期値でつなぐ。
方策の許容性や最適性はC5の既存定理から別に取り出す。 -/
theorem centeredGainEntropyStep_projects_C5_data_trajectory
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    disagreementStateTo27
        (centeredGainEntropyStep 1
          ((1 / 2) * (t - T) +
            Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain
              (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) T t)
          (t - T) (vectorStateToCompleteState x)) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true π x T t := by
  rw [centeredGainEntropyStep_projects_all_C5_gains,
    disagreementStateTo27_right_inverse]
  rfl

/-- C5上位の各許容feedbackが選ぶ有界可測ゲインに対応する共有核trajectory。 -/
noncomputable def c5CoreTrajectory
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) : CompleteState :=
  centeredGainEntropyStep 1
    ((1 / 2) * (t - T) +
      Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain
        (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) T t)
    (t - T) (vectorStateToCompleteState x)

/-- C5の費用データが定める全feedbackの軌道は、同じ核trajectoryへの射影。 -/
theorem c5CoreTrajectory_projects_data_trajectory
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    disagreementStateTo27 (c5CoreTrajectory π x T t) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true π x T t := by
  exact centeredGainEntropyStep_projects_C5_data_trajectory π x T t

/-- C5の実走行費は、同じ実trajectoryを生成する共有核の二次評価の6倍。
許容feedbackの選択も積分区間 `[T,∞)` も変更しない。 -/
theorem c5CoreTrajectory_runningCost
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true π x T t) t =
      6 * centeredQuadraticPotential 1 (c5CoreTrajectory π x T t) := by
  rw [← c5CoreTrajectory_projects_data_trajectory]
  exact c5RunningCost_eq_six_centeredPotential (c5CoreTrajectory π x T t) π t

/-- C5費用の共有核側での割引積分表示。 -/
noncomputable def c5CoreDiscountedCost
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) : ℝ :=
  ∫ t, Tomabechi.Theorem24_26.theorem26DiscountWeight
      Tomabechi.Examples.Theorem27.vectorSourceData.rho T t *
        (6 * centeredQuadraticPotential 1 (c5CoreTrajectory π x T t))
    ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T

/-- 実際のC5割引走行費積分と共有核二次評価積分は等しい。
これはrunning costの単なる点wise比ではなく、費用汎関数そのもののpullbackである。 -/
theorem c5CoreDiscountedCost_eq_dataCost
    (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) :
    c5CoreDiscountedCost π x T =
      ∫ t, Tomabechi.Theorem24_26.theorem26DiscountWeight
          Tomabechi.Examples.Theorem27.vectorSourceData.rho T t *
            Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
              (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true π x T t) t
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
  unfold c5CoreDiscountedCost
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [c5CoreTrajectory_runningCost]

/-- C5の最適方策は、共有核で積分した同じ割引費用も最小化し、最適値を達成する。 -/
theorem c5CoreDiscountedCost_optimal_attained
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) :
    c5CoreDiscountedCost
        (Tomabechi.Examples.Theorem27.vectorSourceData.optimalPolicy true x T) x T =
      Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true x T := by
  rw [c5CoreDiscountedCost_eq_dataCost,
    Tomabechi.Examples.Theorem27.vectorSourceData.optimal_value_attained true x T hT]

/-- 全ての許容feedbackに対するC5最適性も、同じ共有核の費用積分へ移る。 -/
theorem c5CoreDiscountedCost_optimal_minimal
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (π :
      Tomabechi.Examples.Theorem27.VectorSourcePolicy true)
    (hT : 0 ≤ T)
    (hπ : Tomabechi.Examples.Theorem27.vectorSourceData.admissible true π x T) :
    ENNReal.ofReal (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true x T) ≤
      ∫⁻ t, ENNReal.ofReal (Tomabechi.Theorem24_26.theorem26DiscountWeight
        Tomabechi.Examples.Theorem27.vectorSourceData.rho T t *
          (6 * centeredQuadraticPotential 1 (c5CoreTrajectory π x T t)))
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Tomabechi.Theorem24_26.theorem26DiscountWeight
          Tomabechi.Examples.Theorem27.vectorSourceData.rho T t *
          Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
            (Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true π x T t) t)
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T :=
      Tomabechi.Examples.Theorem27.vectorSourceData.optimal_value_minimal
        true x T π hT hπ
    _ = _ := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards with t
      rw [c5CoreTrajectory_runningCost]

/-- 到達時刻列の有限シフトも発散する。固定版MathlibのAPI名は
`tendsto_add_atTop_nat` であり、実数castへ変えてから合成する必要はない。 -/
theorem c6C1C3CenterSamplingAdapter_tendsto_atTop :
    Tendsto c6C1C3CenterSamplingAdapter.sampleTime atTop atTop :=
  c1TimeAtC3StageCenter_tendsto_atTop.comp (tendsto_add_atTop_nat 2)

/-- C2のA7率3に合わせるC3段の完全初期状態。
物理座標は時間を別に数える時計ではなく、全エントロピー値 `3·stageTime` と認知二乗から定める。 -/
noncomputable def c3A7StageInitial (n : ℕ) : CompleteState :=
  ((Tomabechi.Consistency.C3.valleySequence n).initial,
    3 * Tomabechi.Consistency.C3.stageTime n -
      ((Tomabechi.Consistency.C3.valleySequence n).initial) ^ 2)

/-- 元C3認知軌道を保ちながら、完全状態の全エントロピーをC2 A7と同じ率3で増やす。 -/
noncomputable def c3A7StageTrajectory (n : ℕ) (t : ℝ) : CompleteState :=
  centeredGainEntropyStep
    (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
    (t - Tomabechi.Consistency.C3.stageTime n)
    (3 * (t - Tomabechi.Consistency.C3.stageTime n))
    (c3A7StageInitial n)

theorem entropyObservedElapsed_measurable : Measurable entropyObservedElapsed := by
  unfold entropyObservedElapsed cognitiveCoordinate physicalCoordinate
  fun_prop

theorem cognitiveCoordinate_measurable : Measurable cognitiveCoordinate := by
  change Measurable (fun z : CompleteState => z.1)
  exact measurable_fst

theorem c3A7StageTrajectory_entropyObserved (n : ℕ) (t : ℝ) :
    entropyObservedElapsed (c3A7StageTrajectory n t) = 3 * t := by
  rw [c3A7StageTrajectory, centeredGainEntropyStep_entropy]
  simp [c3A7StageInitial, entropyObservedElapsed, physicalCoordinate,
    cognitiveCoordinate]
  ring

/-- C3元stageの物理座標と全正層の重み付き生成率は、原文A7の収支式を満たす。
生産率3をstageの物理成分と層成分へ実際に分配している。 -/
theorem c3A7StageTrajectory_satisfies_A7 (n : ℕ) (t : ℝ) :
    deriv (fun s => physicalEntropy (c3A7StageTrajectory n s)) t =
      -(∑' k : PositiveLayer, layerWeight k *
        deriv (fun s => layerEntropy k (c3A7StageTrajectory n s)) t) + 3 := by
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let z := c3A7StageInitial n
  let A : ℝ → ℝ := fun s => s - Tomabechi.Consistency.C3.stageTime n
  let E : ℝ → ℝ := fun s => 3 * (s - Tomabechi.Consistency.C3.stageTime n)
  have hA : HasDerivAt A 1 t := by
    dsimp [A]
    simpa using (hasDerivAt_id t).sub_const
      (Tomabechi.Consistency.C3.stageTime n)
  have hE : HasDerivAt E 3 t := by
    dsimp [E]
    simpa using ((hasDerivAt_id t).sub_const
      (Tomabechi.Consistency.C3.stageTime n)).const_mul 3
  have hq := centeredGainEntropyStep_cognitive_hasDerivAt c z A E t 1 hA
  have hphys := centeredGainEntropyStep_physical_hasDerivAt c z A E t 1 3 hA hE
  have hlayer (k : PositiveLayer) :
      deriv (fun s => layerEntropy k (c3A7StageTrajectory n s)) t =
        2 * cognitiveCoordinate (c3A7StageTrajectory n t) *
          (c - cognitiveCoordinate (c3A7StageTrajectory n t)) := by
    have h := (hasDerivAt_const t (1 : ℝ)).add (hq.pow 2)
    have hfun : (fun s => layerEntropy k (c3A7StageTrajectory n s)) =
        (fun s => 1 + cognitiveCoordinate (c3A7StageTrajectory n s) ^ 2) := by
      funext s
      simp [layerEntropy]
    rw [hfun]
    have h' : HasDerivAt (fun s => 1 + cognitiveCoordinate (c3A7StageTrajectory n s) ^ 2)
        (2 * cognitiveCoordinate (c3A7StageTrajectory n t) *
          (c - cognitiveCoordinate (c3A7StageTrajectory n t))) t := by
      convert h using 1
      · ext s
        simp [c3A7StageTrajectory, A, E, z, c, cognitiveCoordinate]
      · norm_num
        simp [c3A7StageTrajectory, A, E, z, c, cognitiveCoordinate]
    exact h'.deriv
  have hsum : (∑' k : PositiveLayer, layerWeight k *
      deriv (fun s => layerEntropy k (c3A7StageTrajectory n s)) t) =
      2 * cognitiveCoordinate (c3A7StageTrajectory n t) *
        (c - cognitiveCoordinate (c3A7StageTrajectory n t)) := by
    have hrewrite : (fun k : PositiveLayer => layerWeight k *
        deriv (fun s => layerEntropy k (c3A7StageTrajectory n s)) t) =
        fun k => (2 * cognitiveCoordinate (c3A7StageTrajectory n t) *
          (c - cognitiveCoordinate (c3A7StageTrajectory n t))) * layerWeight k := by
      funext k
      rw [hlayer]
      ring
    rw [hrewrite, tsum_mul_left, layerWeight_tsum]
    ring
  change deriv (fun s => physicalCoordinate
      (centeredGainEntropyStep c (A s) (E s) z)) t = _
  rw [hphys.deriv]
  rw [hsum]
  simp [c3A7StageTrajectory, A, E, z, c, cognitiveCoordinate, one_mul]
  ring

theorem c3A7StageTrajectory_cognitive (n : ℕ) (t : ℝ) :
    cognitiveCoordinate (c3A7StageTrajectory n t) =
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (Tomabechi.Consistency.C3.valleySequence n).initial
        (Tomabechi.Consistency.C3.stageTime n) t := rfl

theorem c3A7StageTrajectory_cognitive_formula (n : ℕ) (t : ℝ) :
    cognitiveCoordinate (c3A7StageTrajectory n t) =
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) +
        ((Tomabechi.Consistency.C3.valleySequence n).initial -
          Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) *
          Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) := by
  rw [c3A7StageTrajectory_cognitive]
  rfl

theorem c3A7StageTrajectory_cognitive_le_center
    (n : ℕ) (t : ℝ) (ht : Tomabechi.Consistency.C3.stageTime n ≤ t) :
    cognitiveCoordinate (c3A7StageTrajectory n t) ≤
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) := by
  rw [c3A7StageTrajectory_cognitive_formula]
  have hinit : (Tomabechi.Consistency.C3.valleySequence n).initial ≤
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) :=
    (Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n).2
  have he := Real.exp_nonneg (-(t - Tomabechi.Consistency.C3.stageTime n))
  nlinarith

/-- 元C3のstage時刻列はduration正値により狭義増加する。 -/
theorem c3StageTime_strictMono :
    StrictMono Tomabechi.Consistency.C3.stageTime := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Tomabechi.Consistency.C3.stageTime_recurrence]
  exact lt_add_of_pos_right _ (Tomabechi.Consistency.C3.stageDuration_pos n)

/-- 元C3のstage時刻は非有界で、全有限時刻のstage番号選択を可能にする。 -/
theorem c3StageTime_tendsto_atTop (B : ℝ) :
    ∃ n, B < Tomabechi.Consistency.C3.stageTime n := by
  obtain ⟨n, hn⟩ := Tomabechi.Consistency.C3.stageTime_unbounded B
  exact ⟨n, by simpa [Tomabechi.Consistency.C3.stageTime] using hn⟩

/-- 任意の実時刻を、C3の最初のまだ先にあるstage endpointで分類する。 -/
noncomputable def c3StageActiveIndex : ℝ → ℕ :=
  Tomabechi.Theorem23.canonicalSwitchStageIndex
    Tomabechi.Consistency.C3.stageTime c3StageTime_strictMono c3StageTime_tendsto_atTop

theorem c3StageActiveIndex_endpoint_bound (t : ℝ) :
    t < Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t + 1) := by
  exact Nat.find_spec
    (Tomabechi.Theorem23.exists_stage_endpoint_after_time
      Tomabechi.Consistency.C3.stageTime c3StageTime_strictMono
      c3StageTime_tendsto_atTop t)

theorem c3StageActiveIndex_eq_zero_iff (t : ℝ) :
    c3StageActiveIndex t = 0 ↔
      t < Tomabechi.Consistency.C3.stageTime 1 := by
  constructor
  · intro h
    have hbound := c3StageActiveIndex_endpoint_bound t
    simpa [h] using hbound
  · intro ht
    have hle : c3StageActiveIndex t ≤ 0 := by
      unfold c3StageActiveIndex Tomabechi.Theorem23.canonicalSwitchStageIndex
      apply Nat.find_min'
      exact ht
    omega

theorem c3StageActiveIndex_eq_on_dwell
    (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)) :
    c3StageActiveIndex t = n := by
  exact Tomabechi.Theorem23.canonicalSwitchStageIndex_eq_on_dwell
    Tomabechi.Consistency.C3.stageTime Tomabechi.Consistency.C3.stageDuration
    c3StageTime_strictMono c3StageTime_tendsto_atTop
    (fun k => Tomabechi.Consistency.C3.stageTime_recurrence k) n ht

theorem c3StageActiveIndex_dwell_iff
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    c3StageActiveIndex t = n ↔
      t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
        (Tomabechi.Consistency.C3.stageTime (n + 1)) := by
  constructor
  · intro hindex
    have hupper := c3StageActiveIndex_endpoint_bound t
    have hlower : Tomabechi.Consistency.C3.stageTime n ≤ t := by
      by_contra hnot
      have hlt : t < Tomabechi.Consistency.C3.stageTime n := lt_of_not_ge hnot
      have hsmall : t < Tomabechi.Consistency.C3.stageTime ((n - 1) + 1) := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))] using hlt
      have hmin : c3StageActiveIndex t ≤ n - 1 := by
        unfold c3StageActiveIndex Tomabechi.Theorem23.canonicalSwitchStageIndex
        apply Nat.find_min'
        exact hsmall
      omega
    have hupper' : t < Tomabechi.Consistency.C3.stageTime (n + 1) := by
      simpa [hindex] using hupper
    exact ⟨hlower, hupper'⟩
  · intro ht
    exact c3StageActiveIndex_eq_on_dwell n (by
      simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using ht)

theorem measurable_c3StageActiveIndex : Measurable c3StageActiveIndex := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n = 0
  · subst n
    have heq : c3StageActiveIndex ⁻¹' ({0} : Set ℕ) =
        Set.Iio (Tomabechi.Consistency.C3.stageTime 1) := by
      ext t
      simp [c3StageActiveIndex_eq_zero_iff]
    rw [heq]
    exact measurableSet_Iio
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have heq : c3StageActiveIndex ⁻¹' ({n} : Set ℕ) =
        Set.Ico (Tomabechi.Consistency.C3.stageTime n)
          (Tomabechi.Consistency.C3.stageTime (n + 1)) := by
      ext t
      simp [c3StageActiveIndex_dwell_iff n hpos t]
    rw [heq]
    exact measurableSet_Ico

theorem c3StageTime_nonneg (n : ℕ) :
    0 ≤ Tomabechi.Consistency.C3.stageTime n := by
  induction n with
  | zero => simp [Tomabechi.Consistency.C3.stageTime]
  | succ n ih =>
      rw [Tomabechi.Consistency.C3.stageTime_recurrence]
      exact add_nonneg ih (Tomabechi.Consistency.C3.stageDuration_pos n).le

/-- 各非負時刻はちょうど選択されたstageのhalf-open dwellに入る。 -/
theorem c3StageActiveIndex_mem_dwell (t : ℝ) (ht : 0 ≤ t) :
    t ∈ Set.Ico
      (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t))
      (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t + 1)) := by
  by_cases hn : c3StageActiveIndex t = 0
  · have hupper := c3StageActiveIndex_endpoint_bound t
    rw [hn] at hupper
    have hzero : Tomabechi.Consistency.C3.stageTime 0 = 0 := by
      simp [Tomabechi.Consistency.C3.stageTime]
    have hone : Tomabechi.Consistency.C3.stageTime 1 =
        Tomabechi.Consistency.C3.stageDuration 0 := by
      rw [Tomabechi.Consistency.C3.stageTime_recurrence, hzero]
      ring
    rw [hn, hzero, hone]
    exact ⟨ht, by simpa [hone] using hupper⟩
  · have hnpos : 0 < c3StageActiveIndex t := Nat.pos_of_ne_zero hn
    exact (c3StageActiveIndex_dwell_iff (c3StageActiveIndex t) hnpos t).mp rfl

/-- C3の一段をC1の中心1・状態依存ゲインで表す候補入力。
stage内では `u=(c-q)/(1-q)` とし、C3認知速度 `q'=c-q` を
C1形式 `q'=u(1-q)` に変換する。段開始前の延長は許容性のため0とする。 -/
noncomputable def c3A7StageC1Gain
    (n : ℕ) : Tomabechi.Consistency.ConsistencyC1.C1GainSignal := by
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let q := fun t : ℝ => cognitiveCoordinate (c3A7StageTrajectory n t)
  refine ⟨fun t => if Tomabechi.Consistency.C3.stageTime n ≤ t then
    (c - q t) / (1 - q t) else 0, ?_, ?_⟩
  · dsimp [q]
    have hq : Measurable (fun t : ℝ =>
        cognitiveCoordinate (c3A7StageTrajectory n t)) := by
      dsimp [c3A7StageTrajectory, centeredGainEntropyStep,
        c3A7StageInitial, cognitiveCoordinate]
      fun_prop
    exact Measurable.ite measurableSet_Ici
      ((measurable_const.sub hq).div (measurable_const.sub hq)) measurable_const
  · intro t
    by_cases ht : Tomabechi.Consistency.C3.stageTime n ≤ t
    · have hq : q t = c +
        ((Tomabechi.Consistency.C3.valleySequence n).initial - c) *
          Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) := by
        dsimp [q]
        rw [c3A7StageTrajectory_cognitive]
        rfl
      have hinit : (Tomabechi.Consistency.C3.valleySequence n).initial ≤ c := by
        exact (Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n).2
      have hc : c < 1 := Tomabechi.Consistency.C3.representation_lt_top (n + 1)
      have hqle : q t ≤ c := by
        exact c3A7StageTrajectory_cognitive_le_center n t ht
      have hden : 0 < 1 - q t := by linarith
      have hbounds : 0 ≤ (c - q t) / (1 - q t) ∧
          (c - q t) / (1 - q t) ≤ 3 := by
        constructor
        · exact div_nonneg (by linarith) hden.le
        · have hle : (c - q t) / (1 - q t) ≤ 1 :=
            (div_le_one hden).2 (by linarith)
          linarith
      simpa only [if_pos ht] using hbounds
    · simp [ht]

/-- C3 stage内の認知軌道は、上で作った許容C1ゲイン信号のCarathéodory方程式を満たす。 -/
theorem c3A7StageC1Gain_ode
    (n : ℕ) (t : ℝ) (ht : Tomabechi.Consistency.C3.stageTime n ≤ t) :
    HasDerivAt (fun s => cognitiveCoordinate (c3A7StageTrajectory n s))
      (-((c3A7StageC1Gain n).1 t) *
        (cognitiveCoordinate (c3A7StageTrajectory n t) - 1)) t := by
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  have hbase := Tomabechi.Examples.Theorem23B.hasDerivAt_quadraticFrozenOrbit
    c (Tomabechi.Consistency.C3.valleySequence n).initial
    (Tomabechi.Consistency.C3.stageTime n) t
  have hq : HasDerivAt
      (fun s => cognitiveCoordinate (c3A7StageTrajectory n s))
      (c - cognitiveCoordinate (c3A7StageTrajectory n t)) t := by
    simpa [c3A7StageTrajectory_cognitive, c, sub_eq_add_neg] using hbase
  have hqle := c3A7StageTrajectory_cognitive_le_center n t ht
  have hc : c < 1 := Tomabechi.Consistency.C3.representation_lt_top (n + 1)
  have hden : 0 < 1 - cognitiveCoordinate (c3A7StageTrajectory n t) := by
    linarith
  have hgain : (c3A7StageC1Gain n).1 t =
      (c - cognitiveCoordinate (c3A7StageTrajectory n t)) /
        (1 - cognitiveCoordinate (c3A7StageTrajectory n t)) := by
    simp [c3A7StageC1Gain, ht, c]
  convert hq using 1 <;> rw [hgain] <;> field_simp <;> ring

/-- 上の対応入力で、C1の実際の積分軌道は各有限stage区間上のC3認知軌道を再現する。
この入力は許容族の一員であり、C1最大ゲインの選択軌道と同一だとは主張しない。 -/
theorem c3A7StageC1Gain_matches_C1_trajectory
    (n : ℕ) (t : ℝ) (ht : Tomabechi.Consistency.C3.stageTime n ≤ t) :
    Tomabechi.Consistency.ConsistencyC1.c1ControlledState 1
        (cognitiveCoordinate (c3A7StageInitial n))
        (Tomabechi.Consistency.C3.stageTime n) (c3A7StageC1Gain n) t =
      cognitiveCoordinate (c3A7StageTrajectory n t) := by
  let s₀ := Tomabechi.Consistency.C3.stageTime n
  let q := fun s : ℝ => cognitiveCoordinate (c3A7StageTrajectory n s)
  have hqcont : Continuous q := by
    dsimp [q]
    rw [show (fun s : ℝ => cognitiveCoordinate (c3A7StageTrajectory n s)) =
      Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
        (Tomabechi.Consistency.C3.valleySequence n).initial
        (Tomabechi.Consistency.C3.stageTime n) by
          funext s
          exact c3A7StageTrajectory_cognitive n s]
    exact Tomabechi.Examples.Theorem23B.continuous_quadraticFrozenOrbit
      _ _ _
  have hderiv : ∀ s, HasDerivAt q
      (Tomabechi.Consistency.C3.representation (n + 1 : ℕ) - q s) s := by
    intro s
    have h := Tomabechi.Examples.Theorem23B.hasDerivAt_quadraticFrozenOrbit
      (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
      (Tomabechi.Consistency.C3.valleySequence n).initial
      (Tomabechi.Consistency.C3.stageTime n) s
    simpa [q, c3A7StageTrajectory_cognitive, sub_eq_add_neg] using h
  have hAC := Tomabechi.Consistency.C2.absolutelyContinuous_of_hasDerivAt
    (f := q)
    (f' := fun s => Tomabechi.Consistency.C3.representation (n + 1 : ℕ) - q s)
    hderiv (continuous_const.sub hqcont) s₀ t
  have hinitial : q s₀ = cognitiveCoordinate (c3A7StageInitial n) := by
    dsimp [q, s₀]
    simp [c3A7StageTrajectory, centeredGainEntropyStep_initial]
  have hode : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Icc s₀ t),
      HasDerivAt q (-((c3A7StageC1Gain n).1 s) * (q s - 1)) s := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards with s
    intro hs
    have hs' : Tomabechi.Consistency.C3.stageTime n ≤ s := by
      exact hs.1
    have h := c3A7StageC1Gain_ode n s hs'
    simpa [q, s₀] using h
  have hle : s₀ ≤ t := ht
  exact (Tomabechi.Consistency.ConsistencyC1.c1ControlledState_unique_on_interval
    1 (cognitiveCoordinate (c3A7StageInitial n)) s₀ t (c3A7StageC1Gain n) q
    hle hAC hinitial hode).symm

theorem c3A7StageTrajectory_initial (n : ℕ) :
    c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n) =
      c3A7StageInitial n := by
  simp [c3A7StageTrajectory, centeredGainEntropyStep_initial]

theorem c3A7StageTrajectory_endpoint (n : ℕ) :
    c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n +
      Tomabechi.Consistency.C3.stageDuration n) = c3A7StageInitial (n + 1) := by
  have htime := Tomabechi.Consistency.C3.stageTime_recurrence n
  have hstage := congrArg Prod.fst (c6C3CoreStageAdapter_endpoint_completeState n)
  have hqold : cognitiveCoordinate (c3CoreStageTrajectory n 0
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)) =
      (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial := by
    change (c3CoreStageTrajectory n 0
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)).1 = _
    exact hstage
  have hvalley : (Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial =
      (Tomabechi.Consistency.C3.valleySequence (n + 1)).initial := by
    have h := congrArg (fun s : Tomabechi.Theorem22.StageValleySpec ℝ => s.initial)
      (Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec (n + 1))
    exact h
  have hq : cognitiveCoordinate (c3A7StageTrajectory n
      (Tomabechi.Consistency.C3.stageTime n +
        Tomabechi.Consistency.C3.stageDuration n)) =
      (Tomabechi.Consistency.C3.valleySequence (n + 1)).initial := by
    rw [c3A7StageTrajectory_cognitive, ← c3CoreStageTrajectory_cognitive]
    exact hqold.trans hvalley
  apply Prod.ext
  · change cognitiveCoordinate (c3A7StageTrajectory n
      (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n)) = _
    exact hq
  ·
    have hobs := c3A7StageTrajectory_entropyObserved n
      (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n)
    change physicalCoordinate (c3A7StageTrajectory n
        (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n)) +
        cognitiveCoordinate (c3A7StageTrajectory n
          (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n)) ^ 2 =
      3 * (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n) at hobs
    rw [hq] at hobs
    rw [← hvalley] at hobs
    change physicalCoordinate (c3A7StageTrajectory n
        (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n)) =
      3 * Tomabechi.Consistency.C3.stageTime (n + 1) -
        ((Tomabechi.Consistency.C3.hStageSequence (n + 1)).initial) ^ 2
    linarith [htime]

/-- 元C3のA7段をactive-stage indexで接続した全時刻完全状態path。 -/
noncomputable def c3A7StitchedTrajectory (t : ℝ) : CompleteState :=
  c3A7StageTrajectory (c3StageActiveIndex t) t

theorem c3A7StitchedTrajectory_eq_active_stage (t : ℝ) :
    c3A7StitchedTrajectory t =
      c3A7StageTrajectory (c3StageActiveIndex t) t := rfl

theorem c3A7StitchedTrajectory_eq_stage
    (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime (n + 1))) :
    c3A7StitchedTrajectory t = c3A7StageTrajectory n t := by
  have hindex := c3StageActiveIndex_eq_on_dwell n (by
    simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using ht)
  simp [c3A7StitchedTrajectory, hindex]

/-- 切替時刻では新しい段を選び、全状態がその段の初期値に一致する。 -/
theorem c3A7StitchedTrajectory_at_stageTime (n : ℕ) :
    c3A7StitchedTrajectory (Tomabechi.Consistency.C3.stageTime n) =
      c3A7StageInitial n := by
  have hindex : c3StageActiveIndex (Tomabechi.Consistency.C3.stageTime n) = n := by
    cases n with
    | zero =>
        apply (c3StageActiveIndex_eq_zero_iff _).2
        rw [Tomabechi.Consistency.C3.stageTime_recurrence]
        simp [Tomabechi.Consistency.C3.stageTime]
        exact Tomabechi.Consistency.C3.stageDuration_pos 0
    | succ n =>
        exact c3StageActiveIndex_eq_on_dwell (n + 1) (by
          rw [Tomabechi.Consistency.C3.stageTime_recurrence]
          simp only [Set.mem_Ico, le_rfl, true_and]
          exact lt_add_of_pos_right _ (Tomabechi.Consistency.C3.stageDuration_pos (n + 1)))
  rw [c3A7StitchedTrajectory, hindex, c3A7StageTrajectory_initial]

/-- stitched path は各stage endpointで次段の完全初期状態へ正確につながる。 -/
theorem c3A7StitchedTrajectory_at_stageEndpoint (n : ℕ) :
    c3A7StitchedTrajectory
        (Tomabechi.Consistency.C3.stageTime n + Tomabechi.Consistency.C3.stageDuration n) =
      c3A7StageInitial (n + 1) := by
  rw [← Tomabechi.Consistency.C3.stageTime_recurrence,
    c3A7StitchedTrajectory_at_stageTime]

/-- stitched完全状態の物理観測と二乗認知観測は、全実時刻で総和 `3t` を保つ。 -/
theorem c3A7StitchedTrajectory_entropyObserved (t : ℝ) :
    entropyObservedElapsed (c3A7StitchedTrajectory t) = 3 * t := by
  simp [c3A7StitchedTrajectory, c3A7StageTrajectory_entropyObserved]

/-- C3/A7の大域完全pathを27の状態へ写すと、C4 true履歴に結び付いたC5上層の
最大方策flowを時間 `3t` で正確に再現する。比較は同じ総エントロピー観測から従う。 -/
theorem c3A7StitchedTrajectory_matches_C5_upper_optimalFlow
    (t : ℝ) (ht : 0 ≤ t) :
    entropyStateTo27 (c3A7StitchedTrajectory t) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 (3 * t) := by
  have hstate : entropyStateTo27 (c3A7StitchedTrajectory t) =
      entropyStateTo27 (trajectory (3 * t)) := by
    unfold entropyStateTo27
    rw [c3A7StitchedTrajectory_entropyObserved,
      entropyObservedElapsed_on_trajectory]
  rw [hstate]
  exact entropyTrajectory_matches_theorem27_data (3 * t) (by linarith)

/-- 共通pathから射影されたC5上層flowは、非負時間で実際に非定常である。 -/
theorem c3A7StitchedTrajectory_C5_flow_nonconstant :
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 0 ≠
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
        Tomabechi.Examples.Theorem27.vectorMaximalPolicy
        Tomabechi.Examples.Theorem27Op.e0 0 3 := by
  intro hflow
  have hmap : entropyStateTo27 (c3A7StitchedTrajectory 0) =
      entropyStateTo27 (c3A7StitchedTrajectory 1) := by
    calc
      _ = Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          Tomabechi.Examples.Theorem27Op.e0 0 0 :=
        by simpa using
          c3A7StitchedTrajectory_matches_C5_upper_optimalFlow 0 (by norm_num)
      _ = Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
          Tomabechi.Examples.Theorem27.vectorMaximalPolicy
          Tomabechi.Examples.Theorem27Op.e0 0 3 := hflow
      _ = _ := by
        simpa using (c3A7StitchedTrajectory_matches_C5_upper_optimalFlow
          1 (by norm_num)).symm
  have htime := entropyStateTo27_injective_observedElapsed hmap
  rw [c3A7StitchedTrajectory_entropyObserved,
    c3A7StitchedTrajectory_entropyObserved] at htime
  norm_num at htime

/-- C2の重み付き無限層和で定義する一般化エントロピーも、全時間で `1+3t` となる。 -/
theorem c3A7StitchedTrajectory_generalizedEntropy (t : ℝ) :
    generalizedEntropy (c3A7StitchedTrajectory t) = 1 + 3 * t := by
  rw [generalizedEntropy_eq_observedElapsed,
    c3A7StitchedTrajectory_entropyObserved]

/-- 完全状態から読むC2一般化エントロピーは、時刻とともに厳密に増加する。 -/
theorem c3A7StitchedTrajectory_generalizedEntropy_strictMono :
    StrictMono (fun t => generalizedEntropy (c3A7StitchedTrajectory t)) := by
  intro s t hst
  change generalizedEntropy (c3A7StitchedTrajectory s) <
    generalizedEntropy (c3A7StitchedTrajectory t)
  rw [c3A7StitchedTrajectory_generalizedEntropy,
    c3A7StitchedTrajectory_generalizedEntropy]
  linarith

/-- stitched完全状態に独立時計を追加しなくても、二時刻の状態再訪は起こらない。 -/
theorem c3A7StitchedTrajectory_injective :
    Function.Injective c3A7StitchedTrajectory := by
  intro s t hstate
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hentropy := c3A7StitchedTrajectory_generalizedEntropy_strictMono hst
    change generalizedEntropy (c3A7StitchedTrajectory s) <
      generalizedEntropy (c3A7StitchedTrajectory t) at hentropy
    rw [hstate] at hentropy
    exact (lt_irrefl _) hentropy
  · have hentropy := c3A7StitchedTrajectory_generalizedEntropy_strictMono hts
    change generalizedEntropy (c3A7StitchedTrajectory t) <
      generalizedEntropy (c3A7StitchedTrajectory s) at hentropy
    rw [hstate] at hentropy
    exact (lt_irrefl _) hentropy

theorem measurable_c3A7StitchedTrajectory :
    Measurable c3A7StitchedTrajectory := by
  let center : ℕ → ℝ := fun n =>
    Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let initial : ℕ → ℝ := fun n =>
    (Tomabechi.Consistency.C3.valleySequence n).initial
  let start : ℕ → ℝ := Tomabechi.Consistency.C3.stageTime
  have hc : Measurable center := measurable_of_countable center
  have hi : Measurable initial := measurable_of_countable initial
  have hs : Measurable start := measurable_of_countable start
  have hq : Measurable (fun t : ℝ =>
      cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t)) := by
    have hjoint : Measurable (fun p : ℕ × ℝ =>
        center p.1 + (initial p.1 - center p.1) *
          Real.exp (-(p.2 - start p.1))) := by
      have hcenter : Measurable (fun p : ℕ × ℝ => center p.1) := hc.comp measurable_fst
      have hinitial : Measurable (fun p : ℕ × ℝ => initial p.1) := hi.comp measurable_fst
      have hstart : Measurable (fun p : ℕ × ℝ => start p.1) := hs.comp measurable_fst
      have htime : Measurable (fun p : ℕ × ℝ => p.2) := measurable_snd
      fun_prop
    have hpair : Measurable (fun t : ℝ => (c3StageActiveIndex t, t)) :=
      measurable_c3StageActiveIndex.prodMk measurable_id
    have hformula : (fun t : ℝ =>
        cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t)) =
      (fun t => center (c3StageActiveIndex t) +
        (initial (c3StageActiveIndex t) - center (c3StageActiveIndex t)) *
          Real.exp (-(t - start (c3StageActiveIndex t)))) := by
      funext t
      rw [c3A7StageTrajectory_cognitive_formula]
    rw [hformula]
    exact hjoint.comp hpair
  have hstate : c3A7StitchedTrajectory = fun t =>
      (cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t),
        3 * t -
          (cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t)) ^ 2) := by
    funext t
    apply Prod.ext
    · rfl
    · have hobs := c3A7StageTrajectory_entropyObserved (c3StageActiveIndex t) t
      change physicalCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) +
          cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) ^ 2 = 3 * t at hobs
      change physicalCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) = _
      linarith
  rw [hstate]
  have hlinear : Measurable (fun t : ℝ => (3 : ℝ) * t) :=
    measurable_const.mul measurable_id
  have hsquare : Measurable (fun t : ℝ =>
      cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) ^ 2) := by
    have heq : (fun t : ℝ =>
        cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) ^ 2) =
      (fun t : ℝ =>
        cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t) *
          cognitiveCoordinate (c3A7StageTrajectory (c3StageActiveIndex t) t)) := by
      funext t
      ring
    rw [heq]
    exact hq.mul hq
  exact hq.prodMk (hlinear.sub hsquare)

/-- 全C3 stage列を一つのC1許容ゲインへ貼り合わせる。
非負時間ではactive stageの中心に対する状態依存ゲインを使い、負時間では0とする。 -/
noncomputable def c3A7StitchedC1Gain :
    Tomabechi.Consistency.ConsistencyC1.C1GainSignal := by
  let center := fun t : ℝ =>
    Tomabechi.Consistency.C3.representation (c3StageActiveIndex t + 1 : ℕ)
  let q := fun t : ℝ => cognitiveCoordinate (c3A7StitchedTrajectory t)
  refine ⟨fun t => if 0 ≤ t then (center t - q t) / (1 - q t) else 0,
    ?_, ?_⟩
  · have hc : Measurable center := by
      have hrep : Measurable (fun n : ℕ =>
          Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) :=
        measurable_of_countable _
      exact hrep.comp measurable_c3StageActiveIndex
    have hq : Measurable q := by
      dsimp [q]
      exact cognitiveCoordinate_measurable.comp measurable_c3A7StitchedTrajectory
    exact Measurable.ite measurableSet_Ici
      ((hc.sub hq).div (measurable_const.sub hq)) measurable_const
  · intro t
    by_cases ht : 0 ≤ t
    · have hactive := c3StageActiveIndex_mem_dwell t ht
      have hqle : q t ≤ center t := by
        dsimp [q, center]
        exact c3A7StageTrajectory_cognitive_le_center
          (c3StageActiveIndex t) t hactive.1
      have hc : center t < 1 :=
        Tomabechi.Consistency.C3.representation_lt_top (c3StageActiveIndex t + 1)
      have hden : 0 < 1 - q t := by linarith
      have hbounds : 0 ≤ (center t - q t) / (1 - q t) ∧
          (center t - q t) / (1 - q t) ≤ 3 := by
        constructor
        · exact div_nonneg (by linarith) hden.le
        · have hle : (center t - q t) / (1 - q t) ≤ 1 :=
            (div_le_one hden).2 (by linarith)
          linarith
      simpa only [if_pos ht] using hbounds
    · simp [ht]

theorem c3A7StitchedC1Gain_eq_stage
    (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime (n + 1))) :
    (c3A7StitchedC1Gain).1 t = (c3A7StageC1Gain n).1 t := by
  have hstart : 0 ≤ t := le_trans (c3StageTime_nonneg n) ht.1
  have hindex := c3StageActiveIndex_eq_on_dwell n (by
    simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using ht)
  simp [c3A7StitchedC1Gain, c3A7StageC1Gain,
    c3A7StitchedTrajectory, hstart, hindex, ht.1]

/-- 各stitched stageで選ばれる実効ゲインは実は高々1である。
これはC1の許容上限3より強く、微分和の一様評価に使う。 -/
theorem c3A7StitchedC1Gain_le_one
    (t : ℝ) (ht : 0 ≤ t) : (c3A7StitchedC1Gain).1 t ≤ 1 := by
  have hactive := c3StageActiveIndex_mem_dwell t ht
  let n := c3StageActiveIndex t
  have hstage : t ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime (n + 1)) := by
    simpa [n, Tomabechi.Consistency.C3.stageTime_recurrence] using hactive
  rw [c3A7StitchedC1Gain_eq_stage n t hstage]
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  let q := cognitiveCoordinate (c3A7StageTrajectory n t)
  have hqle : q ≤ c := by
    exact c3A7StageTrajectory_cognitive_le_center n t hstage.1
  have hc_lt : c < 1 := Tomabechi.Consistency.C3.representation_lt_top (n + 1)
  have hc : c ≤ 1 := hc_lt.le
  have hden : 0 < 1 - q := by
    dsimp [q]
    exact sub_pos.mpr (lt_of_le_of_lt hqle hc_lt)
  have hgain : (c3A7StageC1Gain n).1 t = (c - q) / (1 - q) := by
    simp [c3A7StageC1Gain, hstage.1, q, c]
  rw [hgain]
  apply (div_le_one hden).2
  dsimp [q, c]
  linarith

/-- 区間上で一致する二つの許容ゲインは、その区間内の積分状態を同じにする。 -/
theorem c1ControlledState_eq_of_gain_eq_on_interval
    (r x a b : ℝ) (u v : Tomabechi.Consistency.ConsistencyC1.C1GainSignal)
    (hab : a ≤ b) (hgain : ∀ s, s ∈ Set.Ico a b → u.1 s = v.1 s) :
    ∀ t, t ∈ Set.Icc a b →
      Tomabechi.Consistency.ConsistencyC1.c1ControlledState r x a u t =
        Tomabechi.Consistency.ConsistencyC1.c1ControlledState r x a v t := by
  intro t ht
  have hacc : c1AccumulatedGain u a t = c1AccumulatedGain v a t := by
    unfold c1AccumulatedGain
    apply intervalIntegral.integral_congr_ae
    filter_upwards
      [compl_mem_ae_iff.mpr (by simp : volume ({b} : Set ℝ) = 0)] with s hne hs
    have hs' : s ∈ Set.Ioc a t := by
      simpa [Set.uIoc_of_le ht.1] using hs
    have hslt : s < b := lt_of_le_of_ne (le_trans hs'.2 ht.2) hne
    apply hgain s
    exact ⟨le_of_lt hs'.1, hslt⟩
  simp [Tomabechi.Consistency.ConsistencyC1.c1ControlledState,
    Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit, hacc]

/-- 一つの大域許容入力の積分軌道は、全ての非負時刻でstitched C3/A7認知pathに一致する。
証明は各dwellの一意性とswitchごとのrestartを自然数帰納法でつなぐ。 -/
theorem c3A7StitchedC1Gain_matches_global_C1_trajectory
    (t : ℝ) (ht : 0 ≤ t) :
    Tomabechi.Consistency.ConsistencyC1.c1ControlledState 1 0 0
        c3A7StitchedC1Gain t =
      cognitiveCoordinate (c3A7StitchedTrajectory t) := by
  let q0 : ℕ → ℝ := fun n => cognitiveCoordinate (c3A7StageInitial n)
  have hstart : ∀ n,
      Tomabechi.Consistency.ConsistencyC1.c1ControlledState 1 0 0
          c3A7StitchedC1Gain (Tomabechi.Consistency.C3.stageTime n) = q0 n := by
    intro n
    induction n with
    | zero =>
        have htime : Tomabechi.Consistency.C3.stageTime 0 = 0 := by
          simp [Tomabechi.Consistency.C3.stageTime]
        rw [htime]
        rw [Tomabechi.Consistency.ConsistencyC1.c1ControlledState_initial]
        change 0 = (Tomabechi.Consistency.C3.valleySequence 0).initial
        simp [Tomabechi.Consistency.C3.valleySequence,
          Tomabechi.Consistency.C3.firstValley,
          Tomabechi.Examples.Theorem23B.quadraticStage,
          Tomabechi.Theorem23.endpointCompatibleStageSequence]
    | succ n ih =>
        rw [Tomabechi.Consistency.C3.stageTime_recurrence]
        rw [Tomabechi.Consistency.ConsistencyC1.c1ControlledState_restart
          1 0 0 (Tomabechi.Consistency.C3.stageTime n)
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n) c3A7StitchedC1Gain]
        rw [ih]
        have hlocal := c1ControlledState_eq_of_gain_eq_on_interval
          1 (q0 n) (Tomabechi.Consistency.C3.stageTime n)
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n)
          c3A7StitchedC1Gain (c3A7StageC1Gain n)
          (by linarith [Tomabechi.Consistency.C3.stageDuration_pos n])
          (fun s hs => c3A7StitchedC1Gain_eq_stage n s (by
            simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using hs))
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n)
          ⟨by linarith [Tomabechi.Consistency.C3.stageDuration_pos n], le_rfl⟩
        rw [hlocal]
        rw [show q0 n = cognitiveCoordinate (c3A7StageInitial n) by rfl]
        rw [c3A7StageC1Gain_matches_C1_trajectory n
          (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n)
          (le_add_of_nonneg_right
            (Tomabechi.Consistency.C3.stageDuration_pos n).le)]
        rw [c3A7StageTrajectory_endpoint, c3A7StageInitial]
        rfl
  have hinterval := c3StageActiveIndex_mem_dwell t ht
  rcases hinterval with ⟨hnlower, hnupper⟩
  have hst := hstart (c3StageActiveIndex t)
  rw [Tomabechi.Consistency.ConsistencyC1.c1ControlledState_restart
    1 0 0 (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t)) t
    c3A7StitchedC1Gain, hst]
  have hsame := c1ControlledState_eq_of_gain_eq_on_interval
    1 (q0 (c3StageActiveIndex t))
    (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t))
    (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t + 1))
    c3A7StitchedC1Gain (c3A7StageC1Gain (c3StageActiveIndex t))
    (le_of_lt (c3StageTime_strictMono (by omega)))
    (fun s hs => c3A7StitchedC1Gain_eq_stage (c3StageActiveIndex t) s (by
      simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using hs))
    t ⟨hnlower, hnupper.le⟩
  rw [hsame, show q0 (c3StageActiveIndex t) =
      cognitiveCoordinate (c3A7StageInitial (c3StageActiveIndex t)) by rfl]
  rw [c3A7StageC1Gain_matches_C1_trajectory (c3StageActiveIndex t) t hnlower]
  rw [c3A7StitchedTrajectory_eq_stage (c3StageActiveIndex t) t (by
    simpa [Tomabechi.Consistency.C3.stageTime_recurrence] using
      (show t ∈ Set.Ico
        (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t))
        (Tomabechi.Consistency.C3.stageTime (c3StageActiveIndex t + 1)) from
        ⟨hnlower, hnupper⟩))]

/-- C3/A7で段を貼り合わせた認知座標は、非負有限区間上で絶対連続である。
箱条件に依存しないC1の積分軌道ACを、大域path一致を通して移送する。 -/
theorem c3A7StitchedCognitive_absolutelyContinuousOnInterval
    (b : ℝ) (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s)) 0 b := by
  have hbase :=
    Tomabechi.Consistency.ConsistencyC1.c1ControlledState_absolutelyContinuousOnInterval
      1 0 0 b (by linarith) c3A7StitchedC1Gain
  apply hbase.congr
  intro s hs
  rw [Set.uIcc_of_le hb] at hs
  exact c3A7StitchedC1Gain_matches_global_C1_trajectory s hs.1

/-- 大域stitched認知座標は全ての非負時刻で `[0,1]` に入る。 -/
theorem c3A7StitchedTrajectory_cognitive_mem_unitInterval
    (t : ℝ) (ht : 0 ≤ t) :
    cognitiveCoordinate (c3A7StitchedTrajectory t) ∈ Set.Icc 0 1 := by
  let n := c3StageActiveIndex t
  have hactive := c3StageActiveIndex_mem_dwell t ht
  have hformula := c3A7StageTrajectory_cognitive_formula n t
  have hpath : c3A7StitchedTrajectory t = c3A7StageTrajectory n t := by
    dsimp [n, c3A7StitchedTrajectory]
  rw [hpath, hformula]
  let c := Tomabechi.Consistency.C3.representation (n + 1 : ℕ)
  have hinit0 := (Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n).1
  have hinitc := (Tomabechi.Consistency.C3.hStageSequence_initial_between_centers n).2
  have hinitValley : (Tomabechi.Consistency.C3.valleySequence n).initial =
      (Tomabechi.Consistency.C3.hStageSequence n).initial := by
    rw [← Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec n]
    rfl
  have hinitValley0 : 0 ≤ (Tomabechi.Consistency.C3.valleySequence n).initial := by
    rw [hinitValley]
    exact hinit0
  have hinitValleyc : (Tomabechi.Consistency.C3.valleySequence n).initial ≤
      Tomabechi.Consistency.C3.representation (n + 1 : ℕ) := by
    rw [hinitValley]
    exact hinitc
  have hc1 : c ≤ 1 := le_of_lt (Tomabechi.Consistency.C3.representation_lt_top (n + 1))
  have hdt : 0 ≤ t - Tomabechi.Consistency.C3.stageTime n := by linarith [hactive.1]
  have he0 : 0 ≤ Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) :=
    Real.exp_nonneg _
  have he1 : Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have hgap : 0 ≤ c - (Tomabechi.Consistency.C3.valleySequence n).initial := by
    simpa [c] using sub_nonneg.mpr hinitValleyc
  have hgapmul : (c - (Tomabechi.Consistency.C3.valleySequence n).initial) *
      Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) ≤
        c - (Tomabechi.Consistency.C3.valleySequence n).initial :=
    (mul_le_mul_of_nonneg_left he1 hgap).trans_eq (by ring)
  have hgapmul0 : 0 ≤ (c - (Tomabechi.Consistency.C3.valleySequence n).initial) *
      Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) :=
    mul_nonneg hgap he0
  constructor
  · have hcalc : c + ((Tomabechi.Consistency.C3.valleySequence n).initial - c) *
        Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) =
      (Tomabechi.Consistency.C3.valleySequence n).initial +
        (c - (Tomabechi.Consistency.C3.valleySequence n).initial) *
          (1 - Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n))) := by ring
    rw [hcalc]
    positivity
  · have hcalc : c + ((Tomabechi.Consistency.C3.valleySequence n).initial - c) *
        Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) =
      c - (c - (Tomabechi.Consistency.C3.valleySequence n).initial) *
          Real.exp (-(t - Tomabechi.Consistency.C3.stageTime n)) := by ring
    rw [hcalc]
    linarith [hgapmul0]

/-- 認知座標の二乗も同じ有限区間上で絶対連続である。 -/
theorem c3A7StitchedCognitiveSq_absolutelyContinuousOnInterval
    (b : ℝ) (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) 0 b := by
  have hq := c3A7StitchedCognitive_absolutelyContinuousOnInterval b hb
  have hmul := hq.mul hq
  apply hmul.congr
  intro s hs
  simp [pow_two]

/-- 全ての正層エントロピー `1+q²` は同じstitched path上で絶対連続である。 -/
theorem c3A7StitchedLayerEntropy_absolutelyContinuousOnInterval
    (n : PositiveLayer) (b : ℝ) (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun s => layerEntropy n (c3A7StitchedTrajectory s)) 0 b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hsq := c3A7StitchedCognitiveSq_absolutelyContinuousOnInterval b hb
  change AbsolutelyContinuousOnInterval
    ((fun _ : ℝ => (1 : ℝ)) +
      (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2)) 0 b
  exact hconst.add hsq

/-- 物理エントロピー `3t-q²` も同じstitched path上で絶対連続である。 -/
theorem c3A7StitchedPhysicalEntropy_absolutelyContinuousOnInterval
    (b : ℝ) (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun s => physicalEntropy (c3A7StitchedTrajectory s)) 0 b := by
  have hlinear : AbsolutelyContinuousOnInterval (fun s : ℝ => 3 * s) 0 b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hsq := c3A7StitchedCognitiveSq_absolutelyContinuousOnInterval b hb
  have hsub := hlinear.sub hsq
  apply hsub.congr
  intro s hs
  have htime := c3A7StitchedTrajectory_entropyObserved s
  change physicalCoordinate (c3A7StitchedTrajectory s) +
    cognitiveCoordinate (c3A7StitchedTrajectory s) ^ 2 = 3 * s at htime
  change 3 * s - cognitiveCoordinate (c3A7StitchedTrajectory s) ^ 2 =
    physicalCoordinate (c3A7StitchedTrajectory s)
  linarith

/-- 15→23入口が要求する任意の生存区間[a,b]へ、正層ACを制限する。 -/
theorem c3A7StitchedLayerEntropy_ac_between
    (n : PositiveLayer) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    AbsolutelyContinuousOnInterval
      (fun s => layerEntropy n (c3A7StitchedTrajectory s)) a b := by
  have hb : 0 ≤ b := le_trans ha hab.le
  have h0b := c3A7StitchedLayerEntropy_absolutelyContinuousOnInterval n b hb
  apply h0b.mono
  rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le hb]
  exact Set.Icc_subset_Icc (by linarith) le_rfl

/-- 15→23入口が要求する任意の生存区間[a,b]へ、物理層ACを制限する。 -/
theorem c3A7StitchedPhysicalEntropy_ac_between
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    AbsolutelyContinuousOnInterval
      (fun s => physicalEntropy (c3A7StitchedTrajectory s)) a b := by
  have hb : 0 ≤ b := le_trans ha hab.le
  have h0b := c3A7StitchedPhysicalEntropy_absolutelyContinuousOnInterval b hb
  apply h0b.mono
  rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le hb]
  exact Set.Icc_subset_Icc (by linarith) le_rfl

/-- 同じpathの各有限時刻で、15→23入口の端点層和は可算和可能である。 -/
theorem c3A7Stitched_endpoint_layer_summable (t : ℝ) :
    Summable (fun n : PositiveLayer =>
      layerWeight n * layerEntropy n (c3A7StitchedTrajectory t)) :=
  weightedLayerEntropy_summable (c3A7StitchedTrajectory t)

/-- 生成率3は、非負生存区間のどの長さにも厳密に正の生成積分を与える。 -/
theorem c3A7Stitched_production_integral_pos
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 < ∫ t in a..b, (3 : ℝ) := by
  have hint : (∫ t in a..b, (3 : ℝ)) = 3 * (b - a) := by
    simp [intervalIntegral.integral_const]
    ring
  rw [hint]
  positivity

/-- 生成率を切替時刻を含む区間全体で非負とする。 -/
theorem c3A7Stitched_production_nonnegative_ae
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] (fun _ : ℝ => (3 : ℝ)) := by
  exact Filter.Eventually.of_forall (fun _ => by norm_num)

/-- 15→23のA6′端点条件を、この同じstitched pathの両端で供給する。 -/
theorem c3A7Stitched_A6_endpoint_summable
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Summable (fun n : PositiveLayer =>
        layerWeight n * layerEntropy n (c3A7StitchedTrajectory a)) ∧
      Summable (fun n : PositiveLayer =>
        layerWeight n * layerEntropy n (c3A7StitchedTrajectory b)) := by
  exact ⟨c3A7Stitched_endpoint_layer_summable a,
    c3A7Stitched_endpoint_layer_summable b⟩

/-- 各正の非負時刻区間でstitched認知座標はC1入力方程式をa.e.満たす。
有限切替点は測度零として処理し、区間内部では大域path一致から微分を移す。 -/
theorem c3A7StitchedCognitive_ae_ode
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      HasDerivAt (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s))
        ((c3A7StitchedC1Gain).1 t *
          (1 - cognitiveCoordinate (c3A7StitchedTrajectory t))) t := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hglobalODE :=
    Tomabechi.Consistency.ConsistencyC1.c1ControlledState_ae_ode
      1 0 0 b hb c3A7StitchedC1Gain
  have hglobalODE' : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc 0 b),
      HasDerivAt (fun s =>
        Tomabechi.Consistency.ConsistencyC1.c1ControlledState
          1 0 0 c3A7StitchedC1Gain s)
        (-(c3A7StitchedC1Gain).1 t *
          (Tomabechi.Consistency.ConsistencyC1.c1ControlledState
            1 0 0 c3A7StitchedC1Gain t - 1)) t := by
    simpa using hglobalODE
  have hODEIoc : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc a b),
      HasDerivAt (fun s =>
        Tomabechi.Consistency.ConsistencyC1.c1ControlledState
          1 0 0 c3A7StitchedC1Gain s)
        (-(c3A7StitchedC1Gain).1 t *
          (Tomabechi.Consistency.ConsistencyC1.c1ControlledState
            1 0 0 c3A7StitchedC1Gain t - 1)) t := by
    apply MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (s := Set.Ioc a b) (t := Set.Icc 0 b) ?_ hglobalODE'
    intro s hs
    exact ⟨le_trans ha hs.1.le, hs.2⟩
  rw [Set.uIoc_of_le hab.le]
  filter_upwards [hODEIoc,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hODE ht
  have hloc : (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s)) =ᶠ[𝓝 t]
      (fun s => Tomabechi.Consistency.ConsistencyC1.c1ControlledState
        1 0 0 c3A7StitchedC1Gain s) := by
    have hpos : 0 < t := lt_of_le_of_lt ha ht.1
    filter_upwards [Ioo_mem_nhds hpos (show t < t + 1 by linarith)] with s hs
    exact (c3A7StitchedC1Gain_matches_global_C1_trajectory s hs.1.le).symm
  have hq := hODE.congr_of_eventuallyEq hloc
  have hpoint := c3A7StitchedC1Gain_matches_global_C1_trajectory t
    (le_trans ha ht.1.le)
  convert hq using 1 <;> rw [hpoint] <;> ring

/-- 同じ認知微分を持つとき、全正層のエントロピー導関数は `q²` の導関数に一致する。 -/
theorem c3A7StitchedLayerEntropy_deriv_eq_sq
    (n : PositiveLayer) (t v : ℝ)
    (hq : HasDerivAt (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s)) v t) :
    deriv (fun s => layerEntropy n (c3A7StitchedTrajectory s)) t =
      deriv (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) t := by
  have hsq := hq.fun_pow 2
  have hlayer : HasDerivAt
      (fun s => layerEntropy n (c3A7StitchedTrajectory s))
      (2 * cognitiveCoordinate (c3A7StitchedTrajectory t) * v) t := by
    simpa [layerEntropy, cognitiveCoordinate, add_comm] using hsq.add_const (1 : ℝ)
  have hsqderiv : deriv
      (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) t =
        2 * cognitiveCoordinate (c3A7StitchedTrajectory t) * v := by
    simpa [pow_one] using hsq.deriv
  exact hlayer.deriv.trans hsqderiv.symm

/-- A.e.ではstitched正層の共通導関数は絶対値2以下。
状態と実効ゲインがともに `[0,1]` にあることを使う。 -/
theorem c3A7StitchedCognitiveSq_deriv_bound_ae
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      ‖deriv (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) t‖ ≤ 2 := by
  have hode := c3A7StitchedCognitive_ae_ode a b ha hab
  rw [Set.uIoc_of_le hab.le] at hode ⊢
  filter_upwards [hode, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hq ht
  have hstate := c3A7StitchedTrajectory_cognitive_mem_unitInterval t
    (le_trans ha ht.1.le)
  have hg0 : 0 ≤ (c3A7StitchedC1Gain).1 t := (c3A7StitchedC1Gain.property.2 t).1
  have hg1 : (c3A7StitchedC1Gain).1 t ≤ 1 :=
    c3A7StitchedC1Gain_le_one t (le_trans ha ht.1.le)
  have hq0 : 0 ≤ cognitiveCoordinate (c3A7StitchedTrajectory t) := hstate.1
  have hq1 : cognitiveCoordinate (c3A7StitchedTrajectory t) ≤ 1 := hstate.2
  have hrem0 : 0 ≤ 1 - cognitiveCoordinate (c3A7StitchedTrajectory t) := by linarith
  have hspeed0 : 0 ≤ (c3A7StitchedC1Gain).1 t *
      (1 - cognitiveCoordinate (c3A7StitchedTrajectory t)) := mul_nonneg hg0 hrem0
  have hspeed1 : (c3A7StitchedC1Gain).1 t *
      (1 - cognitiveCoordinate (c3A7StitchedTrajectory t)) ≤ 1 := by
    calc
      _ ≤ 1 * (1 - cognitiveCoordinate (c3A7StitchedTrajectory t)) :=
        mul_le_mul_of_nonneg_right hg1 hrem0
      _ ≤ 1 := by nlinarith
  have hpow := hq.fun_pow 2
  have hderiv : deriv
      (fun s => (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) t =
        2 * cognitiveCoordinate (c3A7StitchedTrajectory t) *
          ((c3A7StitchedC1Gain).1 t *
            (1 - cognitiveCoordinate (c3A7StitchedTrajectory t))) := by
    simpa [pow_one] using hpow.deriv
  rw [hderiv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hprod : cognitiveCoordinate (c3A7StitchedTrajectory t) *
      ((c3A7StitchedC1Gain).1 t *
        (1 - cognitiveCoordinate (c3A7StitchedTrajectory t))) ≤ 1 := by
    calc
      _ ≤ 1 * ((c3A7StitchedC1Gain).1 t *
          (1 - cognitiveCoordinate (c3A7StitchedTrajectory t))) :=
        mul_le_mul_of_nonneg_right hq1 hspeed0
      _ ≤ 1 := by nlinarith
  nlinarith

/-- 有限正層部分集合の実導関数和を固定した時刻関数として表す。 -/
noncomputable def c3A7StitchedFiniteLayerDerivative
    (s : Finset PositiveLayer) (t : ℝ) : ℝ :=
  ∑ n ∈ s, layerWeight n * deriv (fun u =>
    layerEntropy n (c3A7StitchedTrajectory u)) t

/-- 任意の有限正層部分集合に対する導関数和は一様可積分である。
各層の導関数を `q²` の共通導関数へ畳み、幾何重みの部分和≤1を使う。 -/
theorem c3A7Stitched_A6_finite_UI
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.UniformIntegrable
      (fun s : Finset PositiveLayer => c3A7StitchedFiniteLayerDerivative s)
      1 (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.uIoc a b)
  have hμfinite : MeasureTheory.IsFiniteMeasure μ := by
    apply (MeasureTheory.isFiniteMeasure_restrict).2
    simp [μ, Real.volume_uIoc]
  letI : MeasureTheory.IsFiniteMeasure μ := hμfinite
  have hmeas : ∀ s : Finset PositiveLayer,
      MeasureTheory.AEStronglyMeasurable (c3A7StitchedFiniteLayerDerivative s) μ := by
    intro s
    have hterm (n : PositiveLayer) : Measurable (fun t => layerWeight n *
        deriv (fun u => layerEntropy n (c3A7StitchedTrajectory u)) t) := by
      exact measurable_const.mul (measurable_deriv _)
    have hsum : Measurable (c3A7StitchedFiniteLayerDerivative s) := by
      unfold c3A7StitchedFiniteLayerDerivative
      exact Finset.measurable_sum s (by intro n hn; exact hterm n)
    exact hsum.aestronglyMeasurable
  have hbound : ∀ s : Finset PositiveLayer,
      ∀ᵐ t ∂μ, ‖c3A7StitchedFiniteLayerDerivative s t‖ ≤ 2 := by
    intro s
    have hode := c3A7StitchedCognitive_ae_ode a b ha hab
    have hsqbound := c3A7StitchedCognitiveSq_deriv_bound_ae a b ha hab
    filter_upwards [hode, hsqbound,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t hq hderivSqAt ht
    have htt : 0 ≤ t := by
      rw [Set.uIoc_of_le hab.le] at ht
      exact le_trans ha ht.1.le
    have hsum_eq : c3A7StitchedFiniteLayerDerivative s t =
        (∑ n ∈ s, layerWeight n) * deriv
          (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t := by
      unfold c3A7StitchedFiniteLayerDerivative
      simp_rw [fun n => c3A7StitchedLayerEntropy_deriv_eq_sq n t _ hq]
      rw [Finset.sum_mul]
    rw [hsum_eq, Real.norm_eq_abs, abs_mul]
    have hw0 : 0 ≤ ∑ n ∈ s, layerWeight n := by
      apply Finset.sum_nonneg
      intro n hn
      exact le_of_lt (layerWeight_pos n)
    have hw1 := layerWeight_sum_le_one s
    calc
      |∑ n ∈ s, layerWeight n| *
          |deriv (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t|
        = (∑ n ∈ s, layerWeight n) *
          |deriv (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t| := by
            rw [abs_of_nonneg hw0]
      _ ≤ 1 * 2 := by
        calc
          _ ≤ 1 * |deriv
              (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t| :=
            mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
          _ ≤ 1 * 2 := mul_le_mul_of_nonneg_left hderivSqAt (by norm_num)
      _ ≤ 2 := by norm_num
  exact Tomabechi.Consistency.C2.uniformIntegrable_of_bound_two μ
    (fun s : Finset PositiveLayer => c3A7StitchedFiniteLayerDerivative s)
    hmeas hbound

/-- 微分可能な一点では、stitched層の導関数prefixは総層導関数へ収束する。 -/
theorem c3A7Stitched_A6_prefix_tendsto_at
    (t v : ℝ)
    (hq : HasDerivAt (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s)) v t) :
    Filter.Tendsto
      (fun k => ∑ i : Fin k,
        layerWeight (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val) *
          deriv (fun u => layerEntropy
            (Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer i.val)
            (c3A7StitchedTrajectory u)) t)
      atTop
      (𝓝 (∑' n : PositiveLayer, layerWeight n *
        deriv (fun u => layerEntropy n (c3A7StitchedTrajectory u)) t)) := by
  let e := Tomabechi.Theorem15_23.countableLayerEnumeration PositiveLayer
  let d := deriv (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t
  have hsum : Summable (fun n : PositiveLayer => layerWeight n *
      deriv (fun u => layerEntropy n (c3A7StitchedTrajectory u)) t) := by
    have h := layerWeight_summable.mul_right d
    have hrewrite : (fun n : PositiveLayer => layerWeight n *
        deriv (fun u => layerEntropy n (c3A7StitchedTrajectory u)) t) =
      fun n => layerWeight n * d := by
      funext n
      exact congrArg (fun r => layerWeight n * r)
        (c3A7StitchedLayerEntropy_deriv_eq_sq n t v hq)
    rw [hrewrite]
    exact h
  have h := Tomabechi.Theorem15.enumerated_tsum_partial_tendsto_of_summable e
    (fun n : PositiveLayer => layerWeight n *
      deriv (fun u => layerEntropy n (c3A7StitchedTrajectory u)) t) hsum
  simpa [e] using h

/-- A7収支は、微分可能な一点では `physical'=3-Σwₙ(layerₙ')` となる。 -/
theorem c3A7Stitched_A7_at
    (t v : ℝ)
    (hq : HasDerivAt (fun s => cognitiveCoordinate (c3A7StitchedTrajectory s)) v t) :
    deriv (fun s => physicalEntropy (c3A7StitchedTrajectory s)) t =
      -(∑' n : PositiveLayer, layerWeight n *
        deriv (fun s => layerEntropy n (c3A7StitchedTrajectory s)) t) + 3 := by
  let d := deriv (fun u => (cognitiveCoordinate (c3A7StitchedTrajectory u)) ^ 2) t
  have hsq := hq.fun_pow 2
  have hlinear : HasDerivAt (fun s : ℝ => 3 * s) 3 t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul 3
  have hphysical_form (s : ℝ) : physicalEntropy (c3A7StitchedTrajectory s) =
      3 * s - (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2 := by
    have htime := c3A7StitchedTrajectory_entropyObserved s
    change physicalCoordinate (c3A7StitchedTrajectory s) +
      cognitiveCoordinate (c3A7StitchedTrajectory s) ^ 2 = 3 * s at htime
    change (c3A7StitchedTrajectory s).2 =
      3 * s - cognitiveCoordinate (c3A7StitchedTrajectory s) ^ 2
    change (c3A7StitchedTrajectory s).2 +
      cognitiveCoordinate (c3A7StitchedTrajectory s) ^ 2 = 3 * s at htime
    linarith
  have hphysical : HasDerivAt (fun s => physicalEntropy (c3A7StitchedTrajectory s))
      (3 - (2 * cognitiveCoordinate (c3A7StitchedTrajectory t) * v)) t := by
    have hsub := hlinear.sub hsq
    have heq : (fun s => physicalEntropy (c3A7StitchedTrajectory s)) =ᶠ[𝓝 t]
        (fun s => 3 * s - (cognitiveCoordinate (c3A7StitchedTrajectory s)) ^ 2) := by
      filter_upwards [] with s
      exact hphysical_form s
    have h := hsub.congr_of_eventuallyEq heq
    simpa [pow_one] using h
  have hrewrite : (fun n : PositiveLayer => layerWeight n *
      deriv (fun s => layerEntropy n (c3A7StitchedTrajectory s)) t) =
      fun n => d * layerWeight n := by
    funext n
    rw [c3A7StitchedLayerEntropy_deriv_eq_sq n t v hq]
    simp [d, mul_comm]
  have hsum : (∑' n : PositiveLayer, layerWeight n *
      deriv (fun s => layerEntropy n (c3A7StitchedTrajectory s)) t) = d := by
    rw [hrewrite, tsum_mul_left, layerWeight_tsum]
    simp [d, mul_comm]
  have hphysderiv := hphysical.deriv
  have hsqderiv : d = 2 * cognitiveCoordinate (c3A7StitchedTrajectory t) * v := by
    simpa [d, pow_one] using hsq.deriv
  rw [hphysderiv, ← hsqderiv, hsum]
  ring

/-- 同じstitched pathに15(I)→23-A入口を適用し、非再訪を得る。 -/
theorem c3A7Stitched_theorem15_23_nonrecurrence :
    ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Ici 0 → t₂ ∈ Set.Ici 0 → t₁ < t₂ →
      c3A7StitchedTrajectory t₂ ≠ c3A7StitchedTrajectory t₁ := by
  apply Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence
    (Layer := PositiveLayer)
    physicalEntropy layerEntropy layerWeight layerWeight_pos
    (fun n z => by simp [layerEntropy]; positivity)
    c3A7StitchedTrajectory (fun _ => 3) (Set.Ici 0)
  · intro a b ha hb hab
    have hint : (∫ t in a..b, (3 : ℝ)) = 3 * (b - a) := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hint]
    positivity
  · intro a b ha hb hab n
    exact c3A7StitchedLayerEntropy_ac_between n a b ha hab
  · intro a b ha hb hab
    exact c3A7StitchedPhysicalEntropy_ac_between a b ha hab
  · intro a b ha hb hab
    exact c3A7Stitched_A6_endpoint_summable a b ha hab
  · intro a b ha hb hab
    exact c3A7Stitched_A6_finite_UI a b ha hab
  · intro a b ha hb hab
    have hode := c3A7StitchedCognitive_ae_ode a b ha hab
    filter_upwards [hode] with t hq
    exact c3A7Stitched_A6_prefix_tendsto_at t _ hq
  · intro a b ha hb hab
    have hode := c3A7StitchedCognitive_ae_ode a b ha hab
    filter_upwards [hode] with t hq
    exact c3A7Stitched_A7_at t _ hq
  · intro a b ha hb hab
    exact Filter.Eventually.of_forall (fun _ => by norm_num)

/-- C1二主体の実状態flowも、C3/A7の認知座標から復元した状態と一致する。
初期状態 `![1,-1]` はC1の費用最適性用box外なので、この等式を最適性主張には使わない。 -/
theorem c3A7StitchedC1Gain_matches_twoAgent_flow
    (t : ℝ) (ht : 0 ≤ t) :
    controlledConsensusState ![(1 : ℝ), -1] 0 c3A7StitchedC1Gain t =
      completeStateToC1 0 (c3A7StitchedTrajectory t) := by
  have hq := c3A7StitchedC1Gain_matches_global_C1_trajectory t ht
  have hres : c1ControlledOrbit (1 : ℝ) 0 c3A7StitchedC1Gain t =
      1 - cognitiveCoordinate (c3A7StitchedTrajectory t) := by
    rw [← hq]
    simp [c1ControlledState, c1ControlledOrbit]
  ext i
  fin_cases i <;>
    simp [controlledConsensusState, completeStateToC1, meanState,
      halfDifference, hres]

theorem c3A7StitchedC1Gain_twoAgent_initial_not_in_box :
    ![(1 : ℝ), -1] ∉ Tomabechi.Consistency.ConsistencyC1Consensus.box := by
  intro hx
  have h0 := hx 0
  norm_num at h0

/-- C1/C2実flowのサンプル認知値は、対応するA7 stageの凍結中心と一致する。
これはstage中心の一致であり、段有限時刻で軌道値が中心へ到達することや完全状態の一致を意味しない。 -/
theorem c6C1C3CenterSample_eq_A7StageCenter (n : ℕ) :
    cognitiveCoordinate (c6C1C3CenterSamplingAdapter.completeState n) =
      Tomabechi.Consistency.C3.representation (n + 3 : ℕ) := by
  rw [c6C1C3CenterSamplingAdapter.completeState_cognitive_is_stage_center,
    hStageSequence_center_is_commonStage_representation]
  change Tomabechi.Consistency.C3.representation
      (((n + 2 : ℕ) + 1 : ℕ)) = _
  congr 1

/-- C3元H-stageに対応し、A7率3を満たす完全状態の始点・終点も、先の
C1/C2/C4/C5/C3結合lawへ付加する。拡張後も元の結合lawを周辺として回収できる。 -/
noncomputable def c6C1C3C4CoreStageJointLaw
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure
      (((C6C1ObservedState ×
          ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
            (Bool × C6C5ControlledState × ℝ))) ×
        (Unit × (Bool × Bool))) × (CompleteState × CompleteState)) :=
  (c6C1C3C4JointLaw x t₀ t T τ).map (fun z =>
    (z, (c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n),
        c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n))))

theorem c6C1C3C4CoreStageJointLaw_isProbability
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure (c6C1C3C4CoreStageJointLaw n x t₀ t T τ) := by
  rw [c6C1C3C4CoreStageJointLaw, MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C1C3C4JointLaw_isProbability x t₀ t T τ
  · exact (by fun_prop)

theorem c6C1C3C4CoreStageJointLaw_observation_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map Prod.fst =
      c6C1C3C4JointLaw x t₀ t T τ := by
  rw [c6C1C3C4CoreStageJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4JointLaw x t₀ t T τ).map id = _
  rw [MeasureTheory.Measure.map_id]

/-- 結合law上でもA7対応C3段の終点は、元H-stage列の次段初期状態を
物理収支とともに保持する。 -/
theorem c6C1C3C4CoreStageJointLaw_endpoint_ae
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    ∀ᵐ z ∂c6C1C3C4CoreStageJointLaw n x t₀ t T τ,
      z.2.2 = c3A7StageInitial (n + 1) := by
  rw [c6C1C3C4CoreStageJointLaw]
  apply (MeasureTheory.ae_map_iff (by fun_prop) (by measurability)).2
  filter_upwards with z
  exact c3A7StageTrajectory_endpoint n

/-- 結合lawに付加した第n段の終点は、次段A7対応trajectoryの初期状態でもある。
元H-stage切替とlaw上の完全状態座標のrestart一致を結ぶ。 -/
theorem c6C1C3C4CoreStageJointLaw_restart_ae
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    ∀ᵐ z ∂c6C1C3C4CoreStageJointLaw n x t₀ t T τ,
      z.2.2 = c3A7StageTrajectory (n + 1)
        (Tomabechi.Consistency.C3.stageTime (n + 1)) := by
  filter_upwards [c6C1C3C4CoreStageJointLaw_endpoint_ae n x t₀ t T τ] with z hz
  rw [hz]
  exact (c3A7StageTrajectory_initial (n + 1)).symm

/-- C3/A7完全stage pathを含めた共通結合lawの観測型。 -/
abbrev C6C1C3C4A7PathObservation :=
  ((((C6C1ObservedState ×
      ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
        (Bool × C6C5ControlledState × ℝ))) ×
    (Unit × (Bool × Bool))) × (CompleteState × CompleteState)) ×
    (ℝ → CompleteState))

/-- C1中心サンプルも含めた拡張観測型。 -/
abbrev C6C1C3C4A7SamplePathObservation :=
  C6C1C3C4A7PathObservation × CompleteState

/-- C1中心サンプルに加え、全stageを通るstitched C3/A7軌道も保持する観測型。 -/
abbrev C6C1C3C4A7GlobalPathObservation :=
  C6C1C3C4A7SamplePathObservation × (ℝ → CompleteState)

/-- C3/A7完全stage pathを含めた共通結合law。 -/
noncomputable def c6C1C3C4A7PathJointLaw
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure C6C1C3C4A7PathObservation :=
  (c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map
    (fun z => (z, c3A7StageTrajectory n))

theorem c6C1C3C4A7PathJointLaw_isProbability
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure (c6C1C3C4A7PathJointLaw n x t₀ t T τ) := by
  rw [c6C1C3C4A7PathJointLaw, MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C1C3C4CoreStageJointLaw_isProbability n x t₀ t T τ
  · exact (by fun_prop)

theorem c6C1C3C4A7PathJointLaw_observation_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map Prod.fst =
      c6C1C3C4CoreStageJointLaw n x t₀ t T τ := by
  rw [c6C1C3C4A7PathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map id = _
  rw [MeasureTheory.Measure.map_id]

/-- C1が同じC3中心列を実際に通る状態も、A7対応stage pathと同一確率空間へ載せる。
追加座標はC1側の中心サンプルであり、C3 stage pathの有限時刻状態とは同一視しない。 -/
noncomputable def c6C1C3C4A7SamplePathJointLaw
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure C6C1C3C4A7SamplePathObservation :=
  (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
    (fun z => (z, c6C1C3CenterSamplingAdapter.completeState n))

theorem c6C1C3C4A7SamplePathJointLaw_isProbability
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure
      (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ) := by
  rw [c6C1C3C4A7SamplePathJointLaw,
    MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C1C3C4A7PathJointLaw_isProbability n x t₀ t T τ
  · exact (by fun_prop)

theorem c6C1C3C4A7SamplePathJointLaw_path_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map Prod.fst =
      c6C1C3C4A7PathJointLaw n x t₀ t T τ := by
  rw [c6C1C3C4A7SamplePathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map id = _
  rw [MeasureTheory.Measure.map_id]

theorem c6C1C3C4A7SamplePathJointLaw_c1_sample_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map Prod.snd =
      MeasureTheory.Measure.dirac
        (c6C1C3CenterSamplingAdapter.completeState n) := by
  rw [c6C1C3C4A7SamplePathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
    (fun _ => c6C1C3CenterSamplingAdapter.completeState n) = _
  rw [MeasureTheory.Measure.map_const]
  have hprob := c6C1C3C4A7PathJointLaw_isProbability n x t₀ t T τ
  simp [hprob.measure_univ]

theorem c6C1C3C4A7SamplePathJointLaw_c1_center_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map
      (fun z => cognitiveCoordinate z.2) =
      MeasureTheory.Measure.dirac
        (Tomabechi.Consistency.C3.representation (n + 3 : ℕ)) := by
  calc
    _ = ((c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map Prod.snd).map
          cognitiveCoordinate := by
      simpa [Function.comp_def] using
        (MeasureTheory.Measure.map_map cognitiveCoordinate_measurable
          measurable_snd).symm
    _ = (MeasureTheory.Measure.dirac
          (c6C1C3CenterSamplingAdapter.completeState n)).map
          cognitiveCoordinate := by
      rw [c6C1C3C4A7SamplePathJointLaw_c1_sample_marginal]
    _ = _ := by
      rw [MeasureTheory.Measure.map_dirac' cognitiveCoordinate_measurable,
        c6C1C3CenterSample_eq_A7StageCenter]

/-- C1中心サンプルと全stage stitched trajectoryを同じ確率空間に載せる。 -/
noncomputable def c6C1C3C4A7GlobalPathJointLaw
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure C6C1C3C4A7GlobalPathObservation :=
  (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map
    (fun z => (z, c3A7StitchedTrajectory))

/-- 大域A7 path lawから、元のC1/C2/C4/C5介入観測座標を取り出す射影。 -/
def c6C1C4ObservationFromGlobalPath
    (z : C6C1C3C4A7GlobalPathObservation) := z.1.1.1.1.1

/-- 全path lawを元の介入観測へ射影すると、既存のC1/C2/C4/C5 lawへ戻る。
stage端点・サンプル・全pathの追加はSCM観測周辺を変えない。 -/
theorem c6C1C3C4A7GlobalPathJointLaw_C1C4_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ).map
        c6C1C4ObservationFromGlobalPath =
      c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ) := by
  rw [c6C1C3C4A7GlobalPathJointLaw,
    c6C1C3C4A7SamplePathJointLaw,
    c6C1C3C4A7PathJointLaw,
    c6C1C3C4CoreStageJointLaw]
  rw [MeasureTheory.Measure.map_map (by
      unfold c6C1C4ObservationFromGlobalPath
      fun_prop) (by fun_prop)]
  rw [MeasureTheory.Measure.map_map (by
      unfold c6C1C4ObservationFromGlobalPath
      fun_prop) (by fun_prop)]
  rw [MeasureTheory.Measure.map_map (by
      unfold c6C1C4ObservationFromGlobalPath
      fun_prop) (by fun_prop)]
  rw [MeasureTheory.Measure.map_map (by
      unfold c6C1C4ObservationFromGlobalPath
      fun_prop) (by fun_prop)]
  have hcomp :
      (fun z => c6C1C4ObservationFromGlobalPath
        ((((z, (c3A7StageTrajectory n
          (Tomabechi.Consistency.C3.stageTime n),
          c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n +
            Tomabechi.Consistency.C3.stageDuration n))),
          c3A7StageTrajectory n),
          c6C1C3CenterSamplingAdapter.completeState n),
          c3A7StitchedTrajectory)) = Prod.fst := by
    funext z
    rfl
  change (c6C1C3C4JointLaw x t₀ t T τ).map
    (fun z => c6C1C4ObservationFromGlobalPath
      ((((z, (c3A7StageTrajectory n
        (Tomabechi.Consistency.C3.stageTime n),
        c3A7StageTrajectory n (Tomabechi.Consistency.C3.stageTime n +
          Tomabechi.Consistency.C3.stageDuration n))),
        c3A7StageTrajectory n),
        c6C1C3CenterSamplingAdapter.completeState n),
        c3A7StitchedTrajectory)) = _
  rw [hcomp, c6C1C3C4JointLaw_c1C4C5_marginal]

/-- 元の25-C3 SCMの外生法則から直接押し出す、C1/C2・SCM・C5実費用の観測law。 -/
noncomputable def c6C1C4ActualSCMObservationLaw
    (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.Measure
      (C6C1ObservedState ×
        ((Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma × Bool) ×
          (Bool × C6C5ControlledState × ℝ))) :=
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
          ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u))))

/-- A7全path lawのC1/C2・SCM・C5実費用観測は、同じ無作為化25-C3 SCMの
外生法則から直接得るjoint lawと一致する。 -/
theorem c6C1C3C4A7GlobalPathJointLaw_eq_actualSCMLaw
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ).map
        c6C1C4ObservationFromGlobalPath =
      c6C1C4ActualSCMObservationLaw x t₀ t T τ := by
  calc
    _ = c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ) :=
      c6C1C3C4A7GlobalPathJointLaw_C1C4_marginal n x t₀ t T τ
    _ = c6C1C4ActualSCMObservationLaw x t₀ t T τ := by
      simpa [c6C1C4ActualSCMObservationLaw] using
        c6C1C4JointObservationLaw_eq_randomizedActualSCMLaw x t₀ t T τ

theorem c6C1C3C4A7GlobalPathJointLaw_isProbability
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    MeasureTheory.IsProbabilityMeasure
      (c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ) := by
  rw [c6C1C3C4A7GlobalPathJointLaw,
    MeasureTheory.Measure.isProbabilityMeasure_map_iff]
  · exact c6C1C3C4A7SamplePathJointLaw_isProbability n x t₀ t T τ
  · exact (by fun_prop)

theorem c6C1C3C4A7GlobalPathJointLaw_sample_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ).map Prod.fst =
      c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ := by
  rw [c6C1C3C4A7GlobalPathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map id = _
  rw [MeasureTheory.Measure.map_id]

theorem c6C1C3C4A7GlobalPathJointLaw_trajectory_evaluation
    (n : ℕ) (x : AgentState) (t₀ t T τ s : ℝ) :
    (c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ).map
      (fun z => z.2 s) = MeasureTheory.Measure.dirac
        (c3A7StitchedTrajectory s) := by
  rw [c6C1C3C4A7GlobalPathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ).map
    (fun _ => c3A7StitchedTrajectory s) = _
  rw [MeasureTheory.Measure.map_const]
  have hprob := c6C1C3C4A7SamplePathJointLaw_isProbability n x t₀ t T τ
  simp [hprob.measure_univ]

theorem c6C1C3C4A7PathJointLaw_stageEvaluation
    (n : ℕ) (x : AgentState) (t₀ t T τ s : ℝ) :
    (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
      (fun z => z.2 s) = MeasureTheory.Measure.dirac (c3A7StageTrajectory n s) := by
  rw [c6C1C3C4A7PathJointLaw,
    MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
  change (c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map
    (fun _ => c3A7StageTrajectory n s) = _
  rw [MeasureTheory.Measure.map_const]
  have hprob := c6C1C3C4CoreStageJointLaw_isProbability n x t₀ t T τ
  simp [hprob.measure_univ]

theorem c6C1C3C4A7PathJointLaw_entropyEvaluation
    (n : ℕ) (x : AgentState) (t₀ t T τ s : ℝ) :
    (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
      (fun z => entropyObservedElapsed (z.2 s)) =
      MeasureTheory.Measure.dirac (3 * s) := by
  calc
    _ = ((c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
          (fun z => z.2 s)).map entropyObservedElapsed := by
      simpa [Function.comp_def] using
        (MeasureTheory.Measure.map_map entropyObservedElapsed_measurable
          ((measurable_pi_apply s).comp measurable_snd)).symm
    _ = (MeasureTheory.Measure.dirac (c3A7StageTrajectory n s)).map
          entropyObservedElapsed := by
      rw [c6C1C3C4A7PathJointLaw_stageEvaluation]
    _ = MeasureTheory.Measure.dirac (3 * s) := by
      rw [MeasureTheory.Measure.map_dirac' entropyObservedElapsed_measurable,
        c3A7StageTrajectory_entropyObserved]

theorem c6C1C3C4A7PathJointLaw_cognitiveEvaluation
    (n : ℕ) (x : AgentState) (t₀ t T τ s : ℝ) :
    (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
      (fun z => cognitiveCoordinate (z.2 s)) =
      MeasureTheory.Measure.dirac
        (Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit
          (Tomabechi.Consistency.C3.representation (n + 1 : ℕ))
          (Tomabechi.Consistency.C3.valleySequence n).initial
          (Tomabechi.Consistency.C3.stageTime n) s) := by
  calc
    _ = ((c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
          (fun z => z.2 s)).map cognitiveCoordinate := by
      simpa [Function.comp_def] using
        (MeasureTheory.Measure.map_map cognitiveCoordinate_measurable
          (by fun_prop)).symm
    _ = (MeasureTheory.Measure.dirac (c3A7StageTrajectory n s)).map
          cognitiveCoordinate := by
      rw [c6C1C3C4A7PathJointLaw_stageEvaluation]
    _ = _ := by
      rw [MeasureTheory.Measure.map_dirac' cognitiveCoordinate_measurable,
        c3A7StageTrajectory_cognitive]

/-- A7 stage path lawで、同時に観測されるC3の情報joint座標。 -/
theorem c6C1C3C4A7PathJointLaw_c3_marginal
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    (c6C1C3C4A7PathJointLaw n x t₀ t T τ).map
      (fun z => z.1.1.2) = Tomabechi.Consistency.C3.upperJoint := by
  calc
    _ = ((c6C1C3C4A7PathJointLaw n x t₀ t T τ).map Prod.fst).map
          (fun z => z.1.2) := by
      simpa [Function.comp_def] using
        (MeasureTheory.Measure.map_map
          (measurable_snd.comp measurable_fst) measurable_fst).symm
    _ = (c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map
          (fun z => z.1.2) := by
      rw [c6C1C3C4A7PathJointLaw_observation_marginal]
    _ = (c6C1C3C4JointLaw x t₀ t T τ).map Prod.snd := by
      calc
        _ = ((c6C1C3C4CoreStageJointLaw n x t₀ t T τ).map Prod.fst).map
              Prod.snd := by
          simpa [Function.comp_def] using
            (MeasureTheory.Measure.map_map measurable_snd measurable_fst).symm
        _ = _ := by
          rw [c6C1C3C4CoreStageJointLaw_observation_marginal]
    _ = Tomabechi.Consistency.C3.upperJoint :=
      c6C1C3C4JointLaw_c3_marginal x t₀ t T τ

/-- C4の履歴flowと正準TCZ・全層carrierを、共通制御核と同じ制御データへ結ぶ。
固定点の位相・完備性・縮小率の全署名は別途必要である。 -/
structure C6C4FlowTCZAdapter where
  /-- 各履歴・全初期状態のC4勾配flowを共有核の中心更新から回収する。 -/
  history_flow_projection : ∀ (h : Bool) (x y t E : ℝ),
    cognitiveCoordinate
        (centeredGainEntropyStep
          (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) t E (x, y)) =
      Tomabechi.Theorem16_25.theorem16_intervalGradientFlow h x t
  /-- C4の正準TCZは履歴ごとの全Nat carrierに等しい。 -/
  canonical_tcz_eq_carrier : ∀ h : Bool,
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ h =
      Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h 0
  /-- 層ごとのTCZとcarrierの等式を元の全Nat添字で保持する。 -/
  every_layer_carrier_eq_tcz : ∀ (h : Bool) (i : ℕ),
    Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier h i =
      Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ h
  /-- 同じ履歴別SC固定点を保持し、履歴で値が分かれることを明示する。 -/
  fixed_point_system : Tomabechi.Theorem16_25.HistoryFixedPoints Bool
    (∀ i : Nat, ℝ)
  fixed_point_system_is_c4_system : fixed_point_system =
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points
  fixed_points_separate :
    (fixed_point_system.fixedPoint false).1 ≠
      (fixed_point_system.fixedPoint true).1
  /-- 固定点の全座標が共通層の履歴表象を復元する。 -/
  fixed_point_common_profile : ∀ h : Bool,
    (fixed_point_system.fixedPoint h).1 = commonHistoryProfile h
  /-- 固定点をC3のΓ codeへ入れると、25共有SCMの関係状態になる。 -/
  fixed_point_encodes_shared_gamma : ∀ (d a h : Bool),
    Tomabechi.Theorem16_25.theorem25_intervalGradientFlowStateCode d a
        (fixed_point_system.fixedPoint h).1 =
      (Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations).relationalState
        d h a
  /-- 引戻し距離から得るisometryと積部分空間位相のhomeomorphは同じ写像である。 -/
  metric_topology_agrees_with_product : ∀ h : Bool,
    letI : MetricSpace (Tomabechi.Consistency.C4.C4InverseLimit h) :=
      Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric h
    (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitIsometryEquiv h).toEquiv =
      (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitHomeomorph h).toEquiv
  /-- 同じSC距離上でC4の逆極限が完備である。 -/
  inverse_limit_complete : ∀ h : Bool,
    @CompleteSpace (Tomabechi.Consistency.C4.C4InverseLimit h)
      (Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric h).toPseudoMetricSpace.toUniformSpace
  /-- 同じ距離・同じ層作用素が率exp(-1)で縮小する。 -/
  inverse_limit_feedback_contracting : ∀ h : Bool,
    letI : MetricSpace (Tomabechi.Consistency.C4.C4InverseLimit h) :=
      Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric h
    ContractingWith ⟨Real.exp (-1), le_of_lt (Real.exp_pos _)⟩
      (Tomabechi.Theorem16_25.historyInducedAffineInverseLimitMap
        (fun _ : Nat => ℝ)
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.carrier
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.project
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.projectMaps
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.feedback
        Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem.feedbackCommutes h)

noncomputable def c6C4FlowTCZAdapter : C6C4FlowTCZAdapter where
  history_flow_projection := centeredGainEntropyStep_projects_C4_history_flow
  canonical_tcz_eq_carrier := by
    intro h
    rw [Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ_eq_carrier]
    rfl
  every_layer_carrier_eq_tcz :=
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ
  fixed_point_system :=
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points
  fixed_point_system_is_c4_system := rfl
  fixed_points_separate :=
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_generatedFixedPoints_separate
  fixed_point_common_profile :=
    Tomabechi.Consistency.C6.c4_generatedFixedPoint_eq_commonHistoryProfile
  fixed_point_encodes_shared_gamma :=
    Tomabechi.Consistency.C6.c4_generatedFixedPoint_encodes_sharedGamma
  metric_topology_agrees_with_product :=
    Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_metric_product_coordinate_maps_agree
  inverse_limit_complete := by
    intro h
    let metric := Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric h
    letI : MetricSpace (Tomabechi.Consistency.C4.C4InverseLimit h) := metric
    exact (Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitIsometryEquiv h).completeSpace
  inverse_limit_feedback_contracting := by
    intro h
    letI : MetricSpace (Tomabechi.Consistency.C4.C4InverseLimit h) :=
      Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric h
    exact Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimit_contracting h

theorem c6C4FlowTCZAdapter_nonempty : Nonempty C6C4FlowTCZAdapter :=
  ⟨c6C4FlowTCZAdapter⟩

/-- C1–C5の異なる評価量を、係数・baselineを保って共通二次評価または
完全状態entropy生成へ結ぶS2の部分adapter。 -/
structure C6CommonPotentialAdapter where
  /-- C1定理1評価。閾値baseline 1と残差係数16を保つ。 -/
  c1_theorem1_evaluation : ∀ (x : AgentState) (hx : x ∈ box) (t : ℝ),
    consensusV0 x t =
      1 + 16 * centeredQuadraticPotential 1 (c1ToCompleteState x)
  /-- 有限層にC1評価を置く候補において、最大ゲインの割引費用は
  全許容可測ゲインの費用を各時刻で下回る。 -/
  c1_finite_layer_discounted_cost_minimal :
    ∀ (x : AgentState) (T s : ℝ) (u : C1GainSignal), T ≤ s →
      Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T c1MaxGainSignal s)) ^ 2) ≤
        Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (1 + 8 * (halfDifference
            (controlledConsensusState x T u s)) ^ 2)
  /-- C2の完全状態上の一般化entropy生成率1。 -/
  c2_generalized_entropy_production : ∀ (z : CompleteState) (t : ℝ),
    Tomabechi.Consistency.C2.generalizedEntropy (completeEntropyFlow z t) =
      Tomabechi.Consistency.C2.generalizedEntropy z + t
  /-- 元H-stageの段評価を、その段の共通束表象へ同定する。 -/
  c3_stage_potential : ∀ (n : ℕ) (z : CompleteState),
    Tomabechi.Theorem22.stageEffectivePotential
        (Tomabechi.Consistency.C3.hStageSequence n).toStageValleySpec
        (cognitiveCoordinate z) =
      centeredQuadraticPotential
        (Tomabechi.Consistency.C3.representation (n + 1 : ℕ)) z
  /-- C4履歴ごとのポテンシャルを共通二次評価へ同定する。 -/
  c4_history_potential : ∀ (h : Bool) (z : CompleteState),
    centeredQuadraticPotential
        (Tomabechi.Theorem16_25.theorem16_intervalGradientCenter h) z =
      Tomabechi.Theorem16_25.theorem16_intervalGradientPotential h
        (cognitiveCoordinate z)
  /-- C5上位running costは係数6の共通二次評価。 -/
  c5_running_cost : ∀ (z : CompleteState)
      (π : Tomabechi.Examples.Theorem27.VectorSourcePolicy true) (t : ℝ),
    Tomabechi.Examples.Theorem27.vectorSourceData.runningCost true π
        (disagreementStateTo27 z) t = 6 * centeredQuadraticPotential 1 z
  /-- C5上位optimal valueは係数2の共通二次評価。 -/
  c5_optimal_value : ∀ (z : CompleteState) (t : ℝ),
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
        (disagreementStateTo27 z) t = 2 * centeredQuadraticPotential 1 z

theorem c6CommonPotentialAdapter : C6CommonPotentialAdapter where
  c1_theorem1_evaluation := c1V0_eq_baseline_add_centeredPotential
  c1_finite_layer_discounted_cost_minimal :=
    c1FiniteLayer_discounted_cost_minimal_pointwise
  c2_generalized_entropy_production := generalizedEntropy_completeEntropyFlow
  c3_stage_potential := centeredQuadraticPotential_eq_C3_stage
  c4_history_potential := centeredQuadraticPotential_eq_C4
  c5_running_cost := c5RunningCost_eq_six_centeredPotential
  c5_optimal_value := c5OptimalValue_eq_two_centeredPotential

theorem c6CommonPotentialAdapter_nonempty : Nonempty C6CommonPotentialAdapter :=
  ⟨c6CommonPotentialAdapter⟩

/-- C1/C2/C4/C5観測とC3情報lawを保ち、元H-stage全pathのA7収支も満たす
段nの結合law adapter。C3/C4の共通law証人にはN4/N6等の既存条件が含まれる。 -/
structure C6C1C3C4A7PathLawAdapter
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) where
  law : MeasureTheory.Measure C6C1C3C4A7PathObservation
  law_is_path_pushforward : law = c6C1C3C4A7PathJointLaw n x t₀ t T τ
  probability : MeasureTheory.IsProbabilityMeasure law
  endpoint_stage_observation_marginal :
    law.map Prod.fst = c6C1C3C4CoreStageJointLaw n x t₀ t T τ
  c3_information_marginal :
    law.map (fun z => z.1.1.2) = Tomabechi.Consistency.C3.upperJoint
  c3c4_source_adapter : C6C3C4CommonLawAdapter n
  shared_potential_adapter : C6CommonPotentialAdapter
  c4_flow_tcz_adapter : C6C4FlowTCZAdapter
  c1_c2_c5_box_preservation : ∀ (y : AgentState) (hy : y ∈ box)
    (s₀ s : ℝ) (hs₀ : 0 ≤ s₀) (h₀s : s₀ ≤ s),
      Nonempty (C6C1C5Adapter y hy s₀ s hs₀ h₀s)
  /-- 同じC1 box-contextごとの元argminとC5実feedback最適性を、保存式と一体化して保持。 -/
  c1_c2_c5_optimality_preservation : ∀ (y : AgentState) (hy : y ∈ box)
    (s₀ s : ℝ) (hs₀ : 0 ≤ s₀) (h₀s : s₀ ≤ s),
      Nonempty (C6C1C5OptimalityAdapter y hy s₀ s hs₀ h₀s)
  /-- N7で参照するC1/C2/C3/C4/C5各contextの実際の非空証拠を一括する。 -/
  n7_context_families_nonempty :
    (∀ (y : AgentState) (hy : y ∈ box) (s₀ s : ℝ)
      (hs₀ : 0 ≤ s₀) (h₀s : s₀ ≤ s),
        Nonempty (C6C1C5Adapter y hy s₀ s hs₀ h₀s)) ∧
    (∀ h : Bool, Nonempty (C6C4C5ControlAdapter h)) ∧
    (∀ k : ℕ, Nonempty (C6C3InformationAdapter k)) ∧
    (∀ k : ℕ, Nonempty (C6C3CoreStageAdapter k))
  c1_c3_center_sample_time_diverges :
    Tendsto c6C1C3CenterSamplingAdapter.sampleTime atTop atTop
  c1_c3_center_sample_reaches_H_stage : ∀ k : ℕ,
    1 - halfDifference
        (Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness.selectedFlow.flow 0
          ![(1 / 4 : ℝ), -(1 / 4 : ℝ)]
          (c6C1C3CenterSamplingAdapter.sampleTime k)) =
      (Tomabechi.Consistency.C3.hStageSequence (k + 2)).center
  c1_c3_center_sample_C5_value_gap : ∀ k : ℕ, ∀ s : ℝ,
    Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState k)) s =
      (1 / ((k : ℝ) + 4)) ^ 2
  c1_c3_center_sample_C5_value_positive : ∀ k : ℕ, ∀ s : ℝ,
    0 < Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
      (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState k)) s
  c1_c3_center_sample_C5_value_tends_to_zero : ∀ s : ℝ,
    Tendsto
      (fun k : ℕ =>
        Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true
          (disagreementStateTo27 (c6C1C3CenterSamplingAdapter.completeState k)) s)
      atTop (nhds 0)
  stage_c1_gain : Tomabechi.Consistency.ConsistencyC1.C1GainSignal
  stage_c1_gain_eq_candidate : stage_c1_gain = c3A7StageC1Gain n
  stage_c1_cognitive_flow_match : ∀ s : ℝ,
    Tomabechi.Consistency.C3.stageTime n ≤ s →
      Tomabechi.Consistency.ConsistencyC1.c1ControlledState 1
        (cognitiveCoordinate (c3A7StageInitial n))
        (Tomabechi.Consistency.C3.stageTime n) stage_c1_gain s =
        cognitiveCoordinate (c3A7StageTrajectory n s)
  stitched_c1_gain : Tomabechi.Consistency.ConsistencyC1.C1GainSignal
  stitched_c1_gain_eq : stitched_c1_gain = c3A7StitchedC1Gain
  stitched_gain_agrees_on_stage : ∀ s : ℝ,
    s ∈ Set.Ico (Tomabechi.Consistency.C3.stageTime n)
      (Tomabechi.Consistency.C3.stageTime (n + 1)) →
      stitched_c1_gain.1 s = stage_c1_gain.1 s
  stitched_c1_global_cognitive_match : ∀ s : ℝ, 0 ≤ s →
    Tomabechi.Consistency.ConsistencyC1.c1ControlledState 1 0 0
      stitched_c1_gain s = cognitiveCoordinate (c3A7StitchedTrajectory s)
  sampled_center_path_law : MeasureTheory.Measure C6C1C3C4A7SamplePathObservation
  sampled_center_path_law_eq : sampled_center_path_law =
    c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ
  sampled_center_path_probability :
    MeasureTheory.IsProbabilityMeasure sampled_center_path_law
  sampled_center_path_marginal : sampled_center_path_law.map Prod.fst = law
  sampled_center_cognitive_marginal :
    sampled_center_path_law.map (fun z => cognitiveCoordinate z.2) =
      MeasureTheory.Measure.dirac
        (Tomabechi.Consistency.C3.representation (n + 3 : ℕ))
  global_path_law : MeasureTheory.Measure C6C1C3C4A7GlobalPathObservation
  global_path_law_eq : global_path_law =
    c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ
  global_path_probability : MeasureTheory.IsProbabilityMeasure global_path_law
  global_path_sample_marginal :
    global_path_law.map Prod.fst =
      c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ
  global_path_C1C4_observation_law :
    global_path_law.map c6C1C4ObservationFromGlobalPath =
      c4RandomizedInputLaw.map (c6C1C4JointObservation x t₀ t T τ)
  global_path_actual_scm_observation_law :
    global_path_law.map c6C1C4ObservationFromGlobalPath =
      c6C1C4ActualSCMObservationLaw x t₀ t T τ
  c4_randomized_history_law_is_source_scm_law :
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory
  c4_randomized_history_ri_preserves_source_law :
    ((c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c4OutputLaw).map
      Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations.roleInverse =
        (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.c5LayerLaw
  c4_randomized_candidate_has_positive_mass : ∀ s : Bool,
    Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.candidateHasPositiveMass
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.toIndexed)
      false false s
  c4_randomized_self_process_satisfies_25A2 :
    (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedSelfProcessSCM).toLawModel.Condition25A2 ()
  c4_intervention_control_cost_joint_law : ∀ (d a s : Bool) (T t : ℝ),
    (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
      (c4RandomizedInputToC6Intervened d a s)).map
        (c4C6IntervenedJointControlOutcome T t) =
      ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.exogenousLaw.toMeasure).map
        (fun u =>
          (((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.stateEquation
              d a
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
              u,
            (Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.outputEquation
              d a
              ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)
              u s),
          c6C4C5JointControlOutcome T t
            ((Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model).model.scm.globalHistory u)))
  global_path_evaluation : ∀ s : ℝ,
    global_path_law.map (fun z => z.2 s) =
      MeasureTheory.Measure.dirac (c3A7StitchedTrajectory s)
  c4_true_control : C6C4C5UpperControlAdapter
    Tomabechi.Examples.Theorem27Op.e0
  c4_true_control_address_is_history :
    c4_true_control.commonAddress = operationalLayerAddress true
  c4_true_control_N5_mixed_target_witness :
    ∃ x : Tomabechi.Examples.Theorem27Op.E2,
      x ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
      x ∈ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
        Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
        (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) 0 ∧
      c4_true_control.state ∈ Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive ∧
      c4_true_control.state ∉ Tomabechi.Theorem24_26.theorem26ZeroValueTarget
        Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
        (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue true) 0
  c4_true_global_flow_nonconstant :
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
      c4_true_control.policy c4_true_control.state 0 0 ≠
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory true
      c4_true_control.policy c4_true_control.state 0 3
  global_path_C5_optimal_flow : ∀ s : ℝ, 0 ≤ s →
    entropyStateTo27 (c3A7StitchedTrajectory s) =
      Tomabechi.Examples.Theorem27.vectorSourceData.trajectory
        true c4_true_control.policy c4_true_control.state 0 (3 * s)
  global_path_C5_alive : ∀ s : ℝ, 0 ≤ s →
    Tomabechi.Examples.Theorem27.vectorSourceData.trajectory
      true c4_true_control.policy c4_true_control.state 0 (3 * s) ∈
        Tomabechi.Examples.Theorem27.vectorSourceDynamics.alive
  global_path_generalized_entropy : ∀ s : ℝ,
    global_path_law.map (fun z => generalizedEntropy (z.2 s)) =
      MeasureTheory.Measure.dirac (1 + 3 * s)
  stitched_path_injective : Function.Injective c3A7StitchedTrajectory
  stage_A7_balance : ∀ s : ℝ,
    deriv (fun r => physicalEntropy (c3A7StageTrajectory n r)) s =
      -(∑' k : PositiveLayer, layerWeight k *
        deriv (fun r => layerEntropy k (c3A7StageTrajectory n r)) s) + 3
  stage_restart : ∀ᵐ z ∂c6C1C3C4CoreStageJointLaw n x t₀ t T τ,
    z.2.2 = c3A7StageTrajectory (n + 1)
      (Tomabechi.Consistency.C3.stageTime (n + 1))

noncomputable def c6C1C3C4A7PathLawAdapter
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    C6C1C3C4A7PathLawAdapter n x t₀ t T τ where
  law := c6C1C3C4A7PathJointLaw n x t₀ t T τ
  law_is_path_pushforward := rfl
  probability := c6C1C3C4A7PathJointLaw_isProbability n x t₀ t T τ
  endpoint_stage_observation_marginal :=
    c6C1C3C4A7PathJointLaw_observation_marginal n x t₀ t T τ
  c3_information_marginal :=
    c6C1C3C4A7PathJointLaw_c3_marginal n x t₀ t T τ
  c3c4_source_adapter := c6C3C4CommonLawAdapter n
  shared_potential_adapter := c6CommonPotentialAdapter
  c4_flow_tcz_adapter := c6C4FlowTCZAdapter
  c1_c2_c5_box_preservation := by
    intro y hy s₀ s hs₀ h₀s
    exact ⟨c6C1C5Adapter y hy s₀ s hs₀ h₀s⟩
  c1_c2_c5_optimality_preservation := by
    intro y hy s₀ s hs₀ h₀s
    exact ⟨c6C1C5OptimalityAdapter y hy s₀ s hs₀ h₀s⟩
  n7_context_families_nonempty := by
    let common := c6C3C4CommonLawAdapter 0
    refine ⟨?_, common.c4_controls, common.c3_all_stages_nonempty, ?_⟩
    · intro y hy s₀ s hs₀ h₀s
      exact ⟨c6C1C5Adapter y hy s₀ s hs₀ h₀s⟩
    · exact c6C3CoreStageAdapter_nonempty
  c1_c3_center_sample_time_diverges :=
    c6C1C3CenterSamplingAdapter_tendsto_atTop
  c1_c3_center_sample_reaches_H_stage := fun k =>
    c6C1C3CenterSamplingAdapter_reaches k
  c1_c3_center_sample_C5_value_gap := fun k s =>
    c6C1C3_sample_C5_value_eq_layerGap k s
  c1_c3_center_sample_C5_value_positive := fun k s =>
    c6C1C3_sample_C5_value_pos k s
  c1_c3_center_sample_C5_value_tends_to_zero :=
    c6C1C3_sample_C5_value_tendsto_zero
  stage_c1_gain := c3A7StageC1Gain n
  stage_c1_gain_eq_candidate := rfl
  stage_c1_cognitive_flow_match := fun s hs =>
    c3A7StageC1Gain_matches_C1_trajectory n s hs
  stitched_c1_gain := c3A7StitchedC1Gain
  stitched_c1_gain_eq := rfl
  stitched_gain_agrees_on_stage := fun s hs => by
    rw [c3A7StitchedC1Gain_eq_stage n s hs]
  stitched_c1_global_cognitive_match := fun s hs =>
    c3A7StitchedC1Gain_matches_global_C1_trajectory s hs
  sampled_center_path_law := c6C1C3C4A7SamplePathJointLaw n x t₀ t T τ
  sampled_center_path_law_eq := rfl
  sampled_center_path_probability :=
    c6C1C3C4A7SamplePathJointLaw_isProbability n x t₀ t T τ
  sampled_center_path_marginal := by
    calc
      _ = c6C1C3C4A7PathJointLaw n x t₀ t T τ :=
        c6C1C3C4A7SamplePathJointLaw_path_marginal n x t₀ t T τ
      _ = c6C1C3C4A7PathJointLaw n x t₀ t T τ := rfl
  sampled_center_cognitive_marginal :=
    c6C1C3C4A7SamplePathJointLaw_c1_center_marginal n x t₀ t T τ
  global_path_law := c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ
  global_path_law_eq := rfl
  global_path_probability :=
    c6C1C3C4A7GlobalPathJointLaw_isProbability n x t₀ t T τ
  global_path_sample_marginal :=
    c6C1C3C4A7GlobalPathJointLaw_sample_marginal n x t₀ t T τ
  global_path_C1C4_observation_law :=
    c6C1C3C4A7GlobalPathJointLaw_C1C4_marginal n x t₀ t T τ
  global_path_actual_scm_observation_law :=
    c6C1C3C4A7GlobalPathJointLaw_eq_actualSCMLaw n x t₀ t T τ
  c4_randomized_history_law_is_source_scm_law :=
    (c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls).1
  c4_randomized_history_ri_preserves_source_law :=
    (c6C4C5LayerControlLawAdapter c4RandomizedInputLaw).historyLaw.lawAdapter.ri_preserves_c5_law
  c4_randomized_candidate_has_positive_mass :=
    (c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls).2.2.1
  c4_randomized_self_process_satisfies_25A2 :=
    (c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls).2.2.2
  c4_intervention_control_cost_joint_law :=
    c4RandomizedIntervenedJointControlOutcomeLaw_eq_actualModelLaw
  global_path_evaluation := fun s =>
    c6C1C3C4A7GlobalPathJointLaw_trajectory_evaluation n x t₀ t T τ s
  c4_true_control := c6C4C5UpperControlAdapter
    Tomabechi.Examples.Theorem27Op.e0
  c4_true_control_address_is_history := rfl
  c4_true_control_N5_mixed_target_witness := by
    rcases c6_N5_C5LayerTarget_nonempty 0 (by norm_num) with
      ⟨_, x, _, hx_alive, _, hx_target, _⟩
    refine ⟨x, hx_alive, hx_target, Set.mem_univ _, ?_⟩
    change Tomabechi.Examples.Theorem27Op.e0 ∉
      Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (Tomabechi.Examples.Theorem27.vectorSourceData.optimalValue
          (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction)) 0
    rw [Tomabechi.Examples.Theorem27.vectorSourceTargetTop_eq_ring,
      c5_e0_eq_vec_one_zero]
    exact Tomabechi.Consistency.C5.active_state_outside_target 0
  c4_true_global_flow_nonconstant := by
    simpa [c6C4C5UpperControlAdapter] using
      c3A7StitchedTrajectory_C5_flow_nonconstant
  global_path_C5_optimal_flow := by
    intro s hs
    simpa [c6C4C5UpperControlAdapter] using
      c3A7StitchedTrajectory_matches_C5_upper_optimalFlow s hs
  global_path_C5_alive := by
    intro s hs
    exact Tomabechi.Examples.Theorem27.vectorSourceDynamics.trajectory_alive
      (c6C4C5UpperControlAdapter Tomabechi.Examples.Theorem27Op.e0).state
      0 (3 * s) (by norm_num)
      (Set.mem_univ _) (by linarith)
  global_path_generalized_entropy := fun s => by
    have hgen : Measurable generalizedEntropy := by
      have hform : generalizedEntropy =
          (fun z : CompleteState => 1 + entropyObservedElapsed z) := by
        funext z
        rw [generalizedEntropy_eq_observedElapsed]
      rw [hform]
      exact measurable_const.add entropyObservedElapsed_measurable
    calc
      _ = ((c6C1C3C4A7GlobalPathJointLaw n x t₀ t T τ).map
            (fun z => z.2 s)).map generalizedEntropy := by
        simpa [Function.comp_def] using
          (MeasureTheory.Measure.map_map hgen
            (by fun_prop : Measurable (fun z : C6C1C3C4A7GlobalPathObservation => z.2 s))).symm
      _ = (MeasureTheory.Measure.dirac (c3A7StitchedTrajectory s)).map
            generalizedEntropy := by
        rw [c6C1C3C4A7GlobalPathJointLaw_trajectory_evaluation]
      _ = MeasureTheory.Measure.dirac (1 + 3 * s) := by
        rw [MeasureTheory.Measure.map_dirac' hgen,
          c3A7StitchedTrajectory_generalizedEntropy]
  stitched_path_injective := c3A7StitchedTrajectory_injective
  stage_A7_balance := fun s => c3A7StageTrajectory_satisfies_A7 n s
  stage_restart := c6C1C3C4CoreStageJointLaw_restart_ae n x t₀ t T τ

theorem c6C1C3C4A7PathLawAdapter_nonempty
    (n : ℕ) (x : AgentState) (t₀ t T τ : ℝ) :
    Nonempty (C6C1C3C4A7PathLawAdapter n x t₀ t T τ) :=
  ⟨c6C1C3C4A7PathLawAdapter n x t₀ t T τ⟩

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.c3A7Stitched_theorem15_23_nonrecurrence
