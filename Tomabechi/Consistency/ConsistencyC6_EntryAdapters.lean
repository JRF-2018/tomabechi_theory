import Tomabechi.Consistency.ConsistencyC6_FiniteUniqueness
import Tomabechi.Dynamics.InvariantRegion

/-!
# C6：受入済みの共有モデルから一般入口を呼ぶ

同じMの実段列・時刻・完全軌道・D/E・自己過程を用いる。
原文の全対象を一軌道へ押し込まず、箱内C1、凍結段、全履歴逆系、頂点の
適用域を保つ。中心contextの変更と完全状態の更新も区別する。
-/

noncomputable section
namespace Tomabechi.Consistency.C6
open Tomabechi.Consistency.ConsistencyC1
open Tomabechi.Consistency.ConsistencyC1Consensus
open Tomabechi.Consistency.ConsistencyC1CommonModel
open Tomabechi.Theorem22
open Tomabechi.Theorem24_26
open MeasureTheory Filter
open scoped Topology

/-- 元H-stageを満たす同じMから、不変領域版を既存変換で派生させる。
元の証人を緩和条件で置き換える構成ではない。 -/
def ModelSignature.relaxedStages (M : ModelSignature) (n : ℕ) :=
  Tomabechi.Theorem22InvariantRegion.MeanFieldStageInput.toInvariantRegionInput (M.stages n)

/-- 完全核の認知/物理状態に、C1で必要な保存平均を保持する。
平均を射影時に外部から注入せず、入力状態の第一成分から読む。 -/
def ModelSignature.meanStep (M : ModelSignature) (c A E : ℝ) (z : MeanCompleteState) :
    MeanCompleteState := (z.1, M.step c A E z.2)

def ModelSignature.meanFiniteProjection (M : ModelSignature) (c : ℝ)
    (z : MeanCompleteState) : AgentState := M.finiteProjection z.1 c z.2

/-- 同じ署名から定まる自律的な全状態核が、全有限層の全制御軌道を保存する。 -/
theorem AdditionalConditions.mean_state_controls {M : ModelSignature}
    (h : AdditionalConditions M) (k : ℕ) (c a t E : ℝ) (z : MeanCompleteState) (u : C1GainSignal) :
    (M.meanStep c (c1AccumulatedGain u a t) E z).1 = z.1 ∧
    M.meanFiniteProjection c (M.meanStep c (c1AccumulatedGain u a t) E z) =
      M.data.trajectory (some k) u (M.meanFiniteProjection c z) a t :=
  ⟨rfl, h.core_all_finite_controls k z.1 c a t E z.2 u⟩

/-- C1の全入口・O13・O24証拠はM自身のproof-bearingデータに含まれる。
selectedFlowの実D軌道との等式はAdditionalConditions.c1_selected_flowで別途供給する。 -/
def ModelSignature.c1Entries (M : ModelSignature) (x : AgentState) (hx : x ∈ box)
    (T H : ℝ) (hT : 0 ≤ T) (hH : 0 < H) : C1EntryConclusions x T H :=
  M.c1.allEntryConclusions x hx T H hT hH

/-- O01の有限層存在：半差のACと保存平均から全二主体状態のACを得る。 -/
theorem OriginalPremises.finite_control_ac {M : ModelSignature}
    (h : OriginalPremises M) (k : ℕ) (u : C1GainSignal) (x : AgentState)
    (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => M.data.trajectory (some k) u x a t) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => fun _ : Fin 2 => meanState x) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have he : AbsolutelyContinuousOnInterval (fun _ : ℝ => (![1, -1] : AgentState)) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hd := c1ControlledOrbit_absolutelyContinuousOnInterval (halfDifference x) a b hab u
  have heq : (fun t => M.data.trajectory (some k) u x a t) =
      fun t => (fun _ : Fin 2 => meanState x) +
        c1ControlledOrbit (halfDifference x) a u t • (![1, -1] : AgentState) := by
    funext t i
    rw [h.finite_control_solution]
    fin_cases i <;> simp [controlledConsensusState] <;> ring
  rw [heq]
  exact hc.add (hd.smul he)

/-- 全有限層・全可測競合の実二主体ODE。平均の保存と半差のa.e.微分を使う。 -/
theorem OriginalPremises.finite_control_ode {M : ModelSignature}
    (h : OriginalPremises M) (k : ℕ) (u : C1GainSignal) (x : AgentState)
    (a H : ℝ) (hH : 0 < H) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a (a + H)),
      HasDerivAt (fun s => M.data.trajectory (some k) u x a s)
        (M.c1.selectedFlow.vectorField (M.data.trajectory (some k) u x a t) (u.1 t) t) t := by
  filter_upwards [c1ControlledOrbit_ae_ode (halfDifference x) a H hH u] with t ht
  have hh := (hasDerivAt_const t (fun _ : Fin 2 => meanState x)).add
    (ht.smul_const (![1, -1] : AgentState))
  convert hh using 1
  · funext s i
    rw [h.finite_control_solution]
    fin_cases i <;> simp [controlledConsensusState] <;> ring
  · rw [M.c1.selectedFlow_eq_rate3, h.finite_control_solution]
    ext i
    fin_cases i <;> simp [consensusOptimalFlow, controlledConsensusState, meanState] <;> ring

/-- 時刻と入力を固定した有限層場は全状態上で滑らかなので局所Lipschitz。 -/
theorem ModelSignature.finite_field_locallyLipschitz (M : ModelSignature) (g t : ℝ) :
    LocallyLipschitz (fun x => M.c1.selectedFlow.vectorField x g t) := by
  rw [M.c1.selectedFlow_eq_rate3]
  have hc : ContDiff ℝ 1 (fun x => consensusOptimalFlow.vectorField x g t) := by
    apply contDiff_pi.2
    intro i
    fin_cases i <;> dsimp [consensusOptimalFlow, halfDifference] <;> fun_prop
  exact hc.locallyLipschitz

/-- 頂点の任意ゲインでも状態場は全域で滑らか。Borel方策一般への主張ではない。 -/
theorem c6TopGainField_locallyLipschitz
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) (t : ℝ) :
    LocallyLipschitz (c6TopGainField k t) := by
  have hc : ContDiff ℝ 1 (c6TopGainField k t) := by
    unfold c6TopGainField
    fun_prop
  exact hc.locallyLipschitz

/-- O01の頂点存在：全競合方策の実D軌道でACを保つ。 -/
theorem OriginalPremises.top_control_ac {M : ModelSignature}
    (h : OriginalPremises M) (π : C6LayeredPolicy ⊤) (x : C6TopState)
    (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => M.data.trajectory ⊤ π x a t) a b := by
  have heq := funext (h.top_control_solution π x a)
  rw [heq]
  exact Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_absolutelyContinuousOnInterval
    (x 0) (x 1) a b (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) hab

/-- O01の頂点存在：全競合方策の実D軌道は同じ可測ゲイン場のa.e.解である。 -/
theorem OriginalPremises.top_control_ode {M : ModelSignature}
    (h : OriginalPremises M) (π : C6LayeredPolicy ⊤) (x : C6TopState) (a : ℝ) :
    ∀ᵐ t : ℝ, HasDerivAt (fun s => M.data.trajectory ⊤ π x a s)
      (c6TopGainField (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π) t
        (M.data.trajectory ⊤ π x a t)) t := by
  rw [funext (h.top_control_solution π x a)]
  filter_upwards [Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_ae_ode
    (x 0) (x 1) a (Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain π)] with t ht
  convert ht using 1
  ext i
  fin_cases i <;> simp [c6TopGainField, Tomabechi.Examples.Theorem27.measurableGainVectorOrbit,
    Tomabechi.Examples.Theorem27.measurableGainInput, Tomabechi.Examples.Theorem27.vec,
    Tomabechi.Examples.Theorem27Op.e0_apply0, Tomabechi.Examples.Theorem27Op.e1_apply0,
    Tomabechi.Examples.Theorem27Op.e0_apply1, Tomabechi.Examples.Theorem27Op.e1_apply1,
    Tomabechi.Examples.Theorem27Op.omg] <;> ring

/-- 定理1の定量結論を、全有限層の実D選択軌道で読む。 -/
theorem AdditionalConditions.c1_distance {M : ModelSignature}
    (h : AdditionalConditions M) (k : ℕ) (x : AgentState) (hx : x ∈ box)
    (T t : ℝ) (hT : 0 ≤ T) (htt : T ≤ t) :
    Metric.infDist (M.data.trajectory (some k) M.c1.selectedGain x T t)
        (consensusOptimalTheorem1Target T t) ≤
      Real.sqrt (Tomabechi.Examples.Theorem2.DA.potential x T) * Real.exp (-3 * (t - T)) := by
  rw [← h.c1_selected_flow, M.c1.selectedFlow_eq_rate3]
  exact (M.c1Entries x hx T 1 hT (by norm_num)).theorem1_distance t htt

/-- 全非負時間域の15→23-Aを同じ完全pathへ適用する。 -/
theorem OriginalPremises.nonrecurrence {M : ModelSignature} (h : OriginalPremises M) :
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < b → M.completePath b ≠ M.completePath a :=
  h.entropy.nonrecurrence

/-- 保存平均を含む完全状態でも、同じ15→23収支から非再訪が得られる。 -/
theorem OriginalPremises.mean_nonrecurrence {M : ModelSignature} (h : OriginalPremises M)
    (m a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) :
    (m, M.completePath b) ≠ (m, M.completePath a) := by
  intro heq
  exact h.nonrecurrence a b ha hb hab (congrArg Prod.snd heq)

/-- 同じMの固定点族は、受入済み逆系の固定点族そのものである。 -/
theorem OriginalPremises.fixedPoints_eq_original {M : ModelSignature}
    (h : OriginalPremises M) :
    M.fixedPoints = Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points := by
  rcases h.inverse_limit with ⟨A, hA, _⟩
  exact hA.symm.trans A.fixed_point_system_is_c4_system

/-- 固定した全層容量の問題族は、Mが採用する情報lawと同じjoint/referenceを使う。
底層の零問題を全上層へ保存し、正情報問題を底層だけから除く。 -/
theorem AdditionalConditions.information_laws {M : ModelSignature}
    (h : AdditionalConditions M) :
    Tomabechi.Theorem19_22.directActionGoalJoint (M.informationLaw 0) =
      Tomabechi.Consistency.C3.physicalCMIPair.joint ∧
    (∀ n, Tomabechi.Theorem19_22.directActionGoalJoint (M.informationLaw (n + 1)) =
      Tomabechi.Consistency.C3.upperCMIPair.joint) ∧
    Monotone Tomabechi.Consistency.C3.c3LayerCapacity ∧
    Tomabechi.Consistency.C3.c3LayerCapacity ⊥ = 0 ∧
    0 < Tomabechi.Consistency.C3.c3LayerCapacity ⊤ := by
  refine ⟨?_, ?_, Tomabechi.Consistency.C3.c3_sharedWitness⟩
  · rw [h.physical_information]; rfl
  · intro n; rw [h.stage_information]; rfl

/-- 定理21の四結論。情報量はM自身の採用jointから計算する。
谷の一意性・変位・凍結ODE/指数率・正情報/枝帰属をすべて保持する。 -/
def c6Stage21Conclusion (s : MeanFieldStageInput ℝ) (n : ℕ) : Prop :=
  letI := Tomabechi.Consistency.C3.upperJoint_isProbability
    ∃ w : StageValleyWitness s.toStageValleySpec,
      (w.minimizer ∈ interior (Metric.closedBall s.center s.radius) ∧
        IsMinOn (stageEffectivePotential s.toStageValleySpec)
          (Metric.closedBall s.center s.radius) w.minimizer ∧
        (∀ y ∈ Metric.closedBall s.center s.radius,
          stageEffectivePotential s.toStageValleySpec y =
            stageEffectivePotential s.toStageValleySpec w.minimizer → y = w.minimizer)) ∧
      (‖w.minimizer - s.center‖ ≤
          s.gradientBound /
            (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) ∧
        (s.backgroundGradient w.minimizer -
          (s.gain * s.presenceGain) • s.meanFieldGradient w.minimizer = 0) ∧
        0 < s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) ∧
      (w.orbit s.startTime = s.initial ∧
        (∀ t ∈ Set.Ici s.startTime,
          w.orbit t ∈ s.sublevel ∧
          dist (w.orbit t) w.minimizer ≤
            w.decayAmplitude * Real.exp (-w.decayRate * (t - s.startTime))) ∧
        (∀ t, s.startTime ≤ t →
          HasDerivAt w.orbit
            (-(s.mobility (w.orbit t)
              (s.backgroundGradient (w.orbit t) -
                (s.gain * s.presenceGain) • s.meanFieldGradient (w.orbit t)))) t)) ∧
      ((InformationTheory.klDiv
          (Tomabechi.Theorem19_22.directActionGoalJoint Tomabechi.Consistency.C3.upperJoint)
          (Tomabechi.Theorem19_22.directCMIReference Tomabechi.Consistency.C3.upperJoint)).toReal =
            Tomabechi.Theorem21.conditionalGoalEntropy (Measure.dirac ())
              Tomabechi.Consistency.C3.inputMass ∧
        0 < (InformationTheory.klDiv
          (Tomabechi.Theorem19_22.directActionGoalJoint Tomabechi.Consistency.C3.upperJoint)
          (Tomabechi.Theorem19_22.directCMIReference Tomabechi.Consistency.C3.upperJoint)).toReal ∧
        (∀ᵐ x ∂(Measure.dirac ()), ∀ g : Bool,
          0 < Tomabechi.Consistency.C3.inputMass x g →
          ((n + 1 : ℕ) : CommonLayer) ∈ (Tomabechi.Consistency.C3.branchContext n).branch))


/-- 同じMの実jointとの等式を保持して、全段の21一般入口の四結論を取り出す。
局所情報量の結論だけを別lawへ移したものではない。 -/
theorem AdditionalConditions.theorem21 {M : ModelSignature}
    (h : AdditionalConditions M) (n : ℕ) :
    M.informationLaw (n + 1) = Tomabechi.Consistency.C3.upperJoint ∧
      c6Stage21Conclusion (M.stages n) n := by
  refine ⟨h.stage_information n, ?_⟩
  rw [h.original_stages]
  exact Tomabechi.Consistency.C3.stageInformation n

/-- 元のH-stageの全前件から、Mの実段列と実切替時刻で23-B一般入口を呼ぶ。
gap・線分・再始動・対数待ち条件を省かず、緩和版へ置き換えない。 -/
def AdditionalConditions.theorem23B {M : ModelSignature} (h : AdditionalConditions M) :=
  Tomabechi.Theorem23.meanField_stage_specs_and_switches_give_condition23B_core
    Tomabechi.Consistency.C3.layerU Tomabechi.Consistency.C3.layerV
    Tomabechi.Consistency.C3.layerU_update Tomabechi.Consistency.C3.layerU_below_top
    Tomabechi.Consistency.C3.layerV_new M.stages
    Tomabechi.Consistency.C3.representation Tomabechi.Consistency.C3.representation_injective
    (by rw [h.original_stages]; exact Tomabechi.Consistency.C3.hStageSequence_center)
    Tomabechi.Consistency.C3.stageTheta Tomabechi.Consistency.C3.stageTheta_nonneg
    (by rw [h.original_stages]; exact Tomabechi.Consistency.C3.hStageSequence_gap_threshold)
    (by rw [h.original_stages]; exact Tomabechi.Consistency.C3.hStageSequence_segment_in_next_ball)
    M.stageTime Tomabechi.Consistency.C3.stageDuration Tomabechi.Consistency.C3.errorTolerance
    h.stage_start
    (by
      rw [h.original_stages, h.original_stage_times]
      exact Tomabechi.Consistency.C3.hStageSequence_transition)
    (by simpa only [h.original_stage_times] using Tomabechi.Consistency.C3.stageTime_recurrence)
    Tomabechi.Consistency.C3.stageDuration_pos Tomabechi.Consistency.C3.stageTime_unbounded
    Tomabechi.Consistency.C3.errorTolerance_pos
    (by rw [h.original_stages]; exact Tomabechi.Consistency.C3.hStageSequence_wait_bound)

/-- 同じMのD/Eを24→26入口へそのまま渡す。全alive初期状態と全非負開始時刻を保つ。 -/
def ModelSignature.theorem24_26 (M : ModelSignature) :=
  theorem24_to26_from_nonnegativeTimeData M.data M.dynamics

/-- 27-A受入入力から同じMのD/Eを運用入口へ渡す。
全初期状態を量化し、参照場・実入力・随伴評価も同じ入力recordから取る。 -/
def OriginalPremises.theorem27 {M : ModelSignature} (h : OriginalPremises M)
    (x : C6TopState) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ M.dynamics.alive) :=
  Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := CommonLayer) (State := C6LayeredState) (Feedback := C6LayeredPolicy)
    (Control := C6TopState) rfl rfl M.data M.dynamics x T hT hx
    (fun y a s t ha has hst _ => (h.top_actuator x T hT).restart y a s t ha has hst)
    (Tomabechi.Examples.Theorem27Op.dWE x T) (Tomabechi.Examples.Theorem27Op.gradWE x T)
    (Tomabechi.Examples.Theorem27Op.driftE x T) (Tomabechi.Examples.Theorem27Op.u0E x T)
    (Tomabechi.Examples.Theorem27Op.utrE x T) (fun _ => Tomabechi.Examples.Theorem27Op.GE)
    (h.top_actuator x T hT).ode
    (Eventually.of_forall (h.top_actuator x T hT).state_gradient)
    (Eventually.of_forall (h.top_actuator x T hT).reference_cancellation)
    (h.top_actuator x T hT).residual_locally_lipschitz
    (h.top_actuator x T hT).w_derivative (h.top_actuator x T hT).feedback_input
    (2 * |x 0| + 1) (by positivity)
    (by filter_upwards [(h.top_actuator x T hT).adjoint_bound] with t ht _; exact ht)

/-- 全主体/全共通層の25.2を、同じMのSCMから得る。 -/
theorem AdditionalConditions.noAtman {M : ModelSignature} (h : AdditionalConditions M) :
    ∀ d a, ¬ (Tomabechi.Theorem16_25.Theorem25ProbabilityCausalModel.toCausalModel
      M.scm.model.scm.toIndexed.toProbabilityCausalModel).hasAtman d a :=
  h.toCommonDataCouplings.noAtman

end Tomabechi.Consistency.C6

#print axioms Tomabechi.Consistency.C6.AdditionalConditions.theorem23B
#print axioms Tomabechi.Consistency.C6.OriginalPremises.theorem27
#print axioms Tomabechi.Consistency.C6.ModelSignature.theorem24_26
#print axioms Tomabechi.Consistency.C6.AdditionalConditions.c1_distance

#print axioms Tomabechi.Consistency.C6.AdditionalConditions.theorem21

#print axioms Tomabechi.Consistency.C6.OriginalPremises.finite_control_ac
#print axioms Tomabechi.Consistency.C6.OriginalPremises.finite_control_ode
#print axioms Tomabechi.Consistency.C6.OriginalPremises.top_control_ac
#print axioms Tomabechi.Consistency.C6.OriginalPremises.top_control_ode
#print axioms Tomabechi.Consistency.C6.AdditionalConditions.mean_state_controls
