import Tomabechi.Consistency.ConsistencyR123_SharedTopActuator

/-!
# 共有署名の実データを定理27へ渡す

頂点等長座標で構成した27-A入力を元の頂点状態へ戻し、同じNの
24-data/26-dynamicsを一般運用入口へ直接渡す。
-/

noncomputable section
namespace Tomabechi.Consistency.R123
open MeasureTheory Filter
open scoped Topology
open Tomabechi.Consistency.R1 Tomabechi.Consistency.C6
open Tomabechi.Examples.Theorem27Op
open Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_27

local instance : NormedAddCommGroup (fullCommonLayerState (⊤ : CommonConcept)) := sharedTopCompatibleNorm
local instance : InnerProductSpace ℝ (fullCommonLayerState (⊤ : CommonConcept)) := sharedTopCompatibleInner
local instance : CompleteSpace (fullCommonLayerState (⊤ : CommonConcept)) := sharedTopComplete
local instance : ContinuousSMul ℝ (fullCommonLayerState (⊤ : CommonConcept)) := by
  infer_instance

private abbrev topCL := sharedTopCompatibleIso.toContinuousLinearEquiv
private abbrev topProductCL := ContinuousLinearMap.prodMap
  (ContinuousLinearMap.id ℝ ℝ) topCL.toContinuousLinearMap

/-- 頂点等長座標に沿って引き戻したWの微分。 -/
def sharedTopDW (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :=
  (dWE (fullCommonTopStateEquiv x) T t).comp topProductCL

/-- 同じ微分に対応する頂点の勾配。 -/
def sharedTopGradW (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :=
  topCL.symm (gradWE (fullCommonTopStateEquiv x) T t)

/-- 自然ドリフトを元の頂点状態へ戻す。 -/
def sharedTopDrift (x : fullCommonLayerState (⊤ : CommonConcept)) (T t : ℝ) :=
  topCL.symm (driftE (fullCommonTopStateEquiv x) T t)

/-- 入力空間E2から共有束頂点への同じ作用素。 -/
def sharedTopActuator : E2 →L[ℝ] fullCommonLayerState (⊤ : CommonConcept) :=
  topCL.symm.toContinuousLinearMap.comp GE

/-- 一般27入口が要求する元の頂点型での解析入力。 -/
structure SharedTop27Inputs (N : SharedModelSignature)
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop
    extends SharedTopActuatorInputs N x T hT where
  actual_ode : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasDerivAt (N.topPath x T)
      (sharedTopDrift x T t + sharedTopActuator (u0E (fullCommonTopStateEquiv x) T t)) t
  actual_state_gradient : ∀ t z,
    sharedTopDW x T t (0, z) = inner ℝ (sharedTopGradW x T t) z
  actual_reference : ∀ t,
    sharedTopDW x T t (1, 0) + inner ℝ (sharedTopGradW x T t)
      (sharedTopDrift x T t + sharedTopActuator (utrE (fullCommonTopStateEquiv x) T t)) = 0
  actual_w_derivative : ∀ᵐ t ∂futureLebesgueMeasure T,
    HasFDerivAt (fun p : ℝ × fullCommonLayerState (⊤ : CommonConcept) => N.dynamics.W p.2 p.1)
      (sharedTopDW x T t) (t, N.topPath x T t)
  actual_adjoint_bound : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ v : E2,
    |inner ℝ (sharedTopGradW x T t) (sharedTopActuator v)| ≤
      (2 * |(fullCommonTopStateEquiv x) 0| + 1) * ‖v‖

/-- 等長座標での解析入力から、一般入口の元状態型の全入力を構成する。 -/
theorem SharedTopActuatorInputs.toActual {N : SharedModelSignature}
    {x : fullCommonLayerState (⊤ : CommonConcept)} {T : ℝ} {hT : 0 ≤ T}
    (h : SharedTopActuatorInputs N x T hT) : SharedTop27Inputs N x T hT := by
  have he : ∀ y, topCL y = fullCommonTopStateEquiv y := sharedTopCompatibleIso_apply
  have hin : ∀ y z, inner ℝ (topCL.symm y) (topCL.symm z) = inner ℝ y z :=
    fun y z => sharedTopCompatibleIso.symm.inner_map_map y z
  refine {
    toSharedTopActuatorInputs := h
    actual_ode := ?_
    actual_state_gradient := ?_
    actual_reference := ?_
    actual_w_derivative := ?_
    actual_adjoint_bound := ?_ }
  · filter_upwards [h.ode] with t ht
    have hd := topCL.symm.hasFDerivAt.comp_hasDerivAt t ht
    have hcurve : (fun s => topCL.symm (fullCommonTopStateEquiv (N.topPath x T s))) =
        N.topPath x T := by
      funext s
      rw [← he, ContinuousLinearEquiv.symm_apply_apply]
    change HasDerivAt (fun s => topCL.symm (fullCommonTopStateEquiv (N.topPath x T s))) _ t at hd
    rw [hcurve] at hd
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_add, sharedTopDrift, sharedTopActuator] using hd
  · intro t z
    have hz : z = topCL.symm (topCL z) := (topCL.symm_apply_apply z).symm
    rw [hz, sharedTopGradW, hin]
    simpa [sharedTopDW, topProductCL] using h.state_gradient t (topCL z)
  · intro t
    simpa [sharedTopDW, sharedTopGradW, sharedTopDrift, sharedTopActuator,
      topProductCL, ← map_add, hin] using h.reference_cancellation t
  · filter_upwards [h.w_derivative] with t ht
    have ht' : HasFDerivAt
        (fun p : ℝ × E2 => N.dynamics.W (fullCommonTopStateEquiv.symm p.2) p.1)
        (dWE (fullCommonTopStateEquiv x) T t) (topProductCL (t, N.topPath x T t)) := by
      simpa only [topProductCL, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, he] using ht
    have hf := ht'.comp (t, N.topPath x T t) topProductCL.hasFDerivAt
    have hcurve : ((fun p : ℝ × E2 => N.dynamics.W (fullCommonTopStateEquiv.symm p.2) p.1) ∘
        topProductCL) =
        (fun p : ℝ × fullCommonLayerState (⊤ : CommonConcept) => N.dynamics.W p.2 p.1) := by
      funext p
      change N.dynamics.W (fullCommonTopStateEquiv.symm (topCL p.2)) p.1 = _
      rw [he, Equiv.symm_apply_apply]
    rw [hcurve] at hf
    exact hf
  · filter_upwards [h.adjoint_bound] with t ht
    intro v
    simpa [sharedTopGradW, sharedTopActuator, hin] using ht v

/-- 同じ共有署名の実PZS・残差・入力で述べる定理27の全運用結論。 -/
def SharedTop27Conclusion (N : SharedModelSignature)
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T) : Prop :=
    (∀ t, T ≤ t →
      ((
      (¬ FeedbackPZS (N.data.admissible (⊤ : CommonConcept)) futureLebesgueMeasure
        (fun π y a s => N.data.runningCost (⊤ : CommonConcept) π
          (N.data.trajectory (⊤ : CommonConcept) π y a s) s)
        (N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T t) t) ↔
        0 < Tomabechi.Theorem27.residualDescentRateAlong
          (fun s y => N.dynamics.W y s)
          (fun s => N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T s) t))) ∧
    (∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t,
      (¬ FeedbackPZS (N.data.admissible (⊤ : CommonConcept)) futureLebesgueMeasure
        (fun π y a s => N.data.runningCost (⊤ : CommonConcept) π
          (N.data.trajectory (⊤ : CommonConcept) π y a s) s)
        (N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T t) t) ↔
        0 < -(inner ℝ (sharedTopGradW x T t)
          (sharedTopActuator
            ((N.dynamics.policyEquiv N.dynamics.feedback).action
              ⟨⟨t, hT.trans htt⟩,
                N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T t⟩ - utrE (fullCommonTopStateEquiv x) T t)))) ∧
    (∀ᵐ t ∂futureLebesgueMeasure T,
      (¬ FeedbackPZS (N.data.admissible (⊤ : CommonConcept)) futureLebesgueMeasure
        (fun π y a s => N.data.runningCost (⊤ : CommonConcept) π
          (N.data.trajectory (⊤ : CommonConcept) π y a s) s)
        (N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T t) t) →
      (N.dynamics.rate * N.dynamics.c₁ *
        (Metric.infDist (N.data.trajectory (⊤ : CommonConcept) N.dynamics.feedback x T t)
          (theorem26ZeroValueTarget N.dynamics.alive (N.data.optimalValue (⊤ : CommonConcept)) t)) ^ 2) / (2 * |(fullCommonTopStateEquiv x) 0| + 1) ≤
          ‖u0E (fullCommonTopStateEquiv x) T t - utrE (fullCommonTopStateEquiv x) T t‖ ∧ 0 < ‖u0E (fullCommonTopStateEquiv x) T t - utrE (fullCommonTopStateEquiv x) T t‖)

/-- 同じN.data/N.dynamicsを一般27運用入口へ直接渡す。
全時刻の無明⇔残差下降、AEの無明⇔実入力による下降、距離付き入力下限を返す。 -/
theorem SharedTop27Inputs.conclusion {N : SharedModelSignature}
    {x : fullCommonLayerState (⊤ : CommonConcept)} {T : ℝ} {hT : 0 ≤ T}
    (h : SharedTop27Inputs N x T hT) (hx : x ∈ N.dynamics.alive) :
    SharedTop27Conclusion N x T hT :=
  theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := CommonConcept) (State := fullCommonLayerState) (Feedback := fullCommonLayerPolicy)
    (Control := E2) (stateMetric := fullCommonTopPseudoMetricSpace)
    rfl rfl N.data N.dynamics x T hT hx
    (fun y a s t ha has hst _ => h.restart y a s t ha has hst)
    (sharedTopDW x T) (sharedTopGradW x T) (sharedTopDrift x T)
    (u0E (fullCommonTopStateEquiv x) T) (utrE (fullCommonTopStateEquiv x) T)
    (fun _ => sharedTopActuator) h.actual_ode
    (Eventually.of_forall h.actual_state_gradient)
    (Eventually.of_forall h.actual_reference)
    h.residual_locally_lipschitz h.actual_w_derivative h.feedback_input
    (2 * |(fullCommonTopStateEquiv x) 0| + 1) (by positivity)
    (by filter_upwards [h.actual_adjoint_bound] with t ht _; exact ht)

/-- 任意共有kernel入力から全頂点初期状態・全非負開始時刻の27-A実入力を得る。 -/
theorem SharedKernelInputs.theorem27Inputs {N : SharedModelSignature}
    (h : SharedKernelInputs N) (x : fullCommonLayerState (⊤ : CommonConcept))
    (T : ℝ) (hT : 0 ≤ T) : SharedTop27Inputs N x T hT :=
  (h.topActuatorInputs x T hT).toActual

/-- 具体共有署名は外部モデル前提なしに全27-A実入力を満たす。 -/
theorem sharedModel_theorem27Inputs : ∀ x T hT, SharedTop27Inputs sharedModel x T hT :=
  sharedModel_kernelInputs.theorem27Inputs

/-- R3一般入口と27-A実入力を同じ署名で同時に受け入れる。 -/
structure SharedR3And27Inputs (N : SharedModelSignature) : Prop extends SharedR3Inputs N where
  top27 : ∀ x T hT, SharedTop27Inputs N x T hT

/-- 全頂点alive初期状態・全非負開始時刻で一般27の全結論を得る。 -/
theorem SharedR3And27Inputs.theorem27 {N : SharedModelSignature} (h : SharedR3And27Inputs N)
    (x : fullCommonLayerState (⊤ : CommonConcept)) (T : ℝ) (hT : 0 ≤ T)
    (hx : x ∈ N.dynamics.alive) : SharedTop27Conclusion N x T hT :=
  (h.top27 x T hT).conclusion hx

/-- 外部モデル前提なしのR3/27同時存在。全原文受入の最終宣言は別途必要。 -/
theorem shared_r3_and27_model_exists : ∃ N : SharedModelSignature, SharedR3And27Inputs N :=
  by
  refine ⟨sharedModel, ?_⟩
  exact { toSharedR3Inputs := sharedModel_r3Inputs
          top27 := sharedModel_theorem27Inputs }

#print axioms shared_r3_and27_model_exists
#print axioms SharedR3And27Inputs.theorem27

#print axioms SharedTop27Inputs.conclusion
#print axioms SharedKernelInputs.theorem27Inputs

#print axioms SharedTopActuatorInputs.toActual
end Tomabechi.Consistency.R123
