import Theorem27


/-!
# 定理24/26の共通データから定理27(27.6)への接続

定理24の最適化データと定理26の最適費用を達成するfeedback・Lyapunovデータを受け取り、同じ
trajectory上のPZSを零価値目標への所属に移し、26-Aの右傾斜下降条件から
定理27(27.6)の定量残差下降を得る。定理27-Aのアクチュエータ帰属は別条件であり、
この橋では導出しない。`Theorem26NonnegativeTimeDynamics.W_rightSlope` から実数値limsup
によるDini上界への変換は、未来域上の局所Lipschitz条件から導く。
-/

namespace Tomabechi.Theorem24_26_27

open Tomabechi.Theorem24_26
open Tomabechi.Theorem27

/-- The finite-dimensional Euclidean ambient used by condition 27-A already
uses the norm-induced distance and topology required by the 24/26 adapter. -/
theorem euclideanStateMetric_eq_norm_induced
    {ι : Type*} [Fintype ι] :
    (inferInstance : PseudoMetricSpace (EuclideanSpace ℝ ι)) =
      NormedAddCommGroup.toMetricSpace.toPseudoMetricSpace := by
  rfl

theorem euclideanControlTopology_eq_norm_induced
    {ι : Type*} [Fintype ι] :
    (inferInstance : TopologicalSpace (EuclideanSpace ℝ ι)) =
      NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  rfl

/-- Totalize a nonnegative-time Markov feedback along a trajectory by using
`max t 0` outside the physical time domain. On every future ray starting at
`T ≥ 0`, this agrees with the policy's actual input at time `t`. -/
noncomputable def policyInputAlongTrajectory
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [Zero Control]
    (policy : NonnegativeTimeBorelMarkovFeedback State Control)
    (trajectory : State → ℝ → ℝ → State) (x : State) (T : ℝ) : ℝ → Control :=
  fun t => policy.action ⟨⟨max t 0, le_max_right t 0⟩, trajectory x T t⟩

/-- The totalized feedback input is exactly the paper's `u⁰(t,x)=π⁰(t,x)` on
the future ray. This discharges the `hU0Feedback` adapter condition by
construction. -/
theorem policyInputAlongTrajectory_eq_action
    {State Control : Type*} [MeasurableSpace State] [MeasurableSpace Control]
    [Zero Control]
    (policy : NonnegativeTimeBorelMarkovFeedback State Control)
    (trajectory : State → ℝ → ℝ → State) (x : State) (T t : ℝ)
    (hT : 0 ≤ T) (htt : T ≤ t) :
    policyInputAlongTrajectory policy trajectory x T t =
      policy.action ⟨⟨t, hT.trans htt⟩, trajectory x T t⟩ := by
  have ht : 0 ≤ t := hT.trans htt
  simp [policyInputAlongTrajectory, max_eq_left ht]

/-- The source-level control domain and actuator-residual measurability from
condition 27-A, tracked separately from the Euclidean ambient spaces used by
the derivative adapter. `Control` is the ambient ℝᵐ space; this record keeps
the paper's allowed subset U explicit along the selected and reference inputs. -/
structure Theorem27PathActuatorData
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics
      (A := A) (State := fun _ : A => EuclideanSpace ℝ ι)
      (Feedback := Feedback) D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T) where
  allowedInput : Set (EuclideanSpace ℝ κ)
  referenceInput : ℝ → EuclideanSpace ℝ κ
  drift : ℝ → EuclideanSpace ℝ ι
  actuator : ℝ → (EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι)
  L₂₇ : ℝ
  L₂₇_pos : 0 < L₂₇
  referenceInput_allowed : ∀ t, T ≤ t → referenceInput t ∈ allowedInput
  feedbackInput_allowed : ∀ t (htt : T ≤ t),
    (E.policyEquiv E.feedback).action
      ⟨⟨t, hT.trans htt⟩,
        D.trajectory (⊤ : A) E.feedback x T t⟩ ∈ allowedInput
  referenceCancellation_ae : ∀ᵐ t ∂futureLebesgueMeasure T,
    Actuator.jointDerivativeOnPath (fun y s => E.W y s)
        (fun s => D.trajectory (⊤ : A) E.feedback x T s) t (1, 0) +
      inner ℝ
        (Actuator.stateGradientFromFDeriv
          (Actuator.jointDerivativeOnPath (fun y s => E.W y s)
            (fun s => D.trajectory (⊤ : A) E.feedback x T s) t))
        (drift t + actuator t (referenceInput t)) = 0
  adjointBound_ae : ∀ᵐ t ∂futureLebesgueMeasure T,
    (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y a s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y a s) s)
      (D.trajectory (⊤ : A) E.feedback x T t) t) →
      ‖(actuator t).adjoint
        (Actuator.stateGradientFromFDeriv
          (Actuator.jointDerivativeOnPath (fun y s => E.W y s)
            (fun s => D.trajectory (⊤ : A) E.feedback x T s) t))‖ ≤ L₂₇
  actuatorDifference_measurable : Measurable
    (fun t : Set.Ici T => actuator t.1
      (policyInputAlongTrajectory (E.policyEquiv E.feedback)
        (D.trajectory (⊤ : A) E.feedback) x T t.1 - referenceInput t.1))

/-- A time-dependent globally Lipschitz closed-loop ODE has the restart
identity required by the future-ray theorem adapters. Applying this lemma to
abstract `D/E` data still requires proving that every trajectory solves one
common closed-loop vector field. -/
theorem trajectory_restart_of_timeDependent_ode_unique
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (v : ℝ → State → State) (trajectory : State → ℝ → ℝ → State)
    (K : NNReal)
    (hLipschitz : ∀ t, LipschitzWith K (v t))
    (hODE : ∀ (x : State) (a r : ℝ),
      HasDerivAt (trajectory x a) (v r (trajectory x a r)) r)
    (hInitial : ∀ (x : State) (a : ℝ), trajectory x a a = x)
    (x : State) (a b t : ℝ) (hbt : b ≤ t) :
    trajectory (trajectory x a b) b t = trajectory x a t := by
  let restarted : ℝ → State := trajectory (trajectory x a b) b
  let original : ℝ → State := trajectory x a
  have hEq : restarted b = original b := by
    simp [restarted, original, hInitial]
  have hUnique := ODE_solution_unique_of_mem_Icc_right
    (a := b) (b := t) (K := K) (v := v) (s := fun _ => Set.univ)
    (fun r _ => (hLipschitz r).lipschitzOnWith)
    (HasDerivAt.continuousOn fun r _ => hODE (trajectory x a b) b r)
    (fun r _ => (hODE (trajectory x a b) b r).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _)
    (HasDerivAt.continuousOn fun r _ => hODE x a r)
    (fun r _ => (hODE x a r).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) hEq
  have hAt := hUnique ⟨hbt, le_rfl⟩
  simpa [restarted, original] using hAt

/-- Future-domain variant of the restart lemma. Both trajectories need to
solve the same time-dependent vector field only from their own start times;
the proof uses uniqueness on `[b,t]`. -/
theorem trajectory_restart_of_future_ode_unique
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (v : ℝ → State → State) (trajectory : State → ℝ → ℝ → State)
    (K : NNReal)
    (hLipschitz : ∀ t, LipschitzWith K (v t))
    (hODE : ∀ (x : State) (a r : ℝ), a ≤ r →
      HasDerivAt (trajectory x a) (v r (trajectory x a r)) r)
    (x : State) (a b t : ℝ) (hab : a ≤ b) (hbt : b ≤ t)
    (hInitialAt : trajectory (trajectory x a b) b b = trajectory x a b) :
    trajectory (trajectory x a b) b t = trajectory x a t := by
  let restarted : ℝ → State := trajectory (trajectory x a b) b
  let original : ℝ → State := trajectory x a
  have hEq : restarted b = original b := by
    simp [restarted, original, hInitialAt]
  have hUnique := ODE_solution_unique_of_mem_Icc_right
    (a := b) (b := t) (K := K) (v := fun r z => v r z) (s := fun _ => Set.univ)
    (fun r _ => (hLipschitz r).lipschitzOnWith)
    (HasDerivAt.continuousOn fun r hr => hODE (trajectory x a b) b r hr.1)
    (fun r hr => (hODE (trajectory x a b) b r hr.1).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _)
    (HasDerivAt.continuousOn fun r hr => hODE x a r (hab.trans hr.1))
    (fun r hr => (hODE x a r (hab.trans hr.1)).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) hEq
  have hAt := hUnique ⟨hbt, le_rfl⟩
  simpa [restarted, original] using hAt

/-- Derive the restart identity for the selected theorem-24/26 feedback from
one common, time-dependent, globally Lipschitz vector field. Admissibility of
the restarted initial pair follows from the alive invariance and the feedback's
attainment property stored in the theorem-26 data. The common ODE still has to
be connected to the abstract control data by the caller. -/
theorem theorem24_26_feedback_restart_of_unique_ode
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [NormedAddCommGroup (State (⊤ : A))] [NormedSpace ℝ (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (v : ℝ → State (⊤ : A) → State (⊤ : A)) (K : NNReal)
    (hLipschitz : ∀ t, LipschitzWith K (v t))
    (hODE : ∀ (y : State (⊤ : A)) (a r : ℝ), a ≤ r →
      HasDerivAt
        (D.trajectory (⊤ : A) E.feedback y a)
        (v r (D.trajectory (⊤ : A) E.feedback y a r)) r)
    (y : State (⊤ : A)) (a b t : ℝ)
    (ha : 0 ≤ a) (hy : y ∈ E.alive) (hab : a ≤ b) (hbt : b ≤ t) :
    D.trajectory (⊤ : A) E.feedback
      (D.trajectory (⊤ : A) E.feedback y a b) b t =
      D.trajectory (⊤ : A) E.feedback y a t := by
  have hyb : D.trajectory (⊤ : A) E.feedback y a b ∈ E.alive :=
    E.trajectory_alive y a b ha hy hab
  have hRestartedAdm :=
    (E.feedback_attains_optimum (D.trajectory (⊤ : A) E.feedback y a b) b
      (le_trans ha hab) hyb).1
  have hInitial : D.trajectory (⊤ : A) E.feedback
      (D.trajectory (⊤ : A) E.feedback y a b) b b =
        D.trajectory (⊤ : A) E.feedback y a b := by
    exact D.trajectory_initial (⊤ : A) E.feedback
      (D.trajectory (⊤ : A) E.feedback y a b) b (le_trans ha hab) hRestartedAdm
  exact trajectory_restart_of_future_ode_unique
    v (D.trajectory (⊤ : A) E.feedback) K hLipschitz
    (by
      intro z s r hsr
      exact hODE z s r hsr)
    y a b t hab hbt hInitial

private theorem feedbackPZS_iff_zeroTarget_of_dynamics
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    (D : Theorem24NonnegativeTimeData State Feedback)
    (π₀ : Feedback (⊤ : A)) (alive : Set (State (⊤ : A)))
    (attains : ∀ (x : State (⊤ : A)) (T : ℝ), 0 ≤ T → x ∈ alive →
      D.admissible (⊤ : A) π₀ x T ∧
        MeasureTheory.Integrable
          (fun s => theorem26DiscountWeight D.rho T s *
            D.runningCost (⊤ : A) π₀
              (D.trajectory (⊤ : A) π₀ x T s) s)
          (futureLebesgueMeasure T) ∧
        D.optimalValue (⊤ : A) x T = ∫ s,
          theorem26DiscountWeight D.rho T s *
            D.runningCost (⊤ : A) π₀
              (D.trajectory (⊤ : A) π₀ x T s) s
              ∂(futureLebesgueMeasure T))
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ alive) :
    (FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T ↔
      x ∈ theorem26ZeroValueTarget alive (D.optimalValue (⊤ : A)) T) := by
  rcases attains x T hT hx with ⟨hadm, hint, hattains⟩
  exact theorem24_26_top_pzs_from_feedback_attainment
    D π₀ alive x T hT hx hadm hint hattains

/-- 定理26-Aの右差分商評価から定理27で使う実数値 upper right Dini
微分評価を得る。軌道上のLyapunov関数に局所Lipschitz性を追加仮定する。
これは定理26の絶対連続性だけからは導いていない。 -/
theorem theorem26_rightSlope_to_theorem27_Dini
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) :
    ∀ u, T ≤ u →
      E.rate * E.W (D.trajectory (⊤ : A) E.feedback x T u) u ≤
        -Actuator.upperRightDiniDerivative
          (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s) u := by
  intro u hu
  have hDini := Actuator.upperRightDiniDerivative_le_of_rightSlopeBound
    (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)
    T hLocallyLipschitz hu
    (-E.rate * E.W (D.trajectory (⊤ : A) E.feedback x T u) u)
    (E.W_rightSlope x T u hT hx hu)
  linarith

/-- 定理24-Aと定理26の最適費用達成feedbackから、定理27(27.2)の型付き分類を得る。
時刻は原文の定義域 `T ≥ 0` に制限し、上位状態はalive部分型に置く。 -/
theorem theorem24_26_data_to_theorem27_classification
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ s : TypedState27 State E.alive,
      operationalIgnorance27
        (fun a y t => FeedbackPZS (D.admissible a)
          (fun _ => futureLebesgueMeasure t)
          (fun π z u r => D.runningCost a π
            (D.trajectory a π z u r) r) y t)
        E.alive s T ↔
      match s with
      | .inl _ => True
      | .inr x => x.1 ∉
          theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) T := by
  intro s
  cases s with
  | inl lower =>
      rcases lower with ⟨⟨a, ha⟩, y⟩
      have hno : ¬ FeedbackPZS (D.admissible a)
          (fun _ => futureLebesgueMeasure T)
          (fun π z u r => D.runningCost a π
            (D.trajectory a π z u r) r) y T :=
        theorem24_no_feedbackPZS_of_condition24A
          (fun _ => futureLebesgueMeasure T)
          (fun π z u r => D.runningCost a π
            (D.trajectory a π z u r) r)
          (D.admissible a) y T
          (fun π hπ => D.condition24A a ha y T hT π hπ)
      simp [operationalIgnorance27, pzsOnTypedState27, hno]
  | inr upper =>
      have hpzs := feedbackPZS_iff_zeroTarget_of_dynamics
        D E.feedback E.alive E.feedback_attains_optimum upper.1 T hT upper.2
      simpa [FeedbackPZS, operationalIgnorance27, pzsOnTypedState27] using
        (not_congr hpzs)

/-- 定理24/26の同一データから定理27(27.6)を得る一点ごとの合成。
PZS判定は `E.feedback` 自身の最適費用達成から零価値目標へ移す。
Lyapunov下降は定理26-AのDini不等式と下側距離評価から導く。 -/
theorem theorem24_26_data_to_theorem27_residual_descent
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ)
    (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun u => E.W (D.trajectory (⊤ : A) E.feedback x T u) u))
    (hignorance : ¬ FeedbackPZS (D.admissible (⊤ : A))
      futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T) :
    E.rate * E.c₁ *
        (Metric.infDist x
          (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) T)) ^ 2 ≤
      residualDescentRateAlong
        (fun s y => E.W y s)
        (fun s => D.trajectory (⊤ : A) E.feedback x T s) T ∧
      0 < residualDescentRateAlong
        (fun s y => E.W y s)
        (fun s => D.trajectory (⊤ : A) E.feedback x T s) T := by
  let N : Set (State (⊤ : A)) :=
    theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) T
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let WAlong : ℝ → ℝ := fun s => E.W (path s) s
  have hDiniDecay := theorem26_rightSlope_to_theorem27_Dini
    D E x T hT hx hResidualLocallyLipschitz
  have hDiniDecayT := hDiniDecay T le_rfl
  have hpzsTarget := feedbackPZS_iff_zeroTarget_of_dynamics
    D E.feedback E.alive E.feedback_attains_optimum x T hT hx
  have houtside : x ∉ N := by
    intro htarget
    exact hignorance (hpzsTarget.mpr htarget)
  have hclosed : IsClosed N := E.target_closed T hT
  have hnonempty : N.Nonempty := E.target_nonempty T hT
  have hpathT : path T = x := by
    exact D.trajectory_initial (⊤ : A) E.feedback x T hT
      (by
        exact (E.feedback_attains_optimum x T hT hx).1)
  have hWlower : E.c₁ * (Metric.infDist x N) ^ 2 ≤ E.W x T := by
    simpa [N, path, hpathT] using E.W_lower_distance_bound x T T hT hx le_rfl
  have hDini : E.rate * E.W x T ≤
      -Actuator.upperRightDiniDerivative WAlong T := by
    simpa [WAlong, path, hpathT] using hDiniDecayT
  have hdescent : E.rate * E.c₁ * (Metric.infDist x N) ^ 2 ≤
      residualDescentRateAlong (fun s y => E.W y s) path T := by
    unfold residualDescentRateAlong
    calc
      E.rate * E.c₁ * (Metric.infDist x N) ^ 2 ≤ E.rate * E.W x T := by
        have hmul := mul_le_mul_of_nonneg_left hWlower E.rate_pos.le
        nlinarith
      _ ≤ -Actuator.upperRightDiniDerivative WAlong T := hDini
  have hpositive : 0 < residualDescentRateAlong
      (fun s y => E.W y s) path T := by
    have hWpos : 0 < E.W x T := by
      have hdist : 0 < Metric.infDist x N :=
        (hclosed.notMem_iff_infDist_pos hnonempty).mp houtside
      have hsq : 0 < (Metric.infDist x N) ^ 2 := sq_pos_of_pos hdist
      exact lt_of_lt_of_le (mul_pos E.c₁_pos hsq) hWlower
    have hrateW : 0 < E.rate * E.W x T := mul_pos E.rate_pos hWpos
    exact lt_of_lt_of_le hrateW (by simpa [residualDescentRateAlong, WAlong, path]
      using hDini)
  simpa [N, path] using ⟨hdescent, hpositive⟩

/-- Full future-ray form of equation (27.6). The current state at each time
is classified by the PZS/zero-target equivalence at that same start time;
the distance estimate and Dini decay are evaluated along the original common
24/26 trajectory. -/
theorem theorem24_26_data_to_theorem27_future_quantitative_descent
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) :
    ∀ t, T ≤ t →
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t →
        E.rate * E.c₁ *
          (Metric.infDist (D.trajectory (⊤ : A) E.feedback x T t)
            (theorem26ZeroValueTarget E.alive
              (D.optimalValue (⊤ : A)) t)) ^ 2 ≤
              residualDescentRateAlong (fun s y => E.W y s)
                (fun s => D.trajectory (⊤ : A) E.feedback x T s) t ∧
        0 < residualDescentRateAlong (fun s y => E.W y s)
          (fun s => D.trajectory (⊤ : A) E.feedback x T s) t) := by
  intro t htt hIgnorance
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let Wpath : ℝ → State (⊤ : A) → ℝ := fun s y => E.W y s
  have ht0 : 0 ≤ t := hT.trans htt
  have htAlive : path t ∈ E.alive := by
    exact E.trajectory_alive x T t hT hx htt
  have hpzsTarget := feedbackPZS_iff_zeroTarget_of_dynamics
    D E.feedback E.alive E.feedback_attains_optimum (path t) t ht0 htAlive
  have houtside : path t ∉
      theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t := by
    intro htarget
    exact hIgnorance (hpzsTarget.mpr htarget)
  have hclosed : IsClosed
      (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t) :=
    E.target_closed t ht0
  have hnonempty : (theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) t).Nonempty := E.target_nonempty t ht0
  have hDini := theorem26_rightSlope_to_theorem27_Dini
    D E x T hT hx hResidualLocallyLipschitz t htt
  exact residual_descent_of_outside_closed_target
    (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t)
    hclosed hnonempty (fun y => E.W y t) (path t)
    E.c₁ E.rate E.c₁_pos E.rate_pos
    (residualDescentRateAlong Wpath path t)
    (by
      simpa [Wpath, path] using E.W_lower_distance_bound x T t hT hx htt)
    (by simpa [residualDescentRateAlong, Wpath, path] using hDini)
    houtside

/-- 原文(27.6)の不等式連鎖を、同じD/Eの指定軌道について全未来時刻で返す。
既存入口の距離下界に加え、途中の `λ W` と距離項の厳密正値も明示する。
27-Aのアクチュエータ帰属、再始動、追加の正則性は要求しない。 -/
theorem theorem24_26_data_to_theorem27_future_descent_chain
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) :
    ∀ t, T ≤ t →
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t →
        E.rate * E.W (D.trajectory (⊤ : A) E.feedback x T t) t ≤
          residualDescentRateAlong (fun s y => E.W y s)
            (fun s => D.trajectory (⊤ : A) E.feedback x T s) t ∧
        E.rate * E.c₁ *
          (Metric.infDist (D.trajectory (⊤ : A) E.feedback x T t)
            (theorem26ZeroValueTarget E.alive
              (D.optimalValue (⊤ : A)) t)) ^ 2 ≤
          E.rate * E.W (D.trajectory (⊤ : A) E.feedback x T t) t ∧
        0 < E.rate * E.c₁ *
          (Metric.infDist (D.trajectory (⊤ : A) E.feedback x T t)
            (theorem26ZeroValueTarget E.alive
              (D.optimalValue (⊤ : A)) t)) ^ 2) := by
  intro t htt hIgnorance
  have ht0 : 0 ≤ t := hT.trans htt
  have htAlive := E.trajectory_alive x T t hT hx htt
  have hpzs := feedbackPZS_iff_zeroTarget_of_dynamics
    D E.feedback E.alive E.feedback_attains_optimum
    (D.trajectory (⊤ : A) E.feedback x T t) t ht0 htAlive
  have houtside : D.trajectory (⊤ : A) E.feedback x T t ∉
      theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t := by
    intro hmem
    exact hIgnorance (hpzs.mpr hmem)
  have hdist : 0 < Metric.infDist (D.trajectory (⊤ : A) E.feedback x T t)
      (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t) :=
    ((E.target_closed t ht0).notMem_iff_infDist_pos
      (E.target_nonempty t ht0)).mp houtside
  refine ⟨?_, ?_, mul_pos (mul_pos E.rate_pos E.c₁_pos) (sq_pos_of_pos hdist)⟩
  · exact theorem26_rightSlope_to_theorem27_Dini
      D E x T hT hx hResidualLocallyLipschitz t htt
  · have hbound := mul_le_mul_of_nonneg_left
      (E.W_lower_distance_bound x T t hT hx htt) E.rate_pos.le
    simpa only [mul_assoc] using hbound

/-- The zero residual conclusion of equation (27.9) on the shared optimal
trajectory of Theorems 24 and 26. `hrestart` states the flow consistency
needed to apply target invariance after restarting at an intermediate time. -/
theorem theorem24_26_data_to_theorem27_residual_zero_after_entry
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [PseudoMetricSpace (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control] [TopologicalSpace Control]
    [BorelSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hPZS : FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T)
    (hrestart : ∀ (y : State (⊤ : A)) (a s t : ℝ),
      0 ≤ a → a ≤ s → s ≤ t →
      D.admissible (⊤ : A) (E.feedback) y a →
      D.trajectory (⊤ : A) E.feedback
        (D.trajectory (⊤ : A) E.feedback y a s) s t =
        D.trajectory (⊤ : A) E.feedback y a t)
    : ∀ t, T ≤ t → residualDescentRateAlong
      (fun s y => E.W y s)
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) t = 0 := by
  let target : ℝ → Set (State (⊤ : A)) := fun t =>
    if T ≤ t then theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) t else ∅
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let Wpath : ℝ × State (⊤ : A) → ℝ := fun p => E.W p.2 p.1
  have hpzs := feedbackPZS_iff_zeroTarget_of_dynamics
    D E.feedback E.alive E.feedback_attains_optimum x T hT hx
  have hentry : path T ∈ target T := by
    rw [show target T = theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) T by simp [target]]
    have hadm : D.admissible (⊤ : A) E.feedback x T := by
      exact (E.feedback_attains_optimum x T hT hx).1
    rw [show path T = x by
      simp [path, D.trajectory_initial (⊤ : A) E.feedback x T hT hadm]]
    exact hpzs.mp hPZS
  have hforward : ∀ a s, a ≤ s → path a ∈ target a → path s ∈ target s := by
    intro a s has hmem
    by_cases ha : T ≤ a
    · have htargetA : path a ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) a := by simpa [target, ha] using hmem
      have hTa0 : 0 ≤ a := hT.trans ha
      have hInv := E.target_invariant (path a) a s hTa0
        htargetA has
      have hAdm : D.admissible (⊤ : A) E.feedback x T := by
        exact (E.feedback_attains_optimum x T hT hx).1
      have hrestart' := hrestart x T a s hT ha has hAdm
      have hpathEq : path s = D.trajectory (⊤ : A) E.feedback
          (path a) a s := by
        exact hrestart'.symm
      rw [hpathEq]
      simpa [target, le_trans ha has] using hInv
    · simp [target, ha] at hmem
  have hWzero : ∀ s y, y ∈ target s → Wpath (s,y) = 0 := by
    intro s y hy
    by_cases hs : T ≤ s
    · have hy' : y ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) s := by simpa [target, hs] using hy
      have hyAlive : y ∈ E.alive := hy'.1
      have hyValue : D.optimalValue (⊤ : A) y s = 0 := hy'.2
      have hs0 : 0 ≤ s := hT.trans hs
      have hadm : D.admissible (⊤ : A) E.feedback y s := by
        exact (E.feedback_attains_optimum y s hs0 hyAlive).1
      have hinit := D.trajectory_initial (⊤ : A) E.feedback y s hs0 hadm
      have hup := E.W_upper_distance_bound y s s hs0 hyAlive le_rfl
      have hdist : Metric.infDist y
          (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) s) = 0 :=
        Metric.infDist_zero_of_mem hy'
      have : E.W y s ≤ 0 := by
        simpa [hinit, hdist] using hup
      have hn := E.W_nonnegative y s s hs0 hyAlive le_rfl
      rw [hinit] at hn
      simp [Wpath]
      linarith
    · simp [target, hs] at hy
  intro t htt
  have hdinizero := Actuator.residualDescentRate_zero_after_target_entry
    target Wpath path hforward hWzero T t htt hentry
  simpa [residualDescentRateAlong, Wpath, path] using hdinizero

/-- Full (27.9) adapter on the common optimal trajectory. The explicit
`hMetric` identifies Theorem 26's ambient pseudometric with the metric
induced by the Hilbert norm, so the Fréchet derivatives and actuator maps
have the same topology on both sides. `hU0Feedback` ties the actual input to
the common optimal Borel feedback; `hmodel`-style ODE and cancellation data
remain explicit hypotheses from 27-A. -/
theorem theorem24_26_data_to_theorem27_quiescence
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [stateMetric : PseudoMetricSpace (State (⊤ : A))]
    [stateNorm : NormedAddCommGroup (State (⊤ : A))]
    [InnerProductSpace ℝ (State (⊤ : A))]
    [ContinuousSMul ℝ (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control]
    [controlTopology : TopologicalSpace Control]
    [BorelSpace Control] [controlNorm : NormedAddCommGroup Control]
    [InnerProductSpace ℝ Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (hMetric : stateMetric = NormedAddCommGroup.toMetricSpace.toPseudoMetricSpace)
    (hControlTopology : controlTopology =
      controlNorm.toMetricSpace.toUniformSpace.toTopologicalSpace)
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hPZS : FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T)
    (hrestart : ∀ (y : State (⊤ : A)) (a s t : ℝ),
      0 ≤ a → a ≤ s → s ≤ t →
      D.admissible (⊤ : A) E.feedback y a →
      D.trajectory (⊤ : A) E.feedback
        (D.trajectory (⊤ : A) E.feedback y a s) s t =
        D.trajectory (⊤ : A) E.feedback y a t)
    (dW : ℝ → (ℝ × State (⊤ : A) →L[ℝ] ℝ))
    (gradW drift : ℝ → State (⊤ : A))
    (u0 utr : ℝ → Control)
    (actuator : ℝ → Control →L[ℝ] State (⊤ : A))
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T, HasDerivAt
      (fun s => D.trajectory (⊤ : A) E.feedback x T s)
      (drift t + actuator t (u0 t)) t)
    (hStateGrad : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t ∂futureLebesgueMeasure T,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s))
    (hW : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × State (⊤ : A) => E.W p.2 p.1)
      (dW t) (t, D.trajectory (⊤ : A) E.feedback x T t))
    (hU0Feedback : ∀ t htt, u0 t =
      (E.policyEquiv E.feedback).action
        ⟨⟨t, hT.trans htt⟩, D.trajectory (⊤ : A) E.feedback x T t⟩) :
    (∀ t, T ≤ t → residualDescentRateAlong
      (fun s y => E.W y s)
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) t = 0) ∧
    (∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t, inner ℝ (gradW t)
      (actuator t
        ((E.policyEquiv E.feedback).action
          ⟨⟨t, hT.trans htt⟩,
            D.trajectory (⊤ : A) E.feedback x T t⟩ - utr t)) = 0) := by
  cases hMetric
  cases hControlTopology
  let target : ℝ → Set (State (⊤ : A)) := fun t =>
    if T ≤ t then theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) t else ∅
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let Wpath : ℝ × State (⊤ : A) → ℝ := fun p => E.W p.2 p.1
  have hpzs := feedbackPZS_iff_zeroTarget_of_dynamics
    D E.feedback E.alive E.feedback_attains_optimum x T hT hx
  have hentry : path T ∈ target T := by
    rw [show target T = theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) T by simp [target]]
    have hadm : D.admissible (⊤ : A) E.feedback x T := by
      exact (E.feedback_attains_optimum x T hT hx).1
    rw [show path T = x by
      simp [path, D.trajectory_initial (⊤ : A) E.feedback x T hT hadm]]
    exact hpzs.mp hPZS
  have hforward : ∀ a s, a ≤ s → path a ∈ target a → path s ∈ target s := by
    intro a s has hmem
    by_cases ha : T ≤ a
    · have htargetA : path a ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) a := by simpa [target, ha] using hmem
      have hTa0 : 0 ≤ a := hT.trans ha
      have hInv := E.target_invariant (path a) a s hTa0 htargetA has
      have hAdm : D.admissible (⊤ : A) E.feedback x T := by
        exact (E.feedback_attains_optimum x T hT hx).1
      have hrestart' := hrestart x T a s hT ha has hAdm
      have hpathEq : path s = D.trajectory (⊤ : A) E.feedback
          (path a) a s := hrestart'.symm
      rw [hpathEq]
      simpa [target, le_trans ha has] using hInv
    · simp [target, ha] at hmem
  have hWzero : ∀ s y, y ∈ target s → Wpath (s,y) = 0 := by
    intro s y hy
    by_cases hs : T ≤ s
    · have hy' : y ∈ theorem26ZeroValueTarget E.alive
          (D.optimalValue (⊤ : A)) s := by simpa [target, hs] using hy
      have hyAlive : y ∈ E.alive := hy'.1
      have hs0 : 0 ≤ s := hT.trans hs
      have hadm : D.admissible (⊤ : A) E.feedback y s := by
        exact (E.feedback_attains_optimum y s hs0 hyAlive).1
      have hinit := D.trajectory_initial (⊤ : A) E.feedback y s hs0 hadm
      have hup := E.W_upper_distance_bound y s s hs0 hyAlive le_rfl
      have hdist : Metric.infDist y
          (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) s) = 0 :=
        Metric.infDist_zero_of_mem hy'
      have hWle : E.W y s ≤ 0 := by simpa [hinit, hdist] using hup
      have hWge := E.W_nonnegative y s s hs0 hyAlive le_rfl
      rw [hinit] at hWge
      simp [Wpath]
      linarith
    · simp [target, hs] at hy
  have hmodel : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasDerivAt path (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0,z) = inner ℝ (gradW t) z) ∧
      dW t (1,0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0 := by
    filter_upwards [hODE, hStateGrad, hReference] with t ho hg hr
    exact ⟨by simpa [path] using ho, hg, hr⟩
  have hWpath : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt Wpath (dW t) (t, path t) := by
    filter_upwards [hW] with t ht
    simpa [Wpath, path] using ht
  have hAttribution := Actuator.ae_closedLoop_descent_formula_of_ode_under_measure
    Wpath path dW gradW drift u0 utr actuator (futureLebesgueMeasure T)
    hWpath hmodel
  have hLocallyLipschitzWpath : LocallyLipschitzOn (Set.Ici T)
      (fun s => Wpath (s, D.trajectory (⊤ : A) E.feedback x T s)) := by
    simpa [Wpath] using hResidualLocallyLipschitz
  have hzero :=
    Actuator.ae_actuator_contribution_zero_after_target_entry_on_future
      target Wpath path hforward hWzero dW gradW drift u0 utr actuator T
      hWpath hmodel hLocallyLipschitzWpath hentry
  have hdescent : ∀ t, T ≤ t → residualDescentRateAlong
      (fun s y => E.W y s) path t = 0 := by
    intro t htt
    have hdinizero := Actuator.residualDescentRate_zero_after_target_entry
      target Wpath path hforward hWzero T t htt hentry
    simpa [residualDescentRateAlong, Wpath, path] using hdinizero
  have hfeedback : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t,
      inner ℝ (gradW t)
      (actuator t
        ((E.policyEquiv E.feedback).action
          ⟨⟨t, hT.trans htt⟩,
            D.trajectory (⊤ : A) E.feedback x T t⟩ - utr t)) = 0 := by
    filter_upwards [hzero] with t hzero_t
    intro htt
    rw [← hU0Feedback t htt]
    exact hzero_t
  exact ⟨hdescent, hfeedback⟩

/-- Equations (27.10) and (27.8) on the future ray of one common theorem-24/26
optimal-feedback path. PZS is converted to exclusion from the time-dependent
zero-value target. The derivative and input identities from 27-A remain
explicit a.e. inputs. The operator bound in (27.8) is stated as the equivalent
inner-product estimate `|⟪∇W,Gv⟫| ≤ L‖v‖`, avoiding ambiguity between the paper's
norm topology and the independently supplied metric instance. -/
theorem theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [stateMetric : PseudoMetricSpace (State (⊤ : A))]
    [stateNorm : NormedAddCommGroup (State (⊤ : A))]
    [InnerProductSpace ℝ (State (⊤ : A))] [CompleteSpace (State (⊤ : A))]
    [ContinuousSMul ℝ (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))]
    [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control]
    [controlTopology : TopologicalSpace Control]
    [BorelSpace Control] [controlNorm : NormedAddCommGroup Control]
    [InnerProductSpace ℝ Control] [CompleteSpace Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (hMetric : stateMetric = NormedAddCommGroup.toMetricSpace.toPseudoMetricSpace)
    (hControlTopology : controlTopology =
      controlNorm.toMetricSpace.toUniformSpace.toTopologicalSpace)
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (hrestart : ∀ (y : State (⊤ : A)) (a s t : ℝ),
      0 ≤ a → a ≤ s → s ≤ t →
      D.admissible (⊤ : A) E.feedback y a →
      D.trajectory (⊤ : A) E.feedback
        (D.trajectory (⊤ : A) E.feedback y a s) s t =
        D.trajectory (⊤ : A) E.feedback y a t)
    (dW : ℝ → (ℝ × State (⊤ : A) →L[ℝ] ℝ))
    (gradW drift : ℝ → State (⊤ : A))
    (u0 utr : ℝ → Control)
    (actuator : ℝ → Control →L[ℝ] State (⊤ : A))
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T, HasDerivAt
      (fun s => D.trajectory (⊤ : A) E.feedback x T s)
      (drift t + actuator t (u0 t)) t)
    (hStateGrad : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t ∂futureLebesgueMeasure T,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s))
    (hW : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × State (⊤ : A) => E.W p.2 p.1)
      (dW t) (t, D.trajectory (⊤ : A) E.feedback x T t))
    (hU0Feedback : ∀ t htt, u0 t =
      (E.policyEquiv E.feedback).action
        ⟨⟨t, hT.trans htt⟩, D.trajectory (⊤ : A) E.feedback x T t⟩)
    (L₂₇ : ℝ) (hL₂₇ : 0 < L₂₇)
    (hAdjointBound : ∀ᵐ t ∂futureLebesgueMeasure T,
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t) →
      ∀ v, |inner ℝ (gradW t) (actuator t v)| ≤ L₂₇ * ‖v‖) :
    (∀ t, T ≤ t →
      ((
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t) ↔
        0 < residualDescentRateAlong
          (fun s y => E.W y s)
          (fun s => D.trajectory (⊤ : A) E.feedback x T s) t))) ∧
    (∀ᵐ t ∂futureLebesgueMeasure T, ∀ htt : T ≤ t,
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t) ↔
        0 < -(inner ℝ (gradW t)
          (actuator t
            ((E.policyEquiv E.feedback).action
              ⟨⟨t, hT.trans htt⟩,
                D.trajectory (⊤ : A) E.feedback x T t⟩ - utr t)))) ∧
    (∀ᵐ t ∂futureLebesgueMeasure T,
      (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a s => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a s) s)
        (D.trajectory (⊤ : A) E.feedback x T t) t) →
      (E.rate * E.c₁ *
        (Metric.infDist (D.trajectory (⊤ : A) E.feedback x T t)
          (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t)) ^ 2) / L₂₇ ≤
          ‖u0 t - utr t‖ ∧ 0 < ‖u0 t - utr t‖) := by
  cases hMetric
  cases hControlTopology
  let target : ℝ → Set (State (⊤ : A)) := fun s =>
    if T ≤ s then theorem26ZeroValueTarget E.alive
      (D.optimalValue (⊤ : A)) s else ∅
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let Wpath : ℝ × State (⊤ : A) → ℝ := fun p => E.W p.2 p.1
  have hclosed : ∀ s, T ≤ s → IsClosed (target s) := by
    intro s hs
    simpa [target, hs] using E.target_closed s (hT.trans hs)
  have hnonempty : ∀ s, T ≤ s → (target s).Nonempty := by
    intro s hs
    simpa [target, hs] using E.target_nonempty s (hT.trans hs)
  have hLower : ∀ s, T ≤ s →
      E.c₁ * (Metric.infDist (path s) (target s)) ^ 2 ≤ Wpath (s, path s) := by
    intro s hsT
    have hBound := E.W_lower_distance_bound x T s hT hx hsT
    simpa [target, path, Wpath, hsT] using hBound
  have hforward : ∀ s t, T ≤ s → s ≤ t →
      path s ∈ target s → path t ∈ target t := by
    intro s t hs hst hmem
    have hmem' : path s ∈ theorem26ZeroValueTarget E.alive
        (D.optimalValue (⊤ : A)) s := by simpa [target, hs] using hmem
    have hInv := E.target_invariant (path s) s t (hT.trans hs) hmem' hst
    have hAdm : D.admissible (⊤ : A) E.feedback x T := by
      exact (E.feedback_attains_optimum x T hT hx).1
    have hrestart' := hrestart x T s t hT hs hst hAdm
    have hpathEq : path t = D.trajectory (⊤ : A) E.feedback (path s) s t :=
      hrestart'.symm
    rw [hpathEq]
    simpa [target, le_trans hs hst] using hInv
  have hWzero : ∀ s, T ≤ s → ∀ y, y ∈ target s → Wpath (s,y) = 0 := by
    intro s hs y hy
    have hy' : y ∈ theorem26ZeroValueTarget E.alive
        (D.optimalValue (⊤ : A)) s := by simpa [target, hs] using hy
    have hadm : D.admissible (⊤ : A) E.feedback y s := by
      exact (E.feedback_attains_optimum y s (hT.trans hs) hy'.1).1
    have hinit := D.trajectory_initial (⊤ : A) E.feedback y s (hT.trans hs) hadm
    have hup := E.W_upper_distance_bound y s s (hT.trans hs) hy'.1 le_rfl
    have hdist : Metric.infDist y
        (theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) s) = 0 :=
      Metric.infDist_zero_of_mem hy'
    have hWle : E.W y s ≤ 0 := by simpa [hinit, hdist] using hup
    have hWge := E.W_nonnegative y s s (hT.trans hs) hy'.1 le_rfl
    rw [hinit] at hWge
    simp [Wpath]
    linarith
  have hPZSOutside : ∀ (s : ℝ), T ≤ s →
      ((¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a r => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a r) r) (path s) s) ↔ path s ∉ target s) := by
    intro s hs
    have hs0 : 0 ≤ s := hT.trans hs
    have hAlive : path s ∈ E.alive := E.trajectory_alive x T s hT hx hs
    have hpzs := feedbackPZS_iff_zeroTarget_of_dynamics
      D E.feedback E.alive E.feedback_attains_optimum (path s) s hs0 hAlive
    simpa [path, target, hs] using (not_congr hpzs)
  have hmodel : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasDerivAt path (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0,z) = inner ℝ (gradW t) z) ∧
      dW t (1,0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0 := by
    filter_upwards [hODE, hStateGrad, hReference] with t ho hg hr
    exact ⟨by simpa [path] using ho, hg, hr⟩
  have hW' : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt Wpath (dW t) (t, path t) := by
    filter_upwards [hW] with t hWt
    simpa [Wpath, path] using hWt
  have hAttribution := Actuator.ae_closedLoop_descent_formula_of_ode_under_measure
    Wpath path dW gradW drift u0 utr actuator (futureLebesgueMeasure T)
    hW' hmodel
  have hLocallyLipschitzWpath : LocallyLipschitzOn (Set.Ici T)
      (fun s => Wpath (s, D.trajectory (⊤ : A) E.feedback x T s)) := by
    simpa [Wpath] using hResidualLocallyLipschitz
  have hDiniRay := theorem26_rightSlope_to_theorem27_Dini
    D E x T hT hx hResidualLocallyLipschitz
  have hDiniDecay : ∀ s, T ≤ s →
      E.rate * Wpath (s, path s) ≤
        -Actuator.upperRightDiniDerivative (fun t => Wpath (t, path t)) s := by
    intro s hs
    simpa [Wpath, path] using hDiniRay s hs
  have hirr :=
    theorem27_operational_ignorance_iff_descent_and_action_ae_after_time
      T target hclosed hnonempty Wpath path E.c₁ E.rate E.c₁_pos E.rate_pos
      hLower hDiniDecay
      hforward hWzero dW gradW drift u0 utr actuator hW' hmodel
      hLocallyLipschitzWpath
      (fun s => ¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
        (fun π y a r => D.runningCost (⊤ : A) π
          (D.trajectory (⊤ : A) π y a r) r) (path s) s)
      hPZSOutside
  have hgradientBound : ∀ᵐ t ∂futureLebesgueMeasure T,
      path t ∉ target t → ∀ v,
        |inner ℝ (gradW t) (actuator t v)| ≤ L₂₇ * ‖v‖ := by
    filter_upwards [hAdjointBound,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hb ht
    intro houtside
    exact hb ((hPZSOutside t ht).mpr houtside)
  have hcontrol := Actuator.ae_control_difference_distance_lower_bound_of_dini_on_future
    T target hclosed hnonempty Wpath path dW gradW drift u0 utr actuator
    E.c₁ E.rate L₂₇ E.c₁_pos E.rate_pos hL₂₇ hLower hDiniDecay hW' hmodel
    hLocallyLipschitzWpath hgradientBound
  refine ⟨?_, ?_, ?_⟩
  · intro t htt
    simpa [residualDescentRateAlong, Wpath, path] using hirr.1 t htt
  · filter_upwards [hirr.2, MeasureTheory.ae_restrict_mem measurableSet_Ici]
      with t hAction ht
    intro htt
    have hu0 := hU0Feedback t htt
    simpa [Actuator.sankhara27Contribution, hu0] using hAction
  · filter_upwards [hcontrol,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hbound ht
    intro hignor
    have houtside := (hPZSOutside t ht).mp hignor
    change T ≤ t at ht
    have htarget : target t =
        theorem26ZeroValueTarget E.alive (D.optimalValue (⊤ : A)) t := by
      simp [target, ht]
    rw [htarget] at hbound houtside
    simpa [path] using hbound houtside

/-- Equation (27.7)'s actuator attribution along the same theorem-24/26
feedback trajectory. It exposes the chain-rule identity that the other
adapters use internally: ordinary residual descent equals the negative
reference-relative actuator contribution almost everywhere on the future ray. -/
theorem theorem24_26_data_to_theorem27_descent_attribution_ae
    {A : Type*} [PartialOrder A] [OrderTop A]
    {State : A → Type*} {Feedback : A → Type*}
    [stateMetric : PseudoMetricSpace (State (⊤ : A))]
    [stateNorm : NormedAddCommGroup (State (⊤ : A))]
    [InnerProductSpace ℝ (State (⊤ : A))]
    [ContinuousSMul ℝ (State (⊤ : A))]
    [MeasurableSpace (State (⊤ : A))] [BorelSpace (State (⊤ : A))]
    {Control : Type*} [MeasurableSpace Control]
    [controlTopology : TopologicalSpace Control]
    [BorelSpace Control] [controlNorm : NormedAddCommGroup Control]
    [InnerProductSpace ℝ Control]
    [BorelSpace (Set.Ici (0 : ℝ) × State (⊤ : A))]
    (D : Theorem24NonnegativeTimeData State Feedback)
    (E : Theorem26NonnegativeTimeDynamics D Control)
    (x : State (⊤ : A)) (T : ℝ)
    (hMetric : stateMetric = NormedAddCommGroup.toMetricSpace.toPseudoMetricSpace)
    (hControlTopology : controlTopology =
      controlNorm.toMetricSpace.toUniformSpace.toTopologicalSpace)
    (dW : ℝ → (ℝ × State (⊤ : A) →L[ℝ] ℝ))
    (gradW drift : ℝ → State (⊤ : A))
    (u0 utr : ℝ → Control)
    (actuator : ℝ → Control →L[ℝ] State (⊤ : A))
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T, HasDerivAt
      (fun s => D.trajectory (⊤ : A) E.feedback x T s)
      (drift t + actuator t (u0 t)) t)
    (hStateGrad : ∀ᵐ t ∂futureLebesgueMeasure T, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t ∂futureLebesgueMeasure T,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hW : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × State (⊤ : A) => E.W p.2 p.1)
        (dW t) (t, D.trajectory (⊤ : A) E.feedback x T t)) :
    ∀ᵐ t ∂futureLebesgueMeasure T,
      (-(deriv (fun s : ℝ => E.W
        (D.trajectory (⊤ : A) E.feedback x T s) s) t)) =
        -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := by
  cases hMetric
  cases hControlTopology
  let path : ℝ → State (⊤ : A) :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  have hmodel : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasDerivAt path (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0,z) = inner ℝ (gradW t) z) ∧
      dW t (1,0) + inner ℝ (gradW t)
      (drift t + actuator t (utr t)) = 0 := by
    filter_upwards [hODE, hStateGrad, hReference] with t ho hg hr
    exact ⟨by simpa [path] using ho, hg, hr⟩
  have hW' : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × State (⊤ : A) => E.W p.2 p.1)
        (dW t) (t, path t) := by
    filter_upwards [hW] with t ht
    simpa [path] using ht
  simpa [path] using
    (Actuator.ae_closedLoop_descent_formula_of_ode_under_measure
      (fun p : ℝ × State (⊤ : A) => E.W p.2 p.1) path dW gradW drift u0 utr
      actuator (futureLebesgueMeasure T) hW' hmodel)

/-- The finite-dimensional trajectory and regularity clauses of condition
27-A supply the main adapter's curve derivative, joint Fréchet derivative,
state gradient, and feedback input without arbitrary witness functions. The
reference-loop cancellation (27-A2), the adjoint bound, and restart identity
remain separate inputs to the full (27.10)/(27.8) adapter. -/
theorem theorem24_26_data_to_theorem27_canonical_inputs_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (drift : ℝ → EuclideanSpace ℝ ι)
    (actuator : ℝ → (EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι))
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        drift t + actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t)) :
    ∃ dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ),
    ∃ gradW : ℝ → EuclideanSpace ℝ ι,
    ∃ u0 : ℝ → EuclideanSpace ℝ κ,
      (∀ᵐ t ∂futureLebesgueMeasure T, HasDerivAt
        (fun s => D.trajectory (⊤ : A) E.feedback x T s)
        (drift t + actuator t (u0 t)) t) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T,
        HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
          (dW t) (t, D.trajectory (⊤ : A) E.feedback x T t)) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T, ∀ z,
        dW t (0, z) = inner ℝ (gradW t) z) ∧
      (∀ t (htt : T ≤ t), u0 t = (E.policyEquiv E.feedback).action
        ⟨⟨t, hT.trans htt⟩, D.trajectory (⊤ : A) E.feedback x T t⟩) ∧
      dW = Actuator.jointDerivativeOnPath (fun y s => E.W y s)
        (fun s => D.trajectory (⊤ : A) E.feedback x T s) ∧
      gradW = (fun t => Actuator.stateGradientFromFDeriv (dW t)) ∧
      u0 = policyInputAlongTrajectory (E.policyEquiv E.feedback)
        (D.trajectory (⊤ : A) E.feedback) x T := by
  let path : ℝ → EuclideanSpace ℝ ι :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let dW := Actuator.jointDerivativeOnPath (fun y s => E.W y s) path
  let gradW := fun t => Actuator.stateGradientFromFDeriv (dW t)
  let u0 := policyInputAlongTrajectory (E.policyEquiv E.feedback)
    (D.trajectory (⊤ : A) E.feedback) x T
  have hcurve : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasDerivAt path (drift t + actuator t (u0 t)) t := by
    exact Actuator.ae_hasDerivAt_pi_on_future_of_ac_and_ode
      T path (fun t => drift t + actuator t (u0 t)) hac (by
        simpa [path, u0] using hODE)
  have hjoint : ∀ᵐ t ∂futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
        (dW t) (t, path t) := by
    simpa [dW, path] using
      (Actuator.jointDerivativeOnPath_hasFDerivAt_of_contDiffAt
        T (fun y s => E.W y s) path (by
          intro t htt
          simpa [path] using hC1 t htt))
  refine ⟨dW, gradW, u0, hcurve, hjoint, ?_, ?_, rfl, rfl, rfl⟩
  · exact Filter.Eventually.of_forall fun t z =>
      Actuator.stateGradientFromFDeriv_inner (dW t) z
  · intro t htt
    exact policyInputAlongTrajectory_eq_action
      (E.policyEquiv E.feedback) (D.trajectory (⊤ : A) E.feedback)
      x T t hT htt

/-- Combine the analytically constructed canonical inputs with the source-level
actuator record. The result provides one coherent input package for invoking
the (27.7)/(27.8)/(27.9)/(27.10) adapters on the same D/E path, including the
allowed-control subset, reference cancellation, and adjoint estimate. -/
theorem theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (P : Theorem27PathActuatorData D E x T hT)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        P.drift t + P.actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t)) :
    ∃ dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ),
    ∃ gradW : ℝ → EuclideanSpace ℝ ι,
    ∃ u0 : ℝ → EuclideanSpace ℝ κ,
      (∀ᵐ t ∂futureLebesgueMeasure T, HasDerivAt
        (fun s => D.trajectory (⊤ : A) E.feedback x T s)
        (P.drift t + P.actuator t (u0 t)) t) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T,
        HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
          (dW t) (t, D.trajectory (⊤ : A) E.feedback x T t)) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T, ∀ z,
        dW t (0, z) = inner ℝ (gradW t) z) ∧
      (∀ t (htt : T ≤ t), u0 t = (E.policyEquiv E.feedback).action
        ⟨⟨t, hT.trans htt⟩, D.trajectory (⊤ : A) E.feedback x T t⟩) ∧
      (∀ t (htt : T ≤ t), u0 t ∈ P.allowedInput) ∧
      (∀ t (htt : T ≤ t), P.referenceInput t ∈ P.allowedInput) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T,
        dW t (1, 0) + inner ℝ (gradW t)
          (P.drift t + P.actuator t (P.referenceInput t)) = 0) ∧
      (∀ᵐ t ∂futureLebesgueMeasure T,
        (¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
          (fun π y a s => D.runningCost (⊤ : A) π
            (D.trajectory (⊤ : A) π y a s) s)
          (D.trajectory (⊤ : A) E.feedback x T t) t) →
          ‖(P.actuator t).adjoint (gradW t)‖ ≤ P.L₂₇) ∧
      Measurable (fun t : Set.Ici T => P.actuator t.1
        (u0 t.1 - P.referenceInput t.1)) ∧
      dW = Actuator.jointDerivativeOnPath (fun y s => E.W y s)
        (fun s => D.trajectory (⊤ : A) E.feedback x T s) ∧
      gradW = (fun t => Actuator.stateGradientFromFDeriv (dW t)) ∧
      u0 = policyInputAlongTrajectory (E.policyEquiv E.feedback)
        (D.trajectory (⊤ : A) E.feedback) x T := by
  obtain ⟨dW, gradW, u0, hcurve, hW, hstateGradient, hInput,
      hdW, hgradW, hu0⟩ :=
    theorem24_26_data_to_theorem27_canonical_inputs_of_27A
      D E x T hT hac P.drift P.actuator hODE hC1
  subst dW
  subst gradW
  subst u0
  refine ⟨_, _, _, hcurve, hW, hstateGradient, hInput,
    ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro t htt
    rw [hInput t htt]
    exact P.feedbackInput_allowed t htt
  · exact P.referenceInput_allowed
  · exact P.referenceCancellation_ae
  · exact P.adjointBound_ae
  · exact P.actuatorDifference_measurable

/-- Direct source-condition entry point for the complete operational
(27.10)/(27.8) result. This invokes the canonical-input and path-actuator
bridges above, then calls the shared D/E adapter with the paper's metric and
topology identities discharged by `rfl`. -/
noncomputable def theorem24_26_data_to_theorem27_operational_results_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (P : Theorem27PathActuatorData D E x T hT)
    (hrestart : ∀ (y : EuclideanSpace ℝ ι) (a s t : ℝ),
      0 ≤ a → a ≤ s → s ≤ t →
      D.admissible (⊤ : A) E.feedback y a →
      D.trajectory (⊤ : A) E.feedback
        (D.trajectory (⊤ : A) E.feedback y a s) s t =
        D.trajectory (⊤ : A) E.feedback y a t)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        P.drift t + P.actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t))
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) := by
  classical
  let hInputs := theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A
    D E x T hT P hac hODE hC1
  let dW := Classical.choose hInputs
  let hGradExists := Classical.choose_spec hInputs
  let gradW := Classical.choose hGradExists
  let hControlExists := Classical.choose_spec hGradExists
  let u0 := Classical.choose hControlExists
  let hData := Classical.choose_spec hControlExists
  let hODE' := hData.1
  let hW := hData.2.1
  let hStateGrad := hData.2.2.1
  let hU0Feedback := hData.2.2.2.1
  let hReference := hData.2.2.2.2.2.2.1
  let hAdjoint := hData.2.2.2.2.2.2.2.1
  let hAdjointInner := Actuator.ae_inner_action_bound_of_adjoint_norm_bound_on
    (futureLebesgueMeasure T)
    (fun t => ¬ FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y a s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y a s) s)
      (D.trajectory (⊤ : A) E.feedback x T t) t)
    gradW P.actuator P.L₂₇ hAdjoint
  exact theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := A) (State := fun _ : A => EuclideanSpace ℝ ι)
    (Control := EuclideanSpace ℝ κ)
    euclideanStateMetric_eq_norm_induced
    euclideanControlTopology_eq_norm_induced
    D E x T hT hx hrestart dW gradW P.drift u0 P.referenceInput P.actuator
    hODE' hStateGrad hReference hResidualLocallyLipschitz hW hU0Feedback
    P.L₂₇ P.L₂₇_pos hAdjointInner

/-- Source-condition entry point for (27.9), using the same canonical 27-A
inputs as the operational result. Quiescence remains conditional on PZS, as
in the theorem statement. -/
noncomputable def theorem24_26_data_to_theorem27_quiescence_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T) (hx : x ∈ E.alive)
    (P : Theorem27PathActuatorData D E x T hT)
    (hPZS : FeedbackPZS (D.admissible (⊤ : A)) futureLebesgueMeasure
      (fun π y t s => D.runningCost (⊤ : A) π
        (D.trajectory (⊤ : A) π y t s) s) x T)
    (hrestart : ∀ (y : EuclideanSpace ℝ ι) (a s t : ℝ),
      0 ≤ a → a ≤ s → s ≤ t →
      D.admissible (⊤ : A) E.feedback y a →
      D.trajectory (⊤ : A) E.feedback
        (D.trajectory (⊤ : A) E.feedback y a s) s t =
        D.trajectory (⊤ : A) E.feedback y a t)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        P.drift t + P.actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t))
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) := by
  classical
  let hInputs := theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A
    D E x T hT P hac hODE hC1
  let dW := Classical.choose hInputs
  let hGradExists := Classical.choose_spec hInputs
  let gradW := Classical.choose hGradExists
  let hControlExists := Classical.choose_spec hGradExists
  let u0 := Classical.choose hControlExists
  let hData := Classical.choose_spec hControlExists
  exact theorem24_26_data_to_theorem27_quiescence
    (A := A) (State := fun _ : A => EuclideanSpace ℝ ι)
    (Control := EuclideanSpace ℝ κ)
    euclideanStateMetric_eq_norm_induced
    euclideanControlTopology_eq_norm_induced
    D E x T hT hx hPZS hrestart dW gradW P.drift u0
    P.referenceInput P.actuator hData.1 hData.2.2.1
    hData.2.2.2.2.2.2.1 hResidualLocallyLipschitz
    hData.2.1 hData.2.2.2.1

/-- Equation (27.7) with its inputs supplied by the same 27-A path record
used by the (27.8)–(27.10) and (27.9) source entries above. -/
noncomputable def theorem24_26_data_to_theorem27_descent_attribution_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (P : Theorem27PathActuatorData D E x T hT)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        P.drift t + P.actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t)) := by
  classical
  let hInputs := theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A
    D E x T hT P hac hODE hC1
  let dW := Classical.choose hInputs
  let hGradExists := Classical.choose_spec hInputs
  let gradW := Classical.choose hGradExists
  let hControlExists := Classical.choose_spec hGradExists
  let u0 := Classical.choose hControlExists
  let hData := Classical.choose_spec hControlExists
  exact theorem24_26_data_to_theorem27_descent_attribution_ae
    (A := A) (State := fun _ : A => EuclideanSpace ℝ ι)
    (Control := EuclideanSpace ℝ κ)
    D E x T euclideanStateMetric_eq_norm_induced
    euclideanControlTopology_eq_norm_induced dW gradW P.drift u0
    P.referenceInput P.actuator hData.1 hData.2.2.1
    hData.2.2.2.2.2.2.1 hData.2.1

/-- The right-Dini-derivative form of equation (27.7). The chain-rule
identity is combined with the a.e. equality of the Dini derivative and the
ordinary derivative under the paper's local-Lipschitz hypothesis. -/
noncomputable def theorem24_26_data_to_theorem27_dini_attribution_of_27A
    {A : Type*} [PartialOrder A] [OrderTop A]
    {Feedback : A → Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [BorelSpace (Set.Ici (0 : ℝ) × EuclideanSpace ℝ ι)]
    (D : Theorem24NonnegativeTimeData
      (fun _ : A => EuclideanSpace ℝ ι) Feedback)
    (E : Theorem26NonnegativeTimeDynamics D (EuclideanSpace ℝ κ))
    (x : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (P : Theorem27PathActuatorData D E x T hT)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval
      (fun s => D.trajectory (⊤ : A) E.feedback x T s) T b)
    (hODE : ∀ᵐ t ∂futureLebesgueMeasure T,
      deriv (fun s => D.trajectory (⊤ : A) E.feedback x T s) t =
        P.drift t + P.actuator t
          (policyInputAlongTrajectory (E.policyEquiv E.feedback)
            (D.trajectory (⊤ : A) E.feedback) x T t))
    (hC1 : ∀ t, T ≤ t → ContDiffAt ℝ 1
      (fun p : ℝ × EuclideanSpace ℝ ι => E.W p.2 p.1)
      (t, D.trajectory (⊤ : A) E.feedback x T t))
    (hResidualLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => E.W (D.trajectory (⊤ : A) E.feedback x T s) s)) := by
  classical
  let hInputs := theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A
    D E x T hT P hac hODE hC1
  let dW := Classical.choose hInputs
  let hGradExists := Classical.choose_spec hInputs
  let gradW := Classical.choose hGradExists
  let hControlExists := Classical.choose_spec hGradExists
  let u0 := Classical.choose hControlExists
  let hData := Classical.choose_spec hControlExists
  let path : ℝ → EuclideanSpace ℝ ι :=
    fun s => D.trajectory (⊤ : A) E.feedback x T s
  let Wpath : ℝ → EuclideanSpace ℝ ι → ℝ := fun s y => E.W y s
  have hAttribution := theorem24_26_data_to_theorem27_descent_attribution_ae
    (A := A) (State := fun _ : A => EuclideanSpace ℝ ι)
    (Control := EuclideanSpace ℝ κ)
    D E x T euclideanStateMetric_eq_norm_induced
    euclideanControlTopology_eq_norm_induced dW gradW P.drift u0
    P.referenceInput P.actuator hData.1 hData.2.2.1
    hData.2.2.2.2.2.2.1 hData.2.1
  have hDiniEq := Actuator.ae_upperRightDiniDerivative_eq_deriv_on_future
    (fun s => Wpath s (path s)) T hResidualLocallyLipschitz
  have hDiniAttribution : ∀ᵐ t ∂futureLebesgueMeasure T,
      -(Actuator.upperRightDiniDerivative (fun s => Wpath s (path s)) t) =
        -(inner ℝ (gradW t)
          (P.actuator t (u0 t - P.referenceInput t))) := by
    filter_upwards [hAttribution, hDiniEq] with t hchain hDini
    rw [hDini]
    exact hchain
  exact And.intro hAttribution hDiniAttribution


end Tomabechi.Theorem24_26_27


#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_classification
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_residual_descent
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_future_quantitative_descent
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_quiescence
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
#print axioms Tomabechi.Theorem24_26_27.trajectory_restart_of_future_ode_unique
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_feedback_restart_of_unique_ode
#print axioms Tomabechi.Theorem24_26_27.policyInputAlongTrajectory_eq_action
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_canonical_inputs_of_27A
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_descent_attribution_ae
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_results_of_27A
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_quiescence_of_27A
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_descent_attribution_of_27A
#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_dini_attribution_of_27A
#print axioms Tomabechi.Theorem24_26_27.euclideanStateMetric_eq_norm_induced
#print axioms Tomabechi.Theorem24_26_27.euclideanControlTopology_eq_norm_induced

#print axioms Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_future_descent_chain
