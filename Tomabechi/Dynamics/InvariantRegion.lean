import Theorem22

/-!
# 定理22：初期部分準位等式を使わない不変領域入口

この補助モジュールは段階ポテンシャルの閾値条件と、別途与えた前向き
不変領域を組み合わせる。領域は初期値の全エネルギー部分準位集合である
必要がない。谷・大域軌道・一意性および指数率は定理21の既存核から得る。
-/

open Tomabechi.Theorem21 RealInnerProductSpace
open scoped Topology

namespace Tomabechi.Theorem22InvariantRegion

/-- 閾値で得る一意谷を、任意の前向き不変領域上の大域凍結軌道へ接続する。

`C` は初期値の全エネルギー部分準位と等しい必要はない。必要なのは、
初期状態と閾値から得る谷が `C` に属し、`C` の閉包が局所球の内部にあり、
閉ループODEが `C` を前向き不変にすることである。曲率余裕
`κ * p * m - β` と移動度下界 `gamma` による原定量指数率を返す。
不変性と谷の所属は入力条件であり、Hessian閾値のみから導いたとは主張しない。
日本語要約：初期エネルギー部分準位との等式を外し、任意の適切な不変領域から同じ指数率を得る。 -/
theorem per_stage_valley_global_existence_and_decay_on_invariant_region
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcontDiff : ContDiffOn ℝ 1 V (Metric.closedBall center r))
    (hScontDiff : ContDiffOn ℝ 1 S (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E) (C : Set E) (gamma t₀ : ℝ)
    (x₀ : E) (hx₀ : x₀ ∈ C)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1
        (fun y => -(A y (gradV y - (κ * p) • gradS y))) x)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hminimizerInC : ∀ x, x ∈ Metric.closedBall center r →
      IsMinOn (fun y => V y - κ * p * S y)
        (Metric.closedBall center r) x → x ∈ C)
    (hinvariant : ∀ (a d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit a = x → x ∈ C →
      (∀ t ∈ Set.Icc a (a + d),
        HasDerivAt orbit
          (-(A (orbit t) (gradV (orbit t) - (κ * p) • gradS (orbit t)))) t) →
      ∀ t ∈ Set.Icc a (a + d), orbit t ∈ C)
    (hgamma : 0 < gamma)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      gradV xstar - (κ * p) • gradS xstar = 0 ∧
      ∃ trajectory : ℝ → E, ∃ epsilon : ℝ,
        0 < epsilon ∧ trajectory t₀ = x₀ ∧
        (∀ t ∈ Set.Ioi (t₀ - epsilon),
          HasDerivAt trajectory
            (-(A (trajectory t)
              (gradV (trajectory t) - (κ * p) • gradS (trajectory t)))) t) ∧
        (∀ t ∈ Set.Ici t₀, trajectory t ∈ C) ∧
        (∀ t ∈ Set.Ici t₀,
          0 ≤ (V (trajectory t₀) - κ * p * S (trajectory t₀)) -
            (V xstar - κ * p * S xstar) ∧
          (V (trajectory t) - κ * p * S (trajectory t)) -
            (V xstar - κ * p * S xstar) ≤
              ((V (trajectory t₀) - κ * p * S (trajectory t₀)) -
                (V xstar - κ * p * S xstar)) *
                Real.exp (-2 * gamma * (κ * p * m - β) * (t - t₀)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((V (trajectory t₀) - κ * p * S (trajectory t₀)) -
              (V xstar - κ * p * S xstar)) / (κ * p * m - β)) *
              Real.exp (-gamma * (κ * p * m - β) * (t - t₀))) ∧
        (∀ other : ℝ → E, other t₀ = x₀ →
          (∀ t ∈ Set.Ici t₀, other t ∈ C) →
          (∀ t ∈ Set.Ioi (t₀ - epsilon),
            HasDerivAt other
              (-(A (other t)
                (gradV (other t) - (κ * p) • gradS (other t)))) t) →
          ∀ t ∈ Set.Ici t₀, other t = trajectory t) := by
  let U := Metric.closedBall center r
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hVcont : ContinuousOn V U := hVcontDiff.continuousOn
  have hScont : ContinuousOn S U := hScontDiff.continuousOn
  obtain ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary, hmargin⟩ :=
    Tomabechi.Theorem22.per_stage_unique_interior_minimum
      center r κ p m β B hr hκ hm hβ hB hp
      V S gradV gradS HV HS hVcont hScont hV hS hHV hHS
      hVlower hSlower hcenter hVbound
  have hconvex := Tomabechi.Theorem22.per_stage_effective_strong_convexity
    center r κ p m β B
    hr hκ hm hβ hB hp V S gradV gradS HV HS hV hS hHV hHS
    hVlower hSlower
  have hpotential : ∀ x ∈ U,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff U := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hxstarC : xstar ∈ C :=
    hminimizerInC xstar (interior_subset hxstar) (by simpa [Veff] using hmin)
  have hCsub : C ⊆ U := by
    intro x hx
    exact Metric.ball_subset_closedBall (hCclosureInterior (subset_closure hx))
  have hfieldC1' : ∀ x ∈ U,
      ContDiffAt ℝ 1 (fun y => -(A y (geff y))) x := by
    intro x hx
    simpa [geff] using hfieldC1 x hx
  have hstationary' : geff xstar = 0 := by
    simpa [geff] using hstationary
  have hresult :=
    Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_existence_and_decay
      center r t₀ (κ * p * m - β) gamma hr.le hmargin hgamma
      Veff geff A U C xstar x₀ hfieldC1' hCclosureInterior hinvariant hCsub
      hxstarC hx₀ hstationary' hconvex hpotential hpotentialC1 hcoercive
  rcases hresult with ⟨trajectory, epsilon, hepsilon, hinitial, hflow,
      htrajectoryC, hdecay, huniqueFlow⟩
  refine ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary,
    trajectory, epsilon, hepsilon, hinitial, ?_, htrajectoryC, ?_, ?_⟩
  · intro t ht
    simpa [geff] using hflow t ht
  · intro t ht
    simpa [U, Veff, geff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht
  · intro other hotherInit hotherC hotherFlow t ht
    exact huniqueFlow other hotherInit hotherC (by
      intro s hs
      simpa [geff] using hotherFlow s hs) t ht

/-- Apply the relaxed valley and orbit theorem directly to an averaged
mean-field stage. The integral presentation is carried by the input record;
the same `meanField` supplies the potential, gradient, and Hessian throughout.
The C¹ closed-loop hypothesis of the low-level theorem is derived here from
the stage's C² potentials, Riesz gradient representations, and C¹ mobility.
日本語要約：平均場積分表示を保持した不変領域段階入力を、緩和済みの定量軌道結論へ接続する。 -/
theorem meanField_invariant_region_stage_conclusions
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) :
    ∃ xstar ∈ interior (Metric.closedBall s.center s.radius),
      IsMinOn
        (fun x => s.background x - s.gain * s.presenceGain * s.meanField x)
        (Metric.closedBall s.center s.radius) xstar ∧
      (∀ y ∈ Metric.closedBall s.center s.radius,
        s.background y - s.gain * s.presenceGain * s.meanField y =
          s.background xstar - s.gain * s.presenceGain * s.meanField xstar →
          y = xstar) ∧
      ‖xstar - s.center‖ ≤
        s.gradientBound / (s.gain * s.presenceGain * s.curvature -
          s.backgroundCurvature) ∧
      s.backgroundGradient xstar - (s.gain * s.presenceGain) •
        s.meanFieldGradient xstar = 0 ∧
      ∃ trajectory : ℝ → E, ∃ epsilon : ℝ,
        0 < epsilon ∧ trajectory s.startTime = s.initial ∧
        (∀ t ∈ Set.Ioi (s.startTime - epsilon),
          HasDerivAt trajectory
            (-(s.mobility (trajectory t)
              (s.backgroundGradient (trajectory t) -
                (s.gain * s.presenceGain) • s.meanFieldGradient (trajectory t)))) t) ∧
        (∀ t ∈ Set.Ici s.startTime, trajectory t ∈ s.sublevel) ∧
        (∀ t ∈ Set.Ici s.startTime,
          0 ≤ (s.background (trajectory s.startTime) -
            s.gain * s.presenceGain * s.meanField (trajectory s.startTime)) -
              (s.background xstar - s.gain * s.presenceGain * s.meanField xstar) ∧
          (s.background (trajectory t) - s.gain * s.presenceGain *
            s.meanField (trajectory t)) -
              (s.background xstar - s.gain * s.presenceGain * s.meanField xstar) ≤
            ((s.background (trajectory s.startTime) -
              s.gain * s.presenceGain * s.meanField (trajectory s.startTime)) -
                (s.background xstar - s.gain * s.presenceGain *
                  s.meanField xstar)) *
              Real.exp (-2 * s.gamma *
                (s.gain * s.presenceGain * s.curvature -
                  s.backgroundCurvature) * (t - s.startTime)) ∧
          ‖trajectory t - xstar‖ ≤
            Real.sqrt (2 * ((s.background (trajectory s.startTime) -
              s.gain * s.presenceGain * s.meanField (trajectory s.startTime)) -
                (s.background xstar - s.gain * s.presenceGain *
                  s.meanField xstar)) /
              (s.gain * s.presenceGain * s.curvature -
                s.backgroundCurvature)) *
              Real.exp (-s.gamma *
                (s.gain * s.presenceGain * s.curvature -
                  s.backgroundCurvature) * (t - s.startTime))) ∧
        (∀ other : ℝ → E, other s.startTime = s.initial →
          (∀ t ∈ Set.Ici s.startTime, other t ∈ s.sublevel) →
          (∀ t ∈ Set.Ioi (s.startTime - epsilon),
            HasDerivAt other
              (-(s.mobility (other t)
                (s.backgroundGradient (other t) -
                  (s.gain * s.presenceGain) • s.meanFieldGradient (other t)))) t) →
          ∀ t ∈ Set.Ici s.startTime, other t = trajectory t) := by
  have hVcontDiff : ContDiffOn ℝ 1 s.background
      (Metric.closedBall s.center s.radius) := by
    intro x hx
    exact ((s.background_c2_at x hx).of_le (by norm_num)).contDiffWithinAt
  have hScontDiff : ContDiffOn ℝ 1 s.meanField
      (Metric.closedBall s.center s.radius) := by
    intro x hx
    exact ((s.meanField_c2_at x hx).of_le (by norm_num)).contDiffWithinAt
  have hV : ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.background (innerSL ℝ (s.backgroundGradient x)) x := by
    intro x hx
    have hdiff := (s.background_c2_at x hx).differentiableAt (by norm_num)
    convert hdiff.hasFDerivAt using 1
    exact s.background_gradient_representation x
  have hS : ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.meanField (innerSL ℝ (s.meanFieldGradient x)) x := by
    intro x hx
    have hdiff := (s.meanField_c2_at x hx).differentiableAt (by norm_num)
    convert hdiff.hasFDerivAt using 1
    exact s.meanField_gradient_representation x
  have hfieldC1 : ∀ x ∈ Metric.closedBall s.center s.radius,
      ContDiffAt ℝ 1
        (fun y => -(s.mobility y
          (s.backgroundGradient y -
            (s.gain * s.presenceGain) • s.meanFieldGradient y))) x := by
    intro x hx
    have hgradient : ContDiffAt ℝ 1
        (fun y => s.backgroundGradient y -
          (s.gain * s.presenceGain) • s.meanFieldGradient y) x := by
      exact (Tomabechi.Theorem22.contDiffAt_gradient_of_c2 s.background
        s.backgroundGradient x (s.background_c2_at x hx)
        s.background_gradient_representation).sub
        ((Tomabechi.Theorem22.contDiffAt_gradient_of_c2 s.meanField
          s.meanFieldGradient x (s.meanField_c2_at x hx)
          s.meanField_gradient_representation).const_smul
            (s.gain * s.presenceGain))
    exact ((s.mobility_c1 x hx).clm_apply hgradient).neg
  exact per_stage_valley_global_existence_and_decay_on_invariant_region
    s.center s.radius s.gain s.presenceGain s.curvature s.backgroundCurvature
    s.gradientBound s.radius_pos s.gain_pos s.curvature_pos
    s.backgroundCurvature_nonneg s.gradientBound_nonneg s.gain_threshold
    s.background s.meanField s.backgroundGradient s.meanFieldGradient
    s.backgroundHessian s.meanFieldHessian hVcontDiff hScontDiff hV hS
    s.background_gradient_deriv s.meanField_gradient_deriv
    s.background_hessian_lower s.meanField_hessian_upper
    s.meanField_center_stationary s.background_gradient_bound
    s.mobility s.sublevel s.gamma s.startTime s.initial s.initial_mem
    hfieldC1 s.sublevel_barrier s.minimizer_in_sublevel s.forward_invariant
    s.gamma_pos s.mobility_coercive

/-- The previous exact-initial-sublevel input embeds into the relaxed input.
The minimizer membership follows from global minimality and the initial
membership; forward invariance follows from the existing strict-interior
barrier and gradient-flow dissipation lemma. -/
def MeanFieldStageInput.toInvariantRegionInput
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.MeanFieldStageInput E) :
    Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E := by
  let spec := s.toStageValleySpec
  let Veff : E → ℝ := fun x =>
    s.background x - s.gain * s.presenceGain * s.meanField x
  let geff : E → E := fun x =>
    s.backgroundGradient x - (s.gain * s.presenceGain) • s.meanFieldGradient x
  have hpotential : ∀ y ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt Veff (innerSL ℝ (geff y)) y := by
    intro y hy
    have hV := spec.backgroundHasFDerivAt y hy
    have hS := spec.presenceHasFDerivAt y hy
    have h := hV.sub (hS.const_mul (s.gain * s.presenceGain))
    convert h using 1
    · funext z
      simp [Veff, spec, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
        mul_assoc, mul_left_comm, mul_comm]
    · simp [geff, spec, Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
        innerSL_apply_apply, inner_smul_left, mul_assoc, mul_left_comm, mul_comm]
  have hinitialBall : s.initial ∈ Metric.closedBall s.center s.radius := by
    have h := s.initial_mem
    rw [s.sublevel_eq] at h
    exact h.1
  refine {
    toMeanFieldStageCore := s.toMeanFieldStageCore
    minimizer_in_sublevel := ?_
    forward_invariant := ?_ }
  · intro x hx hmin
    rw [s.sublevel_eq]
    refine ⟨hx, ?_⟩
    have hminInitial := hmin hinitialBall
    change Veff x ≤ Veff s.initial at hminInitial
    exact hminInitial
  · intro a d orbit x hd hstart hx hflow t ht
    have hflow' : ∀ τ ∈ Set.Icc a (a + d),
        HasDerivAt orbit (-(s.mobility (orbit τ) (geff (orbit τ)))) τ := by
      intro τ hτ
      simpa [geff] using hflow τ hτ
    have hstay := Tomabechi.Theorem21.forward_invariant_sublevel_of_strict_interior_barrier
      orbit Veff geff s.mobility s.center s.radius s.gamma a (a + d)
      (Veff s.initial) s.gamma_pos (le_add_of_nonneg_right hd)
      s.sublevel s.sublevel_eq
      (fun y hy => s.sublevel_barrier (subset_closure hy))
      x hx hstart hpotential hflow' s.mobility_coercive
    exact hstay t ht

/-- A stage witness indexed by the relaxed mean-field input. Unlike
`StageValleyWitness`, its orbit remains in the supplied invariant region and
does not require that region to be an exact energy sublevel. -/
structure InvariantRegionStageWitness {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) where
  minimizer : E
  minimizer_interior : minimizer ∈ interior
    (Metric.closedBall s.center s.radius)
  minimizer_is_min : IsMinOn
    (fun x => s.background x - s.gain * s.presenceGain * s.meanField x)
    (Metric.closedBall s.center s.radius) minimizer
  minimizer_unique : ∀ y ∈ Metric.closedBall s.center s.radius,
    s.background y - s.gain * s.presenceGain * s.meanField y =
      s.background minimizer - s.gain * s.presenceGain * s.meanField minimizer →
      y = minimizer
  displacement_bound : ‖minimizer - s.center‖ ≤
    s.gradientBound / (s.gain * s.presenceGain * s.curvature -
      s.backgroundCurvature)
  stationary : s.backgroundGradient minimizer -
    (s.gain * s.presenceGain) • s.meanFieldGradient minimizer = 0
  positive_margin : 0 <
    s.gain * s.presenceGain * s.curvature - s.backgroundCurvature
  orbit : ℝ → E
  local_extension : ℝ
  local_extension_pos : 0 < local_extension
  initial_condition : orbit s.startTime = s.initial
  orbit_ode : ∀ t ∈ Set.Ioi (s.startTime - local_extension),
    HasDerivAt orbit
      (-(s.mobility (orbit t)
        (s.backgroundGradient (orbit t) -
          (s.gain * s.presenceGain) • s.meanFieldGradient (orbit t)))) t
  orbit_in_region : ∀ t ∈ Set.Ici s.startTime, orbit t ∈ s.sublevel
  orbit_decay : ∀ t ∈ Set.Ici s.startTime,
    0 ≤ (s.background (orbit s.startTime) -
      s.gain * s.presenceGain * s.meanField (orbit s.startTime)) -
        (s.background minimizer - s.gain * s.presenceGain * s.meanField minimizer) ∧
    (s.background (orbit t) - s.gain * s.presenceGain * s.meanField (orbit t)) -
      (s.background minimizer - s.gain * s.presenceGain * s.meanField minimizer) ≤
        ((s.background (orbit s.startTime) -
          s.gain * s.presenceGain * s.meanField (orbit s.startTime)) -
            (s.background minimizer - s.gain * s.presenceGain * s.meanField minimizer)) *
          Real.exp (-2 * s.gamma *
            (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) *
            (t - s.startTime)) ∧
    ‖orbit t - minimizer‖ ≤
      Real.sqrt (2 * ((s.background (orbit s.startTime) -
        s.gain * s.presenceGain * s.meanField (orbit s.startTime)) -
          (s.background minimizer - s.gain * s.presenceGain * s.meanField minimizer)) /
        (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)) *
        Real.exp (-s.gamma *
          (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) *
          (t - s.startTime))
  orbit_unique : ∀ other : ℝ → E, other s.startTime = s.initial →
    (∀ t ∈ Set.Ici s.startTime, other t ∈ s.sublevel) →
    (∀ t ∈ Set.Ioi (s.startTime - local_extension),
      HasDerivAt other
        (-(s.mobility (other t)
          (s.backgroundGradient (other t) -
            (s.gain * s.presenceGain) • s.meanFieldGradient (other t)))) t) →
    ∀ t ∈ Set.Ici s.startTime, other t = orbit t

namespace InvariantRegionStageWitness

/-- Initial energy gap prefactor for the state-distance estimate. -/
noncomputable def decayAmplitude {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (w : InvariantRegionStageWitness s) : ℝ :=
  Real.sqrt (2 * ((s.background (w.orbit s.startTime) -
    s.gain * s.presenceGain * s.meanField (w.orbit s.startTime)) -
      (s.background w.minimizer - s.gain * s.presenceGain *
        s.meanField w.minimizer)) /
      (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature))

/-- Quantitative exponential rate, matching (22.4). -/
def decayRate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (_w : InvariantRegionStageWitness s) : ℝ :=
  s.gamma * (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)

theorem decayAmplitude_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (w : InvariantRegionStageWitness s) : 0 ≤ w.decayAmplitude :=
  Real.sqrt_nonneg _

theorem decayRate_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (w : InvariantRegionStageWitness s) : 0 < w.decayRate :=
  mul_pos s.gamma_pos w.positive_margin

theorem distance_decay {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (w : InvariantRegionStageWitness s) (t : ℝ) (ht : s.startTime ≤ t) :
    dist (w.orbit t) w.minimizer ≤
      w.decayAmplitude * Real.exp (-w.decayRate * (t - s.startTime)) := by
  have hdecay := (w.orbit_decay t ht).2.2
  have hexponent : -s.gamma *
      (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) *
        (t - s.startTime) = -w.decayRate * (t - s.startTime) := by
    simp [decayRate]
  rw [dist_eq_norm]
  rw [hexponent] at hdecay
  simpa [decayAmplitude] using hdecay

end InvariantRegionStageWitness

/-- The selected relaxed frozen orbit satisfies its ODE at every forward
time, because the local extension interval reaches strictly before the stage
start. -/
theorem InvariantRegionStageWitness.orbit_ode_forward {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E}
    (w : InvariantRegionStageWitness s) (t : ℝ)
    (ht : s.startTime ≤ t) :
    HasDerivAt w.orbit
      (-(s.mobility (w.orbit t)
        (s.backgroundGradient (w.orbit t) -
          (s.gain * s.presenceGain) • s.meanFieldGradient (w.orbit t)))) t := by
  apply w.orbit_ode t
  change s.startTime - w.local_extension < t
  linarith [w.local_extension_pos, ht]

/-- Choose one relaxed witness at every stage from the separately proved
stage theorem. The sequence preserves each input stage and its own region. -/
noncomputable def chooseInvariantRegionStageWitness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) :
    InvariantRegionStageWitness s := by
  classical
  have hn : Nonempty (InvariantRegionStageWitness s) := by
    obtain ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary,
      trajectory, epsilon, hepsilon, hinitial, hflow, hregion, hdecay,
      huniqueFlow⟩ := meanField_invariant_region_stage_conclusions s
    exact ⟨{
    minimizer := xstar
    minimizer_interior := hxstar
    minimizer_is_min := hmin
    minimizer_unique := hunique
    displacement_bound := hdisplacement
    stationary := hstationary
    positive_margin := by
      have h := Tomabechi.Theorem22.gain_threshold_implies_positive_margin
        s.radius s.gain s.presenceGain s.curvature s.backgroundCurvature
        s.gradientBound s.radius_pos s.gain_pos s.curvature_pos
        s.backgroundCurvature_nonneg s.gradientBound_nonneg s.gain_threshold
      exact h.2.1
    orbit := trajectory
    local_extension := epsilon
    local_extension_pos := hepsilon
    initial_condition := hinitial
    orbit_ode := hflow
    orbit_in_region := hregion
    orbit_decay := hdecay
    orbit_unique := huniqueFlow }⟩
  exact Classical.choice hn

noncomputable def chooseAllInvariantRegionStageWitnesses
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) :
    ∀ n, InvariantRegionStageWitness (stages n) :=
  fun n => chooseInvariantRegionStageWitness (stages n)

end Tomabechi.Theorem22InvariantRegion
