import Theorem23
import Theorem22_InvariantRegion

/-!
# 定理23：不変領域段階列のTCZ接続

このファイルは緩和段階入力が持つ凍結軌道と指数評価から、原文と同じ
段階TCZ（局所球・閉到達集合・谷からのポテンシャル差）を構成する。
各段階TCZの非空性と閉性、隣接非一致を新証人型へ移植し、切替軌道の
継ぎ合わせ・待ち時間の端点誤差・条件23-Bの核まで接続する。段階間のギャップ・
線分包含・端点遷移・非Zenoは、原文どおり独立の明示仮定として保つ。
-/

open Tomabechi.Theorem22InvariantRegion
open Tomabechi.Theorem23
open scoped Topology

namespace Tomabechi.Theorem23InvariantRegion

/-- Averaged effective potential for a relaxed mean-field stage. -/
def stagePotential {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) : E → ℝ :=
  fun x => s.background x - s.gain * s.presenceGain * s.meanField x

/-- The source's stage TCZ formed from relaxed stages and their own selected
frozen-orbit witnesses. Its definition matches `Theorem23.stageTCZ`. -/
def invariantRegionStageTCZ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (theta : ℕ → ℝ) (n : ℕ) : Set E :=
  stageTCZ (fun k x => stagePotential (stages k) x)
    (fun k => (witnesses k).minimizer) theta
    (fun k => Metric.closedBall (stages k).center (stages k).radius)
    (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n

/-- Exponential decay puts the relaxed stage minimizer in the closure of its
own forward reachable set, so its zero potential gap puts it in every TCZ
with a nonnegative threshold. -/
theorem relaxed_minimizer_mem_stageTCZ {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (w : InvariantRegionStageWitness s) (theta : ℝ) (htheta : 0 ≤ theta) :
    stageTCZ
      (fun _ : ℕ => stagePotential s) (fun _ => w.minimizer)
      (fun _ => theta) (fun _ => Metric.closedBall s.center s.radius)
      (fun _ => closure (w.orbit '' Set.Ici s.startTime)) 0 w.minimizer := by
  have hreachable := limit_in_closed_reachable_of_exponential_decay
    w.orbit w.minimizer s.startTime w.decayAmplitude w.decayRate
    w.decayAmplitude_nonneg w.decayRate_pos
    (fun t ht => w.distance_decay t ht)
  change w.minimizer ∈ Metric.closedBall s.center s.radius ∧
    (w.minimizer ∈ closure (w.orbit '' Set.Ici s.startTime) ∧
      stagePotential s w.minimizer - stagePotential s w.minimizer ≤ theta)
  exact ⟨interior_subset w.minimizer_interior, hreachable, by linarith⟩

/-- Every TCZ built from a relaxed selected stage witness is nonempty. -/
theorem all_relaxed_stage_TCZs_nonempty {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n) :
    ∀ n, (invariantRegionStageTCZ stages witnesses theta n).Nonempty := by
  intro n
  change (stageTCZ (fun k x => stagePotential (stages k) x)
    (fun k => (witnesses k).minimizer) theta
    (fun k => Metric.closedBall (stages k).center (stages k).radius)
    (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n).Nonempty
  have hreachable := limit_in_closed_reachable_of_exponential_decay
    (witnesses n).orbit (witnesses n).minimizer (stages n).startTime
    (witnesses n).decayAmplitude (witnesses n).decayRate
    (witnesses n).decayAmplitude_nonneg (witnesses n).decayRate_pos
    (fun t ht => (witnesses n).distance_decay t ht)
  refine ⟨(witnesses n).minimizer, ?_⟩
  change (witnesses n).minimizer ∈ Metric.closedBall (stages n).center
      (stages n).radius ∧
    ((witnesses n).minimizer ∈
        closure ((witnesses n).orbit '' Set.Ici (stages n).startTime) ∧
      stagePotential (stages n) (witnesses n).minimizer -
        stagePotential (stages n) (witnesses n).minimizer ≤ theta n)
  exact ⟨interior_subset (witnesses n).minimizer_interior,
    hreachable, by simp [htheta n]⟩

/-- Each relaxed stage TCZ is closed. The potential is continuous on the
closed ball by its C² input; the reachable factor is a closure by definition.
-/
theorem all_relaxed_stage_TCZs_closed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (theta : ℕ → ℝ) :
    ∀ n, IsClosed (invariantRegionStageTCZ stages witnesses theta n) := by
  intro n
  apply isClosed_stageTCZ_of_continuousOn
  · exact Metric.isClosed_closedBall
  · exact isClosed_closure
  · have hbackground : ContDiffOn ℝ 1 (stages n).background
        (Metric.closedBall (stages n).center (stages n).radius) := by
      intro x hx
      exact ((stages n).background_c2_at x hx).of_le (by norm_num) |>.contDiffWithinAt
    have hmeanField : ContDiffOn ℝ 1 (stages n).meanField
        (Metric.closedBall (stages n).center (stages n).radius) := by
      intro x hx
      exact ((stages n).meanField_c2_at x hx).of_le (by norm_num) |>.contDiffWithinAt
    have hpotential : ContDiffOn ℝ 1 (stagePotential (stages n))
        (Metric.closedBall (stages n).center (stages n).radius) := by
      exact hbackground.sub (ContDiffOn.const_smul
        ((stages n).gain * (stages n).presenceGain) hmeanField)
    exact hpotential.continuousOn

/-- The threshold Hessian bounds of a relaxed averaged stage still imply
strong convexity of its effective potential, independently of the shape of
the invariant region. -/
theorem stageEffectiveStrongConvexity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E) :
    Tomabechi.Theorem21.StronglyConvexOn
      (Metric.closedBall s.center s.radius) (stagePotential s)
      (fun x => s.backgroundGradient x -
        (s.gain * s.presenceGain) • s.meanFieldGradient x)
      (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) := by
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
  have hconvex := Tomabechi.Theorem22.per_stage_effective_strong_convexity
    s.center s.radius s.gain s.presenceGain s.curvature
    s.backgroundCurvature s.gradientBound s.radius_pos s.gain_pos
    s.curvature_pos s.backgroundCurvature_nonneg s.gradientBound_nonneg
    s.gain_threshold s.background s.meanField s.backgroundGradient
    s.meanFieldGradient s.backgroundHessian s.meanFieldHessian hV hS
    s.background_gradient_deriv s.meanField_gradient_deriv
    s.background_hessian_lower s.meanField_hessian_upper
  change Tomabechi.Theorem21.StronglyConvexOn
    (Metric.closedBall s.center s.radius)
    (fun x => s.background x - s.gain * s.presenceGain * s.meanField x)
    (fun x => s.backgroundGradient x -
      (s.gain * s.presenceGain) • s.meanFieldGradient x)
    (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)
  exact hconvex

/-- Adjacent relaxed-stage TCZs differ under the same segment and strict-gap
conditions as in the existing Theorem 23 core. Strong convexity is derived
from the shared mean-field Hessian data; the preceding minimizer must lie in
the next closed ball so that this local estimate applies. -/
theorem relaxed_adjacent_stageTCZs_differ {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ k, InvariantRegionStageWitness (stages k))
    (theta delta : ℕ → ℝ) (n : ℕ)
    (hdelta : delta n = ‖(witnesses (n + 1)).minimizer -
      (witnesses n).minimizer‖)
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) <
      ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
        (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 * delta n ^ 2)
    (hregionOld : (witnesses n).minimizer ∈
      Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius) :
    invariantRegionStageTCZ stages witnesses theta (n + 1) ≠
      invariantRegionStageTCZ stages witnesses theta n := by
  let potential : ℕ → E → ℝ := fun k => stagePotential (stages k)
  let region : ℕ → Set E := fun k =>
    Metric.closedBall (stages k).center (stages k).radius
  let reachable : ℕ → Set E := fun k =>
    closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)
  let xstar : ℕ → E := fun k => (witnesses k).minimizer
  let curvature : ℕ → ℝ := fun k =>
    (stages k).gain * (stages k).presenceGain * (stages k).curvature -
      (stages k).backgroundCurvature
  have hcurrent : xstar n ∈ region n :=
    interior_subset (witnesses n).minimizer_interior
  have hreachable : xstar n ∈ reachable n :=
    limit_in_closed_reachable_of_exponential_decay
      (witnesses n).orbit (witnesses n).minimizer (stages n).startTime
      (witnesses n).decayAmplitude (witnesses n).decayRate
      (witnesses n).decayAmplitude_nonneg (witnesses n).decayRate_pos
      (fun t ht => (witnesses n).distance_decay t ht)
  have hconvex := stageEffectiveStrongConvexity (stages (n + 1))
  have hstrong := hconvex (xstar (n + 1))
    (interior_subset (witnesses (n + 1)).minimizer_interior)
    (xstar n) hregionOld
  have hnorm : ‖xstar n - xstar (n + 1)‖ = delta n := by
    rw [norm_sub_rev, ← hdelta]
  have hgap : curvature (n + 1) / 2 * delta n ^ 2 ≤
      potential (n + 1) (xstar n) - potential (n + 1) (xstar (n + 1)) := by
    have hstationary :
        (stages (n + 1)).backgroundGradient (xstar (n + 1)) -
          ((stages (n + 1)).gain * (stages (n + 1)).presenceGain) •
            (stages (n + 1)).meanFieldGradient (xstar (n + 1)) = 0 :=
      (witnesses (n + 1)).stationary
    simpa [potential, curvature, stagePotential, hstationary, hnorm] using hstrong
  have hstrictGap :
      theta (n + 1) < potential (n + 1) (xstar n) -
        potential (n + 1) (xstar (n + 1)) :=
    lt_of_lt_of_le (by simpa [curvature] using hgapThreshold) hgap
  change stageTCZ potential xstar theta region reachable (n + 1) ≠
    stageTCZ potential xstar theta region reachable n
  intro hsame
  have hcurrentTCZ : xstar n ∈
      stageTCZ potential xstar theta region reachable n := by
    change xstar n ∈ region n ∧
      (xstar n ∈ reachable n ∧
        potential n (xstar n) - potential n (xstar n) ≤ theta n)
    exact ⟨hcurrent, hreachable, by simp [htheta]⟩
  have hnextTCZ : xstar n ∈
      stageTCZ potential xstar theta region reachable (n + 1) := by
    rw [hsame]
    exact hcurrentTCZ
  change xstar n ∈ region (n + 1) ∧
    (xstar n ∈ reachable (n + 1) ∧
      potential (n + 1) (xstar n) -
        potential (n + 1) (xstar (n + 1)) ≤ theta (n + 1)) at hnextTCZ
  exact (not_le_of_gt hstrictGap) hnextTCZ.2.2

/-- Nonemptiness, closedness, and adjacent nonfixation of every relaxed
stage TCZ. The strict gap and segment containment remain explicit, matching
the corresponding source inputs; positive valley separation is derived. -/
theorem all_relaxed_stage_TCZs_nonempty_closed_nonfixed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (theta delta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hdelta : ∀ n, delta n = ‖(witnesses (n + 1)).minimizer -
      (witnesses n).minimizer‖)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
          (stages (n + 1)).curvature -
            (stages (n + 1)).backgroundCurvature) / 2 * delta n ^ 2)
    (hsegment : ∀ n,
      segment ℝ (witnesses n).minimizer (witnesses (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius) :
    (∀ n, (invariantRegionStageTCZ stages witnesses theta n).Nonempty) ∧
    (∀ n, IsClosed (invariantRegionStageTCZ stages witnesses theta n)) ∧
    (∀ n, invariantRegionStageTCZ stages witnesses theta (n + 1) ≠
      invariantRegionStageTCZ stages witnesses theta n) ∧
    (∀ n, 0 < ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖) := by
  have hclosed := all_relaxed_stage_TCZs_closed stages witnesses theta
  have hnonempty := all_relaxed_stage_TCZs_nonempty stages witnesses theta htheta
  have hdistinct : ∀ n,
      invariantRegionStageTCZ stages witnesses theta (n + 1) ≠
        invariantRegionStageTCZ stages witnesses theta n := by
    intro n
    have hregionOld := hsegment n (left_mem_segment ℝ
      (witnesses n).minimizer (witnesses (n + 1)).minimizer)
    exact relaxed_adjacent_stageTCZs_differ stages witnesses theta delta n
      (hdelta n) (htheta n) (hgapThreshold n) hregionOld
  have hseparation : ∀ n,
      0 < ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖ := by
    intro n
    have hnonneg := norm_nonneg
      ((witnesses (n + 1)).minimizer - (witnesses n).minimizer)
    by_contra hnot
    have hle : ‖(witnesses (n + 1)).minimizer -
        (witnesses n).minimizer‖ ≤ 0 := le_of_not_gt hnot
    have hz : delta n = 0 := by
      rw [hdelta n]
      exact le_antisymm hle hnonneg
    have hgap := hgapThreshold n
    rw [hz] at hgap
    have : theta (n + 1) < 0 := by simpa using hgap
    linarith [htheta (n + 1)]
  exact ⟨hnonempty, hclosed, hdistinct, hseparation⟩

/-- End-to-end TCZ bridge from a sequence of relaxed mean-field stage inputs.
The selected valley witnesses are exactly those produced by the new Theorem
22 adapter. The source's inter-stage gap and line-segment conditions remain
independent explicit assumptions; no equality with an initial full sublevel
is introduced along this route. -/
theorem meanField_invariant_region_stages_have_TCZs
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
          (stages (n + 1)).curvature -
            (stages (n + 1)).backgroundCurvature) / 2 *
          ‖(chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer -
            (chooseAllInvariantRegionStageWitnesses stages n).minimizer‖ ^ 2)
    (hsegment : ∀ n,
      segment ℝ (chooseAllInvariantRegionStageWitnesses stages n).minimizer
        (chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer ⊆
          Metric.closedBall (stages (n + 1)).center
            (stages (n + 1)).radius) :
    (∀ n,
      (invariantRegionStageTCZ stages
        (chooseAllInvariantRegionStageWitnesses stages) theta n).Nonempty) ∧
    (∀ n, IsClosed (invariantRegionStageTCZ stages
      (chooseAllInvariantRegionStageWitnesses stages) theta n)) ∧
    (∀ n,
      invariantRegionStageTCZ stages
        (chooseAllInvariantRegionStageWitnesses stages) theta (n + 1) ≠
      invariantRegionStageTCZ stages
        (chooseAllInvariantRegionStageWitnesses stages) theta n) ∧
    (∀ n, 0 < ‖(chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer -
      (chooseAllInvariantRegionStageWitnesses stages n).minimizer‖) := by
  let witnesses := chooseAllInvariantRegionStageWitnesses stages
  let delta : ℕ → ℝ := fun n => ‖(witnesses (n + 1)).minimizer -
    (witnesses n).minimizer‖
  have hdelta : ∀ n, delta n = ‖(witnesses (n + 1)).minimizer -
      (witnesses n).minimizer‖ := fun _ => rfl
  have hresult := all_relaxed_stage_TCZs_nonempty_closed_nonfixed
    stages witnesses theta delta htheta hdelta
    (by simpa [witnesses, delta] using hgapThreshold)
    (by simpa [witnesses] using hsegment)
  simpa [witnesses] using hresult

/-- Piecewise select one frozen orbit at each time. -/
def stitchedInvariantRegionOrbit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (activeStage : ℝ → ℕ) : ℝ → E :=
  fun t => (witnesses (activeStage t)).orbit t

/-- With the canonical dwell-index laws and the source transition equality,
the piecewise relaxed orbit agrees with each frozen orbit throughout the
closed dwell interval, including the switch endpoint. This is the key
endpoint compatibility needed before proving switched-orbit continuity and
the waiting-time conclusion. -/
theorem stitched_relaxed_orbits_agree_on_closed_dwell
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (activeStage : ℝ → ℕ) (time duration : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hactive : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) → activeStage t = n)
    (hactiveEndpoint : ∀ n, activeStage (time n + duration n) = n + 1)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (witnesses n).orbit (time n + duration n)) :
    ∀ n, Set.EqOn (stitchedInvariantRegionOrbit stages witnesses activeStage)
      (witnesses n).orbit (Set.Icc (time n) (time n + duration n)) := by
  intro n t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have hindex := hactive n t ⟨ht.1, hlt⟩
    change (witnesses (activeStage t)).orbit t = (witnesses n).orbit t
    rw [hindex]
  · subst t
    change (witnesses (activeStage (time n + duration n))).orbit
      (time n + duration n) = (witnesses n).orbit
        (time n + duration n)
    rw [hactiveEndpoint n]
    have hnextStart : (stages (n + 1)).startTime =
        time n + duration n := by
      rw [hstart (n + 1), hrecurrence n]
    calc
      (witnesses (n + 1)).orbit (time n + duration n) =
          (stages (n + 1)).initial := by
        rw [← hnextStart]
        exact (witnesses (n + 1)).initial_condition
      _ = (witnesses n).orbit (time n + duration n) := htransition n

/-- A compatible schedule turns the selected relaxed frozen orbits into one
continuous switched trajectory on every closed dwell interval. The trajectory
stays in the active stage's local ball and solves that stage's ODE from the
right throughout the corresponding half-open interval. -/
theorem stitched_relaxed_orbits_form_a_switching_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (activeStage : ℝ → ℕ) (time duration : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hactive : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      activeStage t = n)
    (hactiveEndpoint : ∀ n, activeStage (time n + duration n) = n + 1)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (witnesses n).orbit (time n + duration n)) :
    (∀ n, Set.EqOn (stitchedInvariantRegionOrbit stages witnesses activeStage)
      (witnesses n).orbit (Set.Icc (time n) (time n + duration n))) ∧
    (∀ n, ContinuousOn
      (stitchedInvariantRegionOrbit stages witnesses activeStage)
      (Set.Icc (time n) (time n + duration n))) ∧
    (∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      stitchedInvariantRegionOrbit stages witnesses activeStage t ∈
        Metric.closedBall (stages n).center (stages n).radius) ∧
    (∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt
        (stitchedInvariantRegionOrbit stages witnesses activeStage)
        (-( (stages n).mobility
          (stitchedInvariantRegionOrbit stages witnesses activeStage t)
          ((stages n).backgroundGradient
              (stitchedInvariantRegionOrbit stages witnesses activeStage t) -
            ((stages n).gain * (stages n).presenceGain) •
              (stages n).meanFieldGradient
                (stitchedInvariantRegionOrbit stages witnesses activeStage t))))
        (Set.Ici t) t) := by
  let actual := stitchedInvariantRegionOrbit stages witnesses activeStage
  have hagreement := stitched_relaxed_orbits_agree_on_closed_dwell stages
    witnesses activeStage time duration hstart hrecurrence hactive
    hactiveEndpoint htransition
  have horbitContinuous : ∀ n,
      ContinuousOn (witnesses n).orbit (Set.Icc (time n) (time n + duration n)) := by
    intro n
    apply HasDerivAt.continuousOn
    intro t ht
    exact (witnesses n).orbit_ode_forward t (by rw [hstart n]; exact ht.1)
  have hcontinuous : ∀ n, ContinuousOn actual
      (Set.Icc (time n) (time n + duration n)) := by
    intro n
    exact (horbitContinuous n).congr (hagreement n)
  have hball : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (stages n).center (stages n).radius := by
    intro n t ht
    have heq := hagreement n ⟨ht.1, ht.2.le⟩
    change actual t ∈ Metric.closedBall (stages n).center (stages n).radius
    rw [show actual t = (witnesses n).orbit t from heq]
    apply Metric.ball_subset_closedBall
    exact (stages n).sublevel_barrier
      (subset_closure ((witnesses n).orbit_in_region t
        (by rw [hstart n]; exact ht.1)))
  have hflow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-((stages n).mobility (actual t)
          ((stages n).backgroundGradient (actual t) -
            ((stages n).gain * (stages n).presenceGain) •
              (stages n).meanFieldGradient (actual t))))
        (Set.Ici t) t := by
    intro n t ht
    have hlocal : Set.Ici t ∩ Set.Iio (time n + duration n) ∈
        𝓝[Set.Ici t] t :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)
    have hagreementRight : actual =ᶠ[𝓝[Set.Ici t] t] (witnesses n).orbit := by
      filter_upwards [hlocal] with s hs
      have hsDwell : s ∈ Set.Ico (time n) (time n + duration n) :=
        ⟨le_trans ht.1 hs.1, hs.2⟩
      change (witnesses (activeStage s)).orbit s = (witnesses n).orbit s
      rw [hactive n s hsDwell]
    have hfrozen := (witnesses n).orbit_ode_forward t
      (by rw [hstart n]; exact ht.1)
    have hpoint : actual t = (witnesses n).orbit t := by
      change (witnesses (activeStage t)).orbit t = (witnesses n).orbit t
      rw [hactive n t ht]
    have hwithin := hfrozen.hasDerivWithinAt.congr_of_eventuallyEq
      hagreementRight hpoint
    simpa [actual, stitchedInvariantRegionOrbit, hpoint] using hwithin
  exact ⟨hagreement, hcontinuous, hball, hflow⟩

/-- The stitched relaxed orbit inherits the stagewise endpoint tolerance from
the same logarithmic dwell-time bound as Theorem 22. -/
theorem stitched_relaxed_orbits_follow_valleys_before_tolerance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (witnesses : ∀ n, InvariantRegionStageWitness (stages n))
    (activeStage : ℝ → ℕ) (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hactive : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      activeStage t = n)
    (hactiveEndpoint : ∀ n, activeStage (time n + duration n) = n + 1)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (witnesses n).orbit (time n + duration n))
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (witnesses n).decayRate *
        Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n) :
    ∀ n, Set.EqOn (stitchedInvariantRegionOrbit stages witnesses activeStage)
        (witnesses n).orbit (Set.Icc (time n) (time n + duration n)) ∧
      dist (stitchedInvariantRegionOrbit stages witnesses activeStage
        (time n + duration n)) (witnesses n).minimizer ≤ epsilon n := by
  have hsolution := stitched_relaxed_orbits_form_a_switching_solution
    stages witnesses activeStage time duration hstart hrecurrence
    hactive hactiveEndpoint htransition
  intro n
  refine ⟨hsolution.1 n, ?_⟩
  have hendpoint : time n + duration n ∈ Set.Icc (time n)
      (time n + duration n) :=
    ⟨le_add_of_nonneg_right (hpositive n).le, le_rfl⟩
  rw [hsolution.1 n hendpoint]
  have hdecay := (witnesses n).distance_decay (time n + duration n)
    (by rw [hstart n]; exact le_add_of_nonneg_right (hpositive n).le)
  have htime : time n + duration n - (stages n).startTime = duration n := by
    rw [hstart n]
    ring
  rw [htime] at hdecay
  have htol := Tomabechi.Theorem22.dwell_time_suffices_for_error
    (witnesses n).decayAmplitude (epsilon n) (witnesses n).decayRate 1
    (duration n) (witnesses n).decayAmplitude_nonneg (hepsilon n)
    (witnesses n).decayRate_pos (by norm_num) (by simpa using hwait n)
  exact le_trans hdecay (by simpa using htol)

/-- End-to-end relaxed H-stage version of the analytic Condition 23-B core.
It retains the source's independent strict-gap, segment, endpoint-transition,
and non-Zeno hypotheses while constructing the canonical switched orbit. -/
theorem invariant_region_stages_and_switches_give_condition23B_core
    {L E : Type*} [SemilatticeSup L] [OrderTop L]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (hbelowTop : ∀ n, u n < ⊤) (hnew : ∀ n, ¬ v (n + 1) ≤ u n)
    (stages : ℕ → Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput E)
    (stageRepresentation : L → E)
    (hrepresentationFaithful : Function.Injective stageRepresentation)
    (hstageCenter : ∀ n, (stages n).center = stageRepresentation (u n))
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
            (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 *
          ‖(chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer -
            (chooseAllInvariantRegionStageWitnesses stages n).minimizer‖ ^ 2)
    (hsegment : ∀ n,
      segment ℝ (chooseAllInvariantRegionStageWitnesses stages n).minimizer
        (chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer ⊆
          Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius)
    (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (chooseAllInvariantRegionStageWitnesses stages n).orbit
          (time n + duration n))
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (chooseAllInvariantRegionStageWitnesses stages n).decayRate *
        Real.log ((chooseAllInvariantRegionStageWitnesses stages n).decayAmplitude /
          epsilon n)) ≤ duration n) :
    ((∀ n, u n < ⊤) ∧ Monotone u ∧ (∀ n, u n < u (n + 1)) ∧
      (∀ B : ℝ, ∃ n, B < time n) ∧ (∀ n, time n < time (n + 1))) ∧
    (∀ n, (stages n).center ≠ (stages (n + 1)).center) ∧
    (∀ n, 0 < ‖(chooseAllInvariantRegionStageWitnesses stages (n + 1)).minimizer -
      (chooseAllInvariantRegionStageWitnesses stages n).minimizer‖) ∧
    (∀ n, IsClosed (invariantRegionStageTCZ stages
      (chooseAllInvariantRegionStageWitnesses stages) theta n)) ∧
    (∀ n, invariantRegionStageTCZ stages
      (chooseAllInvariantRegionStageWitnesses stages) theta (n + 1) ≠
      invariantRegionStageTCZ stages
        (chooseAllInvariantRegionStageWitnesses stages) theta n) ∧
    (∀ n, (invariantRegionStageTCZ stages
      (chooseAllInvariantRegionStageWitnesses stages) theta n).Nonempty) ∧
    (∀ n, Set.EqOn
      (stitchedInvariantRegionOrbit stages
        (chooseAllInvariantRegionStageWitnesses stages)
        (canonicalSwitchStageIndex time
          (strictMono_nat_of_lt_succ
            (switching_times_unbounded duration time hpositive hrecurrence
              hdiverges).2)
          (switching_times_unbounded duration time hpositive hrecurrence
            hdiverges).1))
      (chooseAllInvariantRegionStageWitnesses stages n).orbit
      (Set.Icc (time n) (time n + duration n)) ∧
      dist (stitchedInvariantRegionOrbit stages
        (chooseAllInvariantRegionStageWitnesses stages)
        (canonicalSwitchStageIndex time
          (strictMono_nat_of_lt_succ
            (switching_times_unbounded duration time hpositive hrecurrence
              hdiverges).2)
          (switching_times_unbounded duration time hpositive hrecurrence
            hdiverges).1)
        (time n + duration n))
        (chooseAllInvariantRegionStageWitnesses stages n).minimizer ≤ epsilon n) ∧
    (∀ t, time 0 ≤ t →
      ∃ n, t ∈ Set.Ico (time n) (time n + duration n)) ∧
    (∀ (T : ℝ) (K : ℕ), ∃ n, K ≤ n ∧ T < time n) := by
  let witnesses := chooseAllInvariantRegionStageWitnesses stages
  let timing := switching_times_unbounded duration time hpositive hrecurrence
    hdiverges
  let timeStrict : StrictMono time := strictMono_nat_of_lt_succ timing.2
  let active := canonicalSwitchStageIndex time timeStrict timing.1
  have hactive : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      active t = n := by
    intro n t ht
    exact canonicalSwitchStageIndex_eq_on_dwell time duration timeStrict
      timing.1 hrecurrence n ht
  have hactiveEndpoint : ∀ n, active (time n + duration n) = n + 1 := by
    intro n
    rw [← hrecurrence n]
    exact canonicalSwitchStageIndex_eq_next_at_endpoint time timeStrict
      timing.1 n
  have horder := condition23B_lub_and_timing_consequences
    u v hupdate hbelowTop hnew duration time hpositive hrecurrence hdiverges
  have hTCZ := meanField_invariant_region_stages_have_TCZs stages theta
    htheta hgapThreshold hsegment
  have hcenterDistinct : ∀ n,
      (stages n).center ≠ (stages (n + 1)).center := by
    intro n hsame
    have hrepresented : stageRepresentation (u n) =
        stageRepresentation (u (n + 1)) := by
      calc
        stageRepresentation (u n) = (stages n).center := (hstageCenter n).symm
        _ = (stages (n + 1)).center := hsame
        _ = stageRepresentation (u (n + 1)) := hstageCenter (n + 1)
    have hsameLUB : u n = u (n + 1) :=
      hrepresentationFaithful hrepresented
    exact (ne_of_lt (horder.2.2.1 n)) hsameLUB
  have hswitch := stitched_relaxed_orbits_follow_valleys_before_tolerance
    stages witnesses active time duration epsilon hstart hrecurrence
    hpositive hactive hactiveEndpoint htransition hepsilon
    (by intro n; simpa [witnesses] using hwait n)
  exact ⟨horder, hcenterDistinct, hTCZ.2.2.2, hTCZ.2.1, hTCZ.2.2.1,
    hTCZ.1, (by simpa [witnesses] using hswitch),
    (by
      intro t ht
      exact every_finite_time_in_some_dwell duration time t ht hrecurrence
        horder.2.2.2.1),
    infinitely_many_switches_after_every_finite_time duration time
      hpositive hrecurrence hdiverges⟩

end Tomabechi.Theorem23InvariantRegion
