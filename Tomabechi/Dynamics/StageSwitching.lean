import Theorem22
import Tomabechi.Analysis.EntropyBalance
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Function.UniformIntegrable

open Filter
open scoped Topology

/-! # 定理23のTCZ・段階切替・非再帰核

旧 `Theorem23.lean` のTCZ閉性・非固定性、完全状態の非再帰、段階切替と条件23-Bを配置。
公開namespaceと宣言名を保ち、定量的な滞在時間・指数率・切替条件を変更しない。
-/

namespace Tomabechi.Theorem23

open Filter
open scoped Topology

/-- The second-law sign clause: nonnegative entropy production throughout an
alive interval gives a nonnegative total production on that interval. The
integrability premise is explicit because pointwise nonnegativity alone does
not make a real-valued integral well-defined.
日本語要約：区間上で総生成率が非負なら、その積分も非負である。 -/
theorem entropy_production_integral_nonnegative
    (production : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (_hint : IntervalIntegrable production MeasureTheory.volume a b)
    (hproduction : ∀ t ∈ Set.Icc a b, 0 ≤ production t) :
    0 ≤ ∫ t in a..b, production t := by
  exact intervalIntegral.integral_nonneg hab (fun t ht =>
    hproduction t ht)

/-- Stage `n`'s closed reachable TCZ, defined as its reachable portion inside
the sublevel set of the stage potential above its local minimum.
日本語要約：段階TCZを、段階領域・閉到達可能集合・最小点からのポテンシャル差条件の共通部分として定義する。 -/
def stageTCZ {X : Type*} (potential : ℕ → X → ℝ)
    (xstar : ℕ → X) (theta : ℕ → ℝ) (region reachable : ℕ → Set X)
    (n : ℕ) : Set X :=
  region n ∩ (reachable n ∩
    {x | potential n x - potential n (xstar n) ≤ theta n})

/-- If the reachable region is closed and the stage potential is continuous,
then the stage TCZ in the source's definition is closed.
日本語要約：閉領域と閉到達可能集合、領域上の連続性からTCZの閉性を導く。 -/
theorem isClosed_stageTCZ
    {X : Type*} [TopologicalSpace X]
    (potential : ℕ → X → ℝ) (xstar : ℕ → X)
    (theta : ℕ → ℝ) (region reachable : ℕ → Set X) (n : ℕ)
    (hregion : IsClosed (region n))
    (hreachable : IsClosed (reachable n))
    (hpotential : Continuous (potential n)) :
    IsClosed (stageTCZ potential xstar theta region reachable n) := by
  unfold stageTCZ
  refine hregion.inter (hreachable.inter ?_)
  exact isClosed_le (hpotential.sub continuous_const) continuous_const

/-- The same closedness conclusion only needs continuity on the closed stage
region. This is useful when regularity is part of a stage package and is not
claimed outside its modeled state space.
日本語要約：全空間連続性を仮定せず、段階領域上の連続性だけでTCZの閉性を示す。 -/
theorem isClosed_stageTCZ_of_continuousOn
    {X : Type*} [TopologicalSpace X]
    (potential : ℕ → X → ℝ) (xstar : ℕ → X)
    (theta : ℕ → ℝ) (region reachable : ℕ → Set X) (n : ℕ)
    (hregion : IsClosed (region n))
    (hreachable : IsClosed (reachable n))
    (hpotential : ContinuousOn (potential n) (region n)) :
    IsClosed (stageTCZ potential xstar theta region reachable n) := by
  have hgap : ContinuousOn
      (fun x => potential n x - potential n (xstar n)) (region n) := by
    exact hpotential.sub continuousOn_const
  have hlevel : IsClosed
      (region n ∩ {x | potential n x - potential n (xstar n) ≤ theta n}) := by
    change IsClosed (region n ∩
      (fun x => potential n x - potential n (xstar n)) ⁻¹' Set.Iic (theta n))
    exact hgap.preimage_isClosed_of_isClosed hregion isClosed_Iic
  unfold stageTCZ
  convert hlevel.inter hreachable using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/-- Exponential convergence places the stage minimizer in the closed
reachable set of the frozen trajectory. This is the closure step used in the
paper to put the preceding minimizer in `TCZₙ`; it follows by sampling the
continuous-time trajectory at integer offsets, which is enough for closure.
日本語要約：指数収束する軌道の極限点が閉到達可能集合に含まれると示す。 -/
theorem limit_in_closed_reachable_of_exponential_decay
    {E : Type*} [PseudoMetricSpace E]
    (trajectory : ℝ → E) (xstar : E) (t₀ C lambda : ℝ)
    (hC : 0 ≤ C) (hlambda : 0 < lambda)
    (hdecay : ∀ t, t₀ ≤ t →
      dist (trajectory t) xstar ≤ C * Real.exp (-lambda * (t - t₀))) :
    xstar ∈ closure (trajectory '' Set.Ici t₀) := by
  have harg : Tendsto (fun n : ℕ => -lambda * (n : ℝ)) atTop atBot := by
    exact Tendsto.const_mul_atTop_of_neg
      (neg_neg_iff_pos.mpr hlambda) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hexp : Tendsto (fun n : ℕ => Real.exp (-lambda * (n : ℝ)))
      atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp harg using 1
    rfl
  have hbound : Tendsto (fun n : ℕ => C * Real.exp (-lambda * (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul hexp
  have htrajectory : Tendsto (fun n : ℕ => trajectory (t₀ + n))
      atTop (𝓝 xstar) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hev := hbound.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hev] with n hn
    have ht : t₀ ≤ t₀ + (n : ℝ) :=
      le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hdist := hdecay (t₀ + (n : ℝ)) ht
    have hrewrite : -lambda * (t₀ + (n : ℝ) - t₀) = -lambda * (n : ℝ) := by ring
    rw [hrewrite] at hdist
    have hnε : C * Real.exp (-lambda * (n : ℝ)) < ε := by
      have hnball := hn
      simpa [abs_of_nonneg hC] using hnball
    exact lt_of_le_of_lt hdist hnε
  apply mem_closure_of_tendsto htrajectory
  exact Eventually.of_forall fun n => Set.mem_image_of_mem trajectory
    (by
      change t₀ ≤ t₀ + (n : ℝ)
      exact le_add_of_nonneg_right (Nat.cast_nonneg n))

/-- The minimizer selected by Theorem 22 belongs to its stage TCZ: the
quantitative frozen-orbit convergence puts it in the closed reachable set,
while its potential gap is zero and the threshold is nonnegative.
日本語要約：定理22の谷の最小点が到達可能閉包と閾値条件を満たし、段階TCZに属すると示す。 -/
theorem chosen_valley_minimizer_in_stageTCZ {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Tomabechi.Theorem22.StageValleySpec E)
    (w : Tomabechi.Theorem22.StageValleyWitness s)
    (theta : ℝ) (htheta : 0 ≤ theta) :
    stageTCZ
      (fun _ : ℕ => Tomabechi.Theorem22.stageEffectivePotential s)
      (fun _ => w.minimizer) (fun _ => theta)
      (fun _ => Metric.closedBall s.center s.radius)
      (fun _ => closure (w.orbit '' Set.Ici s.startTime)) 0
      w.minimizer := by
  have hreachable : w.minimizer ∈ closure (w.orbit '' Set.Ici s.startTime) :=
    limit_in_closed_reachable_of_exponential_decay w.orbit w.minimizer
      s.startTime w.decayAmplitude w.decayRate w.decayAmplitude_nonneg
      w.decayRate_pos (fun t ht => w.distance_decay t ht)
  change w.minimizer ∈ Metric.closedBall s.center s.radius ∧
    (w.minimizer ∈ closure (w.orbit '' Set.Ici s.startTime) ∧
      Tomabechi.Theorem22.stageEffectivePotential s w.minimizer -
        Tomabechi.Theorem22.stageEffectivePotential s w.minimizer ≤ theta)
  exact ⟨interior_subset w.minimizer_interior, hreachable, by linarith⟩

/-- Theorem 22's constructed valleys suffice for adjacent TCZ nonfixation once
the preceding minimizer lies in the next stage's local region and the source
threshold on successive-minimizer displacement holds. The old minimizer's
membership in its own closed reachable TCZ is derived from its selected
exponentially convergent orbit.
日本語要約：段階間の線分包含と曲率ギャップ条件から隣接TCZの不一致を示す。 -/
theorem chosen_valley_adjacent_stageTCZs_differ {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ k, Tomabechi.Theorem22.StageValleyWitness (stages k))
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
    stageTCZ
      (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
      (fun k => (witnesses k).minimizer) theta
      (fun k => Metric.closedBall (stages k).center (stages k).radius)
      (fun k => closure ((witnesses k).orbit ''
        Set.Ici (stages k).startTime)) (n + 1) ≠
    stageTCZ
      (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
      (fun k => (witnesses k).minimizer) theta
      (fun k => Metric.closedBall (stages k).center (stages k).radius)
      (fun k => closure ((witnesses k).orbit ''
        Set.Ici (stages k).startTime)) n := by
  let potential : ℕ → E → ℝ := fun k =>
    Tomabechi.Theorem22.stageEffectivePotential (stages k)
  let gradient : ℕ → E → E := fun k =>
    Tomabechi.Theorem22.stageEffectiveGradient (stages k)
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
  have hreachable : xstar n ∈ reachable n := by
    exact limit_in_closed_reachable_of_exponential_decay
      (witnesses n).orbit (witnesses n).minimizer (stages n).startTime
      (witnesses n).decayAmplitude (witnesses n).decayRate
      (witnesses n).decayAmplitude_nonneg (witnesses n).decayRate_pos
      (fun t ht => (witnesses n).distance_decay t ht)
  have hconvex : Tomabechi.Theorem21.StronglyConvexOn
      (region (n + 1)) (potential (n + 1)) (gradient (n + 1))
        (curvature (n + 1)) := by
    change Tomabechi.Theorem21.StronglyConvexOn
      (Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius)
      (fun x => (stages (n + 1)).background x -
        (stages (n + 1)).gain * (stages (n + 1)).presenceGain *
          (stages (n + 1)).presence x)
      (fun x => (stages (n + 1)).backgroundGradient x -
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain) •
          (stages (n + 1)).presenceGradient x)
      ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
        (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature)
    exact Tomabechi.Theorem22.per_stage_effective_strong_convexity
        (stages (n + 1)).center (stages (n + 1)).radius
        (stages (n + 1)).gain (stages (n + 1)).presenceGain
        (stages (n + 1)).curvature (stages (n + 1)).backgroundCurvature
        (stages (n + 1)).gradientBound
        (stages (n + 1)).radius_pos (stages (n + 1)).gain_pos
        (stages (n + 1)).curvature_pos
        (stages (n + 1)).backgroundCurvature_nonneg
        (stages (n + 1)).gradientBound_nonneg
        (stages (n + 1)).gain_threshold
        (stages (n + 1)).background (stages (n + 1)).presence
        (stages (n + 1)).backgroundGradient
        (stages (n + 1)).presenceGradient
        (stages (n + 1)).backgroundHessian
        (stages (n + 1)).presenceHessian
        (stages (n + 1)).backgroundHasFDerivAt
        (stages (n + 1)).presenceHasFDerivAt
        (stages (n + 1)).background_gradient_deriv
        (stages (n + 1)).presence_gradient_deriv
        (stages (n + 1)).background_hessian_lower
        (stages (n + 1)).presence_hessian_upper
  have hstrong := hconvex (xstar (n + 1))
    (interior_subset (witnesses (n + 1)).minimizer_interior)
    (xstar n) hregionOld
  have hnorm : ‖xstar n - xstar (n + 1)‖ = delta n := by
    rw [norm_sub_rev, ← hdelta]
  have hgap : curvature (n + 1) / 2 * delta n ^ 2 ≤
      potential (n + 1) (xstar n) - potential (n + 1) (xstar (n + 1)) := by
    have hstationary : gradient (n + 1) (xstar (n + 1)) = 0 := by
      simpa [gradient, xstar,
        Tomabechi.Theorem22.stageEffectiveGradient] using
          (witnesses (n + 1)).stationary
    simpa [potential, curvature,
      Tomabechi.Theorem22.stageEffectivePotential, hstationary, hnorm] using hstrong
  have hstrictGap : theta (n + 1) <
      potential (n + 1) (xstar n) - potential (n + 1) (xstar (n + 1)) :=
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

/-- Theorem 22's stage packages and selected valley orbits give closed TCZs
whose values change at every adjacent information update. The previous
minimizer's membership in the next stage's region and the source's strict gap
threshold remain explicit hypotheses.
日本語要約：全段階TCZの閉性と隣接段階での非一致をまとめる。 -/
theorem all_chosen_stage_TCZs_closed_and_nonfixed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ k, Tomabechi.Theorem22.StageValleyWitness (stages k))
    (theta delta : ℕ → ℝ)
    (hdelta : ∀ n, delta n = ‖(witnesses (n + 1)).minimizer -
      (witnesses n).minimizer‖)
    (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) < ((stages (n + 1)).gain *
        (stages (n + 1)).presenceGain * (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 * delta n ^ 2)
    (hsegment : ∀ n,
      segment ℝ (witnesses n).minimizer (witnesses (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius) :
    (∀ n, IsClosed (stageTCZ
      (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
      (fun k => (witnesses k).minimizer) theta
      (fun k => Metric.closedBall (stages k).center (stages k).radius)
      (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n)) ∧
    (∀ n,
      stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (witnesses k).minimizer) theta
        (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime))
        (n + 1) ≠
      stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (witnesses k).minimizer) theta
        (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n) := by
  constructor
  · intro n
    apply isClosed_stageTCZ_of_continuousOn
    · exact Metric.isClosed_closedBall
    · exact isClosed_closure
    · have hpotential : ContDiffOn ℝ 1
        (Tomabechi.Theorem22.stageEffectivePotential (stages n))
        (Metric.closedBall (stages n).center (stages n).radius) := by
        have hpotential0 : ContDiffOn ℝ 1
            (fun x => (stages n).background x -
              ((stages n).gain * (stages n).presenceGain) *
                (stages n).presence x)
            (Metric.closedBall (stages n).center (stages n).radius) :=
          (stages n).backgroundContDiffOnOne.sub
            (ContDiffOn.const_smul
              ((stages n).gain * (stages n).presenceGain)
              (stages n).presenceContDiffOnOne)
        convert hpotential0 using 1
        ext x
        simp [Tomabechi.Theorem22.stageEffectivePotential]
      simpa using hpotential.continuousOn
  · intro n
    have hregionOld : (witnesses n).minimizer ∈
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius :=
      hsegment n (left_mem_segment ℝ
        (witnesses n).minimizer (witnesses (n + 1)).minimizer)
    exact chosen_valley_adjacent_stageTCZs_differ stages witnesses theta delta n
      (hdelta n) (htheta n) (hgapThreshold n) hregionOld

/-- 各段階の谷の最小点は、その凍結軌道の閉到達可能部分に含まれる。
閾値が非負なら部分準位条件も満たすため、各段階TCZは空でない。

Each selected stage minimizer lies in the closure of its frozen orbit, and
its zero potential gap satisfies every nonnegative threshold. Thus every
stage TCZ is nonempty.
日本語要約：各段階の最小点の閉到達可能性から段階TCZの非空性を得る。 -/
theorem all_chosen_stage_TCZs_nonempty {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ k, Tomabechi.Theorem22.StageValleyWitness (stages k))
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n) :
    ∀ n, (stageTCZ
      (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
      (fun k => (witnesses k).minimizer) theta
      (fun k => Metric.closedBall (stages k).center (stages k).radius)
      (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n).Nonempty := by
  intro n
  refine ⟨(witnesses n).minimizer, ?_⟩
  have hreachable : (witnesses n).minimizer ∈
      closure ((witnesses n).orbit '' Set.Ici (stages n).startTime) :=
    limit_in_closed_reachable_of_exponential_decay
      (witnesses n).orbit (witnesses n).minimizer (stages n).startTime
      (witnesses n).decayAmplitude (witnesses n).decayRate
      (witnesses n).decayAmplitude_nonneg (witnesses n).decayRate_pos
      (fun t ht => (witnesses n).distance_decay t ht)
  change (witnesses n).minimizer ∈
    Metric.closedBall (stages n).center (stages n).radius ∧
      ((witnesses n).minimizer ∈
          closure ((witnesses n).orbit '' Set.Ici (stages n).startTime) ∧
        Tomabechi.Theorem22.stageEffectivePotential (stages n)
            (witnesses n).minimizer -
          Tomabechi.Theorem22.stageEffectivePotential (stages n)
            (witnesses n).minimizer ≤ theta n)
  exact ⟨interior_subset (witnesses n).minimizer_interior,
    hreachable, by simp [htheta n]⟩

/-- 定理22の選択軌道から、定理23の各段階TCZの非空性・閉性・隣接非一致を
得る。有限次元での軌道構成を型クラスに明示し、遷移線分条件と厳密ギャップ
閾値を仮定する。隣接最小点間距離の正値は閾値から導く。

Connect Theorem 22's selected stage orbits to Theorem 23's nonempty,
closed, nonfixed TCZ conclusion. Segment containment and the strict gap
threshold remain explicit; positive minimizer separation is derived.
日本語要約：定理22の段階仕様からTCZの非空・閉・隣接非一致を全段階で得る。 -/
theorem theorem22_stage_specs_give_nonfixed_TCZs {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
            (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 *
          ‖(Tomabechi.Theorem22.chooseAllStageValleys stages (n + 1)).minimizer -
            (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer‖ ^ 2)
    (hsegment : ∀ n,
      segment ℝ
          (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer
          (Tomabechi.Theorem22.chooseAllStageValleys stages (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius) :
    ∃ witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n),
      (∀ n, (stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (witnesses k).minimizer) theta
        (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n).Nonempty) ∧
      (∀ n, IsClosed (stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (witnesses k).minimizer) theta
        (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n)) ∧
      (∀ n,
        stageTCZ
          (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
          (fun k => (witnesses k).minimizer) theta
          (fun k => Metric.closedBall (stages k).center (stages k).radius)
          (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime))
          (n + 1) ≠
        stageTCZ
          (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
          (fun k => (witnesses k).minimizer) theta
          (fun k => Metric.closedBall (stages k).center (stages k).radius)
          (fun k => closure ((witnesses k).orbit '' Set.Ici (stages k).startTime)) n) ∧
      (∀ n, 0 < ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖) := by
  let witnesses := Tomabechi.Theorem22.chooseAllStageValleys stages
  let delta : ℕ → ℝ := fun n =>
    ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖
  have hdelta : ∀ n, delta n =
      ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖ := by
    intro n
    rfl
  have hgap : ∀ n, theta (n + 1) <
      ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
          (stages (n + 1)).curvature -
        (stages (n + 1)).backgroundCurvature) / 2 * delta n ^ 2 := by
    intro n
    exact hgapThreshold n
  have hsegment' : ∀ n,
      segment ℝ (witnesses n).minimizer (witnesses (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius :=
    hsegment
  have hresult := all_chosen_stage_TCZs_closed_and_nonfixed
    stages witnesses theta delta hdelta htheta hgap hsegment'
  have hnonempty := all_chosen_stage_TCZs_nonempty
    stages witnesses theta htheta
  refine ⟨witnesses, hnonempty, hresult.1, hresult.2, ?_⟩
  intro n
  have hnonneg := norm_nonneg
      ((witnesses (n + 1)).minimizer - (witnesses n).minimizer)
  by_contra hnot
  have hle : ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖ ≤ 0 :=
    le_of_not_gt hnot
  have heq : delta n = 0 := by
    dsimp [delta]
    exact le_antisymm hle hnonneg
  have hgapn := hgap n
  rw [heq] at hgapn
  have hnegative : theta (n + 1) < 0 := by
    simpa using hgapn
  linarith [htheta (n + 1)]

theorem complete_state_never_repeats
    {State : Type*} (entropy : State → ℝ) (state : ℝ → State)
    (production : ℝ → ℝ) (alive : Set ℝ)
    (hstrict : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      0 < ∫ t in t₁..t₂, production t)
    (hbalance : ∀ t₁ t₂ : ℝ, t₁ ∈ alive → t₂ ∈ alive → t₁ < t₂ →
      entropy (state t₂) - entropy (state t₁) =
        ∫ t in t₁..t₂, production t)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ alive) (ht₂ : t₂ ∈ alive)
    (ht : t₁ < t₂) : state t₂ ≠ state t₁ := by
  intro hsame
  have hentropy : entropy (state t₂) = entropy (state t₁) :=
    congrArg entropy hsame
  have hpos := hstrict t₁ t₂ ht₁ ht₂ ht
  rw [← hbalance t₁ t₂ ht₁ ht₂ ht] at hpos
  rw [hentropy] at hpos
  simp at hpos

/-- Condition 23-B makes every consecutive LUB update strict, provided each
stage supplies information not already below the current LUB.
日本語要約：各段階に既存LUBへ包摂されない新情報があるとき、LUB列が毎段厳密に上昇する。 -/
theorem every_new_stage_strictly_higher
    {L : Type*} [SemilatticeSup L] (u v : ℕ → L)
    (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (hnew : ∀ n, ¬ v (n + 1) ≤ u n) :
    ∀ n, u n < u (n + 1) := by
  intro n
  rw [hupdate n]
  exact Tomabechi.Theorem22.lub_update_is_strict (u n) (v (n + 1)) (hnew n)

/-- The positive sublevel-gap threshold forces adjacent stage minimizers to
be distinct: if their distance were zero, the strict upper bound on the
nonnegative threshold would become impossible. This verifies the successive
minimizer-separation clause of Condition 23-B from the stated threshold.
日本語要約：閾値ギャップ条件から隣接段階の最小点が異なることを導く。 -/
theorem adjacent_stage_minimizers_distinct
    {E : Type*} [NormedAddCommGroup E]
    (xstar : ℕ → E) (theta c delta : ℕ → ℝ) (n : ℕ)
    (hdelta : delta n = ‖xstar (n + 1) - xstar n‖)
    (htheta : 0 ≤ theta (n + 1))
    (hgapThreshold : theta (n + 1) < c (n + 1) / 2 * delta n ^ 2) :
    xstar n ≠ xstar (n + 1) := by
  intro heq
  have hdelta_zero : delta n = 0 := by
    rw [hdelta, heq]
    simp
  rw [hdelta_zero] at hgapThreshold
  simp at hgapThreshold
  linarith

/-- Condition 23-B's stage-gap argument rules out finite-stage TCZ fixation.
The hypotheses state explicitly that the old minimizer is in the old
reachability TCZ and that the next-stage potential gap exceeds its sublevel
threshold. Theorem 22 provides the strong-convexity estimate used to discharge
the latter premise for a concrete model.
日本語要約：旧最小点が旧TCZに属し次段TCZに属さない条件から、隣接TCZの不一致を示す。 -/
theorem no_finite_stage_tcz_fixation
    {X : Type*} (tcz : ℕ → Set X) (xstar : ℕ → X)
    (hseparated : ∀ n, xstar n ∈ tcz n ∧ xstar n ∉ tcz (n + 1)) :
    ∀ n, tcz (n + 1) ≠ tcz n := by
  intro n
  exact Tomabechi.Theorem22.stage_tcz_changes tcz xstar n
    (hseparated n).1 (hseparated n).2

/-- The paper's strong-convexity gap and sublevel threshold show that the old
minimizer belongs to the old TCZ but not the next one, provided it lies in the
old closed reachable set. This is the concrete bridge to equation (23.2).
The gap premise is the result of applying the next stage's strong-convexity
inequality along the segment between the two minimizers; the geometric
hypotheses needed to derive it are recorded at the call site.
日本語要約：旧最小点の旧到達可能性と次段の強凸ギャップからTCZ不一致を示す。 -/
theorem stage_tcz_changes_of_strong_convexity_gap
    {X : Type*} (potential : ℕ → X → ℝ) (xstar : ℕ → X)
    (theta c delta : ℕ → ℝ) (reachable : ℕ → Set X) (n : ℕ)
    (region : ℕ → Set X)
    (hregionCurrent : xstar n ∈ region n)
    (hreachable : xstar n ∈ reachable n)
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) < c (n + 1) / 2 * delta n ^ 2)
    (hgap : c (n + 1) / 2 * delta n ^ 2 ≤
      potential (n + 1) (xstar n) -
        potential (n + 1) (xstar (n + 1))) :
    stageTCZ potential xstar theta region reachable (n + 1) ≠
      stageTCZ potential xstar theta region reachable n := by
  apply Tomabechi.Theorem22.stage_tcz_changes
    (stageTCZ potential xstar theta region reachable) xstar n
  · constructor
    · exact hregionCurrent
    · constructor
      · exact hreachable
      · simp [htheta]
  · intro hmem
    change xstar n ∈ region (n + 1) ∧
      (xstar n ∈ reachable (n + 1) ∧
        potential (n + 1) (xstar n) -
          potential (n + 1) (xstar (n + 1)) ≤ theta (n + 1)) at hmem
    have hstrict := lt_of_lt_of_le hgapThreshold hgap
    exact (not_le_of_gt hstrict) hmem.2.2

/-- Derive the stage gap from Theorem 21's first-order strong-convexity
inequality, instead of assuming the gap itself. The next-stage minimizer must
be stationary, both minimizers must lie in the next local region, and the
segment geometry needed by strong convexity is therefore explicit. The old
minimizer's membership in the old reachable TCZ remains the source's
reachability condition.
日本語要約：次段の強凸性と最小点の停留条件からポテンシャル差の下界を導き、旧最小点の到達可能性と合わせて隣接TCZの不一致を示す。-/
theorem stage_tcz_changes_of_strong_convexity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : ℕ → E → ℝ) (gradient : ℕ → E → E) (U : ℕ → Set E)
    (xstar : ℕ → E) (theta c delta : ℕ → ℝ)
    (reachable : ℕ → Set E) (n : ℕ)
    (hconvex : ∀ k, Tomabechi.Theorem21.StronglyConvexOn (U (k + 1))
      (potential (k + 1)) (gradient (k + 1)) (c (k + 1)))
    (hstationary : ∀ k, gradient (k + 1) (xstar (k + 1)) = 0)
    (hregionOld : xstar n ∈ U (n + 1))
    (hregionNew : xstar (n + 1) ∈ U (n + 1))
    (hregionCurrent : xstar n ∈ U n)
    (hdelta : delta n = ‖xstar (n + 1) - xstar n‖)
    (hreachable : xstar n ∈ reachable n)
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) < c (n + 1) / 2 * delta n ^ 2) :
    stageTCZ potential xstar theta U reachable (n + 1) ≠
      stageTCZ potential xstar theta U reachable n := by
  have hstrong := hconvex n (xstar (n + 1)) hregionNew (xstar n) hregionOld
  have hnorm : ‖xstar n - xstar (n + 1)‖ = delta n := by
    rw [norm_sub_rev, ← hdelta]
  have hgap : c (n + 1) / 2 * delta n ^ 2 ≤
      potential (n + 1) (xstar n) - potential (n + 1) (xstar (n + 1)) := by
    simpa [hstationary n, hnorm] using hstrong
  exact stage_tcz_changes_of_strong_convexity_gap potential xstar theta c delta
    reachable n U hregionCurrent hreachable htheta hgapThreshold hgap

/-- The stagewise TCZ separation can be derived directly from the local
Hessian lower bound used in Theorem 22. Convexity of the region ensures that
the segment between the two minimizers remains inside the region; the
Fréchet derivative and Hessian hypotheses then give the strong-convexity
inequality used for the potential gap.
日本語要約：領域上Hessian下界と線分包含から強凸ギャップを導きTCZ不一致を得る。 -/
theorem stage_tcz_changes_of_hessian_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : ℕ → E → ℝ) (gradient : ℕ → E → E)
    (hessian : ℕ → E → E →L[ℝ] E) (U : ℕ → Set E)
    (xstar : ℕ → E) (theta c delta : ℕ → ℝ)
    (reachable : ℕ → Set E) (n : ℕ)
    (hUconvex : ∀ k, Convex ℝ (U (k + 1)))
    (hgradient : ∀ k x, x ∈ U (k + 1) →
      HasFDerivAt (potential (k + 1))
        (innerSL ℝ (gradient (k + 1) x)) x)
    (hhessian : ∀ k x, x ∈ U (k + 1) →
      HasFDerivAt (gradient (k + 1)) (hessian (k + 1) x) x)
    (hlower : ∀ k x, x ∈ U (k + 1) → ∀ w : E,
      c (k + 1) * ‖w‖ ^ 2 ≤
        inner ℝ (hessian (k + 1) x w) w)
    (hstationary : ∀ k, gradient (k + 1) (xstar (k + 1)) = 0)
    (hregionOld : xstar n ∈ U (n + 1))
    (hregionNew : xstar (n + 1) ∈ U (n + 1))
    (hregionCurrent : xstar n ∈ U n)
    (hdelta : delta n = ‖xstar (n + 1) - xstar n‖)
    (hreachable : xstar n ∈ reachable n)
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) < c (n + 1) / 2 * delta n ^ 2) :
    stageTCZ potential xstar theta U reachable (n + 1) ≠
      stageTCZ potential xstar theta U reachable n := by
  have hstrong : ∀ k, Tomabechi.Theorem21.StronglyConvexOn
      (U (k + 1)) (potential (k + 1)) (gradient (k + 1)) (c (k + 1)) := by
    intro k
    exact Tomabechi.Theorem21.stronglyConvexOn_of_hessian_lower_bound
      (U (k + 1)) (potential (k + 1)) (gradient (k + 1))
      (hessian (k + 1)) (c (k + 1)) (hUconvex k)
      (hgradient k) (hhessian k) (hlower k)
  exact stage_tcz_changes_of_strong_convexity potential gradient U xstar
    theta c delta reachable n hstrong hstationary hregionOld hregionNew
    hregionCurrent hdelta hreachable htheta hgapThreshold

/-- Source-parameter bridge for the stagewise part of Theorem 23. Theorem 22's
gain threshold and the two Hessian bounds produce the effective strongly
convex valleys at every stage; the old minimizer's frozen-orbit reachability,
the next-stage sublevel threshold, and the pointwise stage geometry then give
the nonfixation of adjacent closed TCZs. Reachability and exponential orbit
estimates remain explicit inputs because the gain threshold alone does not
establish them.
日本語要約：定理22の閾値・Hessian条件から強凸な谷を導き定理23のTCZ分離へ接続する。 -/
theorem stage_tcz_changes_of_theorem22_gain_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (center : ℕ → E) (r κ p m β B : ℕ → ℝ)
    (V S : ℕ → E → ℝ) (gradV gradS : ℕ → E → E)
    (HV HS : ℕ → E → E →L[ℝ] E)
    (xstar : ℕ → E) (theta delta : ℕ → ℝ)
    (trajectory : ℕ → ℝ → E) (start C lambda : ℕ → ℝ) (n : ℕ)
    (hr : ∀ k, 0 < r k) (hκ : ∀ k, 0 < κ k)
    (hm : ∀ k, 0 < m k) (hβ : ∀ k, 0 ≤ β k)
    (hB : ∀ k, 0 ≤ B k)
    (hp : ∀ k, p k > (max (β k) (B k / r k)) / (κ k * m k))
    (hV : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      HasFDerivAt (V k) (innerSL ℝ (gradV k x)) x)
    (hS : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      HasFDerivAt (S k) (innerSL ℝ (gradS k x)) x)
    (hHV : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      HasFDerivAt (gradV k) (HV k x) x)
    (hHS : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      HasFDerivAt (gradS k) (HS k x) x)
    (hVlower : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      ∀ w : E, -β k * ‖w‖ ^ 2 ≤ inner ℝ (HV k x w) w)
    (hSlower : ∀ k x, x ∈ Metric.closedBall (center k) (r k) →
      ∀ w : E, inner ℝ (HS k x w) w ≤ -m k * ‖w‖ ^ 2)
    (hstationary : ∀ k,
      gradV (k + 1) (xstar (k + 1)) -
        (κ (k + 1) * p (k + 1)) • gradS (k + 1) (xstar (k + 1)) = 0)
    (hregionOld : xstar n ∈ Metric.closedBall (center (n + 1)) (r (n + 1)))
    (hregionNew : xstar (n + 1) ∈
      Metric.closedBall (center (n + 1)) (r (n + 1)))
    (hregionCurrent : xstar n ∈ Metric.closedBall (center n) (r n))
    (hdelta : delta n = ‖xstar (n + 1) - xstar n‖)
    (hC : ∀ k, 0 ≤ C k) (hlambda : ∀ k, 0 < lambda k)
    (hdecay : ∀ k t, start k ≤ t →
      dist (trajectory k t) (xstar k) ≤
        C k * Real.exp (-lambda k * (t - start k)))
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) <
      (κ (n + 1) * p (n + 1) * m (n + 1) - β (n + 1)) / 2 * delta n ^ 2) :
    stageTCZ
      (fun k x => V k x - κ k * p k * S k x) xstar theta
      (fun k => Metric.closedBall (center k) (r k))
      (fun k => closure (trajectory k '' Set.Ici (start k))) (n + 1) ≠
    stageTCZ
      (fun k x => V k x - κ k * p k * S k x) xstar theta
      (fun k => Metric.closedBall (center k) (r k))
      (fun k => closure (trajectory k '' Set.Ici (start k))) n := by
  let effectiveGradient : ℕ → E → E := fun k x =>
    gradV k x - (κ k * p k) • gradS k x
  let effectiveCurvature : ℕ → ℝ := fun k => κ k * p k * m k - β k
  have hconvex := Tomabechi.Theorem22.all_stages_effective_strong_convexity
    center r κ p m β B V S gradV gradS HV HS hr hκ hm hβ hB hp
    hV hS hHV hHS hVlower hSlower
  have hstationary' : ∀ k,
      effectiveGradient (k + 1) (xstar (k + 1)) = 0 := by
    intro k
    exact hstationary k
  have hreachable : xstar n ∈
      closure (trajectory n '' Set.Ici (start n)) :=
    limit_in_closed_reachable_of_exponential_decay (trajectory n)
      (xstar n) (start n) (C n) (lambda n) (hC n) (hlambda n)
      (fun t ht => hdecay n t ht)
  let reachable : ℕ → Set E := fun k =>
    closure (trajectory k '' Set.Ici (start k))
  exact stage_tcz_changes_of_strong_convexity
    (fun k x => V k x - κ k * p k * S k x) effectiveGradient
    (fun k => Metric.closedBall (center k) (r k)) xstar theta
    effectiveCurvature delta reachable n
    (by
      intro k
      simpa [effectiveGradient, effectiveCurvature] using hconvex (k + 1))
    hstationary' hregionOld hregionNew hregionCurrent hdelta hreachable
    htheta (by simpa [effectiveCurvature] using hgapThreshold)

/-- The previous-stage reachability premise in the TCZ separation theorem is
derived from its exponential convergence estimate. The reachable set here is
the closure of the frozen-stage orbit from its switching state, matching the
`Kₙ` construction in the paper. Strong convexity on the next region, segment
containment, and the threshold gap remain explicit.
日本語要約：指数減衰から旧最小点の閉到達可能性を得て次段の強凸ギャップを適用する。 -/
theorem stage_tcz_changes_of_strong_convexity_and_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : ℕ → E → ℝ) (gradient : ℕ → E → E) (U : ℕ → Set E)
    (xstar : ℕ → E) (theta c delta : ℕ → ℝ)
    (trajectory : ℕ → ℝ → E) (start C lambda : ℕ → ℝ) (n : ℕ)
    (hconvex : ∀ k, Tomabechi.Theorem21.StronglyConvexOn (U (k + 1))
      (potential (k + 1)) (gradient (k + 1)) (c (k + 1)))
    (hstationary : ∀ k, gradient (k + 1) (xstar (k + 1)) = 0)
    (hregionOld : xstar n ∈ U (n + 1))
    (hregionNew : xstar (n + 1) ∈ U (n + 1))
    (hdelta : delta n = ‖xstar (n + 1) - xstar n‖)
    (hregionCurrent : xstar n ∈ U n)
    (hC : 0 ≤ C n) (hlambda : 0 < lambda n)
    (hdecay : ∀ k t, start k ≤ t →
      dist (trajectory k t) (xstar k) ≤
        C k * Real.exp (-lambda k * (t - start k)))
    (htheta : 0 ≤ theta n)
    (hgapThreshold : theta (n + 1) < c (n + 1) / 2 * delta n ^ 2) :
    let reachable : ℕ → Set E := fun k =>
      closure (trajectory k '' Set.Ici (start k))
    stageTCZ potential xstar theta U reachable (n + 1) ≠
      stageTCZ potential xstar theta U reachable n := by
  let reachable : ℕ → Set E := fun k =>
    closure (trajectory k '' Set.Ici (start k))
  have hreachable : xstar n ∈ reachable n := by
    dsimp [reachable]
    exact limit_in_closed_reachable_of_exponential_decay
      (trajectory n) (xstar n) (start n) (C n) (lambda n)
      (hC) (hlambda) (fun t ht => hdecay n t ht)
  exact stage_tcz_changes_of_strong_convexity potential gradient U xstar theta
    c delta reachable n hconvex hstationary hregionOld hregionNew hregionCurrent hdelta
    hreachable htheta hgapThreshold

/-- Non-Zeno switching times diverge, so infinitely many stages cannot all be
completed by a finite physical time.
日本語要約：正の各dwellと総和発散から切替時刻が厳密増加し非有界となることを示す。 -/
theorem switching_times_unbounded
    (duration : ℕ → ℝ) (time : ℕ → ℝ)
    (hpositive : ∀ n, 0 < duration n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k) :
    (∀ B : ℝ, ∃ n, B < time n) ∧ (∀ n, time n < time (n + 1)) := by
  have htime : ∀ n, time n = time 0 + ∑ k ∈ Finset.range n, duration k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hrecurrence n, ih]
      simp [Finset.sum_range_succ, add_assoc]
  constructor
  · intro B
    obtain ⟨n, hn⟩ := hdiverges (B - time 0)
    refine ⟨n, ?_⟩
    rw [htime n]
    linarith
  · intro n
    rw [hrecurrence n]
    linarith [hpositive n]

/-- There are switches arbitrarily far beyond every finite time and every
stage index. Thus no finite physical time can be a permanent termination time
for the infinite operation.
日本語要約：任意の有限時刻・任意の段階番号より後にも切替時刻があり、有限時刻での永久終了を排除する。-/
theorem infinitely_many_switches_after_every_finite_time
    (duration : ℕ → ℝ) (time : ℕ → ℝ)
    (hpositive : ∀ n, 0 < duration n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k) :
    ∀ T : ℝ, ∀ K : ℕ, ∃ n, K ≤ n ∧ T < time n := by
  have ⟨hunbounded, hstrict⟩ := switching_times_unbounded duration time
    hpositive hrecurrence hdiverges
  have hmono : StrictMono time := strictMono_nat_of_lt_succ hstrict
  intro T K
  obtain ⟨n, hn⟩ := hunbounded (max T (time K))
  refine ⟨n, ?_, lt_of_le_of_lt (le_max_left T (time K)) hn⟩
  by_contra hnot
  have hnK : n < K := Nat.lt_of_not_ge hnot
  have htimeLe : time n ≤ time K := hmono.monotone (Nat.le_of_lt hnK)
  exact (not_lt_of_ge htimeLe) (lt_of_le_of_lt (le_max_right T (time K)) hn)

/-- 開始後の任意の有限時刻は、時刻再帰と非有界性のもとで、ある段階の
半開dwell区間に属する。切替時刻は次段階に割り当てられるため、各時刻で
その段階のODE条件を適用できる。

Every finite time after the initial switch lies in a half-open stage dwell
interval when the switching-time sequence follows the recurrence and is
unbounded. A switching instant is assigned to the next stage.
日本語要約：時刻再帰と切替時刻の非有界性から、開始後の各有限時刻がいずれかの半開dwell区間に入ると示す。 -/
theorem every_finite_time_in_some_dwell
    (duration time : ℕ → ℝ) (t : ℝ)
    (hstart : time 0 ≤ t)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hunbounded : ∀ B : ℝ, ∃ n, B < time n) :
    ∃ n, t ∈ Set.Ico (time n) (time n + duration n) := by
  have hcross : ∃ k, t < time k := hunbounded t
  let m := Nat.find hcross
  have hm : t < time m := Nat.find_spec hcross
  have hmPositive : 0 < m := by
    have hmNeZero : m ≠ 0 := by
      intro hmZero
      have hfindZero : Nat.find hcross = 0 := by simpa [m] using hmZero
      have hm' : t < time 0 := by simpa [m, hfindZero] using hm
      exact (not_lt_of_ge hstart) hm'
    exact Nat.pos_of_ne_zero hmNeZero
  let n := m - 1
  have hnSucc : n + 1 = m := by
    dsimp [n]
    omega
  have hnotPrevious : ¬ t < time n := by
    intro hlt
    have hminimal := Nat.find_min hcross (by omega : n < m)
    apply hminimal
    exact hlt
  have hnLeft : time n ≤ t := le_of_not_gt hnotPrevious
  have hnRight : t < time n + duration n := by
    rw [← hrecurrence n, hnSucc]
    exact hm
  exact ⟨n, ⟨hnLeft, hnRight⟩⟩

/-- On every finite dwell interval, a switched trajectory agrees with the
corresponding frozen-stage orbit when both solve the same finite-dimensional
closed-loop ODE from the same switching state. The field regularity,
closed-ball containment, dwell continuity, and right-sided derivatives are
exposed stagewise; the agreement follows from the one-sided ODE uniqueness
API, without differentiability across the switch.
日本語要約：有限次元C¹場の一意性を使い、同じ初期値の実軌道と凍結軌道をdwell上で同定する。 -/
theorem stagewise_frozen_orbits_agree
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : ℕ → E → E →L[ℝ] E) (gradient : ℕ → E → E)
    (center : ℕ → E) (radius time duration : ℕ → ℝ)
    (actual : ℝ → E) (frozen : ℕ → ℝ → E)
    (hfieldC1 : ∀ n x, x ∈ Metric.closedBall (center n) (radius n) →
      ContDiffAt ℝ 1 (fun y => -(A n y (gradient n y))) x)
    (hactualBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (center n) (radius n))
    (hfrozenBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      frozen n t ∈ Metric.closedBall (center n) (radius n))
    (hactualFlow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-(A n (actual t) (gradient n (actual t)))) (Set.Ici t) t)
    (hfrozenFlow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt (frozen n)
        (-(A n (frozen n t) (gradient n (frozen n t)))) (Set.Ici t) t)
    (hinitial : ∀ n, actual (time n) = frozen n (time n))
    (hactualContinuous : ∀ n,
      ContinuousOn actual (Set.Icc (time n) (time n + duration n)))
    (hfrozenContinuous : ∀ n,
      ContinuousOn (frozen n) (Set.Icc (time n) (time n + duration n))) :
    ∀ n, Set.EqOn actual (frozen n)
      (Set.Icc (time n) (time n + duration n)) := by
  intro n
  obtain ⟨L, hL⟩ :=
    Tomabechi.Theorem21.exists_lipschitz_constant_on_closedBall_of_contDiffAt
      (fun x => -(A n x (gradient n x))) (center n) (radius n)
      (fun x hx => hfieldC1 n x hx)
  exact Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval_of_right_derivative
    (fun x => -(A n x (gradient n x))) (center n) (radius n)
    (time n) (time n + duration n) L hL actual (frozen n)
    (hactualBall n) (hfrozenBall n) (hactualContinuous n) (hfrozenContinuous n)
    (hactualFlow n) (hfrozenFlow n) (hinitial n)

/-- A constructed Theorem 22 stage witness agrees with the actual switched
trajectory over one dwell interval when the actual switch state is its
prescribed initial state. The frozen orbit's local Lipschitz uniqueness
constant is derived from the stage spec's C¹ field; its forward ODE,
closed-ball containment, initial continuity, and initial value come from the
global valley witness. Only the actual switched orbit's interval solution,
containment, and continuity on the closed dwell interval are supplied by the
switching model. At the switch, the actual trajectory only needs a right
derivative.
日本語要約：構成済みStageValleyWitnessの軌道と切替軌道を初期値整合の下で同定する。 -/
theorem switched_orbit_agrees_with_stage_valley_witness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (s : Tomabechi.Theorem22.StageValleySpec E)
    (w : Tomabechi.Theorem22.StageValleyWitness s)
    (actual : ℝ → E) (t₀ T : ℝ)
    (hstart : s.startTime = t₀)
    (hactualInitial : actual t₀ = s.initial)
    (hactualBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      actual t ∈ Metric.closedBall s.center s.radius)
    (hactualFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivWithinAt actual
        (-(s.mobility (actual t)
          (Tomabechi.Theorem22.stageEffectiveGradient s (actual t))))
        (Set.Ici t) t)
    (hactualContinuous : ContinuousOn actual (Set.Icc t₀ (t₀ + T))) :
    Set.EqOn actual w.orbit (Set.Icc t₀ (t₀ + T)) := by
  let field : E → E := fun x =>
    -(s.mobility x (Tomabechi.Theorem22.stageEffectiveGradient s x))
  have hfieldC1 : ∀ x ∈ Metric.closedBall s.center s.radius,
      ContDiffAt ℝ 1 field x := by
    intro x hx
    simpa [field, Tomabechi.Theorem22.stageEffectiveGradient] using
      s.closedLoopC1 x hx
  obtain ⟨L, hL⟩ :=
    Tomabechi.Theorem21.exists_lipschitz_constant_on_closedBall_of_contDiffAt
      field s.center s.radius hfieldC1
  have hfreeBall : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      w.orbit t ∈ Metric.closedBall s.center s.radius := by
    intro t ht
    apply w.orbit_in_closedBall
    rw [hstart]
    exact ht.1
  have hfreeFlow : ∀ t ∈ Set.Ico t₀ (t₀ + T),
      HasDerivWithinAt w.orbit (field (w.orbit t)) (Set.Ici t) t := by
    intro t ht
    have hforward : s.startTime ≤ t := by
      rw [hstart]
      exact ht.1
    have hderiv : HasDerivWithinAt w.orbit (field (w.orbit t)) Set.univ t :=
      (w.orbit_ode_forward t hforward).hasDerivWithinAt
    have hright := hderiv.mono (Set.subset_univ (Set.Ici t))
    simpa [field, Tomabechi.Theorem22.stageEffectiveGradient] using hright
  have hfreeContinuous : ContinuousOn w.orbit (Set.Icc t₀ (t₀ + T)) := by
    apply HasDerivAt.continuousOn
    intro t ht
    apply w.orbit_ode_forward
    rw [hstart]
    exact ht.1
  have hinit : actual t₀ = w.orbit t₀ := by
    calc
      actual t₀ = s.initial := hactualInitial
      _ = w.orbit s.startTime := w.initial_condition.symm
      _ = w.orbit t₀ := congrArg w.orbit hstart
  exact Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval_of_right_derivative
    field s.center s.radius t₀ (t₀ + T) L hL actual w.orbit
    hactualBall hfreeBall hactualContinuous hfreeContinuous
    hactualFlow hfreeFlow hinit

/-- Apply the constructed-valley uniqueness argument and the (22.5) waiting
time bound at every switching stage. This yields both agreement with the
selected frozen orbit over each complete dwell interval and the prescribed
endpoint tolerance.
日本語要約：各段階の軌道一致と待ち時間条件を組み合わせ、切替時の誤差境界を得る。 -/
theorem all_stage_switches_follow_selected_valleys_before_tolerance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (actual : ℝ → E) (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hinitial : ∀ n, actual (time n) = (stages n).initial)
    (hpositive : ∀ n, 0 < duration n)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (witnesses n).decayRate *
        Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n)
    (hactualBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (stages n).center (stages n).radius)
    (hactualFlow : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-((stages n).mobility (actual t)
          (Tomabechi.Theorem22.stageEffectiveGradient (stages n) (actual t))))
        (Set.Ici t) t)
    (hactualContinuous : ∀ n,
      ContinuousOn actual (Set.Icc (time n) (time n + duration n))) :
    ∀ n, Set.EqOn actual (witnesses n).orbit
        (Set.Icc (time n) (time n + duration n)) ∧
      dist (actual (time n + duration n)) (witnesses n).minimizer ≤ epsilon n := by
  intro n
  have hagree := switched_orbit_agrees_with_stage_valley_witness
    (stages n) (witnesses n) actual (time n) (duration n)
    (hstart n) (hinitial n)
    (fun t ht => hactualBall n t ht)
    (fun t ht => hactualFlow n t ht) (hactualContinuous n)
  have hendpoint : time n + duration n ∈
      Set.Icc (time n) (time n + duration n) :=
    ⟨le_add_of_nonneg_right (hpositive n).le, le_rfl⟩
  have hdecay := (witnesses n).distance_decay
    (time n + duration n) (by
      rw [← hstart n]
      exact le_add_of_nonneg_right (hpositive n).le)
  have hrate :
      (witnesses n).decayAmplitude * Real.exp
        (-(witnesses n).decayRate * duration n) ≤ epsilon n := by
    have hwait' : max 0
        (1 / ((witnesses n).decayRate * 1) *
          Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n := by
      simpa [mul_one] using hwait n
    have hbound := Tomabechi.Theorem22.dwell_time_suffices_for_error
      (witnesses n).decayAmplitude (epsilon n)
      (witnesses n).decayRate 1 (duration n)
      (witnesses n).decayAmplitude_nonneg (hepsilon n)
      (witnesses n).decayRate_pos (by norm_num) hwait'
    simpa [mul_one] using hbound
  constructor
  · exact hagree
  · calc
      dist (actual (time n + duration n)) (witnesses n).minimizer =
          dist ((witnesses n).orbit (time n + duration n))
            (witnesses n).minimizer := congrArg
              (fun x : E => dist x (witnesses n).minimizer)
              (hagree hendpoint)
      _ ≤ (witnesses n).decayAmplitude * Real.exp
            (-(witnesses n).decayRate * duration n) := by
          have htime : time n + duration n - (stages n).startTime = duration n := by
            rw [← hstart n]
            ring
          simpa [htime] using hdecay
      _ ≤ epsilon n := hrate

/-- Propagate the switching-state compatibility from the initial stage to all
later stages. At each switch, equality of the endpoint with the next stage's
prescribed initial state, together with frozen-orbit uniqueness on the dwell,
establishes the next initial condition.
日本語要約：初段整合と切替端点の状態遷移条件から全段階の初期整合を帰納する。 -/
theorem all_stage_switches_follow_valleys_from_transition_compatibility
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (actual : ℝ → E) (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hinitialZero : actual (time 0) = (stages 0).initial)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (witnesses n).orbit (time n + duration n))
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (witnesses n).decayRate *
        Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n)
    (hactualBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (stages n).center (stages n).radius)
    (hactualFlow : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-((stages n).mobility (actual t)
          (Tomabechi.Theorem22.stageEffectiveGradient (stages n) (actual t))))
        (Set.Ici t) t)
    (hactualContinuous : ∀ n,
      ContinuousOn actual (Set.Icc (time n) (time n + duration n))) :
    ∀ n, Set.EqOn actual (witnesses n).orbit
        (Set.Icc (time n) (time n + duration n)) ∧
      dist (actual (time n + duration n)) (witnesses n).minimizer ≤ epsilon n := by
  have hinitial : ∀ n, actual (time n) = (stages n).initial := by
    intro n
    induction n with
    | zero => exact hinitialZero
    | succ n ih =>
        have hagree := switched_orbit_agrees_with_stage_valley_witness
          (stages n) (witnesses n) actual (time n) (duration n)
          (hstart n) ih
          (fun t ht => hactualBall n t ht)
          (fun t ht => hactualFlow n t ht) (hactualContinuous n)
        have hendpoint : time n + duration n ∈
            Set.Icc (time n) (time n + duration n) :=
          ⟨le_add_of_nonneg_right (hpositive n).le, le_rfl⟩
        calc
          actual (time (n + 1)) = actual (time n + duration n) := by
            rw [hrecurrence n]
          _ = (witnesses n).orbit (time n + duration n) := hagree hendpoint
          _ = (stages (n + 1)).initial := (htransition n).symm
  exact all_stage_switches_follow_selected_valleys_before_tolerance
    stages witnesses actual time duration epsilon hstart hinitial hpositive
    hepsilon hwait hactualBall hactualFlow hactualContinuous

/-- Every real time lies before some stage endpoint when switching times are
strictly increasing and unbounded. -/
theorem exists_stage_endpoint_after_time (time : ℕ → ℝ)
    (htime : StrictMono time)
    (hunbounded : ∀ B : ℝ, ∃ n, B < time n) (t : ℝ) :
    ∃ n, t < time (n + 1) := by
  obtain ⟨k, hk⟩ := hunbounded t
  cases k with
  | zero =>
      exact ⟨0, lt_trans hk (htime (by omega))⟩
  | succ k =>
      exact ⟨k, by simpa using hk⟩

/-- Assign each real time to the first stage endpoint lying strictly after it.
For times in `[time n, time (n+1))`, this selects exactly stage `n`; at the
endpoint `time (n+1)`, it selects stage `n+1`.
日本語要約：切替時刻列の狭義単調性・非有界性から、各時刻を含む段階番号を最小選択で定義する。
-/
noncomputable def canonicalSwitchStageIndex (time : ℕ → ℝ)
    (htime : StrictMono time)
    (hunbounded : ∀ B : ℝ, ∃ n, B < time n) : ℝ → ℕ :=
  fun t => Nat.find (exists_stage_endpoint_after_time time htime hunbounded t)

theorem canonicalSwitchStageIndex_eq_on_dwell (time duration : ℕ → ℝ)
    (htime : StrictMono time)
    (hunbounded : ∀ B : ℝ, ∃ n, B < time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (time n) (time n + duration n)) :
    canonicalSwitchStageIndex time htime hunbounded t = n := by
  let index := canonicalSwitchStageIndex time htime hunbounded t
  have hproperty : t < time (index + 1) := by
    exact Nat.find_spec (exists_stage_endpoint_after_time time htime hunbounded t)
  have hupper : index ≤ n := by
    apply Nat.find_min'
    simpa [hrecurrence n] using ht.2
  have hlower : n ≤ index := by
    by_contra hnot
    have hindex : index < n := Nat.lt_of_not_ge hnot
    have htimele : time (index + 1) ≤ time n :=
      htime.monotone (Nat.succ_le_of_lt hindex)
    linarith [ht.1]
  exact Nat.le_antisymm hupper hlower

theorem canonicalSwitchStageIndex_eq_next_at_endpoint (time : ℕ → ℝ)
    (htime : StrictMono time)
    (hunbounded : ∀ B : ℝ, ∃ n, B < time n) (n : ℕ) :
    canonicalSwitchStageIndex time htime hunbounded (time (n + 1)) = n + 1 := by
  let index := canonicalSwitchStageIndex time htime hunbounded (time (n + 1))
  have hproperty : time (n + 1) < time (index + 1) := by
    exact Nat.find_spec
      (exists_stage_endpoint_after_time time htime hunbounded (time (n + 1)))
  have hupper : index ≤ n + 1 := by
    apply Nat.find_min'
    exact htime (by omega)
  have hlower : n + 1 ≤ index := by
    by_contra hnot
    have hindex : index < n + 1 := Nat.lt_of_not_ge hnot
    have htimele : time (index + 1) ≤ time (n + 1) :=
      htime.monotone (Nat.succ_le_of_lt hindex)
    linarith
  exact Nat.le_antisymm hupper hlower

/-- Build each next stage specification with its initial state set to the
preceding frozen orbit's endpoint. The caller supplies the stage's other
analytic data as a function of that endpoint; the transition equality itself
then follows by construction.
日本語要約：前段凍結軌道の終状態を次段仕様の初期状態に採用し、切替端点整合を構成で保証する。
-/
noncomputable def endpointCompatibleStageSequence {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (first : Tomabechi.Theorem22.StageValleySpec E)
    (next : ℕ → E → ℝ → Tomabechi.Theorem22.StageValleySpec E)
    (nextInitial : ∀ n x t, (next n x t).initial = x)
    (nextStartTime : ∀ n x t, (next n x t).startTime = t)
    (time duration : ℕ → ℝ) : ℕ → Tomabechi.Theorem22.StageValleySpec E
  | 0 => first
  | n + 1 =>
      next n ((Tomabechi.Theorem22.chooseStageValley
        (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).orbit
          (time n + duration n)) (time (n + 1))

theorem endpointCompatibleStageSequence_transition {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (first : Tomabechi.Theorem22.StageValleySpec E)
    (next : ℕ → E → ℝ → Tomabechi.Theorem22.StageValleySpec E)
    (nextInitial : ∀ n x t, (next n x t).initial = x)
    (nextStartTime : ∀ n x t, (next n x t).startTime = t)
    (time duration : ℕ → ℝ) (n : ℕ) :
    (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration
      (n + 1)).initial =
        (Tomabechi.Theorem22.chooseStageValley
          (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).orbit
          (time n + duration n) := by
  simp [endpointCompatibleStageSequence, nextInitial]

theorem endpointCompatibleStageSequence_startTime {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (first : Tomabechi.Theorem22.StageValleySpec E)
    (next : ℕ → E → ℝ → Tomabechi.Theorem22.StageValleySpec E)
    (nextInitial : ∀ n x t, (next n x t).initial = x)
    (nextStartTime : ∀ n x t, (next n x t).startTime = t)
    (time duration : ℕ → ℝ)
    (hfirstStart : first.startTime = time 0) :
    ∀ n, (endpointCompatibleStageSequence first next nextInitial nextStartTime
      time duration n).startTime = time n := by
  intro n
  induction n with
  | zero => exact hfirstStart
  | succ n ih =>
      change (next n _ (time (n + 1))).startTime = time (n + 1)
      exact nextStartTime n _ _

/-- Piecewise-define a switched trajectory by selecting which frozen stage
orbit is active at each time. The schedule laws say that the active index is
`n` on the half-open dwell interval and changes to `n+1` at its endpoint.
Unlike the arbitrary-trajectory interface above, this construction derives
continuity, the right-sided ODE, and local-ball residence from the frozen
witnesses plus endpoint compatibility.
日本語要約：段階番号に応じて凍結軌道をつなぎ、切替互換性から軌道の連続性・ODE・領域滞在を導く。
-/
def stitchedStageOrbit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (activeStage : ℝ → ℕ) : ℝ → E :=
  fun t => (witnesses (activeStage t)).orbit t

/-- A compatible schedule turns the family of global frozen orbits into a
single continuous switched trajectory. The ODE is asserted on each half-open
dwell interval, where the stage field is fixed; at a switch, continuity
follows from equality of the preceding endpoint and the next initial state.
日本語要約：dwellごとの段階番号と切替端点の整合から、切替軌道の各dwell上の結論を構成する。
-/
theorem stitched_stage_orbits_form_a_switching_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (activeStage : ℝ → ℕ) (time duration : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hactive : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      activeStage t = n)
    (hactiveEndpoint : ∀ n, activeStage (time n + duration n) = n + 1)
    (htransition : ∀ n,
      (stages (n + 1)).initial = (witnesses n).orbit
        (time n + duration n)) :
    (∀ n, Set.EqOn (stitchedStageOrbit stages witnesses activeStage)
      (witnesses n).orbit (Set.Icc (time n) (time n + duration n))) ∧
    (∀ n, ContinuousOn (stitchedStageOrbit stages witnesses activeStage)
      (Set.Icc (time n) (time n + duration n))) ∧
    (∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      (stitchedStageOrbit stages witnesses activeStage t) ∈
        Metric.closedBall (stages n).center (stages n).radius) ∧
    (∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt (stitchedStageOrbit stages witnesses activeStage)
        (-((stages n).mobility
            (stitchedStageOrbit stages witnesses activeStage t)
            ((stages n).backgroundGradient
                (stitchedStageOrbit stages witnesses activeStage t) -
              ((stages n).gain * (stages n).presenceGain) •
                (stages n).presenceGradient
                  (stitchedStageOrbit stages witnesses activeStage t))))
        (Set.Ici t) t) := by
  let actual := stitchedStageOrbit stages witnesses activeStage
  have hclosedAgreement : ∀ n, Set.EqOn actual (witnesses n).orbit
      (Set.Icc (time n) (time n + duration n)) := by
    intro n t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have ha := hactive n t ⟨ht.1, hlt⟩
      change (witnesses (activeStage t)).orbit t = (witnesses n).orbit t
      rw [ha]
    · subst t
      change (witnesses (activeStage (time n + duration n))).orbit
        (time n + duration n) = (witnesses n).orbit (time n + duration n)
      rw [hactiveEndpoint n]
      calc
        (witnesses (n + 1)).orbit (time n + duration n) =
            (stages (n + 1)).initial := by
          have hstartNext : (stages (n + 1)).startTime =
              time n + duration n := by rw [hstart, hrecurrence]
          rw [← hstartNext]
          exact (witnesses (n + 1)).initial_condition
        _ = (witnesses n).orbit (time n + duration n) := htransition n
  have horbitContinuous : ∀ n,
      ContinuousOn (witnesses n).orbit
        (Set.Icc (time n) (time n + duration n)) := by
    intro n
    apply HasDerivAt.continuousOn
    intro t ht
    exact (witnesses n).orbit_ode_forward t (by rw [hstart n]; exact ht.1)
  have hcontinuous : ∀ n, ContinuousOn actual
      (Set.Icc (time n) (time n + duration n)) := by
    intro n
    exact (horbitContinuous n).congr (hclosedAgreement n)
  have hball : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (stages n).center (stages n).radius := by
    intro n t ht
    rw [hclosedAgreement n ⟨ht.1, ht.2.le⟩]
    exact (witnesses n).orbit_in_closedBall t (by rw [hstart n]; exact ht.1)
  have hflow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-((stages n).mobility (actual t)
            ((stages n).backgroundGradient (actual t) -
              ((stages n).gain * (stages n).presenceGain) •
                (stages n).presenceGradient (actual t))))
        (Set.Ici t) t := by
    intro n t ht
    have hlocal : Set.Ici t ∩ Set.Iio (time n + duration n) ∈
        𝓝[Set.Ici t] t :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)
    have hagreement : actual =ᶠ[𝓝[Set.Ici t] t] (witnesses n).orbit := by
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
    have hwithin := hfrozen.hasDerivWithinAt.congr_of_eventuallyEq hagreement hpoint
    simpa [actual, stitchedStageOrbit, hpoint] using hwithin
  exact ⟨hclosedAgreement, hcontinuous, hball, hflow⟩

/-- The stitched trajectory satisfies the dwell hypotheses of Theorem 22
automatically. Thus the selected frozen orbits and endpoint compatibility
give the switched-orbit agreement and the prescribed endpoint tolerance,
without assuming an arbitrary actual path already solves the switched ODE.
The stage-index schedule remains explicit in `hactive` and
`hactiveEndpoint`.
日本語要約：継ぎ合わせた軌道を既存のODE一意性・待ち時間定理へ接続し、軌道一致と終端誤差を導く。
-/
theorem stitched_stage_orbits_follow_valleys_before_tolerance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (activeStage : ℝ → ℕ) (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hactive : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      activeStage t = n)
    (hactiveEndpoint : ∀ n, activeStage (time n + duration n) = n + 1)
    (htransition : ∀ n,
      (stages (n + 1)).initial = (witnesses n).orbit
        (time n + duration n))
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (witnesses n).decayRate *
        Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n) :
    ∀ n, Set.EqOn (stitchedStageOrbit stages witnesses activeStage)
        (witnesses n).orbit (Set.Icc (time n) (time n + duration n)) ∧
      dist (stitchedStageOrbit stages witnesses activeStage
        (time n + duration n)) (witnesses n).minimizer ≤ epsilon n := by
  have hsolution := stitched_stage_orbits_form_a_switching_solution
    stages witnesses activeStage time duration hstart hrecurrence hactive
    hactiveEndpoint htransition
  have hinitialZero :
      stitchedStageOrbit stages witnesses activeStage (time 0) =
        (stages 0).initial := by
    have ht : time 0 ∈ Set.Ico (time 0) (time 0 + duration 0) :=
      ⟨le_rfl, by linarith [hpositive 0]⟩
    calc
      stitchedStageOrbit stages witnesses activeStage (time 0) =
          (witnesses 0).orbit (time 0) := by
        change (witnesses (activeStage (time 0))).orbit (time 0) = _
        rw [hactive 0 (time 0) ht]
      _ = (stages 0).initial := by
        rw [← hstart 0]
        exact (witnesses 0).initial_condition
  have hball : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      stitchedStageOrbit stages witnesses activeStage t ∈
        Metric.closedBall (stages n).center (stages n).radius :=
    hsolution.2.2.1
  have hflow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt (stitchedStageOrbit stages witnesses activeStage)
        (-((stages n).mobility
            (stitchedStageOrbit stages witnesses activeStage t)
            (Tomabechi.Theorem22.stageEffectiveGradient (stages n)
              (stitchedStageOrbit stages witnesses activeStage t))))
        (Set.Ici t) t := by
    intro n t ht
    change HasDerivWithinAt (stitchedStageOrbit stages witnesses activeStage)
      (-((stages n).mobility
          (stitchedStageOrbit stages witnesses activeStage t)
          ((stages n).backgroundGradient
              (stitchedStageOrbit stages witnesses activeStage t) -
            ((stages n).gain * (stages n).presenceGain) •
              (stages n).presenceGradient
                (stitchedStageOrbit stages witnesses activeStage t))))
      (Set.Ici t) t
    exact hsolution.2.2.2 n t ht
  exact all_stage_switches_follow_valleys_from_transition_compatibility
    stages witnesses (stitchedStageOrbit stages witnesses activeStage)
    time duration epsilon hstart hinitialZero htransition hrecurrence hpositive
    hepsilon hwait hball hflow hsolution.2.1

/-- The stitched switched trajectory needs no separately supplied schedule
selector: positive dwell durations, the time recurrence, and divergent total
dwell time construct the canonical first-future-endpoint stage index. The
resulting path satisfies (22.5) and agrees with each frozen orbit on its
closed dwell interval.
日本語要約：正のdwell・時刻再帰・総時間発散から段階番号を構成し、切替軌道一致と待ち時間誤差を導く。
-/
theorem canonical_stitched_stage_orbits_follow_valleys_before_tolerance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (witnesses : ∀ n, Tomabechi.Theorem22.StageValleyWitness (stages n))
    (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k)
    (htransition : ∀ n,
      (stages (n + 1)).initial = (witnesses n).orbit
        (time n + duration n))
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (witnesses n).decayRate *
        Real.log ((witnesses n).decayAmplitude / epsilon n)) ≤ duration n) :
    ∀ n, Set.EqOn
        (stitchedStageOrbit stages witnesses
          (canonicalSwitchStageIndex time
            (strictMono_nat_of_lt_succ
              (switching_times_unbounded duration time hpositive hrecurrence
                hdiverges).2)
            (switching_times_unbounded duration time hpositive hrecurrence
              hdiverges).1))
        (witnesses n).orbit (Set.Icc (time n) (time n + duration n)) ∧
      dist
        (stitchedStageOrbit stages witnesses
          (canonicalSwitchStageIndex time
            (strictMono_nat_of_lt_succ
              (switching_times_unbounded duration time hpositive hrecurrence
                hdiverges).2)
            (switching_times_unbounded duration time hpositive hrecurrence
              hdiverges).1)
          (time n + duration n))
        (witnesses n).minimizer ≤ epsilon n := by
  let timing := switching_times_unbounded duration time hpositive hrecurrence
    hdiverges
  let timeStrict : StrictMono time := strictMono_nat_of_lt_succ timing.2
  let active := canonicalSwitchStageIndex time timeStrict timing.1
  have hactive : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) → active t = n := by
    intro n t ht
    exact canonicalSwitchStageIndex_eq_on_dwell time duration timeStrict
      timing.1 hrecurrence n ht
  have hactiveEndpoint : ∀ n,
      active (time n + duration n) = n + 1 := by
    intro n
    rw [← hrecurrence n]
    exact canonicalSwitchStageIndex_eq_next_at_endpoint time timeStrict timing.1 n
  have hresult := stitched_stage_orbits_follow_valleys_before_tolerance
    stages witnesses active time duration epsilon hstart hrecurrence hpositive
    hactive hactiveEndpoint htransition hepsilon hwait
  simpa [active, timeStrict, timing] using hresult

/-- End-to-end switching result from a stage factory that chooses each
stage's initial state from the preceding frozen endpoint. This combines the
endpoint-compatible stage recursion with the canonical switching schedule;
the arbitrary actual trajectory and the transition-equality premise are both
eliminated. Analytic validity of each generated `StageValleySpec` remains a
construction obligation on `next`.
日本語要約：端点から次段仕様を再帰構成し、その列の凍結軌道をcanonicalに接続してdwell一致・終端誤差を得る。
-/
theorem endpoint_compatible_stage_factory_gives_canonical_switch
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (first : Tomabechi.Theorem22.StageValleySpec E)
    (next : ℕ → E → ℝ → Tomabechi.Theorem22.StageValleySpec E)
    (nextInitial : ∀ n x t, (next n x t).initial = x)
    (nextStartTime : ∀ n x t, (next n x t).startTime = t)
    (time duration epsilon : ℕ → ℝ)
    (hfirstStart : first.startTime = time 0)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (Tomabechi.Theorem22.chooseStageValley
        (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).decayRate *
        Real.log ((Tomabechi.Theorem22.chooseStageValley
          (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).decayAmplitude /
            epsilon n)) ≤ duration n) :
    ∃ actual : ℝ → E,
      actual = stitchedStageOrbit
        (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration)
        (Tomabechi.Theorem22.chooseAllStageValleys
          (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration))
        (canonicalSwitchStageIndex time
          (strictMono_nat_of_lt_succ
            (switching_times_unbounded duration time hpositive hrecurrence
              hdiverges).2)
          (switching_times_unbounded duration time hpositive hrecurrence
            hdiverges).1) ∧
      (∀ n, Set.EqOn actual
        (Tomabechi.Theorem22.chooseStageValley
          (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).orbit
          (Set.Icc (time n) (time n + duration n)) ∧
        dist (actual (time n + duration n))
          (Tomabechi.Theorem22.chooseStageValley
            (endpointCompatibleStageSequence first next nextInitial nextStartTime time duration n)).minimizer ≤
          epsilon n) := by
  let stages := endpointCompatibleStageSequence first next nextInitial nextStartTime time duration
  let witnesses := Tomabechi.Theorem22.chooseAllStageValleys stages
  have hstart := endpointCompatibleStageSequence_startTime first next nextInitial
    nextStartTime time duration hfirstStart
  have htransition : ∀ n, (stages (n + 1)).initial =
      (witnesses n).orbit (time n + duration n) := by
    intro n
    simpa [stages, witnesses, Tomabechi.Theorem22.chooseAllStageValleys] using
      endpointCompatibleStageSequence_transition first next nextInitial nextStartTime
        time duration n
  have hresult := canonical_stitched_stage_orbits_follow_valleys_before_tolerance
    stages witnesses time duration epsilon hstart hrecurrence hpositive hdiverges
    htransition hepsilon (by
      intro n
      simpa [witnesses, Tomabechi.Theorem22.chooseAllStageValleys] using hwait n)
  refine ⟨stitchedStageOrbit stages witnesses
    (canonicalSwitchStageIndex time
      (strictMono_nat_of_lt_succ
        (switching_times_unbounded duration time hpositive hrecurrence hdiverges).2)
      (switching_times_unbounded duration time hpositive hrecurrence hdiverges).1), rfl, ?_⟩
  simpa [stages, witnesses, Tomabechi.Theorem22.chooseAllStageValleys] using hresult

/-- The order and timing parts of Condition 23-B assembled into the theorem's
stagewise consequences. The premise `hbelowTop` is deliberately retained:
The source explicitly assumes every finite stage is below `⊤`; strict join
growth alone does not imply that. Durations are real-valued, so finiteness is
built into their type, while positivity and divergence of partial sums are
stated below.
日本語要約：条件23-Bの順序更新・新情報・dwell仮定からLUB列と時刻列の結論をまとめる。 -/
theorem condition23B_lub_and_timing_consequences
    {L : Type*} [SemilatticeSup L] [OrderTop L]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (hbelowTop : ∀ n, u n < ⊤)
    (hnew : ∀ n, ¬ v (n + 1) ≤ u n)
    (duration time : ℕ → ℝ)
    (hpositive : ∀ n, 0 < duration n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k) :
    (∀ n, u n < ⊤) ∧ Monotone u ∧ (∀ n, u n < u (n + 1)) ∧
      (∀ B : ℝ, ∃ n, B < time n) ∧ (∀ n, time n < time (n + 1)) := by
  refine ⟨hbelowTop, Tomabechi.Theorem22.lub_stages_monotone u v hupdate,
    every_new_stage_strictly_higher u v hupdate hnew, ?_⟩
  exact switching_times_unbounded duration time hpositive hrecurrence hdiverges

/-- Combined stagewise conclusion of Theorem 23 under Condition 23-B and the
explicit analytic data used by Theorem 22. It proves strict LUB growth, a
different closed reachable TCZ at every adjacent pair of stages, and
unbounded non-Zeno switching times. Each stage's old minimizer is shown to be
reachable from its frozen orbit by exponential decay; the next-stage
strong-convexity gap then excludes it from the next TCZ. The order condition
`u n < ⊤`, reachability dynamics, and divergent total dwell time remain
explicit assumptions, as in the source. In particular, `hinitial` identifies
each switching state with the next frozen orbit's initial state, and `hdecay`
requires that orbit to converge from that state; together they encode the
next-stage basin-of-attraction condition rather than deriving it from local
Hessian data alone.
日本語要約：定理22の解析条件と条件23-Bの下で、LUB上昇、唯一最小点、切替誤差、TCZ非空・閉・非固定、非Zeno時刻列を導く。制御・到達可能性・減衰条件は明示仮定として残す。 -/
theorem theorem23_conditionB_stagewise_conclusions
    {L E : Type*} [SemilatticeSup L] [OrderTop L]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (potential : ℕ → E → ℝ) (gradient : ℕ → E → E) (U : ℕ → Set E)
    (xstar : ℕ → E) (theta c delta : ℕ → ℝ)
    (representedCenter : ℕ → E)
    (stageRepresentation : L → E)
    (hfaithful : Function.Injective stageRepresentation)
    (hrepresentedCenter : ∀ n,
      representedCenter n = stageRepresentation (u n))
    (A : ℕ → E → E →L[ℝ] E) (center : ℕ → E)
    (radius : ℕ → ℝ)
    (trajectory : ℕ → ℝ → E) (start C lambda epsilon : ℕ → ℝ)
    (duration time : ℕ → ℝ)
    (actual : ℝ → E)
    (hstartMatchesTime : ∀ n, start n = time n)
    (hUeq : ∀ n, U n = Metric.closedBall (center n) (radius n))
    (hfieldC1 : ∀ n x, x ∈ Metric.closedBall (center n) (radius n) →
      ContDiffAt ℝ 1 (fun y => -(A n y (gradient n y))) x)
    (hactualBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (center n) (radius n))
    (htrajectoryBall : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      trajectory n t ∈ Metric.closedBall (center n) (radius n))
    (hactualFlow : ∀ n t, t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-(A n (actual t) (gradient n (actual t)))) (Set.Ici t) t)
    (htrajectoryFlow : ∀ n t, start n ≤ t →
      HasDerivAt (trajectory n)
        (-(A n (trajectory n t) (gradient n (trajectory n t)))) t)
    (hinitial : ∀ n, actual (time n) = trajectory n (time n))
    (hactualContinuous : ∀ n,
      ContinuousOn actual (Set.Icc (time n) (time n + duration n)))
    (hbelowTop : ∀ n, u n < ⊤)
    (hnew : ∀ n, ¬ v (n + 1) ≤ u n)
    (hUconvex : ∀ k, Convex ℝ (U k))
    (hgradient : ∀ k x, x ∈ U k →
      HasFDerivAt (potential k) (innerSL ℝ (gradient k x)) x)
    (hessian : ℕ → E → E →L[ℝ] E)
    (hhessian : ∀ k x, x ∈ U k →
      HasFDerivAt (gradient k) (hessian k x) x)
    (hlower : ∀ k x, x ∈ U k → ∀ w : E,
      c k * ‖w‖ ^ 2 ≤ inner ℝ (hessian k x w) w)
    (hc : ∀ k, 0 < c k)
    (hstationary : ∀ k, gradient k (xstar k) = 0)
    (hregionOld : ∀ n, xstar n ∈ U (n + 1))
    (hregionNew : ∀ n, xstar (n + 1) ∈ U (n + 1))
    (hdelta : ∀ n, delta n = ‖xstar (n + 1) - xstar n‖)
    (hregionCurrent : ∀ n, xstar n ∈ U n)
    (hC : ∀ n, 0 ≤ C n) (hlambda : ∀ n, 0 < lambda n)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hdecay : ∀ n t, start n ≤ t →
      dist (trajectory n t) (xstar n) ≤
        C n * Real.exp (-lambda n * (t - start n)))
    (hwait : ∀ n,
      max 0 (1 / lambda n * Real.log (C n / epsilon n)) ≤ duration n)
    (hpotentialContinuousOn : ∀ n, ContinuousOn (potential n) (U n))
    (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) < c (n + 1) / 2 * delta n ^ 2)
    (hpositive : ∀ n, 0 < duration n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k) :
    (∀ n, u n < ⊤) ∧
      (∀ n, u n < u (n + 1)) ∧
      (∀ n, representedCenter n ≠ representedCenter (n + 1)) ∧
      (∀ n, xstar n ≠ xstar (n + 1)) ∧
      (∀ n, (∀ y ∈ U n,
        potential n (xstar n) ≤ potential n y) ∧
        (∀ y ∈ U n,
          potential n y = potential n (xstar n) → y = xstar n)) ∧
      (∀ n, actual (time n) = trajectory n (start n)) ∧
      (∀ n, dist (actual (time n + duration n)) (xstar n) ≤ epsilon n) ∧
      (∀ n, stageTCZ potential xstar theta U
        (fun k => closure (trajectory k '' Set.Ici (start k))) (n + 1) ≠
          stageTCZ potential xstar theta U
            (fun k => closure (trajectory k '' Set.Ici (start k))) n) ∧
      (∀ n, IsClosed (stageTCZ potential xstar theta U
        (fun k => closure (trajectory k '' Set.Ici (start k))) n)) ∧
      (∀ n, (stageTCZ potential xstar theta U
        (fun k => closure (trajectory k '' Set.Ici (start k))) n).Nonempty) ∧
      (∀ B : ℝ, ∃ n, B < time n) ∧
      (∀ n, time n < time (n + 1)) ∧
      (∀ t, time 0 ≤ t →
        ∃ n, t ∈ Set.Ico (time n) (time n + duration n)) := by
  have horder := condition23B_lub_and_timing_consequences u v hupdate
    hbelowTop hnew duration time hpositive hrecurrence hdiverges
  have hLexists (n : ℕ) : ∃ L : NNReal,
      LipschitzOnWith L (fun x => -(A n x (gradient n x)))
        (Metric.closedBall (center n) (radius n)) :=
    Tomabechi.Theorem21.exists_lipschitz_constant_on_closedBall_of_contDiffAt
      (fun x => -(A n x (gradient n x))) (center n) (radius n)
      (fun x hx => hfieldC1 n x hx)
  let lipschitzConstant : ℕ → NNReal := fun n => Classical.choose (hLexists n)
  have hfieldLipschitz (n : ℕ) : LipschitzOnWith (lipschitzConstant n)
      (fun x => -(A n x (gradient n x)))
      (Metric.closedBall (center n) (radius n)) :=
    Classical.choose_spec (hLexists n)
  have htrajectoryContinuous : ∀ n,
      ContinuousOn (trajectory n) (Set.Icc (time n) (time n + duration n)) := by
    intro n
    apply HasDerivAt.continuousOn
    intro t ht
    apply htrajectoryFlow n t
    rw [hstartMatchesTime n]
    exact ht.1
  have hfreezeAgreement : ∀ n, Set.EqOn actual (trajectory n)
      (Set.Icc (time n) (time n + duration n)) := by
    intro n
    exact Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval_of_right_derivative
      (fun x => -(A n x (gradient n x))) (center n) (radius n)
      (time n) (time n + duration n) (lipschitzConstant n)
      (hfieldLipschitz n) actual (trajectory n)
      (fun t ht => hactualBall n t ht)
      (fun t ht => htrajectoryBall n t ht)
      (hactualContinuous n) (htrajectoryContinuous n)
      (fun t ht => hactualFlow n t ht)
      (fun t ht =>
        have hderiv := (htrajectoryFlow n t (by
          rw [hstartMatchesTime n]
          exact ht.1)).hasDerivWithinAt
        hderiv.mono (Set.subset_univ (Set.Ici t)))
      (hinitial n)
  have hregionClosed : ∀ n, IsClosed (U n) := by
    intro n
    rw [hUeq n]
    exact Metric.isClosed_closedBall
  have hconvex : ∀ k, Tomabechi.Theorem21.StronglyConvexOn
      (U k) (potential k) (gradient k) (c k) := by
    intro k
    exact Tomabechi.Theorem21.stronglyConvexOn_of_hessian_lower_bound
      (U k) (potential k) (gradient k) (hessian k) (c k) (hUconvex k)
      (hgradient k) (hhessian k) (hlower k)
  have hendpointTolerance : ∀ n,
      dist (actual (time n + duration n)) (xstar n) ≤ epsilon n := by
    intro n
    have ht : time n + duration n ∈
        Set.Icc (time n) (time n + duration n) :=
      ⟨le_add_of_nonneg_right (hpositive n).le, le_rfl⟩
    have hagree := hfreezeAgreement n ht
    have hdecayEndpoint := hdecay n (start n + duration n)
      (le_add_of_nonneg_right (hpositive n).le)
    have hdecayEndpoint' :
        dist (trajectory n (start n + duration n)) (xstar n) ≤
          C n * Real.exp (-lambda n * duration n) := by
      have htime : start n + duration n - start n = duration n := by ring
      simpa [htime] using hdecayEndpoint
    have hwaitBound :
        max 0 (1 / (lambda n * 1) * Real.log (C n / epsilon n)) ≤
          duration n := by
      simpa [mul_one] using hwait n
    have hwaitEndpoint := Tomabechi.Theorem22.dwell_time_suffices_for_error
      (C n) (epsilon n) (lambda n) 1 (duration n) (hC n) (hepsilon n)
      (hlambda n) (by norm_num) hwaitBound
    have hwaitEndpoint' :
        C n * Real.exp (-lambda n * duration n) ≤ epsilon n := by
      simpa [mul_one] using hwaitEndpoint
    calc
      dist (actual (time n + duration n)) (xstar n) =
          dist (trajectory n (start n + duration n)) (xstar n) := by
            have hactualEndpoint :
                actual (time n + duration n) =
                  trajectory n (start n + duration n) := by
              calc
                actual (time n + duration n) =
                    trajectory n (time n + duration n) := hagree
                _ = trajectory n (start n + duration n) := by
                  congr 1
                  rw [hstartMatchesTime n]
            rw [hactualEndpoint]
      _ ≤ C n * Real.exp (-lambda n * duration n) := hdecayEndpoint'
      _ ≤ epsilon n := hwaitEndpoint'
  refine ⟨horder.1, horder.2.2.1, ?_, ?_, ?_, ?_, hendpointTolerance,
    ?_, ?_, ?_,
    horder.2.2.2.1,
    horder.2.2.2.2,
    ?_⟩
  · intro n hsame
    have hrepr : stageRepresentation (u n) = stageRepresentation (u (n + 1)) := by
      calc
        stageRepresentation (u n) = representedCenter n := (hrepresentedCenter n).symm
        _ = representedCenter (n + 1) := hsame
        _ = stageRepresentation (u (n + 1)) := hrepresentedCenter (n + 1)
    have hu : u n = u (n + 1) := hfaithful hrepr
    exact (ne_of_lt (horder.2.2.1 n)) hu
  · intro n
    exact adjacent_stage_minimizers_distinct xstar theta c delta n
      (hdelta n) (htheta (n + 1)) (hgapThreshold n)
  · intro n
    exact Tomabechi.Theorem21.stationary_point_is_unique_minimum_on_region
      (potential n) (gradient n) (c n) (hc n) (U n) (hconvex n)
      (xstar n) (hregionCurrent n) (hstationary n)
  · intro n
    simpa [hstartMatchesTime n] using
      hfreezeAgreement n ⟨le_rfl, le_add_of_nonneg_right (hpositive n).le⟩
  · intro n
    exact stage_tcz_changes_of_strong_convexity_and_decay potential gradient U
      xstar theta c delta trajectory start C lambda n
      (fun k => hconvex (k + 1)) (fun k => hstationary (k + 1))
      (hregionOld n) (hregionNew n) (hdelta n) (hregionCurrent n)
      (hC n) (hlambda n)
      hdecay
      (htheta n) (hgapThreshold n)
  · intro n
    exact isClosed_stageTCZ_of_continuousOn potential xstar theta U
      (fun k => closure (trajectory k '' Set.Ici (start k))) n
      (hregionClosed n) isClosed_closure (hpotentialContinuousOn n)
  · intro n
    refine ⟨xstar n, ?_⟩
    have hreachable : xstar n ∈ closure (trajectory n '' Set.Ici (start n)) :=
      limit_in_closed_reachable_of_exponential_decay
        (trajectory n) (xstar n) (start n) (C n) (lambda n)
        (hC n) (hlambda n) (fun t ht => hdecay n t ht)
    change xstar n ∈ U n ∧
      (xstar n ∈ closure (trajectory n '' Set.Ici (start n)) ∧
        potential n (xstar n) - potential n (xstar n) ≤ theta n)
    exact ⟨hregionCurrent n, hreachable, by simp [htheta n]⟩
  · intro t ht
    exact every_finite_time_in_some_dwell duration time t ht hrecurrence
      horder.2.2.2.1

/-- The canonical piecewise trajectory determined by stage specifications
and the time schedule. Each time is assigned to the first future switch.
日本語要約：段階仕様と切替時刻列から一意に定まるcanonicalな切替軌道。
-/
noncomputable def canonicalStageTrajectory {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (time duration : ℕ → ℝ)
    (hpositive : ∀ n, 0 < duration n)
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k) : ℝ → E := by
  let timing := switching_times_unbounded duration time hpositive hrecurrence
    hdiverges
  let timeStrict : StrictMono time := strictMono_nat_of_lt_succ timing.2
  let active := canonicalSwitchStageIndex time timeStrict timing.1
  exact stitchedStageOrbit stages (Tomabechi.Theorem22.chooseAllStageValleys stages)
    active

/-- End-to-end stagewise bridge for the analytic/TCZ part of Theorem 23.
Theorem 22 constructs every frozen valley, Theorem 23 proves adjacent TCZ
nonfixation and closedness, and transition compatibility propagates the
actual switched trajectory through the dwell intervals with the (22.5)
tolerance. Stage centers are linked to the LUB sequence by an injective
representation map, so their adjacent separation follows from strict LUB
growth. The stage gap, segment, and endpoint state-transition compatibility
remain explicit. The switched trajectory and its dwell ODE/continuity conditions
are constructed canonically from the frozen witnesses. It also states directly
that switches occur beyond every finite time and every stage index, ruling out
a permanent finite-time stopping point for the operation.
日本語要約：忠実表象で束列と段階中心を結び、定理22の段階仕様・切替条件から段階TCZと軌道の結論を得る。-/
theorem theorem22_stage_specs_and_switches_give_condition23B_core
    {L E : Type*} [SemilatticeSup L] [OrderTop L]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (hbelowTop : ∀ n, u n < ⊤) (hnew : ∀ n, ¬ v (n + 1) ≤ u n)
    (stages : ℕ → Tomabechi.Theorem22.StageValleySpec E)
    (stageRepresentation : L → E)
    (hrepresentationFaithful : Function.Injective stageRepresentation)
    (hstageCenter : ∀ n,
      (stages n).center = stageRepresentation (u n))
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
            (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 *
          ‖(Tomabechi.Theorem22.chooseAllStageValleys stages (n + 1)).minimizer -
            (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer‖ ^ 2)
    (hsegment : ∀ n,
      segment ℝ
          (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer
          (Tomabechi.Theorem22.chooseAllStageValleys stages (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius)
    (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (Tomabechi.Theorem22.chooseAllStageValleys stages n).orbit
          (time n + duration n))
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (Tomabechi.Theorem22.chooseAllStageValleys stages n).decayRate *
        Real.log ((Tomabechi.Theorem22.chooseAllStageValleys stages n).decayAmplitude /
          epsilon n)) ≤ duration n)
    :
    ((∀ n, u n < ⊤) ∧ Monotone u ∧ (∀ n, u n < u (n + 1)) ∧
      (∀ B : ℝ, ∃ n, B < time n) ∧ (∀ n, time n < time (n + 1))) ∧
    (∀ n, (stages n).center ≠ (stages (n + 1)).center) ∧
    (∀ n, 0 < ‖(Tomabechi.Theorem22.chooseAllStageValleys stages (n + 1)).minimizer -
      (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer‖) ∧
    (∀ n, IsClosed (stageTCZ
      (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
      (fun k => (Tomabechi.Theorem22.chooseAllStageValleys stages k).minimizer)
      theta (fun k => Metric.closedBall (stages k).center (stages k).radius)
      (fun k => closure
        ((Tomabechi.Theorem22.chooseAllStageValleys stages k).orbit ''
          Set.Ici (stages k).startTime)) n)) ∧
    (∀ n,
      stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (Tomabechi.Theorem22.chooseAllStageValleys stages k).minimizer)
        theta (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure
          ((Tomabechi.Theorem22.chooseAllStageValleys stages k).orbit ''
            Set.Ici (stages k).startTime)) (n + 1) ≠
      stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (Tomabechi.Theorem22.chooseAllStageValleys stages k).minimizer)
        theta (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure
          ((Tomabechi.Theorem22.chooseAllStageValleys stages k).orbit ''
            Set.Ici (stages k).startTime)) n) ∧
    (∀ n, (stageTCZ
        (fun k x => Tomabechi.Theorem22.stageEffectivePotential (stages k) x)
        (fun k => (Tomabechi.Theorem22.chooseAllStageValleys stages k).minimizer)
        theta (fun k => Metric.closedBall (stages k).center (stages k).radius)
        (fun k => closure
          ((Tomabechi.Theorem22.chooseAllStageValleys stages k).orbit ''
            Set.Ici (stages k).startTime)) n).Nonempty) ∧
    (∀ n, Set.EqOn
        (canonicalStageTrajectory stages time duration hpositive hrecurrence hdiverges)
        (Tomabechi.Theorem22.chooseAllStageValleys stages n).orbit
        (Set.Icc (time n) (time n + duration n)) ∧
      dist ((canonicalStageTrajectory stages time duration hpositive hrecurrence hdiverges)
        (time n + duration n))
        (Tomabechi.Theorem22.chooseAllStageValleys stages n).minimizer ≤ epsilon n) ∧
    (∀ t, time 0 ≤ t →
      ∃ n, t ∈ Set.Ico (time n) (time n + duration n)) ∧
    (∀ T K, ∃ n, K ≤ n ∧ T < time n) := by
  let witnesses := Tomabechi.Theorem22.chooseAllStageValleys stages
  let timing := switching_times_unbounded duration time hpositive hrecurrence
    hdiverges
  let timeStrict : StrictMono time := strictMono_nat_of_lt_succ timing.2
  let active := canonicalSwitchStageIndex time timeStrict timing.1
  let actual := stitchedStageOrbit stages witnesses active
  have hactive : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) → active t = n := by
    intro n t ht
    exact canonicalSwitchStageIndex_eq_on_dwell time duration timeStrict
      timing.1 hrecurrence n ht
  have hactiveEndpoint : ∀ n,
      active (time n + duration n) = n + 1 := by
    intro n
    rw [← hrecurrence n]
    exact canonicalSwitchStageIndex_eq_next_at_endpoint time timeStrict timing.1 n
  have hsolution := stitched_stage_orbits_form_a_switching_solution
    stages witnesses active time duration hstart hrecurrence hactive
    hactiveEndpoint htransition
  have hinitialZero : actual (time 0) = (stages 0).initial := by
    have htime : time 0 ∈ Set.Icc (time 0) (time 0 + duration 0) :=
      ⟨le_rfl, le_add_of_nonneg_right (hpositive 0).le⟩
    calc
      actual (time 0) = (witnesses 0).orbit (time 0) := hsolution.1 0 htime
      _ = (stages 0).initial := by
        rw [← hstart 0]
        exact (witnesses 0).initial_condition
  have hactualBall : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) →
      actual t ∈ Metric.closedBall (stages n).center (stages n).radius :=
    hsolution.2.2.1
  have hactualFlow : ∀ n t,
      t ∈ Set.Ico (time n) (time n + duration n) →
      HasDerivWithinAt actual
        (-((stages n).mobility (actual t)
          (Tomabechi.Theorem22.stageEffectiveGradient (stages n) (actual t))))
        (Set.Ici t) t := by
    intro n t ht
    change HasDerivWithinAt actual
      (-((stages n).mobility (actual t)
          ((stages n).backgroundGradient (actual t) -
            ((stages n).gain * (stages n).presenceGain) •
              (stages n).presenceGradient (actual t))))
      (Set.Ici t) t
    exact hsolution.2.2.2 n t ht
  have hactualContinuous : ∀ n,
      ContinuousOn actual (Set.Icc (time n) (time n + duration n)) :=
    hsolution.2.1
  let delta : ℕ → ℝ := fun n =>
    ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖
  have hdelta : ∀ n, delta n =
      ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖ := by
    intro n
    rfl
  have hgap : ∀ n, theta (n + 1) <
      ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
          (stages (n + 1)).curvature -
        (stages (n + 1)).backgroundCurvature) / 2 * delta n ^ 2 := by
    intro n
    exact hgapThreshold n
  have hsegment' : ∀ n,
      segment ℝ (witnesses n).minimizer (witnesses (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius :=
    hsegment
  have hTCZ := all_chosen_stage_TCZs_closed_and_nonfixed
    stages witnesses theta delta hdelta htheta hgap hsegment'
  have hnonempty := all_chosen_stage_TCZs_nonempty
    stages witnesses theta htheta
  have hdeltaPositive : ∀ n, 0 < delta n := by
    intro n
    have hnonneg := norm_nonneg
        ((witnesses (n + 1)).minimizer - (witnesses n).minimizer)
    by_contra hnot
    have hle : ‖(witnesses (n + 1)).minimizer - (witnesses n).minimizer‖ ≤ 0 :=
      le_of_not_gt hnot
    have heq : delta n = 0 := by
      dsimp [delta]
      exact le_antisymm hle hnonneg
    have hgapn := hgap n
    rw [heq] at hgapn
    have hnegative : theta (n + 1) < 0 := by
      simpa using hgapn
    linarith [htheta (n + 1)]
  have hswitch := all_stage_switches_follow_valleys_from_transition_compatibility
    stages witnesses actual time duration epsilon hstart hinitialZero
    htransition hrecurrence hpositive hepsilon hwait hactualBall hactualFlow
    hactualContinuous
  have horder := condition23B_lub_and_timing_consequences
    u v hupdate hbelowTop hnew duration time hpositive hrecurrence
    hdiverges
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
  exact ⟨horder, hcenterDistinct,
    (by simpa [witnesses, delta] using hdeltaPositive),
    (by simpa [witnesses] using hTCZ.1),
    (by simpa [witnesses] using hTCZ.2),
    (by simpa [witnesses] using hnonempty),
    (by simpa [witnesses, actual, canonicalStageTrajectory, timing, timeStrict,
      active] using hswitch),
    (by
      intro t ht
      exact every_finite_time_in_some_dwell duration time t ht hrecurrence
        horder.2.2.2.1),
    infinitely_many_switches_after_every_finite_time duration time
      hpositive hrecurrence hdiverges⟩

/-- The same Condition 23-B switching core for H-stage mean-field inputs.
Every stage valley and frozen orbit is selected from the exact sequence
obtained by mapping each mean-field record to `StageValleySpec`; all gap,
representation, transition, new-information, and dwell assumptions remain
the explicit inputs of the underlying theorem.
日本語要約：平均場段階記録を谷仕様へ写した同一系列で23-B核を適用する入口。 -/
noncomputable def meanField_stage_specs_and_switches_give_condition23B_core
    {L E : Type*} [SemilatticeSup L] [OrderTop L]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (u v : ℕ → L) (hupdate : ∀ n, u (n + 1) = u n ⊔ v (n + 1))
    (hbelowTop : ∀ n, u n < ⊤) (hnew : ∀ n, ¬ v (n + 1) ≤ u n)
    (stages : ℕ → Tomabechi.Theorem22.MeanFieldStageInput E)
    (stageRepresentation : L → E)
    (hrepresentationFaithful : Function.Injective stageRepresentation)
    (hstageCenter : ∀ n,
      (stages n).center = stageRepresentation (u n))
    (theta : ℕ → ℝ) (htheta : ∀ n, 0 ≤ theta n)
    (hgapThreshold : ∀ n,
      theta (n + 1) <
        ((stages (n + 1)).gain * (stages (n + 1)).presenceGain *
            (stages (n + 1)).curvature -
          (stages (n + 1)).backgroundCurvature) / 2 *
          ‖(Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages
              (n + 1)).minimizer -
            (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages n).minimizer‖ ^ 2)
    (hsegment : ∀ n,
      segment ℝ
          (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages n).minimizer
          (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages
            (n + 1)).minimizer ⊆
        Metric.closedBall (stages (n + 1)).center (stages (n + 1)).radius)
    (time duration epsilon : ℕ → ℝ)
    (hstart : ∀ n, (stages n).startTime = time n)
    (htransition : ∀ n,
      (stages (n + 1)).initial =
        (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages n).orbit
          (time n + duration n))
    (hrecurrence : ∀ n, time (n + 1) = time n + duration n)
    (hpositive : ∀ n, 0 < duration n)
    (hdiverges : ∀ B : ℝ, ∃ n,
      B < ∑ k ∈ Finset.range n, duration k)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hwait : ∀ n, max 0
      (1 / (Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages n).decayRate *
        Real.log ((Tomabechi.Theorem22.chooseAllMeanFieldStageValleys stages n).decayAmplitude /
          epsilon n)) ≤ duration n) := by
  exact theorem22_stage_specs_and_switches_give_condition23B_core
    u v hupdate hbelowTop hnew
    (Tomabechi.Theorem22.meanFieldStageSequence stages)
    stageRepresentation hrepresentationFaithful
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using hstageCenter)
    theta htheta
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.chooseAllStageValleys,
      Tomabechi.Theorem22.chooseAllMeanFieldStageValleys] using hgapThreshold)
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.chooseAllStageValleys,
      Tomabechi.Theorem22.chooseAllMeanFieldStageValleys] using hsegment)
    time duration epsilon
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec] using hstart)
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.chooseAllStageValleys,
      Tomabechi.Theorem22.chooseAllMeanFieldStageValleys] using htransition)
    hrecurrence hpositive hdiverges hepsilon
    (by simpa [Tomabechi.Theorem22.meanFieldStageSequence,
      Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec,
      Tomabechi.Theorem22.chooseAllStageValleys,
      Tomabechi.Theorem22.chooseAllMeanFieldStageValleys] using hwait)

#print axioms meanField_stage_specs_and_switches_give_condition23B_core



end Tomabechi.Theorem23
