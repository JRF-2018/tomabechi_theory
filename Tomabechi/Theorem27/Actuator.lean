import Theorem1
import Theorem24_26
import Tomabechi.Theorem27.Abstract

/-! 条件27-Aの制御入力・Dini微分・定量散逸補題。-/

namespace Tomabechi.Theorem27.Actuator

open RealInnerProductSpace Filter Topology

/-- The model-relative formation action in (27.5): the reference-subtracted
input has a strictly positive contribution to Lyapunov residual descent. -/
def sankhara27Contribution
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (gradW : E) (actuator : U →L[ℝ] E)
    (controlDifference : U) : Prop :=
  0 < -(inner ℝ gradW (actuator controlDifference))

/-- Upper right Dini derivative, defined as the limsup of forward difference
quotients. -/
noncomputable def upperRightDiniDerivative (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  limsup (slope f t) (𝓝[>] t)

/-- Local Lipschitz regularity bounds the forward difference quotients from
below near the base point. This is the boundedness side needed when converting
the strict-eventual right-slope definition into a real-valued limsup bound. -/
theorem slope_isBoundedUnder_of_locallyLipschitz
    (f : ℝ → ℝ) (hf : LocallyLipschitz f) (t : ℝ) :
    (𝓝[>] t).IsCoboundedUnder (· ≤ ·) (slope f t) := by
  obtain ⟨K, s, hs, hLip⟩ := hf t
  have hmem : ∀ᶠ z in 𝓝[>] t, z ∈ s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hs
  have hslope : ∀ᶠ z in 𝓝[>] t, -(K : ℝ) ≤ slope f t z := by
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzt
    have htz : t < z := by simpa using hzt
    have ht : t ∈ s := mem_of_mem_nhds hs
    have hdist' : |f z - f t| ≤ (K : ℝ) * |z - t| := by
      have hmetric : dist (f z) (f t) ≤ (K : ℝ) * dist z t := by
        simpa [Subtype.dist_eq] using hLip.to_restrict.dist_le_mul ⟨z, hz⟩ ⟨t, ht⟩
      simpa [Real.dist_eq] using hmetric
    have hquot : |slope f t z| ≤ (K : ℝ) := by
      have habs : |slope f t z| = |f z - f t| / |z - t| := by
        simp [slope_def_field, abs_div]
      rw [habs]
      calc
        |f z - f t| / |z - t| ≤ ((K : ℝ) * |z - t|) / |z - t| :=
          div_le_div_of_nonneg_right hdist' (abs_nonneg _)
        _ = (K : ℝ) := by
          rw [abs_of_pos (sub_pos.mpr htz)]
          calc
            (K : ℝ) * (z - t) / (z - t) =
                (K : ℝ) * ((z - t) / (z - t)) := by ring
            _ = K := by rw [div_self (ne_of_gt (sub_pos.mpr htz)), mul_one]
    exact (abs_le.mp hquot).1
  exact Filter.isCoboundedUnder_le_of_eventually_le (𝓝[>] t) hslope

/-- Future-ray local Lipschitz regularity is enough to bound forward slopes
from below at any point of the ray. -/
theorem slope_isBoundedUnder_of_locallyLipschitzOn_Ici
    (f : ℝ → ℝ) (T t : ℝ)
    (hf : LocallyLipschitzOn (Set.Ici T) f) (ht : T ≤ t) :
    (𝓝[>] t).IsCoboundedUnder (· ≤ ·) (slope f t) := by
  obtain ⟨K, s, hs, hLip⟩ := hf ht
  obtain ⟨u, hu, huSub⟩ :=
    (mem_nhdsWithin_iff_exists_mem_nhds_inter).mp hs
  have hU : ∀ᶠ z in 𝓝[>] t, z ∈ u :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hu
  have hmem : ∀ᶠ z in 𝓝[>] t, z ∈ s := by
    filter_upwards [hU, self_mem_nhdsWithin] with z hzu hzt
    apply huSub
    constructor
    · exact hzu
    · exact Set.mem_Ici.mpr (le_trans ht (le_of_lt (by simpa using hzt)))
  have htmem : t ∈ s := mem_of_mem_nhdsWithin ht hs
  have hslope : ∀ᶠ z in 𝓝[>] t, -(K : ℝ) ≤ slope f t z := by
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzt
    have htz : t < z := by simpa using hzt
    have hmetric : dist (f z) (f t) ≤ (K : ℝ) * dist z t := by
      simpa [Subtype.dist_eq] using
        hLip.to_restrict.dist_le_mul ⟨z, hz⟩ ⟨t, htmem⟩
    have hdist : |f z - f t| ≤ (K : ℝ) * |z - t| := by
      simpa [Real.dist_eq] using hmetric
    have hquot : |slope f t z| ≤ (K : ℝ) := by
      have habs : |slope f t z| = |f z - f t| / |z - t| := by
        simp [slope_def_field, abs_div]
      rw [habs]
      calc
        |f z - f t| / |z - t| ≤ ((K : ℝ) * |z - t|) / |z - t| :=
          div_le_div_of_nonneg_right hdist (abs_nonneg _)
        _ = (K : ℝ) := by
          rw [abs_of_pos (sub_pos.mpr htz)]
          calc
            (K : ℝ) * (z - t) / (z - t) =
                (K : ℝ) * ((z - t) / (z - t)) := by ring
            _ = K := by rw [div_self (ne_of_gt (sub_pos.mpr htz)), mul_one]
    exact (abs_le.mp hquot).1
  exact Filter.isCoboundedUnder_le_of_eventually_le (𝓝[>] t) hslope

/-- A lower bound on forward quotients supplies the lower boundedness needed
to convert an eventual right-slope estimate into a real-valued limsup bound.
This isolates the exact auxiliary input; local Lipschitz continuity is one
sufficient way to provide it, but is not required by the conversion itself. -/
theorem upperRightDiniDerivative_le_of_rightSlopeBound_of_lowerBound
    (f : ℝ → ℝ) (t bound lower : ℝ)
    (hLower : ∀ᶠ z in 𝓝[>] t, lower ≤ slope f t z)
    (hSlope : Tomabechi.Theorem1.RightSlopeBound f t bound) :
    upperRightDiniDerivative f t ≤ bound := by
  have hCobounded : (𝓝[>] t).IsCoboundedUnder (· ≤ ·) (slope f t) :=
    Filter.isCoboundedUnder_le_of_eventually_le (𝓝[>] t) hLower
  have hBounded : (𝓝[>] t).IsBoundedUnder (· ≤ ·) (slope f t) := by
    have hev := hSlope (bound + 1) (by linarith : bound < bound + 1)
    have hev' : ∀ᶠ z in 𝓝[>] t, slope f t z ≤ bound + 1 := by
      filter_upwards [hev] with z hz
      have heq : (z - t)⁻¹ * (f z - f t) = slope f t z := by
        rw [slope_def_field, div_eq_mul_inv]
        ring
      rw [← heq]
      exact le_of_lt hz
    exact Filter.isBoundedUnder_of_eventually_le hev'
  unfold upperRightDiniDerivative
  refine (limsup_le_iff
    hCobounded hBounded).2 ?_
  intro r hr
  filter_upwards [hSlope r hr] with z hz
  have heq : (z - t)⁻¹ * (f z - f t) = slope f t z := by
    rw [slope_def_field, div_eq_mul_inv]
    ring
  rw [← heq]
  exact hz

/-- A locally Lipschitz path supplies the lower slope bound and hence the
real-valued upper right Dini estimate. -/
theorem upperRightDiniDerivative_le_of_rightSlopeBound
    (f : ℝ → ℝ) (T : ℝ)
    (hf : LocallyLipschitzOn (Set.Ici T) f) (ht : T ≤ t) (bound : ℝ)
    (hSlope : Tomabechi.Theorem1.RightSlopeBound f t bound) :
    upperRightDiniDerivative f t ≤ bound := by
  have hCobounded : (𝓝[>] t).IsCoboundedUnder (· ≤ ·) (slope f t) :=
    slope_isBoundedUnder_of_locallyLipschitzOn_Ici f T t hf ht
  have hBounded : (𝓝[>] t).IsBoundedUnder (· ≤ ·) (slope f t) := by
    have hev := hSlope (bound + 1) (by linarith : bound < bound + 1)
    have hev' : ∀ᶠ z in 𝓝[>] t, slope f t z ≤ bound + 1 := by
      filter_upwards [hev] with z hz
      have heq : (z - t)⁻¹ * (f z - f t) = slope f t z := by
        rw [slope_def_field, div_eq_mul_inv]
        ring
      rw [← heq]
      exact le_of_lt hz
    exact Filter.isBoundedUnder_of_eventually_le hev'
  unfold upperRightDiniDerivative
  refine (limsup_le_iff hCobounded hBounded).2 ?_
  intro r hr
  filter_upwards [hSlope r hr] with z hz
  have heq : (z - t)⁻¹ * (f z - f t) = slope f t z := by
    rw [slope_def_field, div_eq_mul_inv]
    ring
  rw [← heq]
  exact hz

/-- At a differentiability point, the upper right Dini derivative equals the
ordinary derivative. -/
theorem upperRightDiniDerivative_eq_of_hasDerivAt
    (f : ℝ → ℝ) (f' t : ℝ) (hf : HasDerivAt f f' t) :
    upperRightDiniDerivative f t = f' := by
  exact (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)).limsup_eq

/-- A zero right derivative on the forward ray forces the upper right Dini
derivative to vanish. -/
theorem upperRightDiniDerivative_eq_zero_of_hasDerivWithinAt
    (f : ℝ → ℝ) (t : ℝ)
    (hf : HasDerivWithinAt f 0 (Set.Ici t) t) :
    upperRightDiniDerivative f t = 0 := by
  have hslope := (hasDerivWithinAt_iff_tendsto_slope).mp hf
  have hset : Set.Ici t \ {t} = Set.Ioi t := by
    ext s
    simp [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
  rw [hset] at hslope
  exact hslope.limsup_eq

/-- A locally Lipschitz scalar residual path has an ordinary derivative a.e.
on each compact interval.  Consequently its upper right Dini derivative
agrees with that ordinary derivative a.e. there. -/
theorem ae_upperRightDiniDerivative_eq_deriv_on_interval
    (f : ℝ → ℝ) (a b : ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ t,
      t ∈ Set.uIcc a b → upperRightDiniDerivative f t = deriv f t := by
  have hlip : LocallyLipschitzOn (Set.uIcc a b) f := hf.locallyLipschitzOn
  obtain ⟨K, hK⟩ := hlip.exists_lipschitzOnWith_of_compact isCompact_uIcc
  have hac := hK.absolutelyContinuousOnInterval
  have hdiffAE : ∀ᵐ t,
      t ∈ Set.uIcc a b → DifferentiableAt ℝ f t := hac.ae_differentiableAt
  exact hdiffAE.mono fun t hdiff htmem =>
    upperRightDiniDerivative_eq_of_hasDerivAt f (deriv f t) t
      (hdiff htmem).hasDerivAt

/-- A locally Lipschitz residual path has matching upper right Dini and
ordinary derivatives almost everywhere on the whole real line.  The proof
covers ℝ by countably many compact intervals and applies absolute continuity
on each interval. -/
theorem ae_upperRightDiniDerivative_eq_deriv
    (f : ℝ → ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ t, upperRightDiniDerivative f t = deriv f t := by
  have hinterval : ∀ n : ℕ, ∀ᵐ t,
      t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) →
        upperRightDiniDerivative f t = deriv f t := by
    intro n
    exact ae_upperRightDiniDerivative_eq_deriv_on_interval f
      (-(n : ℝ)) (n : ℝ) hf
  have hall : ∀ᵐ t, ∀ n : ℕ,
      t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) →
        upperRightDiniDerivative f t = deriv f t :=
    MeasureTheory.ae_all_iff.mpr hinterval
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, |t| < n := exists_nat_gt |t|
  have hbound : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmem : t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) := by
    rw [Set.uIcc_of_le (by linarith : -(n : ℝ) ≤ (n : ℝ)), Set.mem_Icc]
    exact ⟨(neg_le_neg (le_of_lt hn)).trans (neg_abs_le t),
      (le_abs_self t).trans (le_of_lt hn)⟩
  exact ht n hmem

/-- Future-domain version: local Lipschitz regularity is required only on
`[T,∞)`, matching a trajectory specified from its initial time onward. -/
theorem ae_upperRightDiniDerivative_eq_deriv_on_future
    (f : ℝ → ℝ) (T : ℝ)
    (hf : LocallyLipschitzOn (Set.Ici T) f) :
    ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      upperRightDiniDerivative f t = deriv f t := by
  have hinterval : ∀ n : ℕ, ∀ᵐ t,
      t ∈ Set.Icc T (T + (n : ℝ) + 1) → DifferentiableAt ℝ f t := by
    intro n
    have hTend : T ≤ T + (n : ℝ) + 1 := by linarith
    have hLipOn : LocallyLipschitzOn
        (Set.uIcc T (T + (n : ℝ) + 1)) f :=
      hf.mono (by
        intro t ht
        rw [Set.uIcc_of_le hTend] at ht
        exact ht.1)
    obtain ⟨K, hK⟩ :=
      hLipOn.exists_lipschitzOnWith_of_compact isCompact_uIcc
    have hdiff := hK.absolutelyContinuousOnInterval.ae_differentiableAt
    rw [Set.uIcc_of_le hTend] at hdiff
    exact hdiff
  have hall : ∀ᵐ t, ∀ n : ℕ,
      t ∈ Set.Icc T (T + (n : ℝ) + 1) → DifferentiableAt ℝ f t :=
    MeasureTheory.ae_all_iff.mpr hinterval
  have hdiffOnIci : ∀ᵐ t, T ≤ t → DifferentiableAt ℝ f t := by
    filter_upwards [hall] with t ht
    intro htT
    obtain ⟨n, hn⟩ := exists_nat_gt (t - T)
    exact ht n ⟨htT, by linarith⟩
  have hdiffFuture : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      DifferentiableAt ℝ f t := by
    rw [_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure]
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ici).2
    filter_upwards [hdiffOnIci] with t hdiff
    intro ht
    exact hdiff ht
  filter_upwards [hdiffFuture] with t hdiff
  exact upperRightDiniDerivative_eq_of_hasDerivAt f (deriv f t) t
    hdiff.hasDerivAt

/-- An absolutely continuous scalar function with an essentially bounded
derivative is Lipschitz on the interval. This is the finite-interval bridge
used to obtain future local Lipschitz regularity from bounded 27-A data. -/
theorem lipschitzOn_Icc_of_absolutelyContinuousOnInterval_of_ae_deriv_bound
    (f : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hac : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t, t ∈ Set.Icc a b → |deriv f t| ≤ C) :
    LipschitzOnWith C.toNNReal f (Set.Icc a b) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have hforward : ∀ p q, p ≤ q → p ∈ Set.Icc a b → q ∈ Set.Icc a b →
      dist (f p) (f q) ≤ C.toNNReal * dist p q := by
    intro p q hpq hp hq
    have hpqSub : Set.uIcc p q ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hpq]
      rw [Set.uIcc_of_le hab]
      intro z hz
      exact ⟨hp.1.trans hz.1, hz.2.trans hq.2⟩
    have hACpq : AbsolutelyContinuousOnInterval f p q := by
      apply hac.mono
      intro z hz
      exact hpqSub hz
    have hboundPQ : ∀ᵐ t, t ∈ Set.uIoc p q → ‖deriv f t‖ ≤ C := by
      filter_upwards [hderiv] with t ht htpq
      have htIcc : t ∈ Set.Icc a b := by
        have htu : t ∈ Set.uIcc p q := Set.uIoc_subset_uIcc htpq
        have hta := hpqSub htu
        simpa [Set.uIcc_of_le hab] using hta
      simpa [Real.norm_eq_abs] using ht htIcc
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae hboundPQ
    have hFTC := hACpq.integral_deriv_eq_sub
    have hnorm : ‖∫ t in p..q, deriv f t‖ = |f q - f p| := by
      rw [hFTC]
      simp [Real.norm_eq_abs]
    calc
      dist (f p) (f q) = |f q - f p| := by
        rw [Real.dist_eq]
        simp [abs_sub_comm]
      _ = ‖∫ t in p..q, deriv f t‖ := hnorm.symm
      _ ≤ C * |q - p| := hInt
      _ = C.toNNReal * dist p q := by
        rw [Real.dist_eq, abs_sub_comm p q, Real.coe_toNNReal C hC]
  rcases le_total x y with hxy | hyx
  · exact hforward x y hxy hx hy
  · calc
      dist (f x) (f y) = dist (f y) (f x) := dist_comm _ _
      _ ≤ C.toNNReal * dist y x := hforward y x hyx hy hx
      _ = C.toNNReal * dist x y := by rw [dist_comm]

/-- If an absolutely continuous future residual has an essentially bounded
derivative on every finite future interval, then it is locally Lipschitz on
the whole future ray. -/
theorem locallyLipschitzOn_Ici_of_absolutelyContinuous_of_local_deriv_bound
    (f : ℝ → ℝ) (T : ℝ)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval f T b)
    (hderiv : ∀ b, T ≤ b → ∃ C, 0 ≤ C ∧
      ∀ᵐ t, t ∈ Set.Icc T b → |deriv f t| ≤ C) :
    LocallyLipschitzOn (Set.Ici T) f := by
  intro t ht
  change T ≤ t at ht
  obtain ⟨C, hC, hderivBound⟩ := hderiv (t + 1) (by linarith)
  have hLip := lipschitzOn_Icc_of_absolutelyContinuousOnInterval_of_ae_deriv_bound
    f T (t + 1) C (by linarith) hC (hac (t + 1) (by linarith)) hderivBound
  refine ⟨C.toNNReal, Set.Icc T (t + 1), ?_, hLip⟩
  apply (mem_nhdsWithin_iff_exists_mem_nhds_inter).2
  refine ⟨Set.Iio (t + 1), Iio_mem_nhds (by linarith), ?_⟩
  intro z hz
  exact ⟨hz.2, le_of_lt hz.1⟩

/-- Absolute continuity of a finite-dimensional real coordinate path implies
almost-everywhere differentiability of the vector path.  The proof applies
the scalar absolute-continuity theorem to each coordinate projection and
reassembles differentiability with `differentiableAt_pi`. -/
theorem ae_differentiableAt_pi_of_absolutelyContinuousOnInterval
    {ι : Type*} [Fintype ι] (x : ℝ → EuclideanSpace ℝ ι) (a b : ℝ)
    (hx : AbsolutelyContinuousOnInterval x a b) :
    ∀ᵐ t, t ∈ Set.uIcc a b → DifferentiableAt ℝ x t := by
  have hcoordinate (i : ι) :
      AbsolutelyContinuousOnInterval (fun t => x t i) a b := by
    let proj : EuclideanSpace ℝ ι → ℝ := fun y => y i
    let projCLM : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
      EuclideanSpace.proj (𝕜 := ℝ) i
    have hproj : LipschitzWith ‖projCLM‖₊ proj := by
      have h := projCLM.lipschitzWith
      simpa [proj, projCLM, EuclideanSpace.coe_proj ℝ] using h
    have hcomp := hproj.comp_absolutelyContinuousOnInterval hx
    simpa [proj, Function.comp_def] using hcomp
  have hdiff : ∀ i : ι, ∀ᵐ t,
      t ∈ Set.uIcc a b → DifferentiableAt ℝ (fun t => x t i) t := by
    intro i
    exact (hcoordinate i).ae_differentiableAt
  have hall : ∀ᵐ t, ∀ i : ι,
      t ∈ Set.uIcc a b → DifferentiableAt ℝ (fun t => x t i) t :=
    MeasureTheory.ae_all_iff.mpr hdiff
  filter_upwards [hall] with t ht hmem
  exact (differentiableAt_piLp (p := (2 : ENNReal))).2 fun i => ht i hmem

/-- If a finite-dimensional state trajectory is absolutely continuous on each
compact interval and satisfies its control-affine ODE almost everywhere, then
the `HasDerivAt` form needed by the chain rule holds almost everywhere. -/
theorem ae_hasDerivAt_pi_of_ac_and_ode
    {ι : Type*} [Fintype ι]
    (x velocity : ℝ → EuclideanSpace ℝ ι)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval x a b)
    (hODE : ∀ᵐ t, deriv x t = velocity t) :
    ∀ᵐ t, HasDerivAt x (velocity t) t := by
  have hinterval : ∀ n : ℕ, ∀ᵐ t,
      t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) → DifferentiableAt ℝ x t := by
    intro n
    exact ae_differentiableAt_pi_of_absolutelyContinuousOnInterval x
      (-(n : ℝ)) (n : ℝ) (hac (-(n : ℝ)) (n : ℝ))
  have hall : ∀ᵐ t, ∀ n : ℕ,
      t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) → DifferentiableAt ℝ x t :=
    MeasureTheory.ae_all_iff.mpr hinterval
  filter_upwards [hall, hODE] with t ht hode
  obtain ⟨n, hn⟩ : ∃ n : ℕ, |t| < n := exists_nat_gt |t|
  have hmem : t ∈ Set.uIcc (-(n : ℝ)) (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Set.uIcc_of_le (by linarith : -(n : ℝ) ≤ (n : ℝ)), Set.mem_Icc]
    exact ⟨(neg_le_neg (le_of_lt hn)).trans (neg_abs_le t),
      (le_abs_self t).trans (le_of_lt hn)⟩
  have hderiv := (ht n hmem).hasDerivAt
  rw [hode] at hderiv
  exact hderiv

/-- Future-ray version matching condition 27-A: compact-interval absolute
continuity supplies differentiability a.e., and the ODE equality is needed
only a.e. on `[T,∞)`. -/
theorem ae_hasDerivAt_pi_on_future_of_ac_and_ode
    {ι : Type*} [Fintype ι]
    (T : ℝ) (x velocity : ℝ → EuclideanSpace ℝ ι)
    (hac : ∀ b, T ≤ b → AbsolutelyContinuousOnInterval x T b)
    (hODE : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      deriv x t = velocity t) :
    ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasDerivAt x (velocity t) t := by
  have hinterval : ∀ n : ℕ, ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      t ∈ Set.uIcc T (T + (n : ℝ)) → HasDerivAt x (velocity t) t := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hTle : T ≤ T + (n : ℝ) := by linarith
    have hdiffVolume := ae_differentiableAt_pi_of_absolutelyContinuousOnInterval
      x T (T + (n : ℝ)) (hac (T + (n : ℝ)) hTle)
    have hdiff : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
        t ∈ Set.uIcc T (T + (n : ℝ)) → DifferentiableAt ℝ x t := by
      rw [_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure]
      exact MeasureTheory.ae_restrict_of_ae hdiffVolume
    filter_upwards [hdiff, hODE] with t hdiff_t hode_t
    intro hmem
    have hderiv := (hdiff_t hmem).hasDerivAt
    rw [hode_t] at hderiv
    exact hderiv
  have hall : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      ∀ n : ℕ, t ∈ Set.uIcc T (T + (n : ℝ)) → HasDerivAt x (velocity t) t :=
    MeasureTheory.ae_all_iff.mpr hinterval
  have hsupport : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      T ≤ t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact ht
  filter_upwards [hall, hsupport] with t ht hTt
  obtain ⟨n, hn⟩ := exists_nat_gt (t - T)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hTle : T ≤ T + (n : ℝ) := by linarith
  have hmem : t ∈ Set.uIcc T (T + (n : ℝ)) := by
    rw [Set.uIcc_of_le hTle, Set.mem_Icc]
    exact ⟨hTt, by linarith⟩
  exact ht n hmem


/-- Chain rule for a time-dependent Lyapunov function along a differentiable
state curve.  The derivative of the joint time-state curve is supplied
explicitly, so this lemma does not assume the closed-loop derivative formula
used by the actuator attribution result. -/
theorem hasDerivAt_timeState_composition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℝ × E → ℝ) (dW : ℝ × E →L[ℝ] ℝ)
    (x : ℝ → E) (t : ℝ) (velocity : ℝ × E)
    (hW : HasFDerivAt W dW (t, x t))
    (hcurve : HasDerivAt (fun s => (s, x s)) velocity t) :
    HasDerivAt (fun s => W (s, x s)) (dW velocity) t := by
  simpa only [Function.comp_def] using HasFDerivAt.comp_hasDerivAt t hW hcurve

/-- Assemble the derivative of time and the state derivative into the joint
time-state velocity needed by the chain rule. -/
theorem hasDerivAt_joint_time_state
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ → E) (t : ℝ) (velocity : E)
    (hx : HasDerivAt x velocity t) :
    HasDerivAt (fun s => (s, x s)) (1, velocity) t := by
  have htime : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  simpa using htime.prodMk hx

/-- Split a space-time Fréchet derivative into its time component and its
state-gradient pairing. -/
theorem timeState_fderiv_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (dW : ℝ × E →L[ℝ] ℝ) (gradW : E) (velocity : E)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z) :
    dW (1, velocity) = dW (1, 0) + inner ℝ gradW velocity := by
  have hp : ((1 : ℝ), velocity) = ((1, 0) + (0, velocity)) := by
    ext <;> simp
  calc
    dW (1, velocity) = dW ((1, 0) + (0, velocity)) := congrArg dW hp
    _ = dW (1, 0) + inner ℝ gradW velocity := by rw [map_add, hstateGradient]

/-- Forward invariance of a time-varying target, together with zero Lyapunov
residual on that target, forces the residual along the trajectory to have
zero right derivative after target entry.  This is the calculus content of
the zero-descent part of equation (27.9). -/
theorem residual_has_right_derivative_zero_after_target_entry
    {E : Type*} (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (T t : ℝ) (hTt : T ≤ t)
    (hinvariant : ∀ s, T ≤ s → x s ∈ N s)
    (hzero : ∀ s y, y ∈ N s → W (s, y) = 0) :
    HasDerivWithinAt (fun s => W (s, x s)) 0 (Set.Ici t) t := by
  apply (hasDerivWithinAt_const (c := (0 : ℝ)) (s := Set.Ici t) (x := t)).congr
  · intro s hs
    exact hzero s (x s) (hinvariant s (hTt.trans hs))
  · exact hzero t (x t) (hinvariant t hTt)

/-- Forward invariance and zero residual on the target force the upper right
Dini derivative to vanish from the instant of target entry onward. -/
theorem upperRightDiniDerivative_zero_on_invariant_target
    {E : Type*} (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (t : ℝ) (htarget : x t ∈ N t) :
    upperRightDiniDerivative (fun s => W (s, x s)) t = 0 := by
  have hright := residual_has_right_derivative_zero_after_target_entry
    N W x t t le_rfl (fun s hs => hforward t s hs htarget) hWzero
  exact upperRightDiniDerivative_eq_zero_of_hasDerivWithinAt _ _ hright

/-- At times strictly after target entry, future vanishing makes any ordinary
derivative of the residual path equal to zero. -/
theorem residual_derivative_zero_after_target_entry
    (q : ℝ → ℝ) (T t derivative : ℝ) (hTt : T < t)
    (hzero : ∀ s, T ≤ s → q s = 0)
    (hq : HasDerivAt q derivative t) :
    derivative = 0 := by
  have hEventually : q =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hTt] with s hs
    exact hzero s hs.le
  have hzeroDeriv : HasDerivAt q 0 t :=
    (hasDerivAt_const (c := (0 : ℝ)) t).congr_of_eventuallyEq hEventually
  exact hq.unique hzeroDeriv

/-- Derive the closed-loop Lyapunov derivative from the time-state chain rule
and a control-affine velocity.  `hsplit` is the usual decomposition of the
Fréchet derivative into its explicit time derivative and state gradient. -/
theorem closedLoop_descent_formula_of_chain_rule
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × E → ℝ) (dW : ℝ × E →L[ℝ] ℝ)
    (x : ℝ → E) (t : ℝ) (gradW drift : E) (u0 utr : U)
    (actuator : U →L[ℝ] E) (descentRate : ℝ)
    (hW : HasFDerivAt W dW (t, x t))
    (hcurve : HasDerivAt (fun s => (s, x s))
      (1, drift + actuator u0) t)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z)
    (hdescent : descentRate = - (dW (1, drift + actuator u0)))
    (hReference : dW (1, 0) + inner ℝ gradW (drift + actuator utr) = 0) :
    descentRate = -(inner ℝ gradW (actuator (u0 - utr))) := by
  have htrajectory := hasDerivAt_timeState_composition W dW x t
    (1, drift + actuator u0) hW hcurve
  have hsplit := timeState_fderiv_decomposition dW gradW
    (drift + actuator u0) hstateGradient
  have hderiv : deriv (fun s => W (s, x s)) t =
      dW (1, 0) + inner ℝ gradW (drift + actuator u0) := by
    rw [htrajectory.deriv, hsplit]
  have hClosedLoop : descentRate =
      -(dW (1, 0) + inner ℝ gradW (drift + actuator u0)) := by
    calc
      descentRate = -(dW (1, drift + actuator u0)) := hdescent
      _ = -deriv (fun s => W (s, x s)) t := by rw [htrajectory.deriv]
      _ = -(dW (1, 0) + inner ℝ gradW (drift + actuator u0)) := by rw [hderiv]
  have hsplitPairing :
      inner ℝ gradW (drift + actuator u0) -
          inner ℝ gradW (drift + actuator utr) =
        inner ℝ gradW (actuator (u0 - utr)) := by
    simp only [inner_add_right, inner_sub_right, map_sub]
    ring
  rw [hClosedLoop]
  nlinarith [hReference, hsplitPairing]

/-- Almost-everywhere version of the chain-rule attribution identity for
time-dependent controls and actuator maps.  The ODE and reference-loop
cancellation are assumed almost everywhere, matching condition 27-A; the
Lyapunov function is Fréchet differentiable along the whole trajectory. -/
theorem ae_closedLoop_descent_formula_of_ode_under_measure
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (μ : MeasureTheory.Measure ℝ)
    (hW : ∀ᵐ t ∂μ, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t ∂μ,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0) :
    ∀ᵐ t ∂μ,
      -(deriv (fun s => W (s, x s)) t) =
        -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := by
  filter_upwards [hW, hmodel] with t hWt ht
  rcases ht with ⟨hstate, hstateGradient, hReference⟩
  have hcurve := hasDerivAt_joint_time_state x t
    (drift t + actuator t (u0 t)) hstate
  have htrajectory := hasDerivAt_timeState_composition W (dW t) x t
    (1, drift t + actuator t (u0 t)) hWt hcurve
  have hdescent : -(deriv (fun s => W (s, x s)) t) =
      -dW t (1, drift t + actuator t (u0 t)) := by
    rw [htrajectory.deriv]
  exact closedLoop_descent_formula_of_chain_rule W (dW t) x t
    (gradW t) (drift t) (u0 t) (utr t) (actuator t) _ hWt hcurve
    hstateGradient hdescent hReference

/-- The 27-A derivative attribution transfers local essential bounds on the
actuator contribution to local essential bounds on the residual derivative. -/
theorem future_residual_derivative_bound_of_attribution
    (q pairing : ℝ → ℝ) (T : ℝ)
    (hAttribution : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      -(deriv q t) = -(pairing t))
    (hPairingBound : ∀ b, T ≤ b → ∃ C, 0 ≤ C ∧
      ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
        t ∈ Set.Icc T b → |pairing t| ≤ C) :
    ∀ b, T ≤ b → ∃ C, 0 ≤ C ∧
      ∀ᵐ t, t ∈ Set.Icc T b → |deriv q t| ≤ C := by
  have hAttributionRay : ∀ᵐ t, T ≤ t → deriv q t = pairing t := by
    rw [_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure] at hAttribution
    have h := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).1 hAttribution
    filter_upwards [h] with t ht
    intro htT
    exact neg_injective (ht htT)
  intro b hTb
  obtain ⟨C, hC, hBound⟩ := hPairingBound b hTb
  have hBoundRay : ∀ᵐ t, T ≤ t → t ∈ Set.Icc T b → |pairing t| ≤ C := by
    rw [_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure] at hBound
    have h := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).1 hBound
    filter_upwards [h] with t ht
    intro htT htIcc
    exact ht htT htIcc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hAttributionRay, hBoundRay] with t hEq hBoundT
  intro htIcc
  have hTt : T ≤ t := htIcc.1
  rw [hEq hTt]
  exact hBoundT hTt htIcc

/-- A continuous actuator-residual pairing is bounded on each compact future
interval, hence supplies the local essential-bound input used by the
future-ray regularity adapters.  The continuity is a model regularity
condition; it is not inferred from condition 27-A alone. -/
theorem future_pairing_ae_bound_of_continuousOn
    (pairing : ℝ → ℝ) (T b : ℝ) (hTb : T ≤ b)
    (hpairing : ContinuousOn pairing (Set.Icc T b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
        t ∈ Set.Icc T b → |pairing t| ≤ C := by
  have hcompact : IsCompact (Set.Icc T b) := isCompact_Icc
  have habs : ContinuousOn (fun t => |pairing t|) (Set.Icc T b) :=
    continuous_abs.comp_continuousOn hpairing
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn habs
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  filter_upwards [] with t
  intro ht
  have hnorm : ‖|pairing t|‖ ≤ C₀ := hC₀ t ht
  have habsBound : |pairing t| ≤ C₀ := by
    simpa only [Real.norm_eq_abs, abs_abs] using hnorm
  exact habsBound.trans (le_max_left _ _)

/-- Local continuity of the gradient and the actuated control difference is a
componentwise sufficient condition for the local essential bound on their
pairing. -/
theorem future_inner_ae_bound_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (grad actuatedResidual : ℝ → E) (T b : ℝ) (hTb : T ≤ b)
    (hgrad : ContinuousOn grad (Set.Icc T b))
    (hactuated : ContinuousOn actuatedResidual (Set.Icc T b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
        t ∈ Set.Icc T b → |inner ℝ (grad t) (actuatedResidual t)| ≤ C := by
  exact future_pairing_ae_bound_of_continuousOn
    (fun t => inner ℝ (grad t) (actuatedResidual t)) T b hTb
    (hgrad.inner hactuated)

/-- Lebesgue-a.e. compatibility wrapper for the measure-generic identity. -/
theorem ae_closedLoop_descent_formula_of_ode
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0) :
    ∀ᵐ t,
      -(deriv (fun s => W (s, x s)) t) =
        -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := by
  exact ae_closedLoop_descent_formula_of_ode_under_measure
    W x dW gradW drift u0 utr actuator MeasureTheory.volume
    (Filter.Eventually.of_forall hW) hmodel

/-- Condition 27-A's absolutely continuous finite-dimensional trajectory and
a.e. control-affine ODE give the derivative premise used in the chain-rule
attribution theorem. The remaining assumptions are the state-gradient
representation and the reference-loop cancellation (27.A2), both a.e. -/
theorem ae_closedLoop_descent_formula_of_ac_ode
    {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × EuclideanSpace ℝ ι → ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ))
    (gradW drift : ℝ → EuclideanSpace ℝ ι)
    (u0 utr : ℝ → U)
    (actuator : ℝ → U →L[ℝ] (EuclideanSpace ℝ ι))
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval x a b)
    (hODE : ∀ᵐ t,
      deriv x t = drift t + actuator t (u0 t))
    (hstateGradient : ∀ᵐ t, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0) :
    ∀ᵐ t,
      -(deriv (fun s => W (s, x s)) t) =
        -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := by
  have hstate := ae_hasDerivAt_pi_of_ac_and_ode x
    (fun t => drift t + actuator t (u0 t)) hac hODE
  have hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0 := by
    filter_upwards [hstate, hstateGradient, hReference]
      with t hstate hgradient hreference
    exact ⟨hstate, hgradient, hreference⟩
  exact ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel

/-- Almost everywhere, the actuator contribution vanishes on a forward
invariant zero-residual target.  The statement includes the target-entry
instant in the pointwise Dini argument; the a.e. conclusion then connects it
to the ordinary chain rule. -/
theorem ae_actuator_contribution_zero_on_invariant_target
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (htarget : ∀ᵐ t, x t ∈ N t) :
    ∀ᵐ t, inner ℝ (gradW t) (actuator t (u0 t - utr t)) = 0 := by
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv
    (fun s => W (s, x s)) hLocallyLipschitz
  have hformula := ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel
  filter_upwards [htarget, hDiniEq, hformula] with t htarget hDini hformula
  have hDiniZero := upperRightDiniDerivative_zero_on_invariant_target
    N W x hforward hWzero t htarget
  rw [hDini] at hDiniZero
  nlinarith

/-- Equation (27.9), first conclusion: after a trajectory enters the
forward-invariant zero-residual target, its residual descent rate is zero at
every later time, including the entry time. -/
theorem residualDescentRate_zero_after_target_entry
    {E : Type*} (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (T t : ℝ) (hTt : T ≤ t) (hTtarget : x T ∈ N T) :
    -upperRightDiniDerivative (fun s => W (s, x s)) t = 0 := by
  have htarget := hforward T t hTt hTtarget
  rw [upperRightDiniDerivative_zero_on_invariant_target
    N W x hforward hWzero t htarget]
  simp

/-- Equation (27.9), second conclusion: on the forward ray after target entry,
the actuator's residual contribution vanishes almost everywhere. -/
theorem ae_actuator_contribution_zero_after_target_entry
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (T : ℝ) (hTtarget : x T ∈ N T) :
    ∀ᵐ t, T ≤ t →
      inner ℝ (gradW t) (actuator t (u0 t - utr t)) = 0 := by
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv
    (fun s => W (s, x s)) hLocallyLipschitz
  have hformula := ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel
  filter_upwards [hDiniEq, hformula] with t hDini hformula ht
  have htarget := hforward T t ht hTtarget
  have hDiniZero := upperRightDiniDerivative_zero_on_invariant_target
    N W x hforward hWzero t htarget
  rw [hDini] at hDiniZero
  nlinarith

/-- Future-measure version of the actuator quiescence implication. It needs
regularity and the 27-A chain-rule data only on the ray beginning at entry. -/
theorem ae_actuator_contribution_zero_after_target_entry_on_future
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (T : ℝ)
    (hW : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => W (s, x s))) (hTtarget : x T ∈ N T) :
    ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      inner ℝ (gradW t) (actuator t (u0 t - utr t)) = 0 := by
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv_on_future
    (fun s => W (s, x s)) T hLocallyLipschitz
  have hformula := ae_closedLoop_descent_formula_of_ode_under_measure
    W x dW gradW drift u0 utr actuator
    (_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T) hW hmodel
  have htargetAE : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      T ≤ t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact ht
  filter_upwards [hDiniEq, hformula, htargetAE] with t hDini hformula ht
  have htarget := hforward T t ht hTtarget
  have hDiniZero := upperRightDiniDerivative_zero_on_invariant_target
    N W x hforward hWzero t htarget
  rw [hDini] at hDiniZero
  have hnegativeDeriv : -(deriv (fun s => W (s, x s)) t) = 0 := by
    rw [hDiniZero]
    simp
  rw [hformula] at hnegativeDeriv
  linarith

/-- Equation (27.7) almost everywhere: condition 26-A supplies positive
residual and strict decay a.e., while condition 27-A's ODE and reference-loop
assumptions give the actuator attribution identity a.e. -/
theorem ae_ignorance_implies_model_relative_action
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (decayRate : ℝ) (hdecayRate : 0 < decayRate)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hresidualPositive : ∀ᵐ t,
      0 < W (t, x t))
    (hdecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤ -(deriv (fun s => W (s, x s)) t)) :
    ∀ᵐ t,
      0 < -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) ∧
      u0 t - utr t ≠ 0 ∧ actuator t (u0 t - utr t) ≠ 0 := by
  have hformula := ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel
  filter_upwards [hformula, hresidualPositive, hdecay] with t htFormula htResidual htDecay
  have hpositive :
      0 < -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := by
    rw [← htFormula]
    exact lt_of_lt_of_le (mul_pos hdecayRate htResidual) htDecay
  refine ⟨hpositive, ?_, ?_⟩
  · intro hzero
    rw [hzero, map_zero, inner_zero_right] at hpositive
    linarith
  · intro hzero
    rw [hzero, inner_zero_right] at hpositive
    linarith

/-- The a.e. form of (27.7) with the paper's upper right Dini derivative in
the decay premise.  Local Lipschitz regularity of the residual path supplies
the a.e. equality between that Dini derivative and the ordinary derivative. -/
theorem ae_ignorance_implies_model_relative_action_of_dini
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (decayRate : ℝ) (hdecayRate : 0 < decayRate)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hresidualPositive : ∀ᵐ t,
      0 < W (t, x t))
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t) :
    ∀ᵐ t,
      0 < -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) ∧
      u0 t - utr t ≠ 0 ∧ actuator t (u0 t - utr t) ≠ 0 := by
  have hDiniEq : ∀ᵐ t,
      upperRightDiniDerivative (fun s => W (s, x s)) t =
        deriv (fun s => W (s, x s)) t :=
    ae_upperRightDiniDerivative_eq_deriv
      (fun s => W (s, x s)) hLocallyLipschitz
  have hderivDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤ -(deriv (fun s => W (s, x s)) t) := by
    filter_upwards [hDiniDecay, hDiniEq] with t hDini hEq
    rw [hEq] at hDini
    exact hDini
  exact ae_ignorance_implies_model_relative_action W x dW gradW drift
    u0 utr actuator decayRate hdecayRate hW hmodel hresidualPositive hderivDecay

/-- Equation (27.7) directly from condition 27-A's absolutely continuous
trajectory and a.e. ODE, for the paper's finite-dimensional Euclidean state
space. This removes the separate a.e. `HasDerivAt` premise from the residual
action conclusion. -/
theorem ae_ignorance_implies_model_relative_action_of_ac_ode
    {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (W : ℝ × EuclideanSpace ℝ ι → ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ))
    (gradW drift : ℝ → EuclideanSpace ℝ ι)
    (u0 utr : ℝ → U)
    (actuator : ℝ → U →L[ℝ] (EuclideanSpace ℝ ι))
    (decayRate : ℝ) (hdecayRate : 0 < decayRate)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval x a b)
    (hODE : ∀ᵐ t,
      deriv x t = drift t + actuator t (u0 t))
    (hstateGradient : ∀ᵐ t, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hresidualPositive : ∀ᵐ t, 0 < W (t, x t))
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t) :
    ∀ᵐ t,
      0 < -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) ∧
      u0 t - utr t ≠ 0 ∧ actuator t (u0 t - utr t) ≠ 0 := by
  have hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0 := by
    have hstate := ae_hasDerivAt_pi_of_ac_and_ode x
      (fun t => drift t + actuator t (u0 t)) hac hODE
    filter_upwards [hstate, hstateGradient, hReference]
      with t hstate hgradient hreference
    exact ⟨hstate, hgradient, hreference⟩
  have hDiniEq : ∀ᵐ t,
      upperRightDiniDerivative (fun s => W (s, x s)) t =
        deriv (fun s => W (s, x s)) t :=
    ae_upperRightDiniDerivative_eq_deriv
      (fun s => W (s, x s)) hLocallyLipschitz
  have hderivDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤ -(deriv (fun s => W (s, x s)) t) := by
    filter_upwards [hDiniDecay, hDiniEq] with t hDini hEq
    rw [hEq] at hDini
    exact hDini
  exact ae_ignorance_implies_model_relative_action W x dW gradW drift
    u0 utr actuator decayRate hdecayRate hW hmodel hresidualPositive hderivDecay

/-- Almost-everywhere norm estimate (27.8) from Dini descent and the
adjoint-gradient bound.  The adjoint pairing identity is supplied by the
already proved a.e. chain rule, and the Dini-to-ordinary derivative step is
supplied by local Lipschitz regularity. -/
theorem ae_control_difference_norm_lower_bound_of_dini
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (decayRate L : ℝ) (hL : 0 < L)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (hgradientBound : ∀ᵐ t,
      ‖(actuator t).adjoint (gradW t)‖ ≤ L) :
    ∀ᵐ t, decayRate * W (t, x t) / L ≤ ‖u0 t - utr t‖ := by
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv
    (fun s => W (s, x s)) hLocallyLipschitz
  have hderivDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤ -(deriv (fun s => W (s, x s)) t) := by
    filter_upwards [hDiniDecay, hDiniEq] with t hDini hEq
    rw [hEq] at hDini
    exact hDini
  have hformula := ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel
  filter_upwards [hderivDecay, hformula, hgradientBound]
    with t hdecay hidentity hbound
  have hcontrol : -(deriv (fun s => W (s, x s)) t) =
      -(inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hidentity
  have hdescentBound : -(deriv (fun s => W (s, x s)) t) ≤
      L * ‖u0 t - utr t‖ := by
    rw [hcontrol]
    calc
      -inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)
          ≤ |-inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)| := le_abs_self _
      _ = |inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)| := by rw [abs_neg]
      _ ≤ ‖(actuator t).adjoint (gradW t)‖ * ‖u0 t - utr t‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ L * ‖u0 t - utr t‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hmul : decayRate * W (t, x t) ≤ L * ‖u0 t - utr t‖ :=
    hdecay.trans hdescentBound
  exact (div_le_iff₀ hL).2 (by nlinarith)

/-- Equation (27.8)'s residual-based control bound from condition 27-A's
absolutely continuous finite-dimensional trajectory and a.e. control-affine
ODE. The adjoint-gradient bound is the stated constant-`L` premise. -/
theorem ae_control_difference_norm_lower_bound_of_dini_of_ac_ode
    {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (W : ℝ × EuclideanSpace ℝ ι → ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ))
    (gradW drift : ℝ → EuclideanSpace ℝ ι)
    (u0 utr : ℝ → U)
    (actuator : ℝ → U →L[ℝ] (EuclideanSpace ℝ ι))
    (decayRate L : ℝ) (hL : 0 < L)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval x a b)
    (hODE : ∀ᵐ t,
      deriv x t = drift t + actuator t (u0 t))
    (hstateGradient : ∀ᵐ t, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (hgradientBound : ∀ᵐ t,
      ‖(actuator t).adjoint (gradW t)‖ ≤ L) :
    ∀ᵐ t, decayRate * W (t, x t) / L ≤ ‖u0 t - utr t‖ := by
  have hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0 := by
    have hstate := ae_hasDerivAt_pi_of_ac_and_ode x
      (fun t => drift t + actuator t (u0 t)) hac hODE
    filter_upwards [hstate, hstateGradient, hReference]
      with t hstate hgradient hreference
    exact ⟨hstate, hgradient, hreference⟩
  exact ae_control_difference_norm_lower_bound_of_dini W x dW gradW drift
    u0 utr actuator decayRate L hL hW hmodel hDiniDecay
    hLocallyLipschitz hgradientBound

/-- Equation (27.8) with the distance term from (26.A): the norm estimate is
obtained a.e. from the absolutely continuous ODE trajectory, and is strictly
positive whenever the state is outside the closed zero-residual target. -/
theorem ae_control_difference_distance_lower_bound_of_dini_of_ac_ode
    {ι U : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (N : ℝ → Set (EuclideanSpace ℝ ι))
    (hNclosed : ∀ t, IsClosed (N t))
    (hNnonempty : ∀ t, (N t).Nonempty)
    (W : ℝ × EuclideanSpace ℝ ι → ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (dW : ℝ → (ℝ × EuclideanSpace ℝ ι →L[ℝ] ℝ))
    (gradW drift : ℝ → EuclideanSpace ℝ ι)
    (u0 utr : ℝ → U)
    (actuator : ℝ → U →L[ℝ] (EuclideanSpace ℝ ι))
    (c₁ decayRate L : ℝ) (hc₁ : 0 < c₁)
    (hdecayRate : 0 < decayRate) (hL : 0 < L)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hac : ∀ a b, AbsolutelyContinuousOnInterval x a b)
    (hODE : ∀ᵐ t,
      deriv x t = drift t + actuator t (u0 t))
    (hstateGradient : ∀ᵐ t, ∀ z,
      dW t (0, z) = inner ℝ (gradW t) z)
    (hReference : ∀ᵐ t,
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hWlower : ∀ᵐ t,
      c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W (t, x t))
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s)))
    (hgradientBound : ∀ᵐ t,
      ‖(actuator t).adjoint (gradW t)‖ ≤ L) :
    ∀ᵐ t,
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 / L ≤
        ‖u0 t - utr t‖ ∧
      (x t ∉ N t → 0 < ‖u0 t - utr t‖) := by
  have hcontrol := ae_control_difference_norm_lower_bound_of_dini_of_ac_ode
    W x dW gradW drift u0 utr actuator decayRate L hL hW hac hODE
    hstateGradient hReference hDiniDecay hLocallyLipschitz hgradientBound
  filter_upwards [hcontrol, hWlower] with t hcontrol hLower
  have hmul : decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤
      decayRate * W (t, x t) := by
    nlinarith [mul_le_mul_of_nonneg_left hLower (le_of_lt hdecayRate)]
  have hdistance :
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 / L ≤
        ‖u0 t - utr t‖ := by
    have hscaled : decayRate * W (t, x t) ≤ ‖u0 t - utr t‖ * L :=
      (div_le_iff₀ hL).1 hcontrol
    exact (div_le_iff₀ hL).2 (hmul.trans hscaled)
  refine ⟨hdistance, ?_⟩
  intro houtside
  have hdist : 0 < Metric.infDist (x t) (N t) :=
    (hNclosed t).notMem_iff_infDist_pos (hNnonempty t) |>.mp houtside
  have hleft : 0 <
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 / L := by
    apply div_pos
    · exact mul_pos (mul_pos hdecayRate hc₁) (sq_pos_of_pos hdist)
    · exact hL
  exact lt_of_lt_of_le hleft hdistance

/-- The reference-loop cancellation and the chain-rule expression for the
closed-loop derivative imply the actuator attribution identity.  State and
input may be different real inner product spaces. -/
theorem actuator_identity_from_reference_cancellation
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (gradW drift : E) (u0 utr : U) (actuator : U →L[ℝ] E)
    (partialW descentRate : ℝ)
    (hReference : partialW + inner ℝ gradW (drift + actuator utr) = 0)
    (hClosedLoop : descentRate =
      -(partialW + inner ℝ gradW (drift + actuator u0))) :
    descentRate = -(inner ℝ gradW (actuator (u0 - utr))) := by
  have hsplit :
      inner ℝ gradW (drift + actuator u0) -
          inner ℝ gradW (drift + actuator utr) =
        inner ℝ gradW (actuator (u0 - utr)) := by
    simp only [inner_add_right, inner_sub_right, map_sub]
    ring
  rw [hClosedLoop]
  nlinarith [hReference, hsplit]

/-- After entering a forward-invariant zero-residual target, the residual
path vanishes in the future.  At every later time where the control-affine
trajectory is differentiable, the chain rule and reference-loop cancellation
therefore force the actuator's residual contribution to be zero.  This is
the pointwise-after-entry form underlying the a.e. conclusion in (27.9). -/
theorem actuator_contribution_zero_after_target_entry
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : ℝ → Set E) (W : ℝ × E → ℝ) (x : ℝ → E)
    (T t : ℝ) (hTt : T < t)
    (hinvariant : ∀ s, T ≤ s → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (dW : ℝ × E →L[ℝ] ℝ) (gradW drift : E) (u0 utr : U)
    (actuator : U →L[ℝ] E)
    (hW : HasFDerivAt W dW (t, x t))
    (hstate : HasDerivAt x (drift + actuator u0) t)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z)
    (hReference : dW (1, 0) + inner ℝ gradW (drift + actuator utr) = 0) :
    inner ℝ gradW (actuator (u0 - utr)) = 0 := by
  have hcurve := hasDerivAt_joint_time_state x t
    (drift + actuator u0) hstate
  have hpath := hasDerivAt_timeState_composition W dW x t
    (1, drift + actuator u0) hW hcurve
  have hpathZero : ∀ s, T ≤ s → W (s, x s) = 0 := by
    intro s hs
    exact hWzero s (x s) (hinvariant s hs)
  have hdWzero := residual_derivative_zero_after_target_entry
    (fun s => W (s, x s)) T t (dW (1, drift + actuator u0)) hTt
    hpathZero hpath
  have hdescent : (0 : ℝ) = -dW (1, drift + actuator u0) := by
    nlinarith
  have hidentity := closedLoop_descent_formula_of_chain_rule W dW x t
    gradW drift u0 utr actuator (0 : ℝ) hW hcurve hstateGradient
    hdescent hReference
  linarith

/-- Algebraic consequence of the actuator attribution part of condition 27-A.

The identity `descentRate = -⟪∇W, G η⟫` is the chain-rule conclusion after
the reference closed loop has zero Lyapunov derivative. -/
theorem positive_actuator_contribution
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (gradW : E) (controlDelta : U) (actuator : U →L[ℝ] E)
    (decayRate W descentRate : ℝ)
    (hdecayRate : 0 < decayRate) (hW : 0 < W)
    (hdecay : decayRate * W ≤ descentRate)
    (hactuator : descentRate = -(inner ℝ gradW (actuator controlDelta))) :
    0 < -(inner ℝ gradW (actuator controlDelta)) ∧
      controlDelta ≠ 0 ∧ actuator controlDelta ≠ 0 := by
  have hpositive : 0 < descentRate := by
    exact lt_of_lt_of_le (mul_pos hdecayRate hW) hdecay
  have hcontribution : 0 < -(inner ℝ gradW (actuator controlDelta)) := by
    rw [← hactuator]
    exact hpositive
  refine ⟨hcontribution, ?_, ?_⟩
  · intro hη
    rw [hη, map_zero, inner_zero_right] at hcontribution
    linarith
  · intro hGη
    rw [hGη, inner_zero_right] at hcontribution
    linarith

/-- Pointwise equivalence in (27.10) between operational ignorance and a
positive actuator contribution.  The reference-loop identity supplies the
attribution, while the zero-descent property on the invariant target supplies
the reverse direction. -/
theorem outside_target_iff_positive_actuator_contribution
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : Set E) (hNclosed : IsClosed N) (hNnonempty : N.Nonempty)
    (W : E → ℝ) (x : E)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (descentRate : ℝ) (hWlower : c₁ * (Metric.infDist x N) ^ 2 ≤ W x)
    (hdecay : decayRate * W x ≤ descentRate)
    (hzero : x ∈ N → descentRate = 0)
    (gradW : E) (controlDelta : U) (actuator : U →L[ℝ] E)
    (hactuator : descentRate = -(inner ℝ gradW (actuator controlDelta))) :
    x ∉ N ↔ 0 < -(inner ℝ gradW (actuator controlDelta)) := by
  constructor
  · intro hx
    rw [← hactuator]
    exact (residual_descent_of_outside_closed_target N hNclosed hNnonempty
      W x c₁ decayRate hc₁ hdecayRate descentRate hWlower hdecay hx).2
  · intro hpositive hx
    have hz := hzero hx
    rw [← hactuator, hz] at hpositive
    exact (lt_irrefl 0 hpositive)

/-- The second equivalence in (27.10), for a time-varying target and almost
every time. Strict residual decay gives a positive actuator contribution
outside the target; forward invariance and zero residual give the converse. -/
theorem ae_outside_target_iff_positive_actuator_contribution_of_dini
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : ℝ → Set E) (hNclosed : ∀ t, IsClosed (N t))
    (hNnonempty : ∀ t, (N t).Nonempty)
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (hWlower : ∀ᵐ t,
      c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W (t, x t))
    (hDiniDecay : ∀ᵐ t,
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t)
    (hforward : ∀ T s, T ≤ s → x T ∈ N T → x s ∈ N s)
    (hWzero : ∀ s y, y ∈ N s → W (s, y) = 0)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (hW : ∀ t, HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hLocallyLipschitz : LocallyLipschitz (fun s => W (s, x s))) :
    ∀ᵐ t, x t ∉ N t ↔
      sankhara27Contribution (gradW t) (actuator t) (u0 t - utr t) := by
  change ∀ᵐ t, x t ∉ N t ↔
    0 < -(inner ℝ (gradW t) (actuator t (u0 t - utr t)))
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv
    (fun s => W (s, x s)) hLocallyLipschitz
  have hformula := ae_closedLoop_descent_formula_of_ode W x dW gradW drift
    u0 utr actuator hW hmodel
  filter_upwards [hWlower, hDiniDecay, hDiniEq, hformula]
    with t hLower hDecay hDini hformula
  constructor
  · intro hx
    have hdist : 0 < Metric.infDist (x t) (N t) :=
      (hNclosed t).notMem_iff_infDist_pos (hNnonempty t) |>.mp hx
    have hWpos : 0 < W (t, x t) := by
      have hsq : 0 < (Metric.infDist (x t) (N t)) ^ 2 := sq_pos_of_pos hdist
      nlinarith
    have hderivDecay : decayRate * W (t, x t) ≤
        -(deriv (fun s => W (s, x s)) t) := by
      rw [hDini] at hDecay
      exact hDecay
    calc
      0 < decayRate * W (t, x t) := mul_pos hdecayRate hWpos
      _ ≤ -(deriv (fun s => W (s, x s)) t) := hderivDecay
      _ = -(inner ℝ (gradW t) (actuator t (u0 t - utr t))) := hformula
  · intro hpositive hx
    have htarget := hforward t t le_rfl hx
    have hDiniZero := upperRightDiniDerivative_zero_on_invariant_target
      N W x hforward hWzero t htarget
    rw [hDini] at hDiniZero
    have hpairing : inner ℝ (gradW t) (actuator t (u0 t - utr t)) = 0 := by
      nlinarith
    rw [hpairing] at hpositive
    norm_num at hpositive

/-- Combined form of the two-stage implication in equation (27.7): strict
Lyapunov descent plus a zero-variation reference loop forces nonzero actuator
contribution and nonzero input/state action. -/
theorem ignorance_implies_model_relative_action
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (gradW drift : E) (u0 utr : U) (actuator : U →L[ℝ] E)
    (partialW decayRate W descentRate : ℝ)
    (hdecayRate : 0 < decayRate) (hW : 0 < W)
    (hdecay : decayRate * W ≤ descentRate)
    (hReference : partialW + inner ℝ gradW (drift + actuator utr) = 0)
    (hClosedLoop : descentRate =
      -(partialW + inner ℝ gradW (drift + actuator u0))) :
    0 < -(inner ℝ gradW (actuator (u0 - utr))) ∧
      u0 - utr ≠ 0 ∧ actuator (u0 - utr) ≠ 0 := by
  have hIdentity := actuator_identity_from_reference_cancellation
    gradW drift u0 utr actuator partialW descentRate hReference hClosedLoop
  exact positive_actuator_contribution gradW (u0 - utr) actuator
    decayRate W descentRate hdecayRate hW hdecay hIdentity

/-- End-to-end actuator attribution from a differentiable control-affine
trajectory.  Given strict Lyapunov decay and a reference loop with zero
Lyapunov variation, the chain rule derives the input-difference identity and
then proves that both the input difference and its effective state action are
nonzero.  This is conditional on the displayed trajectory, derivative-split,
and Lyapunov-decay hypotheses. -/
theorem ignorance_implies_action_of_control_affine_chain_rule
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (Wfun : ℝ × E → ℝ) (dW : ℝ × E →L[ℝ] ℝ)
    (x : ℝ → E) (t : ℝ) (gradW drift : E) (u0 utr : U)
    (actuator : U →L[ℝ] E) (decayRate residual descentRate : ℝ)
    (hdecayRate : 0 < decayRate) (hresidual : 0 < residual)
    (hdecay : decayRate * residual ≤ descentRate)
    (hW : HasFDerivAt Wfun dW (t, x t))
    (hstate : HasDerivAt x (drift + actuator u0) t)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z)
    (hdescent : descentRate = -dW (1, drift + actuator u0))
    (hReference : dW (1, 0) + inner ℝ gradW (drift + actuator utr) = 0) :
    0 < -(inner ℝ gradW (actuator (u0 - utr))) ∧
      u0 - utr ≠ 0 ∧ actuator (u0 - utr) ≠ 0 := by
  have hIdentity := closedLoop_descent_formula_of_chain_rule Wfun dW x t
    gradW drift u0 utr actuator descentRate hW
    (hasDerivAt_joint_time_state x t (drift + actuator u0) hstate)
    hstateGradient hdescent hReference
  exact positive_actuator_contribution gradW (u0 - utr) actuator
    decayRate residual descentRate hdecayRate hresidual hdecay hIdentity

/-- Combined implication (27.6)--(27.7) at a state outside the closed
zero-residual target.  The Lyapunov lower bound and decay inequality give the
quantitative distance descent and its strict positivity; the control-affine
chain rule and reference-loop cancellation attribute that descent to a
nonzero actuator input difference and a nonzero effective state action. -/
theorem outside_target_implies_quantitative_descent_and_action
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (N : Set E) (hNclosed : IsClosed N) (hNnonempty : N.Nonempty)
    (x₀ : E)
    (c₁ decayRate : ℝ) (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (residual descentRate : ℝ)
    (hWlower : c₁ * (Metric.infDist x₀ N) ^ 2 ≤ residual)
    (hdecay : decayRate * residual ≤ descentRate)
    (hx₀ : x₀ ∉ N)
    (Wfun : ℝ × E → ℝ) (dW : ℝ × E →L[ℝ] ℝ)
    (x : ℝ → E) (t : ℝ) (gradW drift : E) (u0 utr : U)
    (actuator : U →L[ℝ] E)
    (hResidual : residual = Wfun (t, x t))
    (hW : HasFDerivAt Wfun dW (t, x t))
    (hstate : HasDerivAt x (drift + actuator u0) t)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z)
    (hdescent : descentRate = -dW (1, drift + actuator u0))
    (hReference : dW (1, 0) + inner ℝ gradW (drift + actuator utr) = 0) :
    decayRate * c₁ * (Metric.infDist x₀ N) ^ 2 ≤ descentRate ∧
      0 < -(inner ℝ gradW (actuator (u0 - utr))) ∧
      u0 - utr ≠ 0 ∧ actuator (u0 - utr) ≠ 0 := by
  subst residual
  have hResidualDecay := residual_descent_of_outside_closed_target
    N hNclosed hNnonempty (fun _ : E => Wfun (t, x t)) x₀
    c₁ decayRate hc₁ hdecayRate
    descentRate hWlower hdecay hx₀
  have hdist : 0 < Metric.infDist x₀ N :=
    (hNclosed.notMem_iff_infDist_pos hNnonempty).mp hx₀
  have hresidual : 0 < Wfun (t, x t) := by
    apply lt_of_lt_of_le
    · exact mul_pos hc₁ (sq_pos_of_pos hdist)
    · exact hWlower
  have hResidualDescent := ignorance_implies_action_of_control_affine_chain_rule
    Wfun dW x t gradW drift u0 utr actuator decayRate (Wfun (t, x t)) descentRate
    hdecayRate hresidual hdecay hW hstate hstateGradient hdescent hReference
  exact ⟨hResidualDecay.1, hResidualDescent.1, hResidualDescent.2.1,
    hResidualDescent.2.2⟩

/-- Quantitative lower bound on the control difference, assuming the bound
`‖G† ∇W‖ ≤ L` from equation (27.8).  The adjoint pairing identity is stated
explicitly as a hypothesis so this lemma isolates the norm estimate. -/
theorem control_difference_norm_lower_bound
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (gradW : E) (controlDelta : U) (actuator : U →L[ℝ] E)
    (decayRate W descentRate L : ℝ)
    (hL : 0 < L)
    (hdecay : decayRate * W ≤ descentRate)
    (hcontrol : descentRate =
      -(inner ℝ (actuator.adjoint gradW) controlDelta))
    (hgradientBound : ‖actuator.adjoint gradW‖ ≤ L) :
    decayRate * W / L ≤ ‖controlDelta‖ := by
  have hdescentBound : descentRate ≤ L * ‖controlDelta‖ := by
    rw [hcontrol]
    calc
      -inner ℝ (actuator.adjoint gradW) controlDelta
          ≤ |-inner ℝ (actuator.adjoint gradW) controlDelta| := le_abs_self _
      _ = |inner ℝ (actuator.adjoint gradW) controlDelta| := by rw [abs_neg]
      _ ≤ ‖actuator.adjoint gradW‖ * ‖controlDelta‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ L * ‖controlDelta‖ :=
        mul_le_mul_of_nonneg_right hgradientBound (norm_nonneg _)
  have hmul : decayRate * W ≤ L * ‖controlDelta‖ := hdecay.trans hdescentBound
  exact (div_le_iff₀ hL).2 (by nlinarith)

/-- Equation (27.8)'s norm estimate from the actuator attribution identity.
The adjoint pairing needed by Cauchy--Schwarz is derived from Mathlib's
continuous-linear-map adjoint identity instead of being an additional
hypothesis. -/
theorem control_difference_norm_lower_bound_of_actuator_identity
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (gradW : E) (controlDelta : U) (actuator : U →L[ℝ] E)
    (decayRate W descentRate L : ℝ)
    (hL : 0 < L)
    (hdecay : decayRate * W ≤ descentRate)
    (hactuator : descentRate =
      -(inner ℝ gradW (actuator controlDelta)))
    (hgradientBound : ‖actuator.adjoint gradW‖ ≤ L) :
    decayRate * W / L ≤ ‖controlDelta‖ := by
  apply control_difference_norm_lower_bound gradW controlDelta actuator
    decayRate W descentRate L hL hdecay ?_ hgradientBound
  rw [actuator.adjoint_inner_left]
  exact hactuator

/-- Combined quantitative conclusions (27.6)--(27.8) for a state outside the
closed zero-residual target.  The final control-size estimate uses the
operator-norm bound on the adjoint actuator-gradient pairing. -/
theorem outside_target_implies_descent_action_and_control_bound
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (N : Set E) (hNclosed : IsClosed N) (hNnonempty : N.Nonempty)
    (x₀ : E) (c₁ decayRate : ℝ)
    (hc₁ : 0 < c₁) (hdecayRate : 0 < decayRate)
    (residual descentRate : ℝ)
    (hWlower : c₁ * (Metric.infDist x₀ N) ^ 2 ≤ residual)
    (hdecay : decayRate * residual ≤ descentRate)
    (hx₀ : x₀ ∉ N)
    (Wfun : ℝ × E → ℝ) (dW : ℝ × E →L[ℝ] ℝ)
    (x : ℝ → E) (t : ℝ) (gradW drift : E) (u0 utr : U)
    (actuator : U →L[ℝ] E) (L : ℝ) (hL : 0 < L)
    (hgradientBound : ‖actuator.adjoint gradW‖ ≤ L)
    (hResidual : residual = Wfun (t, x t))
    (hW : HasFDerivAt Wfun dW (t, x t))
    (hstate : HasDerivAt x (drift + actuator u0) t)
    (hstateGradient : ∀ z, dW (0, z) = inner ℝ gradW z)
    (hdescent : descentRate = -dW (1, drift + actuator u0))
    (hReference : dW (1, 0) + inner ℝ gradW (drift + actuator utr) = 0) :
    decayRate * c₁ * (Metric.infDist x₀ N) ^ 2 ≤ descentRate ∧
      0 < -(inner ℝ gradW (actuator (u0 - utr))) ∧
      u0 - utr ≠ 0 ∧ actuator (u0 - utr) ≠ 0 ∧
      (decayRate * c₁ * (Metric.infDist x₀ N) ^ 2) / L ≤ ‖u0 - utr‖ := by
  have hbase := outside_target_implies_quantitative_descent_and_action
    N hNclosed hNnonempty x₀ c₁ decayRate hc₁ hdecayRate residual descentRate
    hWlower hdecay hx₀ Wfun dW x t gradW drift u0 utr actuator hResidual
    hW hstate hstateGradient hdescent hReference
  have hdecayW : decayRate * Wfun (t, x t) ≤ descentRate := by
    rw [← hResidual]
    exact hdecay
  have hcontrol := control_difference_norm_lower_bound_of_actuator_identity
    gradW (u0 - utr) actuator decayRate (Wfun (t, x t)) descentRate L hL hdecayW
    (closedLoop_descent_formula_of_chain_rule Wfun dW x t gradW drift
      u0 utr actuator descentRate hW
      (hasDerivAt_joint_time_state x t (drift + actuator u0) hstate)
      hstateGradient hdescent hReference)
    hgradientBound
  have hnum :
      decayRate * c₁ * (Metric.infDist x₀ N) ^ 2 ≤ decayRate * residual := by
    calc
      decayRate * c₁ * (Metric.infDist x₀ N) ^ 2 =
          decayRate * (c₁ * (Metric.infDist x₀ N) ^ 2) := by ring
      _ ≤ decayRate * residual :=
        mul_le_mul_of_nonneg_left hWlower (le_of_lt hdecayRate)
  have hnumW :
      decayRate * c₁ * (Metric.infDist x₀ N) ^ 2 ≤
        decayRate * Wfun (t, x t) := by
    rw [← hResidual]
    exact hnum
  have hdiv :
      (decayRate * c₁ * (Metric.infDist x₀ N) ^ 2) / L ≤
        (decayRate * Wfun (t, x t)) / L :=
    (div_le_div_iff₀ hL hL).2
      (mul_le_mul_of_nonneg_right hnumW hL.le)
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2,
    hdiv.trans hcontrol⟩

/-- Riesz representative of the state-coordinate derivative of `W`. -/
noncomputable def stateGradientFromFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (dW : ℝ × E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (dW.comp (ContinuousLinearMap.inr ℝ ℝ E))

/-- Canonical joint Fréchet derivative of a time-dependent potential along a
specified trajectory. -/
noncomputable def jointDerivativeOnPath
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : E → ℝ → ℝ) (x : ℝ → E) : ℝ → (ℝ × E →L[ℝ] ℝ) :=
  fun t => fderiv ℝ (fun p : ℝ × E => W p.2 p.1) (t, x t)

/-- Condition 27-A's local `C¹` assumption on the future trajectory supplies
the Fréchet-derivative field required by the chain-rule adapters. -/
theorem jointDerivativeOnPath_hasFDerivAt_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (W : E → ℝ → ℝ) (x : ℝ → E)
    (hC1 : ∀ t, T ≤ t →
      ContDiffAt ℝ 1 (fun p : ℝ × E => W p.2 p.1) (t, x t)) :
    ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × E => W p.2 p.1)
        (jointDerivativeOnPath W x t) (t, x t) := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
  change T ≤ t at ht
  change HasFDerivAt (fun p : ℝ × E => W p.2 p.1)
    (fderiv ℝ (fun p : ℝ × E => W p.2 p.1) (t, x t)) (t, x t)
  exact (hC1 t ht).differentiableAt_one.hasFDerivAt

/-- The Riesz representative of the state-coordinate derivative supplies
condition 27-A's state-gradient identity directly from the joint Fréchet
derivative. -/
theorem stateGradientFromFDeriv_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (dW : ℝ × E →L[ℝ] ℝ) (z : E) :
    dW (0, z) = inner ℝ (stateGradientFromFDeriv dW) z := by
  change dW (0, z) = inner ℝ
    ((InnerProductSpace.toDual ℝ E).symm
      (dW.comp (ContinuousLinearMap.inr ℝ ℝ E))) z
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem adjoint_norm_bound_implies_inner_action_bound
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (G : U →L[ℝ] E) (g : E) (L : ℝ)
    (hbound : ‖G.adjoint g‖ ≤ L) (v : U) :
    |inner ℝ g (G v)| ≤ L * ‖v‖ := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  calc
    |inner ℝ (G.adjoint g) v| ≤ ‖G.adjoint g‖ * ‖v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ L * ‖v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- Almost-everywhere form of the condition-27-A adjoint estimate. The
operator bound on `G†∇W` supplies the directionwise pairing bound used by the
quantitative input-difference conclusion (27.8). -/
theorem ae_inner_action_bound_of_adjoint_norm_bound
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (μ : MeasureTheory.Measure ℝ) (gradW : ℝ → E)
    (actuator : ℝ → U →L[ℝ] E) (L : ℝ)
    (hbound : ∀ᵐ t ∂μ, ‖(actuator t).adjoint (gradW t)‖ ≤ L) :
    ∀ᵐ t ∂μ, ∀ v, |inner ℝ (gradW t) (actuator t v)| ≤ L * ‖v‖ := by
  filter_upwards [hbound] with t ht
  intro v
  exact adjoint_norm_bound_implies_inner_action_bound
    (actuator t) (gradW t) L ht v

/-- Conditioned form matching equation (27.8): the adjoint estimate is only
required at times satisfying the supplied ignorance predicate. -/
theorem ae_inner_action_bound_of_adjoint_norm_bound_on
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (μ : MeasureTheory.Measure ℝ) (condition : ℝ → Prop)
    (gradW : ℝ → E) (actuator : ℝ → U →L[ℝ] E) (L : ℝ)
    (hbound : ∀ᵐ t ∂μ, condition t →
      ‖(actuator t).adjoint (gradW t)‖ ≤ L) :
    ∀ᵐ t ∂μ, condition t → ∀ v,
      |inner ℝ (gradW t) (actuator t v)| ≤ L * ‖v‖ := by
  filter_upwards [hbound] with t ht
  intro hcondition v
  exact adjoint_norm_bound_implies_inner_action_bound
    (actuator t) (gradW t) L (ht hcondition) v

/-- Future-ray form of the quantitative control bound (27.8).
The operator bound is stated as `|⟪∇W,Gv⟫| ≤ L‖v‖` and is required only
outside the zero-residual target, matching the operational-ignorance clause. -/
theorem ae_control_difference_distance_lower_bound_of_dini_on_future
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [CompleteSpace U]
    (T : ℝ) (N : ℝ → Set E)
    (hNclosed : ∀ t, T ≤ t → IsClosed (N t))
    (hNnonempty : ∀ t, T ≤ t → (N t).Nonempty)
    (W : ℝ × E → ℝ) (x : ℝ → E)
    (dW : ℝ → (ℝ × E →L[ℝ] ℝ)) (gradW drift : ℝ → E)
    (u0 utr : ℝ → U) (actuator : ℝ → U →L[ℝ] E)
    (c₁ decayRate L : ℝ) (hc₁ : 0 < c₁)
    (hdecayRate : 0 < decayRate) (hL : 0 < L)
    (hWlower : ∀ t, T ≤ t →
      c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W (t, x t))
    (hDiniDecay : ∀ t, T ≤ t →
      decayRate * W (t, x t) ≤
        -upperRightDiniDerivative (fun s => W (s, x s)) t)
    (hW : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasFDerivAt W (dW t) (t, x t))
    (hmodel : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (gradW t) z) ∧
      dW t (1, 0) + inner ℝ (gradW t)
        (drift t + actuator t (utr t)) = 0)
    (hLocallyLipschitz : LocallyLipschitzOn (Set.Ici T)
      (fun s => W (s, x s)))
    (hgradientBound : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      x t ∉ N t → ∀ v,
        |inner ℝ (gradW t) (actuator t v)| ≤ L * ‖v‖) :
    ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      x t ∉ N t →
        (decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2) / L ≤
          ‖u0 t - utr t‖ ∧
        0 < ‖u0 t - utr t‖ := by
  let q : ℝ → ℝ := fun s => W (s, x s)
  have htargetAE : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      T ≤ t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact ht
  have hDiniEq := ae_upperRightDiniDerivative_eq_deriv_on_future q T hLocallyLipschitz
  have hformula := ae_closedLoop_descent_formula_of_ode_under_measure
    W x dW gradW drift u0 utr actuator
    (_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T) hW hmodel
  have hWlowerAE : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤ W (t, x t) := by
    filter_upwards [htargetAE] with t ht
    exact hWlower t ht
  have hDiniDecayAE : ∀ᵐ t ∂_root_.Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      decayRate * W (t, x t) ≤ -upperRightDiniDerivative q t := by
    filter_upwards [htargetAE] with t ht
    simpa [q] using hDiniDecay t ht
  filter_upwards [htargetAE, hWlowerAE, hDiniDecayAE, hDiniEq, hformula,
    hgradientBound] with t ht hLower hDini hDiniEq_t hformula_t hbound
  intro houtside
  have hdist : 0 < Metric.infDist (x t) (N t) :=
    (hNclosed t ht).notMem_iff_infDist_pos (hNnonempty t ht) |>.mp houtside
  have hWpos : 0 < W (t, x t) := by
    have hsq : 0 < (Metric.infDist (x t) (N t)) ^ 2 := sq_pos_of_pos hdist
    nlinarith [hLower]
  have hderivDecay : decayRate * W (t, x t) ≤ -(deriv q t) := by
    rw [hDiniEq_t] at hDini
    exact hDini
  have hidentity : -(deriv q t) =
      -(inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hformula_t
  have hboundDescent : -(deriv q t) ≤ L * ‖u0 t - utr t‖ := by
    rw [hidentity]
    calc
      -inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)
          ≤ |-inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)| :=
            le_abs_self _
      _ = |inner ℝ ((actuator t).adjoint (gradW t)) (u0 t - utr t)| := by rw [abs_neg]
      _ ≤ L * ‖u0 t - utr t‖ := by
        simpa only [ContinuousLinearMap.adjoint_inner_left] using
          hbound houtside (u0 t - utr t)
  have hnumerator :
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2 ≤
        L * ‖u0 t - utr t‖ := by
    calc
      decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2
          = decayRate * (c₁ * (Metric.infDist (x t) (N t)) ^ 2) := by ring
      _ ≤ decayRate * W (t, x t) :=
        mul_le_mul_of_nonneg_left hLower hdecayRate.le
      _ ≤ -(deriv q t) := hderivDecay
      _ ≤ L * ‖u0 t - utr t‖ := hboundDescent
  have hnorm :
      (decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2) / L ≤
        ‖u0 t - utr t‖ := (div_le_iff₀ hL).2 (by nlinarith)
  have hpositive : 0 <
      (decayRate * c₁ * (Metric.infDist (x t) (N t)) ^ 2) / L := by
    apply div_pos
    · exact mul_pos (mul_pos hdecayRate hc₁) (sq_pos_of_pos hdist)
    · exact hL
  exact ⟨hnorm, lt_of_lt_of_le hpositive hnorm⟩

end Tomabechi.Theorem27.Actuator
