import Theorem1

/-! # 定理21の閉球最小点と強凸性解析

定理21の局所幾何、境界降下、強凸性・Hessian・唯一最小点・変位上界を収録。
旧namespaceと宣言名を保つ最適化核で、ODE存在論から独立させる。
-/

namespace Tomabechi.Theorem21

open RealInnerProductSpace
open Filter
open scoped Topology NNReal ContDiff

/-- The straight segment from a point in a closed ball toward its center stays
inside the ball. -/
theorem radial_segment_in_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center x : E) (r t : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ Metric.closedBall center r) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    x + t • (center - x) ∈ Metric.closedBall center r := by
  change dist (x + t • (center - x)) center ≤ r
  rw [dist_eq_norm]
  have hsegment : x + t • (center - x) - center = (1 - t) • (x - center) := by
    module
  rw [hsegment, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁)]
  have hxnorm : ‖x - center‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hfactor_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hfactor_le : 1 - t ≤ 1 := by linarith
  calc
    (1 - t) * ‖x - center‖ ≤ (1 - t) * r :=
      mul_le_mul_of_nonneg_left hxnorm hfactor_nonneg
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right hfactor_le hr
    _ = r := one_mul _

/-- A negative right directional derivative gives strict descent arbitrarily
close to the boundary point. The conclusion is restricted to any prescribed
positive radius so it can be combined with a feasible inward segment. -/
theorem exists_small_strict_descent_of_hasDerivAt_neg
    (f : ℝ → ℝ) (d ε : ℝ)
    (hd : HasDerivAt f d 0) (hdneg : d < 0) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ f t < f 0 := by
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := hd.tendsto_slope_zero_right
  have hevent : {t | t⁻¹ • (f (0 + t) - f 0) < 0} ∈ 𝓝[>] (0 : ℝ) :=
    hlim.eventually (isOpen_Iio.mem_nhds hdneg)
  obtain ⟨δ, hδ, hsubset⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hevent
  obtain ⟨t, ht0, htδ⟩ := exists_between (lt_min hε hδ)
  have htε : t < ε := lt_of_lt_of_le htδ (min_le_left _ _)
  have hδ' : t < δ := lt_of_lt_of_le htδ (min_le_right _ _)
  have hneg := hsubset ⟨ht0, hδ'⟩
  have hprod : t⁻¹ * (f t - f 0) < 0 := by
    simpa [smul_eq_mul] using hneg
  have hdiff : f t - f 0 < 0 := by
    rcases (mul_neg_iff.mp hprod) with ⟨_, hdiff⟩ | ⟨hinv, _⟩
    · exact hdiff
    · exact (False.elim ((not_lt_of_ge (le_of_lt (inv_pos.mpr ht0))) hinv))
  exact ⟨t, ht0, htε, by linarith⟩

/-- A continuously differentiable scalar path cannot cross a level upwards if
its derivative is strictly negative every time it meets that level. The proof
chooses the last level contact before a proposed crossing and uses the
one-sided local descent there. -/
theorem never_cross_above_of_negative_derivative_at_level
    (f f' : ℝ → ℝ) (a b level : ℝ)
    (hab : a < b) (hstart : f a < level) (hend : level < f b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hboundary : ∀ t ∈ Set.Icc a b, f t = level → f' t < 0) :
    False := by
  have hroot : level ∈ f '' Set.Icc a b := by
    exact intermediate_value_Icc hab.le hcont
      ⟨le_of_lt hstart, le_of_lt hend⟩
  obtain ⟨τ, hτmem, hτeq⟩ := hroot
  let I := Set.Icc a b
  have hcontI : Continuous (fun t : I => f t) := hcont.domRestrict
  let S : Set I := Set.univ ∩ {t | f t = level}
  have hSne : S.Nonempty := ⟨⟨τ, hτmem⟩, Set.mem_univ _, hτeq⟩
  have hScompact : IsCompact S := by
    letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
    change IsCompact (Set.univ ∩ {t : I | f t = level})
    exact isCompact_univ.inter_right (isClosed_eq hcontI continuous_const)
  obtain ⟨tstar, htstarS, htstarMax⟩ :=
    hScompact.exists_isMaxOn hSne continuousOn_id
  let tstarVal : ℝ := tstar
  have htstarI : tstarVal ∈ Set.Icc a b := tstar.property
  have htstarV : f tstarVal = level := htstarS.2
  have htstarMaxReal : ∀ s ∈ Set.Icc a b, f s = level → s ≤ tstarVal := by
    intro s hs hfs
    have hmem : (⟨s, hs⟩ : I) ∈ S := ⟨Set.mem_univ _, hfs⟩
    have hmax := htstarMax hmem
    change s ≤ tstarVal at hmax
    exact hmax
  have htstar_gt_a : a < tstarVal := by
    by_contra h
    have heq : tstarVal = a := le_antisymm (le_of_not_gt h) htstarI.1
    have hval : f a = level := by simpa [heq] using htstarV
    linarith
  have htstar_lt_b : tstarVal < b := by
    by_contra h
    have heq : tstarVal = b := le_antisymm htstarI.2 (le_of_not_gt h)
    have hval : f b = level := by simpa [heq] using htstarV
    linarith
  have hnear_deriv := hderiv tstarVal htstarI
  have hnear_neg := hboundary tstarVal htstarI htstarV
  let shifted : ℝ → ℝ := fun u => f (tstarVal + u)
  have hshiftedDeriv : HasDerivAt shifted (f' tstarVal) 0 := by
    have hnear' : HasDerivAt f (f' tstarVal) (tstarVal + 0) := by
      simpa using hnear_deriv
    simpa [shifted] using hnear'.comp_const_add tstarVal 0
  obtain ⟨u, hu, huε, hdescent⟩ :=
    exists_small_strict_descent_of_hasDerivAt_neg shifted (f' tstarVal)
      (b - tstarVal) hshiftedDeriv hnear_neg (sub_pos.mpr htstar_lt_b)
  have htstaru : tstarVal + u ∈ Set.Icc a b := by
    constructor <;> linarith [htstarI.1]
  have hnotroot : f (tstarVal + u) ≠ level := by
    intro hroot'
    have hle := htstarMaxReal (tstarVal + u) htstaru hroot'
    linarith
  have hafter : level < f (tstarVal + u) := by
    by_contra hle
    have hbelow : f (tstarVal + u) < level :=
      lt_of_le_of_ne (le_of_not_gt hle) hnotroot
    have hcontSub : ContinuousOn f (Set.Icc (tstarVal + u) b) :=
      hcont.mono (by
        intro s hs
        exact ⟨le_trans htstarI.1 (le_trans (le_add_of_nonneg_right hu.le) hs.1), hs.2⟩)
    have hcross : level ∈ f '' Set.Icc (tstarVal + u) b := by
      exact intermediate_value_Icc (by linarith [htstaru.2])
        hcontSub ⟨le_of_lt hbelow, le_of_lt hend⟩
    obtain ⟨z, hzI, hzval⟩ := hcross
    have hzmax := htstarMaxReal z
      ⟨le_trans htstarI.1 (le_trans (le_add_of_nonneg_right hu.le) hzI.1), hzI.2⟩ hzval
    linarith [hzI.1, hu]
  have : f (tstarVal + u) < level := by simpa [shifted, htstarV] using hdescent
  linarith

/-- A strict inward derivative at every boundary contact keeps a scalar path
below the boundary level, provided it starts strictly below it. -/
theorem scalar_level_barrier_of_negative_derivative
    (f f' : ℝ → ℝ) (a b level : ℝ)
    (hab : a ≤ b) (hstart : f a ≤ level)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hboundary : ∀ t ∈ Set.Icc a b, f t = level → f' t < 0) :
    ∀ t ∈ Set.Icc a b, f t ≤ level := by
  intro t ht
  by_contra hnot
  have hlevel : level < f t := lt_of_not_ge hnot
  by_cases hstartlt : f a < level
  · have hcont_t : ContinuousOn f (Set.Icc a t) :=
      hcont.mono (fun s hs => ⟨hs.1, le_trans hs.2 ht.2⟩)
    exact (never_cross_above_of_negative_derivative_at_level f f' a t level
      (by
        by_contra h
        have hEq : t = a := le_antisymm (le_of_not_gt h) ht.1
        subst t
        exact (not_le_of_gt hstartlt) (le_of_lt hlevel))
      hstartlt hlevel hcont_t
      (fun s hs => hderiv s ⟨hs.1, le_trans hs.2 ht.2⟩)
      (fun s hs hval => hboundary s ⟨hs.1, le_trans hs.2 ht.2⟩ hval))
  · have hstartEq : f a = level := le_antisymm hstart (le_of_not_gt hstartlt)
    have hat : a < t := by
      by_contra h
      have hEq : t = a := le_antisymm (le_of_not_gt h) ht.1
      subst t
      linarith
    have haDeriv := hderiv a ⟨le_rfl, hab⟩
    have haNeg := hboundary a ⟨le_rfl, hab⟩ hstartEq
    let shifted : ℝ → ℝ := fun u => f (a + u)
    have hshiftedDeriv : HasDerivAt shifted (f' a) 0 := by
      have haDeriv' : HasDerivAt f (f' a) (a + 0) := by simpa using haDeriv
      simpa [shifted] using haDeriv'.comp_const_add a 0
    obtain ⟨u, hu, huε, hdescent⟩ :=
      exists_small_strict_descent_of_hasDerivAt_neg shifted (f' a) (t - a)
        hshiftedDeriv haNeg (sub_pos.mpr hat)
    have hstart' : f (a + u) < level := by
      simpa [shifted, hstartEq] using hdescent
    have hab' : a + u < t := by linarith
    have hcont_t : ContinuousOn f (Set.Icc (a + u) t) :=
      hcont.mono (fun s hs => ⟨le_trans (le_of_lt (by linarith [hu])) hs.1,
        le_trans hs.2 ht.2⟩)
    exact (never_cross_above_of_negative_derivative_at_level f f' (a + u) t level
      hab' hstart' hlevel hcont_t
      (fun s hs => hderiv s ⟨le_trans (le_of_lt (by linarith [hu])) hs.1,
        le_trans hs.2 ht.2⟩)
      (fun s hs hval => hboundary s ⟨le_trans (le_of_lt (by linarith [hu])) hs.1,
        le_trans hs.2 ht.2⟩ hval))

/-- A differentiable trajectory starting strictly inside a closed ball stays
inside as long as its radial velocity is strictly inward whenever it meets the
boundary. This is the finite-interval forward-invariance result used to keep
the local-potential hypotheses available along the flow. -/
theorem trajectory_stays_in_closedBall_of_inward_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (center : E) (velocity : ℝ → E)
    (a b r : ℝ) (hab : a ≤ b) (hr : 0 ≤ r)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hcont : ContinuousOn trajectory (Set.Icc a b))
    (hflow : ∀ t ∈ Set.Icc a b, HasDerivAt trajectory (velocity t) t)
    (hinward : ∀ t ∈ Set.Icc a b,
      ‖trajectory t - center‖ ^ 2 = r ^ 2 →
        inner ℝ (trajectory t - center) (velocity t) < 0) :
    ∀ t ∈ Set.Icc a b, trajectory t ∈ Metric.closedBall center r := by
  let radial : ℝ → ℝ := fun t => ‖trajectory t - center‖ ^ 2
  let radialDeriv : ℝ → ℝ := fun t =>
    2 * inner ℝ (trajectory t - center) (velocity t)
  have hradialCont : ContinuousOn radial (Set.Icc a b) := by
    exact (continuous_norm.comp_continuousOn (hcont.sub continuousOn_const)).pow 2
  have hradialDeriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt radial (radialDeriv t) t := by
    intro t ht
    have hshift : HasDerivAt (fun s => trajectory s - center) (velocity t) t :=
      (hflow t ht).sub_const center
    simpa [radial, radialDeriv] using hshift.norm_sq
  have hradialBoundary : ∀ t ∈ Set.Icc a b,
      radial t = r ^ 2 → radialDeriv t < 0 := by
    intro t ht hboundary
    have hin := hinward t ht (by simpa [radial] using hboundary)
    simpa [radialDeriv] using (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 2) hin)
  have hstay := scalar_level_barrier_of_negative_derivative radial radialDeriv a b
    (r ^ 2) hab (by simpa [radial] using hstart) hradialCont hradialDeriv
    hradialBoundary
  intro t ht
  have hrad := hstay t ht
  change dist (trajectory t) center ≤ r
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (trajectory t - center), hr]

/-- For the identity-mobility gradient flow, an outward radial gradient at the
boundary is exactly the inward radial velocity condition needed above. -/
theorem gradient_flow_stays_in_closedBall_of_radial_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (center : E) (gradient : E → E)
    (a b r : ℝ) (hab : a ≤ b) (hr : 0 ≤ r)
    (hstart : ‖trajectory a - center‖ ^ 2 ≤ r ^ 2)
    (hcont : ContinuousOn trajectory (Set.Icc a b))
    (hflow : ∀ t ∈ Set.Icc a b,
      HasDerivAt trajectory (-(gradient (trajectory t))) t)
    (hradial : ∀ t ∈ Set.Icc a b,
      ‖trajectory t - center‖ ^ 2 = r ^ 2 →
        0 < inner ℝ (gradient (trajectory t)) (trajectory t - center)) :
    ∀ t ∈ Set.Icc a b, trajectory t ∈ Metric.closedBall center r := by
  apply trajectory_stays_in_closedBall_of_inward_boundary trajectory center
    (fun t => -(gradient (trajectory t))) a b r hab hr hstart hcont hflow
  intro t ht hbdy
  have hpos := hradial t ht hbdy
  rw [inner_neg_right, real_inner_comm]
  exact neg_lt_zero.mpr hpos

/-- First-order support inequality encoding `c`-strong convexity on the local
region `U`. The derivation of this inequality from the paper's C² Hessian
bounds is a separate calculus obligation. -/
def StronglyConvexOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (c : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, c / 2 * ‖y - x‖ ^ 2 ≤
    potential y - potential x - inner ℝ (gradient x) (y - x)

/-- A continuous strongly convex potential attains its infimum on any closed,
convex, nonempty subset of a complete inner product space, provided it is
bounded below there. Strong convexity makes every minimizing sequence Cauchy,
so this existence result does not need compactness or finite dimensionality. -/
theorem exists_minimum_of_stronglyConvexOn_of_complete
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (c : ℝ)
    (hUclosed : IsClosed U) (hUconvex : Convex ℝ U) (hUne : U.Nonempty)
    (hcont : ∀ x ∈ U, ContinuousAt potential x)
    (hstrong : StronglyConvexOn U potential gradient c) (hc : 0 < c)
    (hbounded : BddBelow (potential '' U)) :
    ∃ x ∈ U, IsMinOn potential U x := by
  classical
  let values : Set ℝ := potential '' U
  have hvaluesNe : values.Nonempty := by
    rcases hUne with ⟨x, hx⟩
    exact ⟨potential x, ⟨x, hx, rfl⟩⟩
  obtain ⟨u, huanti, hutendsto, humem⟩ :=
    exists_seq_tendsto_sInf hvaluesNe hbounded
  have hchoose : ∀ n : ℕ, ∃ x ∈ U, potential x = u n := by
    intro n
    have hmem : u n ∈ potential '' U := by simpa [values] using humem n
    rcases hmem with ⟨x, hx, hval⟩
    exact ⟨x, hx, hval⟩
  let xseq : ℕ → E := fun n => Classical.choose (hchoose n)
  have hxseq (n : ℕ) : xseq n ∈ U ∧ potential (xseq n) = u n :=
    Classical.choose_spec (hchoose n)
  have hxcauchy : CauchySeq xseq := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    let η : ℝ := c / 8 * ε ^ 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hnear : ∀ᶠ n : ℕ in atTop, u n < sInf values + η := by
      have hlt : sInf values < sInf values + η := by linarith
      have h := (tendsto_order.1 hutendsto).2 (sInf values + η) hlt
      simpa using h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hnear
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hnnear : u n < sInf values + η := hN n hn
    have hmnear : u m < sInf values + η := hN m hm
    let z : E := (1 / 2 : ℝ) • xseq n + (1 / 2 : ℝ) • xseq m
    have hmid : z ∈ U := by
      exact hUconvex (hxseq n).1 (hxseq m).1 (by norm_num) (by norm_num) (by norm_num)
    have hleft := hstrong z hmid (xseq n) (hxseq n).1
    have hright := hstrong z hmid (xseq m) (hxseq m).1
    have hmid_lower : sInf values ≤ potential z :=
      csInf_le hbounded ⟨z, hmid, rfl⟩
    have hdist : c / 8 * dist (xseq n) (xseq m) ^ 2 < η := by
      rw [dist_eq_norm]
      have hxz : xseq n - z = (1 / 2 : ℝ) • (xseq n - xseq m) := by
        dsimp [z]
        module
      have hyz : xseq m - z = (1 / 2 : ℝ) • (xseq m - xseq n) := by
        dsimp [z]
        module
      have hlin : inner ℝ (gradient z) (xseq n - z) +
          inner ℝ (gradient z) (xseq m - z) = 0 := by
        have hsum : (xseq n - z) + (xseq m - z) = 0 := by
          simp only [z]
          module
        rw [← inner_add_right]
        rw [hsum, inner_zero_right]
      have hconvexsum : c / 2 * ‖xseq n - z‖ ^ 2 +
          c / 2 * ‖xseq m - z‖ ^ 2 ≤
          potential (xseq n) + potential (xseq m) - 2 * potential z := by
        nlinarith [hleft, hright, hlin]
      have hnormmid : ‖xseq n - z‖ ^ 2 + ‖xseq m - z‖ ^ 2 =
          ‖xseq n - xseq m‖ ^ 2 / 2 := by
        have hnormrev : ‖xseq m - xseq n‖ = ‖xseq n - xseq m‖ := by
          rw [← dist_eq_norm, dist_comm, dist_eq_norm]
        rw [hxz, hyz, norm_smul, norm_smul, hnormrev]
        norm_num
        ring
      have hstrongmid : c / 8 * ‖xseq n - xseq m‖ ^ 2 ≤
          (potential (xseq n) + potential (xseq m)) / 2 - potential z := by
        nlinarith [hconvexsum, hnormmid]
      have hupper : potential (xseq n) + potential (xseq m) -
          2 * potential z < 2 * η := by
        have h1 : potential (xseq n) < sInf values + η := by rw [(hxseq n).2]; exact hnnear
        have h2 : potential (xseq m) < sInf values + η := by rw [(hxseq m).2]; exact hmnear
        linarith [hmid_lower]
      have : (potential (xseq n) + potential (xseq m)) / 2 - potential z < η := by
        linarith
      exact lt_of_le_of_lt hstrongmid this
    have hdistlt : dist (xseq n) (xseq m) < ε := by
      have hsq : dist (xseq n) (xseq m) ^ 2 < ε ^ 2 := by
        have hc8 : 0 < c / 8 := by positivity
        have hdist' : c / 8 * dist (xseq n) (xseq m) ^ 2 <
            c / 8 * ε ^ 2 := by simpa [η] using hdist
        exact (mul_lt_mul_iff_of_pos_left hc8).mp hdist'
      have hnonneg : 0 ≤ dist (xseq n) (xseq m) := dist_nonneg
      nlinarith [hnonneg, hsq]
    exact hdistlt
  obtain ⟨xlim, hxtendsto⟩ := cauchySeq_tendsto_of_complete hxcauchy
  have hxlim : xlim ∈ U := by
    exact hUclosed.mem_of_tendsto hxtendsto
      (Filter.Eventually.of_forall fun n => (hxseq n).1)
  have hpotlim : Tendsto (fun n => potential (xseq n)) atTop (𝓝 (potential xlim)) :=
    (hcont xlim hxlim).tendsto.comp hxtendsto
  have hseqval : (fun n => potential (xseq n)) = u := by
    funext n
    exact (hxseq n).2
  rw [hseqval] at hpotlim
  have hvalueq : potential xlim = sInf values := tendsto_nhds_unique hpotlim hutendsto
  refine ⟨xlim, hxlim, ?_⟩
  intro y hy
  calc
    potential xlim = sInf values := hvalueq
    _ ≤ potential y := csInf_le hbounded ⟨y, hy, rfl⟩

/-- Convexity of `V - c‖x‖²/2`, together with the gradient representation,
implies the first-order strong-convexity inequality used above. This turns the
Hessian task into proving convexity of the shifted potential. -/
theorem stronglyConvexOn_of_convex_shifted_potential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (c : ℝ)
    (hU : Convex ℝ U)
    (hshifted : ConvexOn ℝ U (fun z => potential z - c / 2 * ‖z‖ ^ 2))
    (hgradient : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x) :
    StronglyConvexOn U potential gradient c := by
  intro x hx y hy
  let line : ℝ → E := fun t => x + t • (y - x)
  have hline_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ U := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hline_eq : line t = (1 - t) • x + t • y := by
      dsimp [line]
      module <;> nlinarith
    rw [hline_eq]
    apply hU hx hy ht1 ht0
    ring
  have hlineConv :
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
        (fun t => potential (line t) - c / 2 * ‖line t‖ ^ 2) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro a ha b hb u v hu hv huv
    have hcomb : line (u • a + v • b) = u • line a + v • line b := by
      dsimp [line]
      simp only [smul_add, mul_smul]
      have hv_eq : v = 1 - u := by linarith
      rw [hv_eq]
      module <;> ring
    change potential (line (u • a + v • b)) -
      c / 2 * ‖line (u • a + v • b)‖ ^ 2 ≤
        u • (potential (line a) - c / 2 * ‖line a‖ ^ 2) +
        v • (potential (line b) - c / 2 * ‖line b‖ ^ 2)
    rw [hcomb]
    exact hshifted.2 (hline_mem a ha) (hline_mem b hb) hu hv huv
  have hpath : HasDerivAt line (y - x) 0 := by
    dsimp [line]
    convert ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x using 1 <;> simp
  have hqderiv := (hgradient x hx).sub
    ((hasFDerivAt_id x).norm_sq.const_mul (c / 2))
  have hcomp := hqderiv.comp_hasDerivAt_of_eq 0 hpath (by simp [line])
  have hderiv : HasDerivAt
      (fun t : ℝ => potential (line t) - c / 2 * ‖line t‖ ^ 2)
      (inner ℝ (gradient x) (y - x) - c * inner ℝ x (y - x)) 0 := by
    convert hcomp using 1 <;>
      simp [Function.comp_def, innerSL_apply_apply, smul_eq_mul, mul_assoc] <;> ring
  have hsecant := hlineConv.le_slope_of_hasDerivAt
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (0 : ℝ) < 1) hderiv
  have hsecant' :
      inner ℝ (gradient x) (y - x) - c * inner ℝ x (y - x) ≤
        (potential y - c / 2 * ‖y‖ ^ 2) -
          (potential x - c / 2 * ‖x‖ ^ 2) := by
    simpa [line, slope_def_field] using hsecant
  have hnorm : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - ‖x‖ ^ 2 -
      2 * inner ℝ x (y - x) := by
    have hdecomp : y = x + (y - x) := by abel
    rw [hdecomp, norm_add_sq_real]
    simp [real_inner_self_eq_norm_sq, inner_add_right]
    ring
  have hnorm' := congrArg (fun z : ℝ => c / 2 * z) hnorm
  nlinarith [hsecant', hnorm']

/-- A pointwise lower bound on the derivative of the gradient implies
convexity of the shifted potential. The Hessian is supplied as the Fréchet
derivative of the gradient; the proof restricts to each segment and applies
Mathlib's one-dimensional second-derivative convexity criterion. -/
theorem stronglyConvexOn_of_hessian_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E)
    (hessian : E → E →L[ℝ] E) (c : ℝ)
    (hU : Convex ℝ U)
    (hgradient : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hhessian : ∀ x ∈ U, HasFDerivAt gradient (hessian x) x)
    (hlower : ∀ x ∈ U, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ inner ℝ (hessian x v) v) :
    StronglyConvexOn U potential gradient c := by
  apply stronglyConvexOn_of_convex_shifted_potential U potential gradient c hU ?_ hgradient
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  let d : E := y - x
  let line : ℝ → E := fun t => x + t • d
  let q : ℝ → ℝ := fun t => potential (line t) - c / 2 * ‖line t‖ ^ 2
  let q' : ℝ → ℝ := fun t =>
    inner ℝ (gradient (line t)) d - c * inner ℝ (line t) d
  let q'' : ℝ → ℝ := fun t =>
    inner ℝ (hessian (line t) d) d - c * ‖d‖ ^ 2
  have hline_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ U := by
    intro t ht
    have hline_eq : line t = (1 - t) • x + t • y := by
      dsimp [line, d]
      module <;> nlinarith [ht.2]
    rw [hline_eq]
    apply hU hx hy (sub_nonneg.mpr ht.2) ht.1
    ring
  have hpath (t : ℝ) : HasDerivAt line d t := by
    dsimp [line]
    convert ((hasDerivAt_id t).smul_const d).const_add x using 1 <;> simp
  have hqderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt q (q' t) t := by
    have hpot := hgradient (line t) (hline_mem t ht)
    have hnorm := (hasFDerivAt_id (line t)).norm_sq.const_mul (c / 2)
    have hcomp := hpot.sub hnorm |>.comp_hasDerivAt_of_eq t (hpath t) (by simp [line])
    convert hcomp using 1 <;>
      simp [q, q', Function.comp_def, innerSL_apply_apply, smul_eq_mul] <;> ring
  have hq'deriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt q' (q'' t) t := by
    have hg := (hhessian (line t) (hline_mem t ht)).comp_hasDerivAt_of_eq t
      (hpath t) (by simp [line])
    have hgd : HasDerivAt (fun s => inner ℝ (gradient (line s)) d)
        (inner ℝ (hessian (line t) d) d) t := by
      simpa [Function.comp_def, q'', inner_smul_left] using
        (HasDerivAt.inner ℝ hg (hasDerivAt_const t d))
    have hxd : HasDerivAt (fun s => inner ℝ (line s) d)
        (inner ℝ d d) t := by
      simpa [inner_smul_left] using
        (HasDerivAt.inner ℝ (hpath t) (hasDerivAt_const t d))
    have hsub := hgd.sub (hxd.const_mul c)
    convert hsub using 1 <;> simp [q', q'', real_inner_self_eq_norm_sq]
  have hq''_nonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ q'' t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    have hh := hlower (line t) (hline_mem t ht') d
    dsimp [q'']
    simpa [real_inner_self_eq_norm_sq] using hh
  have hqconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) q :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (fun t ht => (hqderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hqderiv t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hq'deriv t (interior_subset ht)).hasDerivWithinAt)
      hq''_nonneg
  have hqsecant := hqconvex.2
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) ha hb hab
  have hlinea : line (a • 0 + b • 1) = a • x + b • y := by
    dsimp [line, d]
    have hb' : b = 1 - a := by linarith
    rw [hb']
    module
  have hline0 : line 0 = x := by simp [line]
  have hline1 : line 1 = y := by simp [line, d] <;> abel
  have hqsecant' : q b ≤ a • q 0 + b • q 1 := by simpa using hqsecant
  have hlineb : line b = a • x + b • y := by simpa using hlinea
  simp only [q] at hqsecant'
  rw [hlineb, hline0, hline1] at hqsecant'
  simpa [smul_eq_mul] using hqsecant'

theorem effective_hessian_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ p m β : ℝ) (Hbase Hbias : E →L[ℝ] E) (v : E)
    (hbase : -β * ‖v‖ ^ 2 ≤ inner ℝ (Hbase v) v)
    (hbias : inner ℝ (Hbias v) v ≤ -m * ‖v‖ ^ 2)
    (hκp : 0 ≤ κ * p) :
    (κ * p * m - β) * ‖v‖ ^ 2 ≤
      inner ℝ ((Hbase - (κ * p) • Hbias) v) v := by
  change (κ * p * m - β) * ‖v‖ ^ 2 ≤
    inner ℝ (Hbase v - (κ * p) • Hbias v) v
  rw [inner_sub_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  have hbias' := mul_le_mul_of_nonneg_left hbias hκp
  nlinarith [hbase, hbias']

/-- Apply the paper's separate base-potential and biased-kernel Hessian
bounds to their effective potential `V₀ - κ p S`. -/
theorem effective_potential_strongly_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E) (κ p m β : ℝ)
    (hU : Convex ℝ U)
    (hV : ∀ x ∈ U, HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ U, HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ U, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ U, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ U, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ U, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hκp : 0 ≤ κ * p) :
    StronglyConvexOn U (fun x => V x - κ * p * S x)
      (fun x => gradV x - (κ * p) • gradS x) (κ * p * m - β) := by
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  let Heff : E → E →L[ℝ] E := fun x => HV x - (κ * p) • HS x
  have hVeff : ∀ x ∈ U,
      HasFDerivAt (fun z => V z - κ * p * S z) (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [geff, innerSL_apply_apply, inner_smul_left]
  have hgeff : ∀ x ∈ U, HasFDerivAt geff (Heff x) x := by
    intro x hx
    change HasFDerivAt (fun z => gradV z - (κ * p) • gradS z)
      (HV x - (κ * p) • HS x) x
    exact (hHV x hx).sub ((hHS x hx).const_smul (κ * p))
  have hHeff : ∀ x ∈ U, ∀ v : E,
      (κ * p * m - β) * ‖v‖ ^ 2 ≤ inner ℝ (Heff x v) v := by
    intro x hx v
    have h := effective_hessian_lower_bound κ p m β (HV x) (HS x) v
      (hVlower x hx v) (hSlower x hx v) hκp
    simpa [Heff] using h
  have hconvex := stronglyConvexOn_of_hessian_lower_bound U
    (fun x => V x - κ * p * S x) geff Heff (κ * p * m - β)
    hU hVeff hgeff hHeff
  simpa [geff] using hconvex

/-- The Hessian upper bound on the biased kernel, together with its zero
gradient at the reference center, yields the radial directional estimate at
the boundary. The base-gradient estimate is the Cauchy–Schwarz bound. -/
theorem boundary_directional_estimates_of_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (center x : E) (gradBase gradBias : E → E)
    (Hbias : E → E →L[ℝ] E) (B m r : ℝ)
    (hU : Convex ℝ U) (hcenter : center ∈ U) (hx : x ∈ U)
    (hzero : gradBias center = 0)
    (hderiv : ∀ z ∈ U, HasFDerivAt gradBias (Hbias z) z)
    (hcurvature : ∀ z ∈ U, ∀ v : E,
      inner ℝ (Hbias z v) v ≤ -m * ‖v‖ ^ 2)
    (hbase : ‖gradBase x‖ ≤ B)
    (hr : ‖x - center‖ = r) :
    -B * r ≤ inner ℝ (gradBase x) (x - center) ∧
      inner ℝ (gradBias x) (x - center) ≤ -m * r ^ 2 := by
  let d : E := x - center
  let line : ℝ → E := fun t => center + t • d
  let f : ℝ → ℝ := fun t => inner ℝ (gradBias (line t)) d +
    t * (m * ‖d‖ ^ 2)
  have hline_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ U := by
    intro t ht
    have hline_eq : line t = (1 - t) • center + t • x := by
      dsimp [line, d]
      module <;> nlinarith [ht.2]
    rw [hline_eq]
    apply hU hcenter hx (sub_nonneg.mpr ht.2) ht.1
    ring
  have hpath (t : ℝ) : HasDerivAt line d t := by
    dsimp [line]
    convert ((hasDerivAt_id t).smul_const d).const_add center using 1 <;> simp
  have hfderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt f (inner ℝ (Hbias (line t) d) d + m * ‖d‖ ^ 2) t := by
    have hg := (hderiv (line t) (hline_mem t ht)).comp_hasDerivAt_of_eq t
      (hpath t) (by simp [line])
    have hinner : HasDerivAt (fun s => inner ℝ (gradBias (line s)) d)
        (inner ℝ (Hbias (line t) d) d) t := by
      simpa [Function.comp_def, inner_smul_left] using
        (HasDerivAt.inner ℝ hg (hasDerivAt_const t d))
    have hscalar : HasDerivAt (fun s : ℝ => s * (m * ‖d‖ ^ 2))
        (m * ‖d‖ ^ 2) t := by
      convert (hasDerivAt_id t).mul_const (m * ‖d‖ ^ 2) using 1 <;> simp
    convert hinner.add hscalar using 1 <;> simp [f, add_comm, add_left_comm, add_assoc]
  have hfderiv_nonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      inner ℝ (Hbias (line t) d) d + m * ‖d‖ ^ 2 ≤ 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    have hh := hcurvature (line t) (hline_mem t ht') d
    nlinarith
  have hfantitone : AntitoneOn f (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hfderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (by
        intro t ht
        rw [(hfderiv t (interior_subset ht)).deriv]
        exact hfderiv_nonpos t ht)
  have hvalues := hfantitone
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hradial : inner ℝ (gradBias x) d ≤ -m * ‖d‖ ^ 2 := by
    have hline0 : line 0 = center := by simp [line]
    have hline1 : line 1 = x := by simp [line, d]
    dsimp [f] at hvalues
    rw [hline0, hline1, hzero] at hvalues
    simp only [inner_zero_left, zero_add, zero_mul] at hvalues
    nlinarith
  have hbaseRadial : -B * r ≤ inner ℝ (gradBase x) d := by
    have hcs := abs_real_inner_le_norm (gradBase x) d
    have hinnerLower : -‖gradBase x‖ * ‖d‖ ≤ inner ℝ (gradBase x) d := by
      simpa [neg_mul] using (abs_le.mp hcs).1
    have hrd : ‖d‖ = r := by simpa [d] using hr
    have hr0 : 0 ≤ r := by rw [← hrd]; positivity
    have hproduct : ‖gradBase x‖ * ‖d‖ ≤ B * r := by
      rw [hrd]
      exact mul_le_mul_of_nonneg_right hbase hr0
    nlinarith [hinnerLower, hproduct]
  constructor
  · simpa [d] using hbaseRadial
  · rw [hr] at hradial
    simpa [d] using hradial

/-- A continuous potential attains an interior minimum on a compact local
region if every point outside the interior has a feasible strict descent
point. This isolates the compactness-and-boundary step of Theorem 21. -/
theorem exists_interior_minimum_of_boundary_descent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (potential : E → ℝ)
    (hcompact : IsCompact U) (hU : U.Nonempty)
    (hcontinuous : ContinuousOn potential U)
    (hboundary : ∀ x ∈ U, x ∉ interior U →
      ∃ (v : E) (ε d : ℝ), 0 < ε ∧ HasDerivAt (fun t : ℝ => potential (x + t • v)) d 0 ∧
        d < 0 ∧ ∀ t ∈ Set.Ioo 0 ε, x + t • v ∈ U) :
    ∃ x ∈ interior U, IsMinOn potential U x := by
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hU hcontinuous
  have hinterior : x ∈ interior U := by
    by_contra hnot
    obtain ⟨v, ε, d, hε, hderiv, hd, hfeasible⟩ := hboundary x hx hnot
    obtain ⟨t, htpos, htε, hlt⟩ :=
      exists_small_strict_descent_of_hasDerivAt_neg
        (fun t : ℝ => potential (x + t • v)) d ε hderiv hd hε
    have hy : x + t • v ∈ U := hfeasible t ⟨htpos, htε⟩
    exact (not_lt_of_ge (hmin hy)) (by simpa using hlt)
  exact ⟨x, hinterior, hmin⟩

/-- On a finite-dimensional inner product space, a strict negative derivative
along the inward radial direction rules out every boundary point as a
minimizer. Compactness of the closed ball then gives an interior minimum.
The derivative can be supplied as `D (center - x) < 0`; for the paper's
gradient, this is the boundary condition `⟪∇V(x), x-center⟫ > 0`. -/
theorem exists_interior_minimum_of_radial_boundary_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (center : E) (r : ℝ) (hr : 0 < r) (potential : E → ℝ)
    (hpotential : ContinuousOn potential (Metric.closedBall center r))
    (hboundary : ∀ x ∈ Metric.closedBall center r,
      x ∉ interior (Metric.closedBall center r) →
      ∃ D : E →L[ℝ] ℝ, HasFDerivAt potential D x ∧ D (center - x) < 0) :
    ∃ x ∈ interior (Metric.closedBall center r),
      IsMinOn potential (Metric.closedBall center r) x := by
  let _ : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcenter : center ∈ Metric.closedBall center r := by
    simp [Metric.mem_closedBall, hr.le]
  apply exists_interior_minimum_of_boundary_descent
    (Metric.closedBall center r) potential (isCompact_closedBall center r)
    ⟨center, hcenter⟩ hpotential
  intro x hx hnot
  obtain ⟨D, hD, hderiv_neg⟩ := hboundary x hx hnot
  have hpath : HasDerivAt (fun t : ℝ => x + t • (center - x))
      (center - x) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const (center - x)).const_add x using 1 <;>
      simp
  have hcomp := hD.comp_hasDerivAt_of_eq 0 hpath (by simp)
  refine ⟨center - x, 1, D (center - x), by norm_num, ?_, hderiv_neg, ?_⟩
  · simpa [Function.comp_def] using hcomp
  · intro t ht
    exact radial_segment_in_closedBall center x r t hr.le hx
      (le_of_lt ht.1) (le_of_lt ht.2)

/-- A strict inward radial derivative excludes boundary minimizers whenever a
minimum is known to exist. This implication is independent of compactness. -/
theorem exists_interior_minimum_of_radial_boundary_derivative_of_exists_minimum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center : E) (r : ℝ) (hr : 0 ≤ r) (potential : E → ℝ)
    (hminimum : ∃ x ∈ Metric.closedBall center r,
      IsMinOn potential (Metric.closedBall center r) x)
    (hboundary : ∀ x ∈ Metric.closedBall center r,
      x ∉ interior (Metric.closedBall center r) →
      ∃ D : E →L[ℝ] ℝ, HasFDerivAt potential D x ∧ D (center - x) < 0) :
    ∃ x ∈ interior (Metric.closedBall center r),
      IsMinOn potential (Metric.closedBall center r) x := by
  obtain ⟨x, hx, hmin⟩ := hminimum
  have hinterior : x ∈ interior (Metric.closedBall center r) := by
    by_contra hnot
    obtain ⟨D, hD, hDneg⟩ := hboundary x hx hnot
    have hpath : HasDerivAt (fun t : ℝ => x + t • (center - x))
        (center - x) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).smul_const (center - x)).const_add x using 1 <;>
        simp
    have hcomp := hD.comp_hasDerivAt_of_eq 0 hpath (by simp)
    have hderiv : HasDerivAt (fun t : ℝ => potential (x + t • (center - x)))
        (D (center - x)) 0 := by
      simpa [Function.comp_def] using hcomp
    obtain ⟨t, htpos, htone, hdescent⟩ :=
      exists_small_strict_descent_of_hasDerivAt_neg _ _ 1 hderiv hDneg one_pos
    have hfeasible := radial_segment_in_closedBall center x r t hr hx
      (le_of_lt htpos) (le_of_lt htone)
    have hminval := hmin hfeasible
    have hdescent' : potential (x + t • (center - x)) < potential x := by
      simpa using hdescent
    exact (not_lt_of_ge hminval) hdescent'
  exact ⟨x, hinterior, hmin⟩

/-- Strong convexity makes a stationary point the unique minimizer on `U`.
This is a conditional uniqueness result; it does not assert existence. -/
theorem stationary_point_is_unique_minimum_on_region
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : E → ℝ) (gradient : E → E) (c : ℝ) (hc : 0 < c)
    (U : Set E) (hconvex : StronglyConvexOn U potential gradient c)
    (xstar : E) (hxstar : xstar ∈ U) (hstationary : gradient xstar = 0) :
    (∀ y ∈ U, potential xstar ≤ potential y) ∧
      (∀ y ∈ U, potential y = potential xstar → y = xstar) := by
  constructor
  · intro y hy
    have h := hconvex xstar hxstar y hy
    rw [hstationary] at h
    simp only [inner_zero_left, sub_zero] at h
    nlinarith [sq_nonneg ‖y - xstar‖]
  · intro y hy hvalue
    have h := hconvex xstar hxstar y hy
    rw [hstationary, hvalue] at h
    simp only [inner_zero_left, sub_self] at h
    have hnorm_sq : ‖y - xstar‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖y - xstar‖]
    have hnorm : ‖y - xstar‖ = 0 := (sq_eq_zero_iff).mp hnorm_sq
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Strong convexity implies strong monotonicity of the gradient. -/
theorem strongly_monotone_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : E → ℝ) (gradient : E → E) (c : ℝ)
    (U : Set E) (hconvex : StronglyConvexOn U potential gradient c) :
    ∀ x ∈ U, ∀ y ∈ U, c * ‖y - x‖ ^ 2 ≤
      inner ℝ (gradient y) (y - x) - inner ℝ (gradient x) (y - x) := by
  intro x hx y hy
  have hxy := hconvex x hx y hy
  have hyx := hconvex y hy x hx
  have hyx' : c / 2 * ‖y - x‖ ^ 2 ≤
      potential x - potential y + inner ℝ (gradient y) (y - x) := by
    have hneg : x - y = -(y - x) := by abel
    rw [hneg, norm_neg, inner_neg_right] at hyx
    simpa only [sub_neg_eq_add] using hyx
  have hsum := add_le_add hxy hyx'
  calc
    c * ‖y - x‖ ^ 2 = c / 2 * ‖y - x‖ ^ 2 + c / 2 * ‖y - x‖ ^ 2 := by ring
    _ ≤ potential y - potential x - inner ℝ (gradient x) (y - x) +
        (potential x - potential y + inner ℝ (gradient y) (y - x)) := hsum
    _ = inner ℝ (gradient y) (y - x) - inner ℝ (gradient x) (y - x) := by ring

/-- The unique minimizer lies within `‖∇V(x₀)‖/c` of the reference center.
This is the displacement estimate used in Theorem 21, assuming the center
gradient and the strong-convexity hypotheses have already been established. -/
theorem minimizer_displacement_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : E → ℝ) (gradient : E → E) (c B : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B)
    (U : Set E) (hconvex : StronglyConvexOn U potential gradient c)
    (xstar xcenter : E) (hxstar : xstar ∈ U) (hxcenter : xcenter ∈ U)
    (hstationary : gradient xstar = 0)
    (hcenter : ‖gradient xcenter‖ ≤ B) :
    ‖xstar - xcenter‖ ≤ B / c := by
  have hmono := strongly_monotone_gradient potential gradient c U hconvex
    xstar hxstar xcenter hxcenter
  have hmono' : c * ‖xstar - xcenter‖ ^ 2 ≤
      inner ℝ (gradient xcenter) (xcenter - xstar) := by
    rw [hstationary, inner_zero_left, sub_zero] at hmono
    simpa [norm_sub_rev] using hmono
  have hinner : inner ℝ (gradient xcenter) (xcenter - xstar) ≤
      B * ‖xstar - xcenter‖ := by
    calc
      inner ℝ (gradient xcenter) (xcenter - xstar)
          ≤ |inner ℝ (gradient xcenter) (xcenter - xstar)| := le_abs_self _
      _ ≤ ‖gradient xcenter‖ * ‖xcenter - xstar‖ := abs_real_inner_le_norm _ _
      _ ≤ B * ‖xstar - xcenter‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)
  have hdist_nonneg : 0 ≤ ‖xstar - xcenter‖ := norm_nonneg _
  by_cases hzero : ‖xstar - xcenter‖ = 0
  · rw [hzero]
    positivity
  · have hdist_pos : 0 < ‖xstar - xcenter‖ := lt_of_le_of_ne hdist_nonneg (Ne.symm hzero)
    apply (le_div_iff₀ hc).2
    have hmul : c * ‖xstar - xcenter‖ ≤ B := by
      nlinarith [hmono', hinner, hdist_pos]
    simpa [mul_comm] using hmul

/-- Strong convexity gives the Polyak–Łojasiewicz gradient bound relative to
the stationary minimizer. This is the estimate needed to turn gradient-flow
dissipation into an exponential rate for the potential gap. -/
theorem polyak_gradient_bound_of_strong_convexity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (potential : E → ℝ) (gradient : E → E) (c : ℝ) (hc : 0 < c)
    (U : Set E) (hconvex : StronglyConvexOn U potential gradient c)
    (xstar x : E) (hxstar : xstar ∈ U) (hx : x ∈ U) :
    2 * c * (potential x - potential xstar) ≤ ‖gradient x‖ ^ 2 := by
  have hsupport := hconvex x hx xstar hxstar
  have hgap : potential x - potential xstar ≤
      inner ℝ (gradient x) (x - xstar) - c / 2 * ‖x - xstar‖ ^ 2 := by
    have hrev : xstar - x = -(x - xstar) := by abel
    rw [hrev, inner_neg_right, norm_neg] at hsupport
    nlinarith
  have hinner : inner ℝ (gradient x) (x - xstar) ≤
      ‖gradient x‖ * ‖x - xstar‖ := by
    calc
      inner ℝ (gradient x) (x - xstar)
          ≤ |inner ℝ (gradient x) (x - xstar)| := le_abs_self _
      _ ≤ ‖gradient x‖ * ‖x - xstar‖ := abs_real_inner_le_norm _ _
  have hyoung : 2 * c * (‖gradient x‖ * ‖x - xstar‖ -
        c / 2 * ‖x - xstar‖ ^ 2) ≤ ‖gradient x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖gradient x‖ - c * ‖x - xstar‖)]
  have h2c : 0 < 2 * c := by positivity
  have hmid : 2 * c * (potential x - potential xstar) ≤
      2 * c * (‖gradient x‖ * ‖x - xstar‖ -
        c / 2 * ‖x - xstar‖ ^ 2) := by
    nlinarith [hgap, hinner, h2c]
  exact hmid.trans hyoung


end Tomabechi.Theorem21
