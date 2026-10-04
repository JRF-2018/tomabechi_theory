import Theorem21

/-! # 定理22の段階データと谷・指数軌道

旧 `Theorem22.lean` の段階ごとの強凸性、谷証人、平均場入力、および定量軌道API。
LUB容量更新とは独立した段階力学核として、既存namespace・宣言名・証明を保持する。
-/

open Tomabechi.Theorem21 RealInnerProductSpace Filter
open scoped Topology NNReal

namespace Tomabechi.Theorem22

/-- 閾値 (22.2) から実効ポテンシャルの強凸性余裕が正であることを導く。
指数減衰評価に使う `cₙ > 0` へのスカラーな接続である。

The gain threshold (22.2) makes the effective potential's strong-convexity
margin positive.
日本語要約：(22.2) の利得閾値から (c=κpm-β>0) と境界方向評価の余裕を導く。 -/
theorem gain_threshold_implies_positive_margin
    (r κ p m β B : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m)) :
    0 < p ∧ 0 < κ * p * m - β ∧ 0 ≤ B / r ∧ B / r < κ * p * m := by
  have hden : 0 < κ * m := mul_pos hκ hm
  have hthreshold : max β (B / r) < p * (κ * m) := by
    have h := (div_lt_iff₀ hden).mp (by linarith :
      max β (B / r) / (κ * m) < p)
    simpa [mul_comm] using h
  have hbeta : β ≤ max β (B / r) := le_max_left _ _
  have hBr : B / r ≤ max β (B / r) := le_max_right _ _
  have hBr_nonneg : 0 ≤ B / r := div_nonneg hB hr.le
  have hp_nonneg : 0 ≤ (max β (B / r)) / (κ * m) :=
    div_nonneg (le_trans hβ hbeta) hden.le
  have hmargin : 0 < κ * p * m - β := by nlinarith [hthreshold]
  have hboundary : B / r < κ * p * m := by nlinarith [hthreshold]
  constructor
  · linarith
  · exact ⟨hmargin, hBr_nonneg, hboundary⟩

/-- At any fixed LUB stage, the paper's local Hessian, center, gradient, and
gain-threshold assumptions give the unique interior minimum and displacement
bound already proved in Theorem 21. This stage API preserves the full
closed-ball hypotheses; it does not assert that switching itself supplies
them.
日本語要約：定理22.2の段階条件から閉球内部の唯一最小点、中心からの移動量上界、停留条件、正の曲率余裕を導く。切替整合性は扱わない。 -/
theorem per_stage_unique_interior_minimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (center : E) (r κ p m β B : ℝ) (hr : 0 < r)
    (hκ : 0 < κ) (hm : 0 < m) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hVcont : ContinuousOn V (Metric.closedBall center r))
    (hScont : ContinuousOn S (Metric.closedBall center r))
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      gradV xstar - (κ * p) • gradS xstar = 0 ∧
      0 < κ * p * m - β := by
  obtain ⟨xstar, hxstar, hmin, hunique, hdisplacement⟩ :=
    Tomabechi.Theorem21.exists_unique_interior_minimum_of_threshold
      center r κ p m β B hr hκ hm hβ hB hp V S gradV gradS HV HS
      hVcont hScont hV hS hHV hHS hVlower hSlower hcenter hVbound
  refine ⟨xstar, hxstar, hmin, hunique, hdisplacement, ?_, ?_⟩
  · let U := Metric.closedBall center r
    let Veff : E → ℝ := fun x => V x - κ * p * S x
    let geff : E → E := fun x => gradV x - (κ * p) • gradS x
    have hinterior_nhds : interior U ∈ 𝓝 xstar := isOpen_interior.mem_nhds hxstar
    have hU_nhds : U ∈ 𝓝 xstar :=
      Filter.mem_of_superset hinterior_nhds interior_subset
    have hlocal : IsLocalMin Veff xstar := hmin.isLocalMin hU_nhds
    have hVeff_deriv : HasFDerivAt Veff (innerSL ℝ (geff xstar)) xstar := by
      have h := (hV xstar (interior_subset hxstar)).sub
        ((hS xstar (interior_subset hxstar)).const_mul (κ * p))
      convert h using 1 <;> simp [geff]
    have hstationary_map := hlocal.hasFDerivAt_eq_zero hVeff_deriv
    have heval := congrArg (fun D : E →L[ℝ] ℝ => D (geff xstar)) hstationary_map
    have hinner : inner ℝ (geff xstar) (geff xstar) = 0 := by
      simpa [innerSL_apply_apply] using heval
    have hnorm : ‖geff xstar‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner
    have hgeff : geff xstar = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simpa [geff] using hgeff
  · exact (gain_threshold_implies_positive_margin r κ p m β B hr hκ hm hβ hB hp).2.1

/-- Simultaneous version of the valley theorem: under the stagewise hypotheses
of (22.2), each layer has a unique interior minimizer, the source displacement
bound, stationarity, and a positive curvature margin. Classical choice
assembles the individually proved stage minimizers into one sequence; this
does not impose any switching compatibility on that sequence.
日本語要約：定理22.2を全段階に適用し、各段階の唯一最小点などを一つの列に選ぶ。段階間の切替整合は仮定も結論もしない。 -/
theorem all_stages_unique_interior_minima
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (center : ℕ → E) (r κ p m β B : ℕ → ℝ)
    (V S : ℕ → E → ℝ) (gradV gradS : ℕ → E → E)
    (HV HS : ℕ → E → E →L[ℝ] E)
    (hr : ∀ n, 0 < r n) (hκ : ∀ n, 0 < κ n)
    (hm : ∀ n, 0 < m n) (hβ : ∀ n, 0 ≤ β n)
    (hB : ∀ n, 0 ≤ B n)
    (hp : ∀ n, p n > (max (β n) (B n / r n)) / (κ n * m n))
    (hVcont : ∀ n, ContinuousOn (V n) (Metric.closedBall (center n) (r n)))
    (hScont : ∀ n, ContinuousOn (S n) (Metric.closedBall (center n) (r n)))
    (hV : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (V n) (innerSL ℝ (gradV n x)) x)
    (hS : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (S n) (innerSL ℝ (gradS n x)) x)
    (hHV : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (gradV n) (HV n x) x)
    (hHS : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (gradS n) (HS n x) x)
    (hVlower : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      ∀ w : E, -β n * ‖w‖ ^ 2 ≤ inner ℝ (HV n x w) w)
    (hSlower : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      ∀ w : E, inner ℝ (HS n x w) w ≤ -m n * ‖w‖ ^ 2)
    (hcenter : ∀ n, gradS n (center n) = 0)
    (hVbound : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      ‖gradV n x‖ ≤ B n) :
    ∃ xstar : ℕ → E, ∀ n,
      xstar n ∈ interior (Metric.closedBall (center n) (r n)) ∧
      IsMinOn (fun x => V n x - κ n * p n * S n x)
        (Metric.closedBall (center n) (r n)) (xstar n) ∧
      (∀ y ∈ Metric.closedBall (center n) (r n),
        V n y - κ n * p n * S n y =
          V n (xstar n) - κ n * p n * S n (xstar n) → y = xstar n) ∧
      ‖xstar n - center n‖ ≤ B n / (κ n * p n * m n - β n) ∧
      gradV n (xstar n) - (κ n * p n) • gradS n (xstar n) = 0 ∧
      0 < κ n * p n * m n - β n := by
  classical
  have hstage (n : ℕ) := per_stage_unique_interior_minimum
    (center n) (r n) (κ n) (p n) (m n) (β n) (B n)
    (hr n) (hκ n) (hm n) (hβ n) (hB n) (hp n)
    (V n) (S n) (gradV n) (gradS n) (HV n) (HS n)
    (hVcont n) (hScont n)
    (fun x hx => hV n x hx) (fun x hx => hS n x hx)
    (fun x hx => hHV n x hx) (fun x hx => hHS n x hx)
    (fun x hx w => hVlower n x hx w)
    (fun x hx w => hSlower n x hx w)
    (hcenter n) (fun x hx => hVbound n x hx)
  refine ⟨fun n => Classical.choose (hstage n), ?_⟩
  intro n
  exact Classical.choose_spec (hstage n)

/-- The Hessian assumptions in (22.2), together with its gain threshold,
produce the `StronglyConvexOn` premise required by the stagewise exponential
estimate. This exposes the analytic bridge instead of requiring callers to
reprove strong convexity from the effective-potential Hessian.
日本語要約：基礎・臨場感ポテンシャルのHessian境界とゲイン閾値から実効ポテンシャルの強凸性を導く。 -/
theorem per_stage_effective_strong_convexity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (center : E) (r κ p m β B : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hm : 0 < m)
    (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hp : p > (max β (B / r)) / (κ * m))
    (V S : E → ℝ) (gradV gradS : E → E)
    (HV HS : E → E →L[ℝ] E)
    (hV : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt V (innerSL ℝ (gradV x)) x)
    (hS : ∀ x ∈ Metric.closedBall center r,
      HasFDerivAt S (innerSL ℝ (gradS x)) x)
    (hHV : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2) :
    StronglyConvexOn (Metric.closedBall center r)
      (fun x => V x - κ * p * S x)
      (fun x => gradV x - (κ * p) • gradS x) (κ * p * m - β) := by
  have hp_pos := (gain_threshold_implies_positive_margin r κ p m β B
    hr hκ hm hβ hB hp).1
  have hκp : 0 ≤ κ * p := mul_nonneg hκ.le hp_pos.le
  exact Tomabechi.Theorem21.effective_potential_strongly_convex
    (Metric.closedBall center r) V S gradV gradS HV HS κ p m β
    (convex_closedBall center r) hV hS hHV hHS hVlower hSlower hκp

/-- Apply the gain threshold and the background/presence Hessian bounds at
every stage. This produces the indexed effective strong-convexity premise
used by Theorem 23, with the stage margin `cₙ = κ pₙ mₙ - βₙ` derived rather
than postulated. The closed-ball geometry, derivative data, and Hessian bounds
are exactly the stagewise analytic inputs; no switching or reachability claim
is included here.
日本語要約：各段階の解析条件から曲率余裕 (c_n=\kappa p_nm_n-\beta_n>0) と強凸性を導く。切替・到達可能性は扱わない。 -/
theorem all_stages_effective_strong_convexity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (center : ℕ → E) (r κ p m β B : ℕ → ℝ)
    (V S : ℕ → E → ℝ) (gradV gradS : ℕ → E → E)
    (HV HS : ℕ → E → E →L[ℝ] E)
    (hr : ∀ n, 0 < r n) (hκ : ∀ n, 0 < κ n)
    (hm : ∀ n, 0 < m n) (hβ : ∀ n, 0 ≤ β n)
    (hB : ∀ n, 0 ≤ B n)
    (hp : ∀ n, p n > (max (β n) (B n / r n)) / (κ n * m n))
    (hV : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (V n) (innerSL ℝ (gradV n x)) x)
    (hS : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (S n) (innerSL ℝ (gradS n x)) x)
    (hHV : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (gradV n) (HV n x) x)
    (hHS : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      HasFDerivAt (gradS n) (HS n x) x)
    (hVlower : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      ∀ w : E, -β n * ‖w‖ ^ 2 ≤ inner ℝ (HV n x w) w)
    (hSlower : ∀ n x, x ∈ Metric.closedBall (center n) (r n) →
      ∀ w : E, inner ℝ (HS n x w) w ≤ -m n * ‖w‖ ^ 2) :
    ∀ n, Tomabechi.Theorem21.StronglyConvexOn
      (Metric.closedBall (center n) (r n))
      (fun x => V n x - κ n * p n * S n x)
      (fun x => gradV n x - (κ n * p n) • gradS n x)
      (κ n * p n * m n - β n) := by
  intro n
  exact per_stage_effective_strong_convexity
    (center n) (r n) (κ n) (p n) (m n) (β n) (B n)
    (hr n) (hκ n) (hm n) (hβ n) (hB n) (hp n)
    (V n) (S n) (gradV n) (gradS n) (HV n) (HS n)
    (fun x hx => hV n x hx) (fun x hx => hS n x hx)
    (fun x hx => hHV n x hx) (fun x hx => hHS n x hx)
    (fun x hx w => hVlower n x hx w)
    (fun x hx w => hSlower n x hx w)

/-- At a fixed stage, Theorem 21's state-dependent-mobility estimate gives
the quantitative potential-gap and state-distance rates. As in the source
theorem, the global orbit and forward-invariant sublevel are explicit
hypotheses; this result does not establish switching reachability.
日本語要約：前方不変部分準位に留まる一段階軌道に、定理21のエネルギー差・状態距離の指数評価を適用する。 -/
theorem per_stage_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U C : Set E) (c gamma t₀ : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma)
    (hfield : Continuous (fun x => -(A x (gradient x))))
    (hCsub : C ⊆ U)
    (htrajectory_sublevel : ∀ t ∈ Set.Ici t₀, trajectory t ∈ C)
    (xstar : E) (hxstar : xstar ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hflow : ∀ t,
      HasDerivAt trajectory (-(A (trajectory t) (gradient (trajectory t)))) t)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∀ t ∈ Set.Ici t₀,
      0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀)) ∧
      ‖trajectory t - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * (t - t₀)) := by
  exact Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_exponential_decay
    trajectory potential gradient A U C c gamma t₀ hc hgamma hfield hCsub
    htrajectory_sublevel xstar hxstar hstationary hconvex hpotential
    hpotential_c1 hflow hcoercive

/-- Quantitative decay from a forward orbit with only the local extension
needed to apply the open-interval chain-rule theorem. The ODE is required on
an open interval containing `[t₀,∞)`; no dynamics before that interval or on
all of `ℝ` are imposed. `htrajectory_local` is the local-domain condition
typically supplied by local ODE existence at the initial state.
日本語要約：開始時刻の直前まで延長された局所ODE解について、強凸性と移動度coercivityから指数減衰を示す。 -/
theorem per_stage_exponential_decay_of_local_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (trajectory : ℝ → E) (potential : E → ℝ) (gradient : E → E)
    (A : E → E →L[ℝ] E) (U C : Set E) (c gamma t₀ epsilon : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (hepsilon : 0 < epsilon)
    (hfield : ∀ x ∈ U,
      ContinuousAt (fun y => -(A y (gradient y))) x)
    (hCsub : C ⊆ U)
    (htrajectory_sublevel : ∀ t ∈ Set.Ici t₀, trajectory t ∈ C)
    (htrajectory_local : ∀ t ∈ Set.Ioi (t₀ - epsilon),
      trajectory t ∈ U)
    (xstar : E) (hxstar : xstar ∈ C)
    (hstationary : gradient xstar = 0)
    (hconvex : StronglyConvexOn U potential gradient c)
    (hpotential : ∀ x ∈ U,
      HasFDerivAt potential (innerSL ℝ (gradient x)) x)
    (hpotential_c1 : ContDiffOn ℝ 1 potential U)
    (hflow : ∀ t ∈ Set.Ioi (t₀ - epsilon),
      HasDerivAt trajectory (-(A (trajectory t) (gradient (trajectory t)))) t)
    (hcoercive : ∀ x ∈ U, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∀ t ∈ Set.Ici t₀,
      0 ≤ potential (trajectory t₀) - potential xstar ∧
      potential (trajectory t) - potential xstar ≤
        (potential (trajectory t₀) - potential xstar) *
          Real.exp (-2 * gamma * c * (t - t₀)) ∧
      ‖trajectory t - xstar‖ ≤
        Real.sqrt (2 * (potential (trajectory t₀) - potential xstar) / c) *
          Real.exp (-gamma * c * (t - t₀)) := by
  intro t ht
  have ht₀ : t₀ ≤ t := by simpa using ht
  exact Tomabechi.Theorem21.theorem21_state_dependent_mobility_exponential_decay
    trajectory potential gradient A U C (Set.Ioi (t₀ - epsilon)) c gamma
    t₀ t hc hgamma ht₀ isOpen_Ioi
    (fun s hs => hfield (trajectory s) (htrajectory_local s hs))
    (by
      intro s hs
      change t₀ ≤ s ∧ s ≤ t at hs
      change t₀ - epsilon < s
      linarith [hs.1, hepsilon])
    hCsub (fun s hs => htrajectory_sublevel s hs.1) xstar hxstar
    hstationary hconvex hpotential hpotential_c1 hflow hcoercive

/-- One-stage integration of (22.2) and (22.4). The Hessian and gain
conditions construct the unique interior valley and its stationary effective
gradient; Theorem 21's strong-convexity result then supplies quantitative
decay on an explicitly forward-invariant sublevel. The trajectory, mobility,
and sublevel conditions remain assumptions, matching the source theorem.
日本語要約：(22.2) の局所条件から唯一の内点谷を作り、追加の軌道条件下で (22.4) の指数減衰を示す。 -/
theorem per_stage_valley_and_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
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
    (hHV : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E) (trajectory : ℝ → E)
    (C : Set E) (gamma t₀ epsilon : ℝ) (hgamma : 0 < gamma)
    (hepsilon : 0 < epsilon)
    (hfield : ∀ x ∈ Metric.closedBall center r,
      ContinuousAt (fun y =>
        -(A y (gradV y - (κ * p) • gradS y))) x)
    (hCsub : C ⊆ Metric.closedBall center r)
    (htrajectory_sublevel : ∀ t ∈ Set.Ici t₀, trajectory t ∈ C)
    (htrajectory_local : ∀ t ∈ Set.Ioi (t₀ - epsilon),
      trajectory t ∈ Metric.closedBall center r)
    (hminimizers_in_C : ∀ x,
      IsMinOn (fun y => V y - κ * p * S y)
        (Metric.closedBall center r) x → x ∈ C)
    (hflow : ∀ t ∈ Set.Ioi (t₀ - epsilon), HasDerivAt trajectory
      (-(A (trajectory t)
        (gradV (trajectory t) - (κ * p) • gradS (trajectory t)))) t)
    (hcoercive : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      gamma * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) :
    ∃ xstar ∈ interior (Metric.closedBall center r),
      IsMinOn (fun x => V x - κ * p * S x)
        (Metric.closedBall center r) xstar ∧
      (∀ y ∈ Metric.closedBall center r,
        V y - κ * p * S y = V xstar - κ * p * S xstar → y = xstar) ∧
      ‖xstar - center‖ ≤ B / (κ * p * m - β) ∧
      gradV xstar - (κ * p) • gradS xstar = 0 ∧
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
            Real.exp (-gamma * (κ * p * m - β) * (t - t₀))) := by
  let U := Metric.closedBall center r
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hVcont : ContinuousOn V U := hVcontDiff.continuousOn
  have hScont : ContinuousOn S U := hScontDiff.continuousOn
  obtain ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary, hmargin⟩ :=
    per_stage_unique_interior_minimum center r κ p m β B hr hκ hm hβ hB hp
      V S gradV gradS HV HS hVcont hScont hV hS hHV hHS hVlower hSlower
      hcenter hVbound
  have hconvex := per_stage_effective_strong_convexity center r κ p m β B
    hr hκ hm hβ hB hp V S gradV gradS HV HS hV hS hHV hHS hVlower hSlower
  have hpotential : ∀ x ∈ U,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff, innerSL_apply_apply, inner_smul_left]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff U := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hxstarU : xstar ∈ U := interior_subset hxstar
  have hxstarC : xstar ∈ C := hminimizers_in_C xstar hmin
  have hdecay := per_stage_exponential_decay_of_local_extension trajectory
    Veff geff A U C (κ * p * m - β) gamma t₀ epsilon hmargin hgamma hepsilon
    hfield hCsub htrajectory_sublevel htrajectory_local xstar hxstarC
    hstationary hconvex hpotential hpotentialC1 hflow hcoercive
  refine ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary, ?_⟩
  intro t ht
  simpa [U, Veff, geff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht

/-- A finite-dimensional stage theorem that constructs its forward orbit
instead of taking the trajectory as input. Theorem 21's local ODE existence,
invariant-sublevel continuation, and uniqueness are applied after (22.2) has
produced the unique valley. The invariant region is the initial-energy
sublevel in the closed ball; dissipation proves its forward invariance. The
strict interior containment of its closure remains an explicit barrier
condition, as in Theorem 21's global-existence argument.
日本語要約：有限次元で初期エネルギー部分準位を不変領域として前向き軌道を構成し、指数減衰を得る。部分準位閉包の厳密な内部包含は障壁条件として仮定する。 -/
theorem per_stage_valley_global_existence_and_decay
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
    (hHV : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradV (HV x) x)
    (hHS : ∀ x ∈ Metric.closedBall center r, HasFDerivAt gradS (HS x) x)
    (hVlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      -β * ‖v‖ ^ 2 ≤ inner ℝ (HV x v) v)
    (hSlower : ∀ x ∈ Metric.closedBall center r, ∀ v : E,
      inner ℝ (HS x v) v ≤ -m * ‖v‖ ^ 2)
    (hcenter : gradS center = 0)
    (hVbound : ∀ x ∈ Metric.closedBall center r, ‖gradV x‖ ≤ B)
    (A : E → E →L[ℝ] E) (C : Set E) (gamma t₀ : ℝ)
    (x₀ : E) (hx₀ : x₀ ∈ C)
    (hfieldC1 : ∀ x ∈ Metric.closedBall center r,
      ContDiffAt ℝ 1 (fun y => -(A y (gradV y - (κ * p) • gradS y))) x)
    (hCclosureInterior : closure C ⊆ Metric.ball center r)
    (hCsublevel : C = {x | x ∈ Metric.closedBall center r ∧
      V x - κ * p * S x ≤ V x₀ - κ * p * S x₀})
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
              (-(A (other t) (gradV (other t) - (κ * p) • gradS (other t)))) t) →
          ∀ t ∈ Set.Ici t₀, other t = trajectory t) := by
  let U := Metric.closedBall center r
  let Veff : E → ℝ := fun x => V x - κ * p * S x
  let geff : E → E := fun x => gradV x - (κ * p) • gradS x
  have hVcont : ContinuousOn V U := hVcontDiff.continuousOn
  have hScont : ContinuousOn S U := hScontDiff.continuousOn
  obtain ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary, hmargin⟩ :=
    per_stage_unique_interior_minimum center r κ p m β B hr hκ hm hβ hB hp
      V S gradV gradS HV HS hVcont hScont hV hS hHV hHS hVlower hSlower
      hcenter hVbound
  have hconvex := per_stage_effective_strong_convexity center r κ p m β B
    hr hκ hm hβ hB hp V S gradV gradS HV HS hV hS hHV hHS hVlower hSlower
  have hpotential : ∀ x ∈ U,
      HasFDerivAt Veff (innerSL ℝ (geff x)) x := by
    intro x hx
    have h := (hV x hx).sub ((hS x hx).const_mul (κ * p))
    convert h using 1 <;> simp [Veff, geff]
  have hpotentialC1 : ContDiffOn ℝ 1 Veff U := by
    simpa [Veff, smul_eq_mul] using
      hVcontDiff.sub (ContDiffOn.const_smul (κ * p) hScontDiff)
  have hCsub : C ⊆ U := by
    intro x hx
    rw [hCsublevel] at hx
    exact hx.1
  have hx₀ball : x₀ ∈ U := hCsub hx₀
  have hxstarC : xstar ∈ C := by
    rw [hCsublevel]
    refine ⟨interior_subset hxstar, ?_⟩
    exact hmin hx₀ball
  have hinvariant : ∀ (a d : ℝ) (orbit : ℝ → E) (x : E),
      0 ≤ d → orbit a = x → x ∈ C →
      (∀ t ∈ Set.Icc a (a + d),
        HasDerivAt orbit
          (-(A (orbit t) (gradV (orbit t) - (κ * p) • gradS (orbit t)))) t) →
      ∀ t ∈ Set.Icc a (a + d), orbit t ∈ C := by
    intro a d orbit x hd horbit hx hflow
    exact Tomabechi.Theorem21.forward_invariant_sublevel_of_strict_interior_barrier
      orbit Veff geff A center r gamma a (a + d) (Veff x₀) hgamma
      (le_add_of_nonneg_right hd) C hCsublevel
      (fun y hy => hCclosureInterior (subset_closure hy)) x hx
      horbit hpotential hflow hcoercive
  obtain ⟨trajectory, epsilon, hepsilon, hinitial, hflow, htrajectoryC,
      hdecay, huniqueFlow⟩ :=
    Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_existence_and_decay
      center r t₀ (κ * p * m - β) gamma hr.le hmargin hgamma
      Veff geff A U C xstar x₀ hfieldC1 hCclosureInterior hinvariant hCsub
      hxstarC hx₀ hstationary
      hconvex hpotential hpotentialC1 hcoercive
  refine ⟨xstar, hxstar, hmin, hunique, hdisplacement, hstationary,
    trajectory, epsilon, hepsilon, hinitial, hflow, htrajectoryC, ?_, huniqueFlow⟩
  intro t ht
  simpa [U, Veff, geff, mul_assoc, mul_left_comm, mul_comm] using hdecay t ht

/-- 各段階の谷・凍結軌道の構成に必要な入力。
sublevelの厳密な内部障壁と移動度の一様coercivityは、原文の局所Hessian
閾値だけからは従わないため、独立条件として保持する。原文に合わせて
移動度場のC¹性・対称性とポテンシャルのC²性を入力する。勾配が
ポテンシャルのFréchet微分をRiesz表現する条件から、勾配場と
閉ループ場の局所C¹性を導く。

Input data for one stage of the global valley and orbit construction.
The source's symmetric C¹ mobility and C² potentials yield local C¹
regularity of the closed-loop field through the Riesz representation of
their gradients. The strict interior barrier remains an additional
condition because it is not implied by the local Hessian bounds alone.
日本語要約：対称C¹移動度、C²ポテンシャル、勾配のRiesz表現を段階データとして与え、閉ループ場のC¹性を導いて谷と軌道を構成する。初期部分準位が球の内部に留まる障壁条件は独立仮定として残す。 -/
structure StageValleySpec (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  center : E
  radius : ℝ
  gain : ℝ
  presenceGain : ℝ
  curvature : ℝ
  backgroundCurvature : ℝ
  gradientBound : ℝ
  gamma : ℝ
  startTime : ℝ
  background : E → ℝ
  presence : E → ℝ
  backgroundGradient : E → E
  presenceGradient : E → E
  backgroundHessian : E → E →L[ℝ] E
  presenceHessian : E → E →L[ℝ] E
  mobility : E → E →L[ℝ] E
  sublevel : Set E
  initial : E
  radius_pos : 0 < radius
  gain_pos : 0 < gain
  curvature_pos : 0 < curvature
  backgroundCurvature_nonneg : 0 ≤ backgroundCurvature
  gradientBound_nonneg : 0 ≤ gradientBound
  gain_threshold : presenceGain >
    (max backgroundCurvature (gradientBound / radius)) / (gain * curvature)
  background_c2_at : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 2 background x
  presence_c2_at : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 2 presence x
  background_gradient_representation : ∀ x,
    innerSL ℝ (backgroundGradient x) = fderiv ℝ background x
  presence_gradient_representation : ∀ x,
    innerSL ℝ (presenceGradient x) = fderiv ℝ presence x
  background_gradient_deriv : ∀ x ∈ Metric.closedBall center radius,
    HasFDerivAt backgroundGradient (backgroundHessian x) x
  presence_gradient_deriv : ∀ x ∈ Metric.closedBall center radius,
    HasFDerivAt presenceGradient (presenceHessian x) x
  mobility_c1 : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 1 mobility x
  mobility_symmetric : ∀ x ∈ Metric.closedBall center radius, ∀ v w : E,
    inner ℝ (mobility x v) w = inner ℝ v (mobility x w)
  background_hessian_lower : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    -backgroundCurvature * ‖w‖ ^ 2 ≤ inner ℝ (backgroundHessian x w) w
  presence_hessian_upper : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    inner ℝ (presenceHessian x w) w ≤ -curvature * ‖w‖ ^ 2
  presence_center_stationary : presenceGradient center = 0
  background_gradient_bound : ∀ x ∈ Metric.closedBall center radius,
    ‖backgroundGradient x‖ ≤ gradientBound
  initial_mem : initial ∈ sublevel
  sublevel_barrier : closure sublevel ⊆ Metric.ball center radius
  sublevel_eq : sublevel = {x | x ∈ Metric.closedBall center radius ∧
    background x - gain * presenceGain * presence x ≤
      background initial - gain * presenceGain * presence initial}
  gamma_pos : 0 < gamma
  mobility_coercive : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    gamma * ‖w‖ ^ 2 ≤ inner ℝ (mobility x w) w

universe u

/-- A presentation of the averaged reconstruction field in (21.1), including
the layer support, its least upper bound, and the represented center. The
kernel is integrated as a scalar field; no derivatives of the kernel or
interchange of differentiation and integration are assumed. -/
structure MeanFieldAveragePresentation (E : Type u) where
  Atom : Type u
  atomOrder : PartialOrder Atom
  abstractTop : Atom
  abstractTop_greatest : ∀ a, atomOrder.le a abstractTop
  sourceLayer : Set Atom
  abstractTop_not_in_sourceLayer : abstractTop ∉ sourceLayer
  atomTopology : TopologicalSpace Atom
  atomMeasurableSpace : MeasurableSpace Atom
  atomMeasure : @MeasureTheory.Measure Atom atomMeasurableSpace
  atomMeasure_probability : MeasureTheory.IsProbabilityMeasure atomMeasure
  measureSupport : Set Atom
  measureSupport_eq_topological_support : measureSupport =
    @MeasureTheory.Measure.support Atom atomTopology atomMeasurableSpace atomMeasure
  measureSupport_measurable : @MeasurableSet Atom atomMeasurableSpace measureSupport
  measureSupport_full : atomMeasure measureSupportᶜ = 0
  measureSupport_subset_sourceLayer : measureSupport ⊆ sourceLayer
  supportLub : Atom
  supportLub_upper : ∀ a ∈ measureSupport, atomOrder.le a supportLub
  supportLub_least : ∀ b, (∀ a ∈ measureSupport, atomOrder.le a b) →
    atomOrder.le supportLub b
  supportLub_mem_sourceLayer : supportLub ∈ sourceLayer
  centerRepresentation : Atom → E
  reconstructionKernel : E → Atom → ℝ
  reconstructionKernel_integrable : ∀ x,
    MeasureTheory.Integrable (fun a => reconstructionKernel x a) atomMeasure

namespace MeanFieldAveragePresentation

/-- The pointwise scalar integral used in the averaged field. -/
noncomputable def integralValue {E : Type u} (p : MeanFieldAveragePresentation E)
    (x : E) : ℝ := by
  letI : MeasurableSpace p.Atom := p.atomMeasurableSpace
  exact ∫ a, p.reconstructionKernel x a ∂p.atomMeasure

end MeanFieldAveragePresentation

/-- One Theorem 22 stage whose presence potential is already the averaged
field `S_μ` from Theorem 21. The record takes the mean field, its gradient,
and its Hessian as stage data; it does not require pointwise kernel derivatives
or an interchange-of-differentiation proof over the atoms. It records the
layer support, its LUB `b`, the representation `x_b`, and an integral
presentation proving `meanField x = ∫ K(x,a) ∂μ`. All remaining
barrier, mobility, and initial-sublevel conditions are explicit H-stage
inputs. -/
structure MeanFieldStageCore (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  center : E
  radius : ℝ
  gain : ℝ
  presenceGain : ℝ
  curvature : ℝ
  backgroundCurvature : ℝ
  gradientBound : ℝ
  gamma : ℝ
  startTime : ℝ
  background : E → ℝ
  meanField : E → ℝ
  averagePresentation : MeanFieldAveragePresentation E
  center_eq_supportLub_representation :
    center = averagePresentation.centerRepresentation
      averagePresentation.supportLub
  meanField_eq_integral : ∀ x,
    meanField x = averagePresentation.integralValue x
  backgroundGradient : E → E
  meanFieldGradient : E → E
  backgroundHessian : E → E →L[ℝ] E
  meanFieldHessian : E → E →L[ℝ] E
  mobility : E → E →L[ℝ] E
  sublevel : Set E
  initial : E
  radius_pos : 0 < radius
  gain_pos : 0 < gain
  curvature_pos : 0 < curvature
  backgroundCurvature_nonneg : 0 ≤ backgroundCurvature
  gradientBound_nonneg : 0 ≤ gradientBound
  gain_threshold : presenceGain >
    (max backgroundCurvature (gradientBound / radius)) / (gain * curvature)
  background_c2_at : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 2 background x
  meanField_c2_at : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 2 meanField x
  background_gradient_representation : ∀ x,
    innerSL ℝ (backgroundGradient x) = fderiv ℝ background x
  meanField_gradient_representation : ∀ x,
    innerSL ℝ (meanFieldGradient x) = fderiv ℝ meanField x
  background_gradient_deriv : ∀ x ∈ Metric.closedBall center radius,
    HasFDerivAt backgroundGradient (backgroundHessian x) x
  meanField_gradient_deriv : ∀ x ∈ Metric.closedBall center radius,
    HasFDerivAt meanFieldGradient (meanFieldHessian x) x
  mobility_c1 : ∀ x ∈ Metric.closedBall center radius,
    ContDiffAt ℝ 1 mobility x
  mobility_symmetric : ∀ x ∈ Metric.closedBall center radius, ∀ v w : E,
    inner ℝ (mobility x v) w = inner ℝ v (mobility x w)
  background_hessian_lower : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    -backgroundCurvature * ‖w‖ ^ 2 ≤ inner ℝ (backgroundHessian x w) w
  meanField_hessian_upper : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    inner ℝ (meanFieldHessian x w) w ≤ -curvature * ‖w‖ ^ 2
  meanField_center_stationary : meanFieldGradient center = 0
  background_gradient_bound : ∀ x ∈ Metric.closedBall center radius,
    ‖backgroundGradient x‖ ≤ gradientBound
  initial_mem : initial ∈ sublevel
  sublevel_barrier : closure sublevel ⊆ Metric.ball center radius
  gamma_pos : 0 < gamma
  mobility_coercive : ∀ x ∈ Metric.closedBall center radius, ∀ w : E,
    gamma * ‖w‖ ^ 2 ≤ inner ℝ (mobility x w) w

/-- The original exact-sublevel stage input, retained as a specialization of
the shared mean-field analytic data. -/
structure MeanFieldStageInput (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] extends MeanFieldStageCore E where
  sublevel_eq : sublevel = {x | x ∈ Metric.closedBall center radius ∧
    background x - gain * presenceGain * meanField x ≤
      background initial - gain * presenceGain * meanField initial}

/-- H-stage mean-field data with an arbitrary forward-invariant region. The
shared core retains the integral presentation and all analytic threshold
conditions; the region need not be the complete initial-energy sublevel.
Membership of the threshold minimizer and forward invariance are explicit
conditions, as in the source's dynamical hypothesis. -/
structure InvariantRegionMeanFieldStageInput (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends MeanFieldStageCore E where
  minimizer_in_sublevel : ∀ x, x ∈ Metric.closedBall center radius →
    IsMinOn (fun y => background y - gain * presenceGain * meanField y)
      (Metric.closedBall center radius) x → x ∈ sublevel
  forward_invariant : ∀ (a d : ℝ) (orbit : ℝ → E) (x : E),
    0 ≤ d → orbit a = x → x ∈ sublevel →
    (∀ t ∈ Set.Icc a (a + d),
      HasDerivAt orbit
        (-(mobility (orbit t)
          (backgroundGradient (orbit t) -
            (gain * presenceGain) • meanFieldGradient (orbit t)))) t) →
    ∀ t ∈ Set.Icc a (a + d), orbit t ∈ sublevel

/-- Convert mean-field stage data to the common valley specification. This is
a field-by-field construction, with `presence` set to the very same mean field
used in the potential and the sublevel condition. -/
def MeanFieldStageInput.toStageValleySpec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : MeanFieldStageInput E) : StageValleySpec E :=
  { center := s.center
    radius := s.radius
    gain := s.gain
    presenceGain := s.presenceGain
    curvature := s.curvature
    backgroundCurvature := s.backgroundCurvature
    gradientBound := s.gradientBound
    gamma := s.gamma
    startTime := s.startTime
    background := s.background
    presence := s.meanField
    backgroundGradient := s.backgroundGradient
    presenceGradient := s.meanFieldGradient
    backgroundHessian := s.backgroundHessian
    presenceHessian := s.meanFieldHessian
    mobility := s.mobility
    sublevel := s.sublevel
    initial := s.initial
    radius_pos := s.radius_pos
    gain_pos := s.gain_pos
    curvature_pos := s.curvature_pos
    backgroundCurvature_nonneg := s.backgroundCurvature_nonneg
    gradientBound_nonneg := s.gradientBound_nonneg
    gain_threshold := s.gain_threshold
    background_c2_at := s.background_c2_at
    presence_c2_at := s.meanField_c2_at
    background_gradient_representation := s.background_gradient_representation
    presence_gradient_representation := s.meanField_gradient_representation
    background_gradient_deriv := s.background_gradient_deriv
    presence_gradient_deriv := s.meanField_gradient_deriv
    mobility_c1 := s.mobility_c1
    mobility_symmetric := s.mobility_symmetric
    background_hessian_lower := s.background_hessian_lower
    presence_hessian_upper := s.meanField_hessian_upper
    presence_center_stationary := s.meanField_center_stationary
    background_gradient_bound := s.background_gradient_bound
    initial_mem := s.initial_mem
    sublevel_barrier := s.sublevel_barrier
    sublevel_eq := s.sublevel_eq
    gamma_pos := s.gamma_pos
    mobility_coercive := s.mobility_coercive }

/-- Convert an LUB-indexed stage sequence without changing any mean field. -/
def meanFieldStageSequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (stages : ℕ → MeanFieldStageInput E) :
    ℕ → StageValleySpec E := fun n => (stages n).toStageValleySpec

/-- The presence-weighted stage potential from a packaged stage input.
日本語要約：背景ポテンシャルから利得加重された臨場感ポテンシャルを引いた段階実効ポテンシャル。 -/
def stageEffectivePotential {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : StageValleySpec E) (x : E) : ℝ :=
  s.background x - s.gain * s.presenceGain * s.presence x

/-- The gradient of the presence-weighted stage potential.
日本語要約：段階実効ポテンシャルを構成する勾配場を定義する。 -/
def stageEffectiveGradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : StageValleySpec E) (x : E) : E :=
  s.backgroundGradient x -
    (s.gain * s.presenceGain) • s.presenceGradient x

/-- Derive C¹ regularity on the stage ball from its pointwise ambient C² data.
日本語要約：閉球上の各点でのポテンシャルC²性から、閉球上のC¹性を導く。-/
theorem StageValleySpec.backgroundContDiffOnOne {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : StageValleySpec E) :
    ContDiffOn ℝ 1 s.background (Metric.closedBall s.center s.radius) := by
  intro x hx
  exact ((s.background_c2_at x hx).of_le (by norm_num)).contDiffWithinAt

/-- 同上を臨場感ポテンシャルに適用する。
日本語要約：臨場感ポテンシャルのC²性から、閉球上のC¹性を導く。-/
theorem StageValleySpec.presenceContDiffOnOne {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : StageValleySpec E) :
    ContDiffOn ℝ 1 s.presence (Metric.closedBall s.center s.radius) := by
  intro x hx
  exact ((s.presence_c2_at x hx).of_le (by norm_num)).contDiffWithinAt

/-- The Riesz representation identifies the gradient with the derivative of
the background potential on the stage ball.
日本語要約：背景ポテンシャルのRiesz勾配表現から微分可能性を得る。-/
theorem StageValleySpec.backgroundHasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : StageValleySpec E) :
    ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.background (innerSL ℝ (s.backgroundGradient x)) x := by
  intro x hx
  have hdiff := (s.background_c2_at x hx).differentiableAt (by norm_num)
  convert hdiff.hasFDerivAt using 1
  exact s.background_gradient_representation x

/-- Apply the same argument to the presence potential.
日本語要約：臨場感ポテンシャルのRiesz勾配表現から微分可能性を得る。-/
theorem StageValleySpec.presenceHasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : StageValleySpec E) :
    ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.presence (innerSL ℝ (s.presenceGradient x)) x := by
  intro x hx
  have hdiff := (s.presence_c2_at x hx).differentiableAt (by norm_num)
  convert hdiff.hasFDerivAt using 1
  exact s.presence_gradient_representation x

/-- A scalar C² potential has a C¹ gradient when that gradient is represented
by its Fréchet derivative through the Riesz map on a Hilbert space.
日本語要約：Riesz表現で勾配を微分として定めると、ポテンシャルC²性から勾配C¹性が従う。-/
theorem contDiffAt_gradient_of_c2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (gradient : E → E) (x : E)
    (hf : ContDiffAt ℝ 2 f x)
    (hrepresentation : ∀ y,
      innerSL ℝ (gradient y) = fderiv ℝ f y) :
    ContDiffAt ℝ 1 gradient x := by
  have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right_succ
  have hRiesz : ContDiffAt ℝ 1
      (fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x := by
    exact ((LinearIsometryEquiv.contDiff
      (InnerProductSpace.toDual ℝ E).symm).contDiffAt.comp x hfderiv)
  apply hRiesz.congr_of_eventuallyEq
  filter_upwards with y
  have hdual : InnerProductSpace.toDual ℝ E (gradient y) =
      fderiv ℝ f y := by
    ext z
    have hz := congrArg (fun d : E →L[ℝ] ℝ => d z)
      (hrepresentation y)
    simpa [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using hz
  calc
    gradient y = (InnerProductSpace.toDual ℝ E).symm
        (InnerProductSpace.toDual ℝ E (gradient y)) := by simp
    _ = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y) :=
      congrArg (InnerProductSpace.toDual ℝ E).symm hdual

/-- 原文の各因子のC¹性から、段階閉ループベクトル場の局所C¹性を導く。
日本語要約：移動度場と有効勾配場のC¹性を合成し、ODE構成に必要な閉ループ場の正則性を得る。-/
theorem StageValleySpec.closedLoopC1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : StageValleySpec E) (x : E)
    (hx : x ∈ Metric.closedBall s.center s.radius) :
    ContDiffAt ℝ 1
      (fun y => -(s.mobility y (stageEffectiveGradient s y))) x := by
  have hgradient : ContDiffAt ℝ 1 (stageEffectiveGradient s) x := by
    change ContDiffAt ℝ 1
      (fun y => s.backgroundGradient y -
        (s.gain * s.presenceGain) • s.presenceGradient y) x
    exact (contDiffAt_gradient_of_c2 s.background s.backgroundGradient x
      (s.background_c2_at x hx) s.background_gradient_representation).sub
      ((contDiffAt_gradient_of_c2 s.presence s.presenceGradient x
        (s.presence_c2_at x hx) s.presence_gradient_representation).const_smul
          (s.gain * s.presenceGain))
  have happly := (s.mobility_c1 x hx).clm_apply hgradient
  simpa [stageEffectiveGradient] using happly.neg

/-- The selected minimizer and global frozen orbit supplied by a stage's
analytic data. `orbit_decay` retains both the energy-gap and state-distance
rates with their exact stage constants.
日本語要約：段階の唯一最小点、初期状態からの凍結軌道、減衰と一意性の証明情報をまとめる。 -/
structure StageValleyWitness {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : StageValleySpec E) where
  minimizer : E
  minimizer_interior : minimizer ∈ interior
    (Metric.closedBall s.center s.radius)
  minimizer_is_min : IsMinOn
    (fun x => s.background x - s.gain * s.presenceGain * s.presence x)
    (Metric.closedBall s.center s.radius) minimizer
  minimizer_unique : ∀ y ∈ Metric.closedBall s.center s.radius,
    s.background y - s.gain * s.presenceGain * s.presence y =
      s.background minimizer - s.gain * s.presenceGain * s.presence minimizer →
      y = minimizer
  displacement_bound : ‖minimizer - s.center‖ ≤
    s.gradientBound / (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)
  stationary : s.backgroundGradient minimizer -
    (s.gain * s.presenceGain) • s.presenceGradient minimizer = 0
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
          (s.gain * s.presenceGain) • s.presenceGradient (orbit t)))) t
  orbit_in_sublevel : ∀ t ∈ Set.Ici s.startTime, orbit t ∈ s.sublevel
  orbit_decay : ∀ t ∈ Set.Ici s.startTime,
    0 ≤ (s.background (orbit s.startTime) -
      s.gain * s.presenceGain * s.presence (orbit s.startTime)) -
        (s.background minimizer - s.gain * s.presenceGain * s.presence minimizer) ∧
    (s.background (orbit t) - s.gain * s.presenceGain * s.presence (orbit t)) -
      (s.background minimizer - s.gain * s.presenceGain * s.presence minimizer) ≤
        ((s.background (orbit s.startTime) -
          s.gain * s.presenceGain * s.presence (orbit s.startTime)) -
            (s.background minimizer - s.gain * s.presenceGain * s.presence minimizer)) *
          Real.exp (-2 * s.gamma *
            (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) *
            (t - s.startTime)) ∧
    ‖orbit t - minimizer‖ ≤
      Real.sqrt (2 * ((s.background (orbit s.startTime) -
        s.gain * s.presenceGain * s.presence (orbit s.startTime)) -
          (s.background minimizer - s.gain * s.presenceGain * s.presence minimizer)) /
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
            (s.gain * s.presenceGain) • s.presenceGradient (other t)))) t) →
    ∀ t ∈ Set.Ici s.startTime, other t = orbit t

namespace StageValleyWitness

/-- The initial energy gap gives the distance prefactor in (22.4).
日本語要約：初期ポテンシャル差と曲率余裕で定まる距離評価の係数を定義する。 -/
noncomputable def decayAmplitude {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) : ℝ :=
  Real.sqrt (2 * ((s.background (w.orbit s.startTime) -
    s.gain * s.presenceGain * s.presence (w.orbit s.startTime)) -
      (s.background w.minimizer -
        s.gain * s.presenceGain * s.presence w.minimizer)) /
        (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature))

/-- The exponential state-distance rate `γₙ cₙ` of (22.4).
日本語要約：移動度定数と曲率余裕の積で指数減衰率を定義する。 -/
def decayRate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (_w : StageValleyWitness s) : ℝ :=
  s.gamma * (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)

theorem decayAmplitude_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) : 0 ≤ w.decayAmplitude :=
  Real.sqrt_nonneg _

theorem decayRate_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) : 0 < w.decayRate :=
  mul_pos s.gamma_pos w.positive_margin

/-- Repackage the state-distance part of (22.4) in the constants consumed by
Theorem 23.
日本語要約：選択軌道の状態距離に対する定量指数評価を取り出す。 -/
theorem distance_decay {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) :
    ∀ t ∈ Set.Ici s.startTime,
      dist (w.orbit t) w.minimizer ≤
        w.decayAmplitude * Real.exp
          (-w.decayRate * (t - s.startTime)) := by
  intro t ht
  have hdecay := (w.orbit_decay t ht).2.2
  have hexponent : -s.gamma *
      (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature) *
      (t - s.startTime) = -w.decayRate * (t - s.startTime) := by
    simp [decayRate]
  rw [dist_eq_norm]
  rw [hexponent] at hdecay
  simpa [decayAmplitude] using hdecay

/-- The chosen frozen orbit solves its closed-loop ODE at every forward time;
the local extension supplied by ODE existence covers the initial endpoint.
日本語要約：構成した凍結軌道が段階開始後の全時刻で閉ループODEを満たす。 -/
theorem orbit_ode_forward {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) (t : ℝ) (ht : s.startTime ≤ t) :
    HasDerivAt w.orbit
      (-(s.mobility (w.orbit t)
        (s.backgroundGradient (w.orbit t) -
          (s.gain * s.presenceGain) • s.presenceGradient (w.orbit t)))) t := by
  apply w.orbit_ode t
  change s.startTime - w.local_extension < t
  linarith [w.local_extension_pos, ht]

/-- The invariant sublevel used in the global existence proof is contained in
the stage's closed ball, so every forward orbit state remains in the local
region where the Hessian and mobility conditions were assumed.
日本語要約：部分準位の閉球包含を用い、全前向き軌道が段階閉球に留まると示す。 -/
theorem orbit_in_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : StageValleySpec E}
    (w : StageValleyWitness s) (t : ℝ) (ht : s.startTime ≤ t) :
    w.orbit t ∈ Metric.closedBall s.center s.radius := by
  have hmem := w.orbit_in_sublevel t ht
  rw [s.sublevel_eq] at hmem
  exact hmem.1

end StageValleyWitness

/-- For every stage satisfying Theorem 22's local hypotheses together with
the stated global-existence barrier, choose its unique valley and its unique
forward orbit. The construction is pointwise in the stage index and therefore
does not assume a common radius, gain, or mobility across stages.
日本語要約：有限次元の段階条件から谷と全前向き凍結軌道の証人を構成する。 -/
noncomputable def chooseStageValley {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : StageValleySpec E) : StageValleyWitness s := by
  classical
  have hbackgroundC1 : ContDiffOn ℝ 1 s.background
      (Metric.closedBall s.center s.radius) := by
    exact s.backgroundContDiffOnOne
  have hpresenceC1 : ContDiffOn ℝ 1 s.presence
      (Metric.closedBall s.center s.radius) := by
    exact s.presenceContDiffOnOne
  have hbackgroundDeriv : ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.background (innerSL ℝ (s.backgroundGradient x)) x := by
    exact s.backgroundHasFDerivAt
  have hpresenceDeriv : ∀ x ∈ Metric.closedBall s.center s.radius,
      HasFDerivAt s.presence (innerSL ℝ (s.presenceGradient x)) x := by
    exact s.presenceHasFDerivAt
  let hvalley := per_stage_valley_global_existence_and_decay
      s.center s.radius s.gain s.presenceGain s.curvature
      s.backgroundCurvature s.gradientBound
      s.radius_pos s.gain_pos s.curvature_pos s.backgroundCurvature_nonneg
      s.gradientBound_nonneg s.gain_threshold s.background s.presence
      s.backgroundGradient s.presenceGradient s.backgroundHessian
      s.presenceHessian hbackgroundC1 hpresenceC1 hbackgroundDeriv
      hpresenceDeriv s.background_gradient_deriv
      s.presence_gradient_deriv s.background_hessian_lower
      s.presence_hessian_upper s.presence_center_stationary
      s.background_gradient_bound s.mobility s.sublevel s.gamma s.startTime
      s.initial s.initial_mem (fun x hx => s.closedLoopC1 x hx)
      s.sublevel_barrier s.sublevel_eq
      s.gamma_pos s.mobility_coercive
  let minimizer := Classical.choose hvalley
  have hminimizerData := Classical.choose_spec hvalley
  rcases hminimizerData with ⟨hminimizer, hmin, hunique, hdisplacement,
    hstationary, horbitExists⟩
  let orbit := Classical.choose horbitExists
  have horbitExists' := Classical.choose_spec horbitExists
  let localExtension := Classical.choose horbitExists'
  have horbitData := Classical.choose_spec horbitExists'
  rcases horbitData with ⟨hlocalExtension, hinitial, horbitODE,
    horbitSublevel, horbitDecay, horbitUnique⟩
  exact {
    minimizer := minimizer
    minimizer_interior := hminimizer
    minimizer_is_min := hmin
    minimizer_unique := hunique
    displacement_bound := hdisplacement
    stationary := hstationary
    positive_margin := by
      exact gain_threshold_implies_positive_margin s.radius s.gain
        s.presenceGain s.curvature s.backgroundCurvature s.gradientBound
        s.radius_pos s.gain_pos s.curvature_pos s.backgroundCurvature_nonneg
        s.gradientBound_nonneg s.gain_threshold |>.2.1
    orbit := orbit
    local_extension := localExtension
    local_extension_pos := hlocalExtension
    initial_condition := hinitial
    orbit_ode := horbitODE
    orbit_in_sublevel := horbitSublevel
    orbit_decay := horbitDecay
    orbit_unique := horbitUnique
  }

/-- The four conclusion groups of Theorem 21 for an averaged stage field:
unique interior valley, displacement/stationarity, an invariant global orbit
with its quantitative exponential rate, and the independent positive
information-capacity conclusion. The information law is explicit input; it is
not inferred from the valley dynamics. -/
theorem meanField_stage_theorem21_four_conclusions
    {L X G Y : Type*} [CompleteLattice L] [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (s : MeanFieldStageInput E) (D : Theorem21BranchContext L)
    (μ : MeasureTheory.Measure X) (mass : X → G → ℝ)
    (action : X → G → Y) (goalAbstraction : G → L)
    (haction_meas : ∀ g, Measurable (fun x => action x g))
    (hgoals_in_branch : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      goalAbstraction g ∈ D.branch)
    (hmass_nonneg_ae : ∀ᵐ x ∂μ, ∀ g, 0 ≤ mass x g)
    (hmass_sum_one_ae : ∀ᵐ x ∂μ, ∑ g : G, mass x g = 1)
    (hinjective_ae : ∀ᵐ x ∂μ, ∀ g, 0 < mass x g →
      ∀ g', action x g' = action x g → g' = g)
    (hmass_meas : ∀ g, MeasureTheory.AEStronglyMeasurable
      (fun x => mass x g) μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hinput_entropy_positive : 0 < conditionalGoalEntropy μ mass)
    (branchRepresentation : s.averagePresentation.Atom → L)
    (hbranchRepresentation_injective : Function.Injective branchRepresentation)
    (hbranchRepresentation_monotone : ∀ a b,
      s.averagePresentation.atomOrder.le a b → branchRepresentation a ≤ branchRepresentation b)
    (hbranch_eq_image : D.branch =
      branchRepresentation '' s.averagePresentation.sourceLayer)
    (hsymbolSupport_eq_image : D.symbolSupport =
      branchRepresentation '' s.averagePresentation.measureSupport)
    (hbranch_top : branchRepresentation s.averagePresentation.abstractTop = ⊤)
    (hbranch_lub : branchRepresentation s.averagePresentation.supportLub =
      sSup D.symbolSupport) :
    ∃ w : StageValleyWitness s.toStageValleySpec,
      (w.minimizer ∈ interior
        (Metric.closedBall s.center s.radius) ∧
        IsMinOn (stageEffectivePotential s.toStageValleySpec)
          (Metric.closedBall s.center s.radius) w.minimizer ∧
        (∀ y ∈ Metric.closedBall s.center s.radius,
          stageEffectivePotential s.toStageValleySpec y =
            stageEffectivePotential s.toStageValleySpec w.minimizer →
              y = w.minimizer)) ∧
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
            w.decayAmplitude * Real.exp
              (-w.decayRate * (t - s.startTime))) ∧
        (∀ t, s.startTime ≤ t →
          HasDerivAt w.orbit
            (-(s.mobility (w.orbit t)
              (s.backgroundGradient (w.orbit t) -
                (s.gain * s.presenceGain) • s.meanFieldGradient (w.orbit t)))) t)) ∧
      (conditionalGoalMutualInformation μ mass action =
        conditionalGoalEntropy μ mass ∧
        0 < conditionalGoalMutualInformation μ mass action ∧
        (∀ᵐ x ∂μ, ∀ g, 0 < mass x g → goalAbstraction g ∈ D.branch)) := by
  let stage := s.toStageValleySpec
  let w := chooseStageValley stage
  have hinfo := theorem21_branch_constrained_information_capacity D μ mass
    action goalAbstraction haction_meas hgoals_in_branch hmass_nonneg_ae
    hmass_sum_one_ae hinjective_ae hmass_meas hinput_entropy_positive
  refine ⟨w, ?_, ?_, ?_, hinfo⟩
  · exact ⟨w.minimizer_interior, w.minimizer_is_min, w.minimizer_unique⟩
  · exact ⟨w.displacement_bound, w.stationary, w.positive_margin⟩
  · constructor
    · exact w.initial_condition
    · constructor
      · intro t ht
        exact ⟨w.orbit_in_sublevel t ht, w.distance_decay t ht⟩
      · intro t ht
        exact w.orbit_ode_forward t ht

/-- Simultaneously select the stagewise minimizers and frozen trajectories
from individually verified global valley constructions.
日本語要約：段階ごとに構成した谷の証人を全段階にわたって選ぶ。 -/
noncomputable def chooseAllStageValleys {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → StageValleySpec E) :
    ∀ n, StageValleyWitness (stages n) :=
  fun n => chooseStageValley (stages n)

/-- Package the independently constructed stage witnesses in the exact
forward-orbit form used by the stagewise results: each selected orbit starts
at its stage's prescribed initial state, stays in the closed local region,
solves the closed-loop ODE for every forward time, and has an explicit
exponential distance estimate.
日本語要約：全段階の谷、軌道、指数減衰、ODE成立、閉球内滞在を一括して結論する。 -/
theorem all_stages_have_global_valley_orbits {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → StageValleySpec E) :
    ∃ witnesses : ∀ n, StageValleyWitness (stages n),
      (∀ n, (witnesses n).minimizer ∈
        interior (Metric.closedBall (stages n).center (stages n).radius) ∧
        IsMinOn
          (fun x => (stages n).background x -
            (stages n).gain * (stages n).presenceGain *
              (stages n).presence x)
          (Metric.closedBall (stages n).center (stages n).radius)
          (witnesses n).minimizer ∧
        (∀ y ∈ Metric.closedBall (stages n).center (stages n).radius,
          (stages n).background y -
              (stages n).gain * (stages n).presenceGain *
                (stages n).presence y =
            (stages n).background (witnesses n).minimizer -
              (stages n).gain * (stages n).presenceGain *
            (stages n).presence (witnesses n).minimizer →
            y = (witnesses n).minimizer)) ∧
      (∀ n, (witnesses n).orbit (stages n).startTime =
        (stages n).initial) ∧
      (∀ n, 0 ≤ (witnesses n).decayAmplitude ∧
        0 < (witnesses n).decayRate) ∧
      (∀ n t, (stages n).startTime ≤ t →
        dist ((witnesses n).orbit t) (witnesses n).minimizer ≤
          (witnesses n).decayAmplitude * Real.exp
            (-(witnesses n).decayRate * (t - (stages n).startTime))) ∧
      (∀ n t, (stages n).startTime ≤ t →
        HasDerivAt (witnesses n).orbit
          (-((stages n).mobility ((witnesses n).orbit t)
            ((stages n).backgroundGradient ((witnesses n).orbit t) -
              ((stages n).gain * (stages n).presenceGain) •
                (stages n).presenceGradient ((witnesses n).orbit t)))) t) ∧
      (∀ n t, (stages n).startTime ≤ t →
        (witnesses n).orbit t ∈
          Metric.closedBall (stages n).center (stages n).radius) := by
  refine ⟨chooseAllStageValleys stages, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(chooseAllStageValleys stages n).minimizer_interior,
      (chooseAllStageValleys stages n).minimizer_is_min,
      (chooseAllStageValleys stages n).minimizer_unique⟩
  · intro n
    exact (chooseAllStageValleys stages n).initial_condition
  · intro n
    exact ⟨(chooseAllStageValleys stages n).decayAmplitude_nonneg,
      (chooseAllStageValleys stages n).decayRate_pos⟩
  · intro n t ht
    exact (chooseAllStageValleys stages n).distance_decay t ht
  · intro n t ht
    exact (chooseAllStageValleys stages n).orbit_ode_forward t ht
  · intro n t ht
    exact (chooseAllStageValleys stages n).orbit_in_closedBall t ht

/-- Construct all Theorem 21/22 minimizers and frozen orbits directly from an
LUB-indexed family of mean-field stage inputs. This keeps every stage's
averaged field, mobility, local sublevel, and orbit in the same indexed data. -/
noncomputable def chooseAllMeanFieldStageValleys {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → MeanFieldStageInput E) :
    ∀ n, StageValleyWitness ((meanFieldStageSequence stages) n) :=
  chooseAllStageValleys (meanFieldStageSequence stages)

/-- The stagewise valley theorem applied to averaged fields rather than
atomwise reconstruction kernels. Each selected witness also carries the
unique minimizer and stationary-point proofs from Theorem 21. The strict
barrier and coercive mobility remain explicit H-stage conditions. -/
theorem all_mean_field_stages_have_global_valley_orbits {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (stages : ℕ → MeanFieldStageInput E) :
    ∃ witnesses : ∀ n,
      StageValleyWitness ((meanFieldStageSequence stages) n),
      (∀ n, (witnesses n).minimizer ∈ interior
        (Metric.closedBall (stages n).center (stages n).radius)) ∧
      (∀ n, ‖(witnesses n).minimizer - (stages n).center‖ ≤
        (stages n).gradientBound /
          ((stages n).gain * (stages n).presenceGain *
            (stages n).curvature - (stages n).backgroundCurvature)) ∧
      (∀ n t, (stages n).startTime ≤ t →
        (witnesses n).orbit t ∈ (stages n).sublevel ∧
        dist ((witnesses n).orbit t) (witnesses n).minimizer ≤
          (witnesses n).decayAmplitude * Real.exp
            (-(witnesses n).decayRate * (t - (stages n).startTime)) ∧
        HasDerivAt (witnesses n).orbit
          (-((meanFieldStageSequence stages n).mobility
              ((witnesses n).orbit t)
              ((meanFieldStageSequence stages n).backgroundGradient
                  ((witnesses n).orbit t) -
                ((meanFieldStageSequence stages n).gain *
                  (meanFieldStageSequence stages n).presenceGain) •
                  (meanFieldStageSequence stages n).presenceGradient
                    ((witnesses n).orbit t)))) t) := by
  refine ⟨chooseAllMeanFieldStageValleys stages, ?_, ?_, ?_⟩
  · intro n
    exact (chooseAllMeanFieldStageValleys stages n).minimizer_interior
  · intro n
    exact (chooseAllMeanFieldStageValleys stages n).displacement_bound
  · intro n t ht
    exact ⟨(chooseAllMeanFieldStageValleys stages n).orbit_in_sublevel t ht,
      (chooseAllMeanFieldStageValleys stages n).distance_decay t ht,
      (chooseAllMeanFieldStageValleys stages n).orbit_ode_forward t ht⟩

#print axioms meanField_stage_theorem21_four_conclusions
#print axioms all_mean_field_stages_have_global_valley_orbits


end Tomabechi.Theorem22
