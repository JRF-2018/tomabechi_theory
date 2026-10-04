import Theorem24_26_Model
import Tomabechi.Theorem27.Actuator
import Tomabechi.Examples.Theorem27_Operational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# 定理26/27の制御クラス拡張：線形ゲインによる境界

走行費用 `3r²`、割引率 `1`、自然ドリフト `-μr`、入力 `u=-Kr` の連続時間モデルを扱う。
無制限の非負ゲインでは費用の下限0は得られるが、非零初期値からは達成されない。
一方、`0≤K≤κ` に制限すると最大ゲインκが費用最小となる複数方策族になる。
定数ゲインの族に加え、連続および有界可測な時間依存ゲイン信号の全体についても、最大ゲインが
費用最小（`0≤k(t)≤1/2` のとき価値 `x²`）となることを証明し、24→26→27 の一般定理へ接続する。
任意の Borel フィードバックの閉ループ解の存在・一意性は扱わない（一意性が破れる例を末尾に置く）。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem26_27ControlClasses

open Filter MeasureTheory Set Topology Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model

/-- 初期値が非零の連続経路では、割引二次走行費の拡張実数積分が正。
費用が無限大となる経路もこの結論に含む。 -/
theorem continuous_path_discounted_cost_pos (r : ℝ → ℝ) (T : ℝ)
    (hr : Continuous r) (hrT : r T ≠ 0) :
    0 < ∫⁻ s, ENNReal.ofReal (Real.exp (-(s - T)) * (3 * r s ^ 2))
      ∂futureLebesgueMeasure T := by
  have hnear : ∀ᶠ s : ℝ in 𝓝 T, |r s - r T| < |r T| / 2 := by
    have hrad : 0 < |r T| / 2 := by positivity
    filter_upwards [hr.continuousAt.eventually (Metric.ball_mem_nhds (r T) hrad)] with s hs
    simpa [Real.dist_eq, Set.mem_setOf_eq] using hs
  obtain ⟨δ, hδ, hinterval⟩ := Metric.mem_nhds_iff.mp hnear
  have hδpos : 0 < δ := by linarith
  have hpath (s : ℝ) (hs : s ∈ Set.Ioo T (T + δ)) : |r T| / 2 ≤ |r s| := by
    have hsball : s ∈ Metric.ball T δ := Metric.mem_ball.mpr (by
      have hsT : T ≤ s := le_of_lt hs.1
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hsT)]
      have hsupper : s - T < δ := by linarith [hs.2]
      exact hsupper)
    have hdiff : |r s - r T| < |r T| / 2 := hinterval hsball
    have htri : |r T| ≤ |r T - r s| + |r s| := by
      calc
        |r T| = |(r T - r s) + r s| := by congr 1 <;> ring
        _ ≤ |r T - r s| + |r s| := abs_add_le _ _
    rw [abs_sub_comm] at hdiff
    linarith
  let f : ℝ → ENNReal := fun s => ENNReal.ofReal (Real.exp (-(s - T)) * (3 * r s ^ 2))
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_id.sub continuous_const |>.neg)).mul
        (continuous_const.mul (hr.pow 2))).measurable
  rw [MeasureTheory.lintegral_pos_iff_support hf]
  have hsubset : Set.Ioo T (T + δ) ⊆ Function.support f := by
    intro s hs
    change f s ≠ 0
    have hrs := hpath s hs
    have hsq : 0 < r s ^ 2 := by
      have : r s ≠ 0 := by
        intro hz
        have habs : 0 < |r T| := abs_pos.mpr hrT
        rw [hz, abs_zero] at hrs
        have habs : 0 < |r T| / 2 := by positivity
        linarith
      positivity
    have harg : 0 < Real.exp (-(s - T)) * (3 * r s ^ 2) := by
      apply mul_pos (Real.exp_pos _)
      apply mul_pos (by norm_num)
      exact hsq
    change ENNReal.ofReal _ ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr harg)
  have hmeasure : 0 < futureLebesgueMeasure T (Set.Ioo T (T + δ)) := by
    rw [futureLebesgueMeasure, MeasureTheory.Measure.restrict_apply]
    · have hset : Set.Ioo T (T + δ) ∩ Set.Ici T = Set.Ioo T (T + δ) := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ici]
        constructor
        · rintro ⟨⟨hT, hupper⟩, _⟩
          exact ⟨hT, hupper⟩
        · intro hs
          exact ⟨hs, le_of_lt hs.1⟩
      rw [hset, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    · exact measurableSet_Ioo
  exact lt_of_lt_of_le hmeasure (MeasureTheory.measure_mono hsubset)

/-- 共通の非零初期値を持つ連続経路族では、どの経路も費用ゼロを達成しない。
費用を任意に小さくできるなら、下限は0だが達成されない。 -/
theorem continuous_family_zero_infimum_not_attained
    {P : Type*} (path : P → ℝ → ℝ) (T : ℝ)
    (cost : P → ENNReal)
    (hcontinuous : ∀ p, Continuous (path p))
    (hinitial : ∀ p, path p T ≠ 0)
    (hcost : ∀ p, cost p = ∫⁻ s,
      ENNReal.ofReal (Real.exp (-(s - T)) * (3 * path p s ^ 2))
        ∂futureLebesgueMeasure T)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p, cost p < ENNReal.ofReal ε) :
    (∀ ε : ℝ, 0 < ε → ∃ p, cost p < ENNReal.ofReal ε) ∧
      (∀ p, 0 < cost p) := by
  refine ⟨hsmall, ?_⟩
  intro p
  rw [hcost p]
  exact continuous_path_discounted_cost_pos (path p) T (hcontinuous p) (hinitial p)

/-- 自然ドリフトと線形フィードバックを合わせた減衰率。 -/
def rate (μ K : ℝ) : ℝ := μ + K

/-- `r' = -(μ+K)r` の初期時刻Tからの実軌道。 -/
def orbit (r₀ μ K T s : ℝ) : ℝ := r₀ * Real.exp (-(rate μ K) * (s - T))

/-- 割引走行費 `3r²` の積分。 -/
def cost (r₀ μ K T : ℝ) : ℝ :=
  ∫ s, theorem26DiscountWeight 1 T s * (3 * orbit r₀ μ K T s ^ 2)
    ∂futureLebesgueMeasure T

/-- 非自明な方策モデルにおける、許容される有界な定数ゲイン。 -/
abbrev BoundedGain := {K : ℝ // 0 ≤ K ∧ K ≤ 1 / 2}

/-- 各有界ゲインは、実際の Borel マルコフフィードバックとして表される。 -/
def boundedGainFeedback (K : BoundedGain) : BorelMarkovFeedback ℝ ℝ :=
  ⟨fun p => -K.val * p.2, by fun_prop⟩

/-- 有界族は少なくとも 2 つの異なるフィードバック則を含む。 -/
theorem bounded_gain_family_nontrivial :
    boundedGainFeedback ⟨0, by norm_num⟩ ≠
      boundedGainFeedback ⟨1 / 2, by norm_num⟩ := by
  intro h
  have heq := congrArg (fun π : BorelMarkovFeedback ℝ ℝ => π.action (0, 1)) h
  norm_num [boundedGainFeedback] at heq

theorem orbit_initial (r₀ μ K T : ℝ) : orbit r₀ μ K T T = r₀ := by
  simp [orbit]

theorem orbit_solves_ode (r₀ μ K T s : ℝ) :
    HasDerivAt (fun u => orbit r₀ μ K T u)
      (-(rate μ K) * orbit r₀ μ K T s) s := by
  have hlin : HasDerivAt (fun u : ℝ => -(rate μ K) * (u - T)) (-(rate μ K)) s := by
    have h := (hasDerivAt_id s).sub_const T |>.const_mul (-(rate μ K))
    convert h using 1 <;> simp [sub_eq_add_neg]
  have he := (HasDerivAt.exp hlin).const_mul r₀
  simpa [orbit, rate, mul_comm, mul_left_comm, mul_assoc] using he

theorem cost_eq (r₀ μ K T : ℝ) (hα : 0 < 1 + 2 * rate μ K) :
    cost r₀ μ K T = 3 * r₀ ^ 2 / (1 + 2 * rate μ K) := by
  unfold cost
  have hpoint (s : ℝ) : theorem26DiscountWeight 1 T s *
      (3 * orbit r₀ μ K T s ^ 2) =
      (3 * r₀ ^ 2) * Real.exp (-(1 + 2 * rate μ K) * (s - T)) := by
    rw [theorem26DiscountWeight, orbit]
    rw [show (r₀ * Real.exp (-(rate μ K) * (s - T))) ^ 2 =
      r₀ ^ 2 * Real.exp (2 * (-(rate μ K) * (s - T))) by
        rw [mul_pow]
        rw [show Real.exp (-(rate μ K) * (s - T)) ^ 2 =
          Real.exp (-(rate μ K) * (s - T) + -(rate μ K) * (s - T)) by
            calc
              _ = Real.exp _ * Real.exp _ := by ring
              _ = Real.exp (_ + _) := by rw [← Real.exp_add]]
        congr 1 <;> ring]
    rw [show -1 * (s - T) = -(s - T) by ring]
    calc
      Real.exp (-(s - T)) * (3 * (r₀ ^ 2 *
          Real.exp (2 * (-(rate μ K) * (s - T))))) =
        3 * r₀ ^ 2 * Real.exp (-(s - T) + 2 * (-(rate μ K) * (s - T))) := by
          calc
            _ = 3 * r₀ ^ 2 * (Real.exp (-(s - T)) *
                Real.exp (2 * (-(rate μ K) * (s - T)))) := by ring
            _ = 3 * r₀ ^ 2 * Real.exp (-(s - T) +
                2 * (-(rate μ K) * (s - T))) := by rw [← Real.exp_add]
      _ = 3 * r₀ ^ 2 * Real.exp (-(1 + 2 * rate μ K) * (s - T)) := by
          congr 2 <;> ring
  simp_rw [hpoint]
  calc
    (∫ s, (3 * r₀ ^ 2) * Real.exp (-(1 + 2 * rate μ K) * (s - T))
        ∂futureLebesgueMeasure T) =
      (3 * r₀ ^ 2) * (∫ s, Real.exp (-(1 + 2 * rate μ K) * (s - T))
        ∂futureLebesgueMeasure T) := by rw [integral_const_mul]
    _ = 3 * r₀ ^ 2 / (1 + 2 * rate μ K) := by
      rw [future_exp_integral hα T]
      field_simp

/-- 同じ初期値に対するコストは減衰率（従ってゲイン）とともに減る。 -/
theorem cost_antitone_gain (r₀ μ K₁ K₂ T : ℝ)
    (hμ : 0 ≤ μ) (hK₁ : 0 ≤ K₁) (hK₂ : K₁ ≤ K₂) :
    cost r₀ μ K₂ T ≤ cost r₀ μ K₁ T := by
  have hα₁ : 0 < 1 + 2 * rate μ K₁ := by dsimp [rate]; positivity
  have hα₂ : 0 < 1 + 2 * rate μ K₂ := by dsimp [rate]; nlinarith
  rw [cost_eq r₀ μ K₁ T hα₁, cost_eq r₀ μ K₂ T hα₂]
  have hden : 0 < 1 + 2 * rate μ K₁ := hα₁
  have hdenle : 1 + 2 * rate μ K₁ ≤ 1 + 2 * rate μ K₂ := by
    dsimp [rate]; nlinarith
  have hinv : (1 + 2 * rate μ K₂)⁻¹ ≤ (1 + 2 * rate μ K₁)⁻¹ := by
    simpa only [one_div] using (one_div_le_one_div_of_le hden hdenle)
  have hsquare : 0 ≤ 3 * r₀ ^ 2 := by positivity
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hsquare

/-- 有限ゲイン上限の定数方策族では、最大ゲインκが費用最小である。 -/
theorem bounded_constant_gain_optimal (r₀ μ κ K T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hKκ : K ≤ κ) :
    cost r₀ μ κ T ≤ cost r₀ μ K T :=
  cost_antitone_gain r₀ μ K κ T hμ hK hKκ

/-- 表示した状態経路は、自然ドリフト `-μr` とゲインフィードバック `u=-Kr` の閉ループ解である。 -/
theorem gainFeedback_ode (r₀ μ K T s : ℝ) :
    HasDerivAt (fun u => orbit r₀ μ K T u)
      (-μ * orbit r₀ μ K T s + (-K * orbit r₀ μ K T s)) s := by
  convert orbit_solves_ode r₀ μ K T s using 1 <;> dsimp [rate] <;> ring

/-- μ=κ=1/2 では、最大ゲイン方策の割引費用は既存の `r₀²` と一致する。 -/
theorem half_gain_cost_is_square (r₀ T : ℝ) :
    cost r₀ (1 / 2) (1 / 2) T = r₀ ^ 2 := by
  rw [cost_eq r₀ (1 / 2) (1 / 2) T (by norm_num [rate])]
  norm_num [rate]

/-- 連続体 `0≤K≤1/2` のどの方策も費用は少なくとも `r₀²` であり、自然ドリフトが `μ=1/2` のとき端点のゲイン `K=1/2` がそれを達成する。 -/
theorem bounded_family_value_attained_and_minimal (r₀ T : ℝ) :
    cost r₀ (1 / 2) (1 / 2) T = r₀ ^ 2 ∧
      ∀ K : BoundedGain, r₀ ^ 2 ≤ cost r₀ (1 / 2) K.val T := by
  refine ⟨half_gain_cost_is_square r₀ T, ?_⟩
  intro K
  have hmin := bounded_constant_gain_optimal r₀ (1 / 2) (1 / 2) K.val T
    (by norm_num) (by norm_num) K.property.1 K.property.2
  rw [half_gain_cost_is_square] at hmin
  exact hmin

/-- 許容される有界ゲイン方策に沿った走行苦。 -/
def boundedPolicyRunningValue (K : BoundedGain) (x T s : ℝ) : ℝ :=
  3 * orbit x (1 / 2) K.val T s ^ 2

/-- 有界ゲイン方策はすべて、価値ゼロの目標集合でちょうど将来の苦がゼロになる。これは非自明な族について 26 の PZS／零価値集合の対応を検証するものである。 -/
theorem bounded_family_pzs_iff_value_zero (x T : ℝ) :
    FeedbackPZS (fun (_ : BoundedGain) (_x : ℝ) (_T : ℝ) => True)
      futureLebesgueMeasure
      (fun K y t s => boundedPolicyRunningValue K y t s) x T ↔ x ^ 2 = 0 := by
  constructor
  · rintro ⟨K, _, hzero⟩
    by_contra hx
    have hμ : futureLebesgueMeasure T Set.univ ≠ 0 := by
      rw [futureLebesgueMeasure, MeasureTheory.Measure.restrict_apply
        MeasurableSet.univ]
      simp [Real.volume_Ici]
    have hpositive : ∀ᵐ s ∂futureLebesgueMeasure T,
        0 < boundedPolicyRunningValue K x T s := by
      filter_upwards with s
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hx
        simp [hx0]
      have hpath : orbit x (1 / 2) K.val T s ≠ 0 := by
        apply mul_ne_zero hx0
        exact Real.exp_ne_zero _
      dsimp [boundedPolicyRunningValue]
      positivity
    exact (not_ae_zero_of_ae_strictlyPositive
      (futureLebesgueMeasure T) (boundedPolicyRunningValue K x T)
      hμ hpositive) hzero
  · intro hx
    have hx0 : x = 0 := (sq_eq_zero_iff).1 hx
    refine ⟨⟨0, by norm_num⟩, trivial, ?_⟩
    filter_upwards with s
    simp [boundedPolicyRunningValue, orbit, hx0]

/-- 有界な動径ゲインの連続体は、2 次元運用モデルと同じ零価値の環をもつ。非 PZS の状態は、既存の 27-A 適用で使われた運用上の無明状態と一致する。 -/
theorem bounded_family_target_matches_operational (x : Tomabechi.Examples.Theorem27Op.E2)
    (T : ℝ) :
    (¬ FeedbackPZS (fun (_ : BoundedGain) (_y : ℝ) (_t : ℝ) => True)
      futureLebesgueMeasure
      (fun K y t s => boundedPolicyRunningValue K y t s) (x 0) T) ↔
      x ∉ Tomabechi.Examples.Theorem27Op.ringE T := by
  rw [bounded_family_pzs_iff_value_zero]
  rw [Tomabechi.Examples.Theorem27Op.ringE_eq]
  simp [sq_eq_zero_iff]

/-- 有界ゲイン族に永久苦痛ゼロの方策がなければ、対応する 27 の運用モデルは零目標の外にとどまり、作動量の寄与は a.e. で正になる。幾何的な目標と 27 の作動に関する主張は、族全体の PZS 分類を通して結びつく。 -/
theorem bounded_family_ignorance_has_27_action
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T)
    (hnot : ¬ FeedbackPZS (fun (_ : BoundedGain) (_y : ℝ) (_t : ℝ) => True)
      futureLebesgueMeasure
      (fun K y t s => boundedPolicyRunningValue K y t s) (x 0) T) :
    (∀ t, Tomabechi.Examples.Theorem27Op.flowE x T t ∉
      Tomabechi.Examples.Theorem27Op.ringE t) ∧
      ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
        0 < -(inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            (Tomabechi.Examples.Theorem27Op.u0E x T t -
              Tomabechi.Examples.Theorem27Op.utrE x T t))) := by
  have hxnot : x 0 ≠ 0 := by
    intro hx0
    apply hnot
    apply (bounded_family_pzs_iff_value_zero (x 0) T).2
    simp [hx0]
  exact Tomabechi.Examples.Theorem27Op.ignorance_gives_action x T hT hxnot

/-- 規定の区間に各点で値をとる連続信号で表される、時間依存ゲイン。連続信号は、計画にある有界可測制御の厳密な部分族を与える。 -/
abbrev ContinuousGainSignal :=
  {k : C(ℝ, ℝ) // ∀ t, 0 ≤ k t ∧ k t ≤ 1 / 2}

/-- 連続信号と同じ各点の上下界をもつ、有界可測ゲイン。可測制御版のモデルが要求する信号のクラスである。 -/
abbrev BoundedMeasurableGainSignal :=
  {k : ℝ → ℝ // Measurable k ∧ ∀ t, 0 ≤ k t ∧ k t ≤ 1 / 2}

/-- 有界可測な実関数は、すべての有限区間で可積分である。コンパクト区間は有限ルベーグ測度を持ち、ゲインはそこで定数 `1/2` により抑えられる。 -/
theorem boundedMeasurableGain_intervalIntegrable (k : BoundedMeasurableGainSignal)
    (T s : ℝ) : IntervalIntegrable k.1 MeasureTheory.volume T s := by
  rw [intervalIntegrable_iff]
  let μ := MeasureTheory.volume.restrict (Set.uIoc T s)
  have hfinite : MeasureTheory.volume (Set.uIoc T s) < ⊤ := by
    apply lt_of_le_of_lt (MeasureTheory.measure_mono Set.uIoc_subset_uIcc)
    exact isCompact_uIcc.measure_lt_top
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hfinite
  have hconst : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := integrable_const _
  refine hconst.mono' (k.2.1.stronglyMeasurable.aestronglyMeasurable) ?_
  filter_upwards with t
  have hk := k.2.2 t
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- 有界可測ゲインは局所可積分である。各コンパクト集合上で、有限ルベーグ測度と一様な上界が可積分性を与える。 -/
theorem boundedMeasurableGain_locallyIntegrable (k : BoundedMeasurableGainSignal) :
    LocallyIntegrable k.1 MeasureTheory.volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let μ := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hK.measure_lt_top
  have hc : Integrable (fun _ : ℝ => (1 / 2 : ℝ)) μ := integrable_const _
  have hk := hc.mono' (k.2.1.stronglyMeasurable.aestronglyMeasurable) ?_
  · exact hk
  · filter_upwards with t
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(k.2.2 t).1], by linarith [(k.2.2 t).2]⟩

/-- 有界可測ゲインはいずれも、本物の Borel マルコフフィードバック `u(t,r)=-k(t)r` を定める。 -/
def measurableGainFeedback (k : BoundedMeasurableGainSignal) :
    BorelMarkovFeedback ℝ ℝ :=
  ⟨fun q => -(k.1 q.1) * q.2, by
    exact (k.2.1.comp measurable_fst).neg.mul measurable_snd⟩

/-- 開始時刻からの累積可測ゲイン。 -/
def measurableAccumulatedGain (k : BoundedMeasurableGainSignal) (T s : ℝ) : ℝ :=
  ∫ u in T..s, k.1 u

/-- ルベーグ積分は、前向き区間でゲインの各点評価を保つ。 -/
theorem measurableAccumulatedGain_bounds (k : BoundedMeasurableGainSignal)
    (T s : ℝ) (hTs : T ≤ s) :
    0 ≤ measurableAccumulatedGain k T s ∧
      measurableAccumulatedGain k T s ≤ (1 / 2) * (s - T) := by
  have hkint := boundedMeasurableGain_intervalIntegrable k T s
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hmax : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hlo := intervalIntegral.integral_mono_on hTs hzero hkint
    (fun u _ => (k.2.2 u).1)
  have hhi := intervalIntegral.integral_mono_on hTs hkint hmax
    (fun u _ => (k.2.2 u).2)
  constructor
  · simpa [measurableAccumulatedGain] using hlo
  · calc
      measurableAccumulatedGain k T s ≤ (s - T) * (1 / 2) := by
        simpa [measurableAccumulatedGain, intervalIntegral.integral_const] using hhi
      _ = (1 / 2) * (s - T) := by ring

/-- 有界可測ゲインに対する明示的な候補経路。a.e. の ODE の性質は、後の `measurableGainOrbit_ae_ode` で与える。 -/
def measurableGainOrbit (x : ℝ) (k : BoundedMeasurableGainSignal) (T s : ℝ) : ℝ :=
  x * Real.exp (-((1 / 2) * (s - T) + measurableAccumulatedGain k T s))

theorem measurableGainOrbit_initial (x : ℝ) (k : BoundedMeasurableGainSignal) (T : ℝ) :
    measurableGainOrbit x k T T = x := by
  simp [measurableGainOrbit, measurableAccumulatedGain]

/-- 有界可測信号の軌道は、閉ループ ODE をほとんど至るところ満たす。累積ゲインの導関数がゲインそのものであることは、区間積分についてのルベーグの微分定理による。 -/
theorem measurableGainOrbit_ae_ode (x : ℝ) (k : BoundedMeasurableGainSignal) (T : ℝ) :
    ∀ᵐ s : ℝ, HasDerivAt (fun u => measurableGainOrbit x k T u)
      (-(1 / 2 + k.1 s) * measurableGainOrbit x k T s) s := by
  have hder := LocallyIntegrable.ae_hasDerivAt_integral
    (boundedMeasurableGain_locallyIntegrable k)
  filter_upwards [hder] with s hs
  have hacc : HasDerivAt (fun u => measurableAccumulatedGain k T u) (k.1 s) s := by
    simpa [measurableAccumulatedGain] using hs T
  have htime : HasDerivAt (fun u : ℝ => (1 / 2) * (u - T)) (1 / 2) s := by
    convert ((hasDerivAt_id s).sub_const T).const_mul (1 / 2) using 1
    · funext u
      dsimp [id]
    · ring
  have harg : HasDerivAt
      (fun u => -((1 / 2) * (u - T) + measurableAccumulatedGain k T u))
      (-(1 / 2 + k.1 s)) s := by
    convert (htime.add hacc).neg using 1 <;> simp only [one_div] <;> ring
  have hexp := (HasDerivAt.exp harg).const_mul x
  simpa [measurableGainOrbit, mul_comm, mul_left_comm, mul_assoc] using hexp

/-- 明示的な軌道は、各コンパクトな前向き区間で絶対連続である。その指数を総減衰率 `1/2+k` の区間積分とみなし、その原始関数は絶対連続である。 -/
theorem measurableGainOrbit_absolutelyContinuousOnInterval (x : ℝ)
    (k : BoundedMeasurableGainSignal) (T s : ℝ) (hTs : T ≤ s) :
    AbsolutelyContinuousOnInterval (fun u => measurableGainOrbit x k T u) T s := by
  have hprim : AbsolutelyContinuousOnInterval
      (fun u => measurableAccumulatedGain k T u) T s :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (boundedMeasurableGain_intervalIntegrable k T s) (c := T) (by
        rw [uIcc_of_le hTs]
        exact left_mem_Icc.mpr hTs)
  have hconstInt : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ))
      MeasureTheory.volume T s := continuous_const.intervalIntegrable T s
  have hconstPrim : AbsolutelyContinuousOnInterval
      (fun u => ∫ v in T..u, (1 / 2 : ℝ)) T s :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      hconstInt (c := T) (by
        rw [uIcc_of_le hTs]
        exact left_mem_Icc.mpr hTs)
  have hlinearEq : Set.EqOn (fun u : ℝ => ∫ v in T..u, (1 / 2 : ℝ))
      (fun u => (1 / 2) * (u - T)) (uIcc T s) := by
    intro u hu
    change ∫ v in T..u, (1 / 2 : ℝ) = (1 / 2) * (u - T)
    rw [intervalIntegral.integral_const]
    ring
  have hlinear : AbsolutelyContinuousOnInterval
      (fun u : ℝ => (1 / 2) * (u - T)) T s := hconstPrim.congr hlinearEq
  have harg : AbsolutelyContinuousOnInterval
      (fun u => -((1 / 2) * (u - T) + measurableAccumulatedGain k T u)) T s :=
    (hlinear.add hprim).neg
  have hexpLip : LipschitzOnWith 1 Real.exp (Set.Iic (0 : ℝ)) := by
    refine (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f := Real.exp) (s := Set.Iic (0 : ℝ))
      (f' := fun z : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (Real.exp z))
      (C := 1) ?_ ?_
    · intro z hz
      simpa only [Function.comp_def, id_eq, mul_one] using
        ((HasDerivAt.exp (hasDerivAt_id z)).hasDerivWithinAt).hasFDerivWithinAt
    · intro z hz
      rw [ContinuousLinearMap.nnnorm_toSpanSingleton]
      have hreal : (‖Real.exp z‖₊ : ℝ) ≤ 1 := by
        rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg z)]
        exact Real.exp_le_one_iff.mpr hz
      exact_mod_cast hreal
  have hexpMaps : MapsTo
      (fun u => -((1 / 2) * (u - T) + measurableAccumulatedGain k T u))
      (uIcc T s) (Set.Iic 0) := by
    intro u hu
    rw [uIcc_of_le hTs] at hu
    have hacc := measurableAccumulatedGain_bounds k T u hu.1
    change -((1 / 2) * (u - T) + measurableAccumulatedGain k T u) ≤ 0
    nlinarith [hacc.1]
  have hexpAC := hexpLip.comp_absolutelyContinuousOnInterval hexpMaps harg
  simpa [Function.comp_def, measurableGainOrbit] using hexpAC.const_mul x

/-- 再開時刻で原始関数を分割しても同じ明示経路になる。証明は区間可積分性と区間積分の加法性だけを使う。 -/
theorem measurableAccumulatedGain_add (k : BoundedMeasurableGainSignal)
    (T u s : ℝ) :
    measurableAccumulatedGain k T s =
      measurableAccumulatedGain k T u + measurableAccumulatedGain k u s := by
  symm
  exact intervalIntegral.integral_add_adjacent_intervals
    (boundedMeasurableGain_intervalIntegrable k T u)
    (boundedMeasurableGain_intervalIntegrable k u s)

/-- 上界 `1/2` のゲインの原始関数は、大域的に `1/2`-Lipschitz である。これにより、経路が始点より前の時刻でも連続であることも得られる。 -/
theorem measurableAccumulatedGain_lipschitz (k : BoundedMeasurableGainSignal)
    (T : ℝ) : LipschitzWith (Real.toNNReal (1 / 2))
      (measurableAccumulatedGain k T) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hdiff : measurableAccumulatedGain k T s - measurableAccumulatedGain k T t =
      measurableAccumulatedGain k t s := by
    have hsplit := measurableAccumulatedGain_add k T t s
    dsimp [measurableAccumulatedGain] at hsplit ⊢
    linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := k.1) (a := t) (b := s) (C := 1 / 2) (fun u _ => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(k.2.2 u).1], by linarith [(k.2.2 u).2]⟩)
  have hreal : |measurableAccumulatedGain k T s - measurableAccumulatedGain k T t| ≤
      (1 / 2 : ℝ) * |s - t| := by
    rw [hdiff, ← Real.norm_eq_abs]
    exact hnorm
  rw [Real.dist_eq, Real.dist_eq]
  have hcoef : ((Real.toNNReal (1 / 2 : ℝ) : NNReal) : ℝ) = (1 / 2 : ℝ) := by
    exact Real.coe_toNNReal (1 / 2 : ℝ) (by norm_num)
  rw [hcoef]
  exact hreal

/-- 有界可測信号の軌道は、累積ゲインが Lipschitz なので実数直線全体で連続である。 -/
theorem measurableGainOrbit_continuous (x : ℝ) (k : BoundedMeasurableGainSignal)
    (T : ℝ) : Continuous (measurableGainOrbit x k T) := by
  have hacc : Continuous (measurableAccumulatedGain k T) :=
    (measurableAccumulatedGain_lipschitz k T).continuous
  have hlin : Continuous (fun s : ℝ => (1 / 2) * (s - T)) := by fun_prop
  have hexp : Continuous (fun s : ℝ => Real.exp
      (-((1 / 2) * (s - T) + measurableAccumulatedGain k T s))) := by
    exact Real.continuous_exp.comp (hlin.add hacc).neg
  convert hexp.const_mul x using 1
  ext s
  simp [measurableGainOrbit]

/-! ### 定理24の有界可測ゲイン方策族 -/

/-- 定数の最大可測信号。 -/
def maximalMeasurableGain : BoundedMeasurableGainSignal :=
  ⟨fun _ => 1 / 2, measurable_const, by intro t; norm_num⟩

/-- 可測な有界ゲイン制御に対する割引走行費。 -/
def measurableGainDiscountedCost (x : ℝ) (k : BoundedMeasurableGainSignal)
    (T s : ℝ) : ℝ :=
  theorem26DiscountWeight 1 T s * (3 * (measurableGainOrbit x k T s) ^ 2)

/-- 最大信号は、スカラーの指数流を再現する。 -/
theorem maximalMeasurableGain_orbit (x T s : ℝ) :
    measurableGainOrbit x maximalMeasurableGain T s = orbit x (1 / 2) (1 / 2) T s := by
  unfold measurableGainOrbit maximalMeasurableGain measurableAccumulatedGain orbit rate
  simp only
  rw [intervalIntegral.integral_const]
  congr 2
  ring

abbrev MeasurableSignalPolicy := NonnegativeTimeBorelMarkovFeedback ℝ ℝ

/-- 有界可測ゲインのフィードバックを、方策の非負時間領域に制限する。 -/
def measurableSignalPolicy (k : BoundedMeasurableGainSignal) : MeasurableSignalPolicy :=
  ⟨fun q => -(k.1 q.1.1) * q.2, by
    exact (k.2.1.comp (measurable_subtype_coe.comp measurable_fst)).neg.mul measurable_snd⟩

/-- マルコフ方策が、有界可測な時間依存ゲインから生成されるとき、この族に属する。 -/
def measurableSignalPolicyAdmissible (π : MeasurableSignalPolicy) : Prop :=
  ∃ k : BoundedMeasurableGainSignal, ∀ q : Set.Ici (0 : ℝ) × ℝ,
    π.action q = -(k.1 q.1.1) * q.2

/-- 許容方策に対して、有界可測ゲインの代表を選ぶ。フォールバックによって、すべての Borel フィードバックについて軌道が定義される。 -/
noncomputable def measurablePolicySignal (π : MeasurableSignalPolicy) :
    BoundedMeasurableGainSignal := by
  classical
  exact if h : measurableSignalPolicyAdmissible π then Classical.choose h
    else maximalMeasurableGain

theorem measurablePolicySignal_spec (π : MeasurableSignalPolicy)
    (hπ : measurableSignalPolicyAdmissible π) (t : ℝ) (ht : 0 ≤ t) :
    π.action (⟨⟨t, ht⟩, (1 : ℝ)⟩) = -(measurablePolicySignal π).1 t := by
  classical
  have hrep := Classical.choose_spec hπ
  have h := hrep ⟨⟨t, ht⟩, (1 : ℝ)⟩
  simpa [measurablePolicySignal, hπ] using h

abbrev MeasurableMultiSourcePolicy (a : SourceAbstraction) : Type :=
  match a with
  | false => PUnit
  | true => MeasurableSignalPolicy

noncomputable def measurableMultiSourceTrajectory :
    (a : SourceAbstraction) → MeasurableMultiSourcePolicy a →
      SourceState a → ℝ → ℝ → SourceState a
  | false, _, x, _, _ => x
  | true, π, x, T, s => measurableGainOrbit x (measurablePolicySignal π) T s

def measurableMultiSourceRunningCost :
    (a : SourceAbstraction) → MeasurableMultiSourcePolicy a →
      SourceState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, y, _ => 3 * y ^ 2

def measurableMultiSourceAdmissible :
    (a : SourceAbstraction) → MeasurableMultiSourcePolicy a →
      SourceState a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, _, _ => measurableSignalPolicyAdmissible π

def measurableMultiSourceValue :
    (a : SourceAbstraction) → SourceState a → ℝ → ℝ
  | false, _, T => lowerValue T
  | true, x, _ => x ^ 2

def measurableMultiSourceOptimalPolicy :
    (a : SourceAbstraction) → SourceState a → ℝ → MeasurableMultiSourcePolicy a
  | false, _, _ => PUnit.unit
  | true, _, _ => measurableSignalPolicy maximalMeasurableGain

theorem measurablePolicySignal_eq_witness_future (π : MeasurableSignalPolicy)
    (k : BoundedMeasurableGainSignal)
    (hπ : ∀ q : Set.Ici (0 : ℝ) × ℝ,
      π.action q = -(k.1 q.1.1) * q.2)
    (t : ℝ) (ht : 0 ≤ t) : (measurablePolicySignal π).1 t = k.1 t := by
  have hselected := measurablePolicySignal_spec π ⟨k, hπ⟩ t ht
  have hw := hπ ⟨⟨t, ht⟩, (1 : ℝ)⟩
  linarith

theorem measurableAccumulatedGain_eq_of_future_agreement
    (k₁ k₂ : BoundedMeasurableGainSignal) (T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    measurableAccumulatedGain k₁ T s = measurableAccumulatedGain k₂ T s := by
  unfold measurableAccumulatedGain
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hTs] at ht
  exact hfuture t (le_trans hT ht.1)

theorem measurableGainOrbit_eq_of_future_agreement (x T s : ℝ)
    (k₁ k₂ : BoundedMeasurableGainSignal) (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    measurableGainOrbit x k₁ T s = measurableGainOrbit x k₂ T s := by
  unfold measurableGainOrbit
  rw [measurableAccumulatedGain_eq_of_future_agreement k₁ k₂ T s hT hTs hfuture]

theorem measurableMaxPolicy_future_orbit (x T s : ℝ) (hT : 0 ≤ T) (hTs : T ≤ s) :
    measurableGainOrbit x
      (measurablePolicySignal (measurableSignalPolicy maximalMeasurableGain)) T s =
      measurableGainOrbit x maximalMeasurableGain T s := by
  apply measurableGainOrbit_eq_of_future_agreement x T s _ _ hT hTs
  intro t ht
  have hspec := measurablePolicySignal_spec
    (measurableSignalPolicy maximalMeasurableGain)
    ⟨maximalMeasurableGain, fun _ => rfl⟩ t ht
  simpa [measurableSignalPolicy] using hspec.symm

theorem measurableMaxPolicy_trajectory_ae (x T : ℝ) (hT : 0 ≤ T) :
    (fun s => measurableGainOrbit x
      (measurablePolicySignal (measurableSignalPolicy maximalMeasurableGain)) T s) =ᵐ[
        futureLebesgueMeasure T] (fun s => measurableGainOrbit x maximalMeasurableGain T s) := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
  exact measurableMaxPolicy_future_orbit x T s hT hs

theorem measurableGainOrbit_restart (x : ℝ) (k : BoundedMeasurableGainSignal)
    (T u s : ℝ) :
    measurableGainOrbit (measurableGainOrbit x k T u) k u s =
      measurableGainOrbit x k T s := by
  have hacc := measurableAccumulatedGain_add k T u s
  unfold measurableGainOrbit
  calc
    x * Real.exp (-((1 / 2) * (u - T) + measurableAccumulatedGain k T u)) *
        Real.exp (-((1 / 2) * (s - u) + measurableAccumulatedGain k u s)) =
      x * (Real.exp (-((1 / 2) * (u - T) + measurableAccumulatedGain k T u)) *
        Real.exp (-((1 / 2) * (s - u) + measurableAccumulatedGain k u s))) := by ring
    _ = x * Real.exp (-((1 / 2) * (u - T) + measurableAccumulatedGain k T u) +
        -((1 / 2) * (s - u) + measurableAccumulatedGain k u s)) := by rw [← Real.exp_add]
    _ = x * Real.exp (-((1 / 2) * (s - T) + measurableAccumulatedGain k T s)) := by
        congr 2
        linear_combination hacc

/-- 上界 `1/2` の可測ゲインは、状態を最大ゲイン経路より 0 に近づけることはできない。各点比較で、将来時刻について成り立つ。 -/
theorem measurableGainOrbit_sq_lower_bound (x : ℝ)
    (k : BoundedMeasurableGainSignal) (T s : ℝ) (hTs : T ≤ s) :
    (orbit x (1 / 2) (1 / 2) T s) ^ 2 ≤ (measurableGainOrbit x k T s) ^ 2 := by
  have hacc := measurableAccumulatedGain_bounds k T s hTs
  have hexp : -((1 / 2) * (s - T) + (1 / 2) * (s - T)) ≤
      -((1 / 2) * (s - T) + measurableAccumulatedGain k T s) := by
    nlinarith [hacc.2]
  have hexp' := Real.exp_le_exp.mpr hexp
  have hsqexp := (sq_le_sq₀ (Real.exp_nonneg _) (Real.exp_nonneg _)).2 hexp'
  have hprod := mul_le_mul_of_nonneg_left hsqexp (sq_nonneg x)
  have horbit : Real.exp (-(rate (1 / 2) (1 / 2)) * (s - T)) =
      Real.exp (-((1 / 2) * (s - T) + (1 / 2) * (s - T))) := by
    congr 1 <;> norm_num [rate] <;> ring
  calc
    (orbit x (1 / 2) (1 / 2) T s) ^ 2 =
        x ^ 2 * Real.exp (-((1 / 2) * (s - T) + (1 / 2) * (s - T))) ^ 2 := by
          simp only [orbit, horbit]
          ring
    _ ≤ x ^ 2 * Real.exp (-((1 / 2) * (s - T) +
          measurableAccumulatedGain k T s)) ^ 2 := hprod
    _ = (measurableGainOrbit x k T s) ^ 2 := by
          simp [measurableGainOrbit]
          ring

/-- 最大ゲイン経路は、すべての有界可測ゲイン信号の中で拡張実数の費用を最小にする。比較は各点で行うので、候補の可積分性を仮定する必要はない。 -/
theorem measurable_time_gain_cost_minimal (x : ℝ)
    (k : BoundedMeasurableGainSignal) (T : ℝ) :
    ENNReal.ofReal (x ^ 2) ≤
      ∫⁻ s, ENNReal.ofReal (measurableGainDiscountedCost x k T s)
        ∂futureLebesgueMeasure T := by
  have hbaseInt := discountedIntegrand_integrable x T
  have hbaseNonneg : 0 ≤ᵐ[futureLebesgueMeasure T] (discountedIntegrand x T) := by
    filter_upwards with s
    dsimp [discountedIntegrand, theorem26DiscountWeight, runningCost]
    positivity
  have hbaseLin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbaseInt hbaseNonneg
  have hbaseValue : ENNReal.ofReal (x ^ 2) =
      ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
        ∂futureLebesgueMeasure T := by
    rw [← value_eq_sq]
    exact hbaseLin
  have hpoint : ∀ᵐ s ∂futureLebesgueMeasure T,
      discountedIntegrand x T s ≤ measurableGainDiscountedCost x k T s := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
    have hsT : T ≤ s := hs
    have hsq := measurableGainOrbit_sq_lower_bound x k T s hsT
    have hflow : orbit x (1 / 2) (1 / 2) T s = flow x T s := by
      unfold orbit rate Tomabechi.Theorem24_26_Model.flow
      congr 1
      norm_num
    rw [hflow] at hsq
    have hexp : 0 ≤ theorem26DiscountWeight 1 T s := by
      rw [theorem26DiscountWeight]
      positivity
    rw [discountedIntegrand, measurableGainDiscountedCost,
      theorem26DiscountWeight, runningCost, flow]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq (by norm_num : 0 ≤ (3 : ℝ))) hexp
  calc
    ENNReal.ofReal (x ^ 2) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := hbaseValue
    _ ≤ ∫⁻ s, ENNReal.ofReal (measurableGainDiscountedCost x k T s)
          ∂futureLebesgueMeasure T := by
        apply MeasureTheory.lintegral_mono_ae
        filter_upwards [hpoint] with s hs
        exact ENNReal.ofReal_le_ofReal hs

/-- 最大の可測信号は価値 `x²` を達成し、すべての有界可測信号の費用はこれ以上である。 -/
theorem measurable_time_gain_value_attained_and_minimal (x T : ℝ) :
    (∫⁻ s, ENNReal.ofReal
        (measurableGainDiscountedCost x maximalMeasurableGain T s)
        ∂futureLebesgueMeasure T) = ENNReal.ofReal (x ^ 2) ∧
      ∀ k : BoundedMeasurableGainSignal,
        ENNReal.ofReal (x ^ 2) ≤
          ∫⁻ s, ENNReal.ofReal (measurableGainDiscountedCost x k T s)
            ∂futureLebesgueMeasure T := by
  refine ⟨?_, ?_⟩
  · have hbaseInt := discountedIntegrand_integrable x T
    have hbaseNonneg : 0 ≤ᵐ[futureLebesgueMeasure T] (discountedIntegrand x T) := by
      filter_upwards with s
      dsimp [discountedIntegrand, theorem26DiscountWeight, runningCost]
      positivity
    have hbaseValue : ENNReal.ofReal (x ^ 2) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := by
      rw [← value_eq_sq]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbaseInt hbaseNonneg
    have hcost : ∀ s, measurableGainDiscountedCost x maximalMeasurableGain T s =
        discountedIntegrand x T s := by
      intro s
      rw [measurableGainDiscountedCost, maximalMeasurableGain_orbit,
        discountedIntegrand, theorem26DiscountWeight, runningCost, flow, orbit, rate]
      ring
    have hlinEq :
        (∫⁻ s, ENNReal.ofReal
          (measurableGainDiscountedCost x maximalMeasurableGain T s)
          ∂futureLebesgueMeasure T) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards with s
      exact congrArg ENNReal.ofReal (hcost s)
    rw [hlinEq, ← hbaseValue]
  · intro k
    exact measurable_time_gain_cost_minimal x k T

/-- この族の有界可測ゲインは、初期状態がゼロのときに限り、永久に走行苦がゼロとなる。 -/
theorem measurable_family_pzs_iff_value_zero (x T : ℝ) :
    FeedbackPZS (fun (_ : BoundedMeasurableGainSignal) (_x : ℝ) (_T : ℝ) => True)
      futureLebesgueMeasure
      (fun k y t s => 3 * (measurableGainOrbit y k t s) ^ 2) x T ↔ x ^ 2 = 0 := by
  constructor
  · rintro ⟨k, _, hzero⟩
    by_contra hx
    have hμ : futureLebesgueMeasure T Set.univ ≠ 0 := by
      rw [futureLebesgueMeasure, MeasureTheory.Measure.restrict_apply
        MeasurableSet.univ]
      simp [Real.volume_Ici]
    have hpositive : ∀ᵐ s ∂futureLebesgueMeasure T,
        0 < 3 * (measurableGainOrbit x k T s) ^ 2 := by
      filter_upwards with s
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hx
        simp [hx0]
      have hpath : measurableGainOrbit x k T s ≠ 0 := by
        apply mul_ne_zero hx0
        exact Real.exp_ne_zero _
      positivity
    exact (not_ae_zero_of_ae_strictlyPositive
      (futureLebesgueMeasure T) (fun s => 3 * (measurableGainOrbit x k T s) ^ 2)
      hμ hpositive) hzero
  · intro hx
    have hx0 : x = 0 := (sq_eq_zero_iff).1 hx
    refine ⟨maximalMeasurableGain, trivial, ?_⟩
    filter_upwards with s
    simp [hx0, measurableGainOrbit]

/-- 有界可測ゲイン族の零価値集合は、対応する 27 のモデルの運用上の環に一致する。 -/
theorem measurable_family_target_matches_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) :
    (¬ FeedbackPZS (fun (_ : BoundedMeasurableGainSignal) (_y : ℝ) (_t : ℝ) => True)
      futureLebesgueMeasure
      (fun k y t s => 3 * (measurableGainOrbit y k t s) ^ 2) (x 0) T) ↔
      x ∉ Tomabechi.Examples.Theorem27Op.ringE T := by
  rw [measurable_family_pzs_iff_value_zero]
  rw [Tomabechi.Examples.Theorem27Op.ringE_eq]
  simp [sq_eq_zero_iff]

/-- 有界可測ゲイン族の永久苦痛ゼロの目標から離れていれば、対応する運用モデルは a.e. で正の行作動をもつ。27-A の適用が要求する条件を満たす。 -/
theorem measurable_family_ignorance_has_27_action
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T)
    (hnot : ¬ FeedbackPZS
      (fun (_ : BoundedMeasurableGainSignal) (_y : ℝ) (_t : ℝ) => True)
      futureLebesgueMeasure
      (fun k y t s => 3 * (measurableGainOrbit y k t s) ^ 2) (x 0) T) :
    (∀ t, Tomabechi.Examples.Theorem27Op.flowE x T t ∉
      Tomabechi.Examples.Theorem27Op.ringE t) ∧
      ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
        0 < -(inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            (Tomabechi.Examples.Theorem27Op.u0E x T t -
              Tomabechi.Examples.Theorem27Op.utrE x T t))) := by
  have hxnot : x 0 ≠ 0 := by
    intro hx0
    apply hnot
    apply (measurable_family_pzs_iff_value_zero (x 0) T).2
    simp [hx0]
  exact Tomabechi.Examples.Theorem27Op.ignorance_gives_action x T hT hxnot

/-- 時間依存ゲイン信号を、実際の Borel マルコフ入力則 `u(t,r)=-k(t)r` にする。 -/
def continuousGainFeedback (k : ContinuousGainSignal) :
    BorelMarkovFeedback ℝ ℝ :=
  ⟨fun q => -(k.1 q.1) * q.2, by fun_prop⟩

/-- 零の定数信号と最大の定数信号は、異なる Borel マルコフ方策を与える。許容信号族は、実際に 1 点より大きい。 -/
theorem continuous_gain_feedback_nontrivial :
    continuousGainFeedback ⟨ContinuousMap.const ℝ 0, by intro t; norm_num⟩ ≠
      continuousGainFeedback ⟨ContinuousMap.const ℝ (1 / 2), by intro t; norm_num⟩ := by
  intro h
  have heq := congrArg (fun π : BorelMarkovFeedback ℝ ℝ => π.action (0, 1)) h
  norm_num [continuousGainFeedback] at heq

/-- 連続信号は、`[0,∞)` 上の方策が決して見ることのできない、時刻 0 より前の値を持ちうる。この証拠となる信号は、すべての非負時刻でゼロだが、時刻 `-1` で値 `1/2` をとる。 -/
def negativeTimeOnlyGain : ContinuousGainSignal :=
  ⟨⟨fun t => min (1 / 2) (max 0 (-t)),
    continuous_const.min (continuous_const.max continuous_neg)⟩,
    by
      intro t
      constructor
      · exact le_min (by norm_num) (le_max_left _ _)
      · exact min_le_left _ _⟩

theorem negativeTimeOnlyGain_zero_on_future (t : ℝ) (ht : 0 ≤ t) :
    negativeTimeOnlyGain.1 t = 0 := by
  simp [negativeTimeOnlyGain, max_eq_left (neg_nonpos.mpr ht), min_eq_right]

theorem negativeTimeOnlyGain_nonzero_past : negativeTimeOnlyGain.1 (-1) = 1 / 2 := by
  norm_num [negativeTimeOnlyGain]

/-- 完全な時間の信号族を方策の実際の時間領域に制限すると、単射性が失われる。2 つの異なる連続信号が、まったく同じ非負時間の Borel マルコフフィードバックを定める。これが、データの接続が将来区間でほとんど至るところの軌道だけを比較しなければならない理由である。 -/
theorem nonnegative_policy_forgets_past_signal :
    negativeTimeOnlyGain ≠
        ⟨ContinuousMap.const ℝ 0, by intro t; norm_num⟩ ∧
      (fun q : Set.Ici (0 : ℝ) × ℝ =>
          -(negativeTimeOnlyGain.1 q.1.1) * q.2) =
      (fun q : Set.Ici (0 : ℝ) × ℝ =>
          -((⟨ContinuousMap.const ℝ 0, by intro t; norm_num⟩ : ContinuousGainSignal).1
            q.1.1) * q.2) := by
  constructor
  · intro h
    have heq := congrArg (fun k : ContinuousGainSignal => k.1 (-1)) h
    norm_num [negativeTimeOnlyGain] at heq
  · have hact :
        (fun q : Set.Ici (0 : ℝ) × ℝ =>
          -(negativeTimeOnlyGain.1 q.1.1) * q.2) =
        (fun q : Set.Ici (0 : ℝ) × ℝ =>
          -((⟨ContinuousMap.const ℝ 0, by intro t; norm_num⟩ : ContinuousGainSignal).1
            q.1.1) * q.2) := by
      funext q
      rw [negativeTimeOnlyGain_zero_on_future q.1.1 q.1.2]
      simp
    exact hact

/-- 2 つの生成された方策が一致すれば、方策が観測できる各時刻でゲイン信号も一致する。 -/
theorem gain_eq_of_nonnegative_policy_action_eq (k₁ k₂ : ContinuousGainSignal)
    (h : ∀ q : Set.Ici (0 : ℝ) × ℝ,
      -(k₁.1 q.1.1) * q.2 = -(k₂.1 q.1.1) * q.2)
    (t : ℝ) (ht : 0 ≤ t) : k₁.1 t = k₂.1 t := by
  have hval := h (⟨⟨t, ht⟩, (1 : ℝ)⟩)
  linarith

/-- 開始時刻から現在時刻までの累積ゲイン。 -/
def accumulatedGain (k : ContinuousGainSignal) (T s : ℝ) : ℝ :=
  ∫ u in T..s, k.1 u

/-- 累積した時間依存ゲインは、0 と、最大の定数ゲインに対応するものとの間にある。 -/
theorem accumulatedGain_bounds (k : ContinuousGainSignal) (T s : ℝ)
    (hTs : T ≤ s) :
    0 ≤ accumulatedGain k T s ∧ accumulatedGain k T s ≤ (1 / 2) * (s - T) := by
  have hkint : IntervalIntegrable (fun u => k.1 u) MeasureTheory.volume T s :=
    k.1.continuous.intervalIntegrable T s
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hmax : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hlo := intervalIntegral.integral_mono_on hTs hzero hkint
    (fun u hu => (k.2 u).1)
  have hhi := intervalIntegral.integral_mono_on hTs hkint hmax
    (fun u hu => (k.2 u).2)
  constructor
  · simpa [accumulatedGain] using hlo
  · calc
      accumulatedGain k T s ≤ (s - T) * (1 / 2) := by
        simpa [accumulatedGain, intervalIntegral.integral_const] using hhi
      _ = (1 / 2) * (s - T) := by ring

/-- 連続な時間依存ゲインの厳密な経路。 -/
def timeVaryingOrbit (x : ℝ) (k : ContinuousGainSignal) (T s : ℝ) : ℝ :=
  x * Real.exp (-((1 / 2) * (s - T) + accumulatedGain k T s))

/-- 可変ゲイン経路は、指定された初期状態から始まる。 -/
theorem timeVaryingOrbit_initial (x : ℝ) (k : ContinuousGainSignal) (T : ℝ) :
    timeVaryingOrbit x k T T = x := by
  simp [timeVaryingOrbit, accumulatedGain]

/-- 連続信号の軌道は微分可能で、意図した閉ループ方程式 `r'=-(1/2+k(t))r` をすべての時刻で満たす。 -/
theorem timeVaryingOrbit_ode (x : ℝ) (k : ContinuousGainSignal) (T s : ℝ) :
    HasDerivAt (fun u => timeVaryingOrbit x k T u)
      (-(1 / 2 + k.1 s) * timeVaryingOrbit x k T s) s := by
  have hacc : HasDerivAt (fun u => accumulatedGain k T u) (k.1 s) s := by
    exact intervalIntegral.integral_hasDerivAt_right
      (k.1.continuous.intervalIntegrable T s)
      (k.1.continuous.stronglyMeasurableAtFilter MeasureTheory.volume (nhds s))
      k.1.continuous.continuousAt
  have htime : HasDerivAt (fun u : ℝ => (1 / 2) * (u - T)) (1 / 2) s := by
    convert ((hasDerivAt_id s).sub_const T).const_mul (1 / 2) using 1
    · funext u
      dsimp [id]
    · ring
  have harg : HasDerivAt
      (fun u => -((1 / 2) * (u - T) + accumulatedGain k T u))
      (-(1 / 2 + k.1 s)) s := by
    convert (htime.add hacc).neg using 1 <;> simp only [one_div] <;> ring
  have hexp := (HasDerivAt.exp harg).const_mul x
  simpa [timeVaryingOrbit, mul_comm, mul_left_comm, mul_assoc] using hexp

/-- ODE の証拠によって、各信号が生成する軌道は連続になる。 -/
theorem timeVaryingOrbit_continuous (x : ℝ) (k : ContinuousGainSignal) (T : ℝ) :
    Continuous (timeVaryingOrbit x k T) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (timeVaryingOrbit_ode x k T s).continuousAt

/-- 累積ゲインは、途中の再開時刻で分割できる。 -/
theorem accumulatedGain_add (k : ContinuousGainSignal) (T u s : ℝ) :
    accumulatedGain k T s = accumulatedGain k T u + accumulatedGain k u s := by
  symm
  exact intervalIntegral.integral_add_adjacent_intervals
    (k.1.continuous.intervalIntegrable T u)
    (k.1.continuous.intervalIntegrable u s)

/-- 将来時刻で一致する信号は、時刻 0 より前の値が異なっていても、任意の将来区間で同じ累積ゲインをもつ。 -/
theorem accumulatedGain_eq_of_future_agreement (k₁ k₂ : ContinuousGainSignal)
    (T s : ℝ) (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    accumulatedGain k₁ T s = accumulatedGain k₂ T s := by
  unfold accumulatedGain
  apply intervalIntegral.integral_congr
  intro t ht
  exact hfuture t (le_trans hT (by simpa [uIcc, min_eq_left hTs] using ht.1))

/-- 厳密な軌道は、方策の将来時刻の信号値のみに依存する。これは、非負時間の割引データに必要な等式である。 -/
theorem timeVaryingOrbit_eq_of_future_agreement (x T s : ℝ)
    (k₁ k₂ : ContinuousGainSignal) (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    timeVaryingOrbit x k₁ T s = timeVaryingOrbit x k₂ T s := by
  unfold timeVaryingOrbit
  rw [accumulatedGain_eq_of_future_agreement k₁ k₂ T s hT hTs hfuture]

/-- 同じ非自励フィードバックを途中の状態から再開しても、元の軌道が再現される。 -/
theorem timeVaryingOrbit_restart (x : ℝ) (k : ContinuousGainSignal)
    (T u s : ℝ) :
    timeVaryingOrbit (timeVaryingOrbit x k T u) k u s =
      timeVaryingOrbit x k T s := by
  have hacc := accumulatedGain_add k T u s
  unfold timeVaryingOrbit
  calc
    x * Real.exp (-((1 / 2) * (u - T) + accumulatedGain k T u)) *
        Real.exp (-((1 / 2) * (s - u) + accumulatedGain k u s)) =
      x * (Real.exp (-((1 / 2) * (u - T) + accumulatedGain k T u)) *
        Real.exp (-((1 / 2) * (s - u) + accumulatedGain k u s))) := by ring
    _ = x * Real.exp (-((1 / 2) * (u - T) + accumulatedGain k T u) +
        -((1 / 2) * (s - u) + accumulatedGain k u s)) := by rw [← Real.exp_add]
    _ = x * Real.exp (-((1 / 2) * (s - T) + accumulatedGain k T s)) := by
        congr 2
        linear_combination hacc

/-- 厳密な時間依存の軌道は、自然ドリフトとフィードバックを合わせた ODE `r'=-r/2+u(t,r)` を解く。ここで `G=id`。 -/
theorem timeVaryingFeedback_ode (x : ℝ) (k : ContinuousGainSignal) (T s : ℝ) :
    HasDerivAt (fun u => timeVaryingOrbit x k T u)
      (-(1 / 2) * timeVaryingOrbit x k T s +
        (continuousGainFeedback k).action (s, timeVaryingOrbit x k T s)) s := by
  have h := timeVaryingOrbit_ode x k T s
  convert h using 1 <;> simp [continuousGainFeedback] <;> ring

/-- `[0,1/2]` に入る連続な時間依存ゲインは、最大の定数ゲイン経路以上に 0 から離れた経路を与える。この各点比較が、制御努力の項を加えずに費用最適性を示す鍵である。 -/
theorem timeVaryingOrbit_sq_lower_bound (x : ℝ) (k : ContinuousGainSignal)
    (T s : ℝ) (hTs : T ≤ s) :
    (orbit x (1 / 2) (1 / 2) T s) ^ 2 ≤ (timeVaryingOrbit x k T s) ^ 2 := by
  have hacc := accumulatedGain_bounds k T s hTs
  have hexp : -((1 / 2) * (s - T) + (1 / 2) * (s - T)) ≤
      -((1 / 2) * (s - T) + accumulatedGain k T s) := by
    nlinarith [hacc.2]
  have hexp' := Real.exp_le_exp.mpr hexp
  have hsqexp := (sq_le_sq₀ (Real.exp_nonneg _) (Real.exp_nonneg _)).2 hexp'
  have hprod := mul_le_mul_of_nonneg_left hsqexp (sq_nonneg x)
  have horbit : Real.exp (-(rate (1 / 2) (1 / 2)) * (s - T)) =
      Real.exp (-((1 / 2) * (s - T) + (1 / 2) * (s - T))) := by
    congr 1 <;> norm_num [rate] <;> ring
  calc
    (orbit x (1 / 2) (1 / 2) T s) ^ 2 =
        x ^ 2 * Real.exp (-((1 / 2) * (s - T) + (1 / 2) * (s - T))) ^ 2 := by
          simp only [orbit, horbit]
          ring
    _ ≤ x ^ 2 * Real.exp (-((1 / 2) * (s - T) +
          accumulatedGain k T s)) ^ 2 := hprod
    _ = (timeVaryingOrbit x k T s) ^ 2 := by
          simp [timeVaryingOrbit]
          ring

/-- 連続な時間依存ゲインに沿った割引走行費。 -/
def timeVaryingDiscountedCost (x : ℝ) (k : ContinuousGainSignal) (T s : ℝ) : ℝ :=
  theorem26DiscountWeight 1 T s * (3 * (timeVaryingOrbit x k T s) ^ 2)

/-- どの許容な連続時間依存ゲインも、定数の最大ゲインを改善できない。その拡張実数の割引費用は `x²` 以上である。これは、割引費用が無限大になりうる信号を含む、連続信号族全体についての費用の比較である。 -/
theorem continuous_time_gain_cost_minimal (x : ℝ) (k : ContinuousGainSignal)
    (T : ℝ) :
    ENNReal.ofReal (x ^ 2) ≤
      ∫⁻ s, ENNReal.ofReal (timeVaryingDiscountedCost x k T s)
        ∂futureLebesgueMeasure T := by
  have hbaseInt := discountedIntegrand_integrable x T
  have hbaseNonneg : 0 ≤ᵐ[futureLebesgueMeasure T] (discountedIntegrand x T) := by
    filter_upwards with s
    dsimp [discountedIntegrand, theorem26DiscountWeight, runningCost]
    positivity
  have hbaseLin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbaseInt hbaseNonneg
  have hbaseValue : ENNReal.ofReal (x ^ 2) =
      ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
        ∂futureLebesgueMeasure T := by
    rw [← value_eq_sq]
    exact hbaseLin
  have hpoint : ∀ᵐ s ∂futureLebesgueMeasure T,
      discountedIntegrand x T s ≤ timeVaryingDiscountedCost x k T s := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
    have hsT : T ≤ s := hs
    have hsq := timeVaryingOrbit_sq_lower_bound x k T s hsT
    have hflow : orbit x (1 / 2) (1 / 2) T s = flow x T s := by
      unfold orbit rate Tomabechi.Theorem24_26_Model.flow
      congr 1
      norm_num
    rw [hflow] at hsq
    have hexp : 0 ≤ theorem26DiscountWeight 1 T s := by
      rw [theorem26DiscountWeight]
      positivity
    rw [discountedIntegrand, timeVaryingDiscountedCost,
      theorem26DiscountWeight, runningCost, flow]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq (by norm_num : 0 ≤ (3 : ℝ))) hexp
  calc
    ENNReal.ofReal (x ^ 2) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := hbaseValue
    _ ≤ ∫⁻ s, ENNReal.ofReal (timeVaryingDiscountedCost x k T s)
          ∂futureLebesgueMeasure T := by
        apply MeasureTheory.lintegral_mono_ae
        filter_upwards [hpoint] with s hs
        exact ENNReal.ofReal_le_ofReal hs

/-- 許容な連続信号のうち、最大のもの。 -/
def maximalContinuousGain : ContinuousGainSignal :=
  ⟨ContinuousMap.const ℝ (1 / 2), by intro t; norm_num⟩

/-- 最大信号は、定数ゲインのモデルとまったく同じ経路をもつ。 -/
theorem maximalContinuousGain_orbit (x T s : ℝ) :
    timeVaryingOrbit x maximalContinuousGain T s =
      orbit x (1 / 2) (1 / 2) T s := by
  unfold timeVaryingOrbit orbit rate accumulatedGain maximalContinuousGain
  have hconst : (fun u : ℝ => (⟨ContinuousMap.const ℝ (1 / 2),
      by intro t; norm_num⟩ : ContinuousGainSignal).1 u) = fun _ => (1 / 2 : ℝ) := by
    funext u
    rfl
  rw [hconst, intervalIntegral.integral_const]
  congr 2
  norm_num
  ring

/-- 最大の連続信号は価値 `x²` を達成する。各点の下界と合わせて、連続な時間依存ゲインの全クラスで最適である。 -/
theorem continuous_time_gain_optimal_value (x T : ℝ) :
    (∫⁻ s, ENNReal.ofReal
        (timeVaryingDiscountedCost x maximalContinuousGain T s)
        ∂futureLebesgueMeasure T) = ENNReal.ofReal (x ^ 2) ∧
      ∀ k : ContinuousGainSignal,
        ENNReal.ofReal (x ^ 2) ≤
          ∫⁻ s, ENNReal.ofReal (timeVaryingDiscountedCost x k T s)
            ∂futureLebesgueMeasure T := by
  refine ⟨?_, ?_⟩
  · have hbase := continuous_time_gain_cost_minimal x maximalContinuousGain T
    apply le_antisymm ?_ hbase
    have hbaseValue : ENNReal.ofReal (x ^ 2) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := by
      have hI := discountedIntegrand_integrable x T
      have hnonneg : 0 ≤ᵐ[futureLebesgueMeasure T] (discountedIntegrand x T) := by
        filter_upwards with s
        dsimp [discountedIntegrand, theorem26DiscountWeight, runningCost]
        positivity
      rw [← value_eq_sq]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnonneg
    have heq : ∀ s, timeVaryingDiscountedCost x maximalContinuousGain T s =
        discountedIntegrand x T s := by
      intro s
      rw [timeVaryingDiscountedCost, discountedIntegrand,
        maximalContinuousGain_orbit, orbit, rate, theorem26DiscountWeight,
        runningCost, flow]
      ring
    have hlinEq :
        (∫⁻ s, ENNReal.ofReal (timeVaryingDiscountedCost x maximalContinuousGain T s)
          ∂futureLebesgueMeasure T) =
        ∫⁻ s, ENNReal.ofReal (discountedIntegrand x T s)
          ∂futureLebesgueMeasure T := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards with s
      exact congrArg ENNReal.ofReal (heq s)
    exact (hlinEq.trans hbaseValue.symm).le
  · intro k
    exact continuous_time_gain_cost_minimal x k T

/-- 許容される上位層のフィードバックが、まさに有界可測ゲインから生成される方策であるような、定理24の完全なデータ構造。 -/
noncomputable def measurableMultiPolicyData :
    Theorem24NonnegativeTimeData SourceState MeasurableMultiSourcePolicy where
  rho := 1
  rho_pos := by norm_num
  trajectory := measurableMultiSourceTrajectory
  runningCost := measurableMultiSourceRunningCost
  admissible := measurableMultiSourceAdmissible
  optimalValue := measurableMultiSourceValue
  optimalPolicy := measurableMultiSourceOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true => exact measurableGainOrbit_initial x (measurablePolicySignal π) T
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [measurableMultiSourceRunningCost]
    | true => simp [measurableMultiSourceRunningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [measurableMultiSourceRunningCost, theorem26DiscountWeight]
    | true =>
      have hc := measurableGainOrbit_continuous x (measurablePolicySignal π) T
      have hm : Measurable (fun s => theorem26DiscountWeight 1 T s *
          (3 * measurableGainOrbit x (measurablePolicySignal π) T s ^ 2)) := by
        fun_prop [theorem26DiscountWeight]
      exact ENNReal.measurable_ofReal.comp hm
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact lower_discounted_integrand_integrable T
    | true =>
      have hbase := discountedIntegrand_integrable x T
      have htraj := measurableMaxPolicy_trajectory_ae x T hT
      apply hbase.congr
      filter_upwards [htraj] with s hs
      simp only [measurableMultiSourceRunningCost, measurableMultiSourceTrajectory,
        measurableMultiSourceOptimalPolicy]
      rw [hs, maximalMeasurableGain_orbit]
      simp [discountedIntegrand, runningCost, theorem26DiscountWeight,
        flow, orbit, rate]
      ring
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | false => trivial
    | true => exact ⟨maximalMeasurableGain, fun _ => rfl⟩
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | false => exact (lower_policy_value_attained () T).2.1
    | true =>
      have hbase : value x T = ∫ s, theorem26DiscountWeight 1 T s *
          (3 * measurableGainOrbit x maximalMeasurableGain T s ^ 2)
            ∂futureLebesgueMeasure T := by
        unfold value
        apply MeasureTheory.integral_congr_ae
        filter_upwards with s
        rw [maximalMeasurableGain_orbit]
        simp [discountedIntegrand, runningCost, orbit, rate,
          theorem26DiscountWeight, flow]
        ring
      have htraj := measurableMaxPolicy_trajectory_ae x T hT
      calc
        x ^ 2 = value x T := (value_eq_sq x T).symm
        _ = ∫ s, theorem26DiscountWeight 1 T s *
            (3 * measurableGainOrbit x
              (measurablePolicySignal (measurableSignalPolicy maximalMeasurableGain)) T s ^ 2)
              ∂futureLebesgueMeasure T := by
          rw [hbase]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [htraj] with s hs
          rw [hs]
        _ = ∫ s, theorem26DiscountWeight 1 T s *
            measurableMultiSourceRunningCost true
              (measurableMultiSourceOptimalPolicy true x T)
              (measurableMultiSourceTrajectory true
                (measurableMultiSourceOptimalPolicy true x T) x T s) s
              ∂futureLebesgueMeasure T := by
          simp [measurableMultiSourceRunningCost,
            measurableMultiSourceOptimalPolicy, measurableMultiSourceTrajectory]
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
      apply le_of_eq
      simpa [measurableMultiSourceValue, measurableMultiSourceTrajectory,
        measurableMultiSourceRunningCost, lowerRunningCost] using source_lower_lintegral_eq T
    | true =>
      change ENNReal.ofReal (x ^ 2) ≤
        ∫⁻ s, ENNReal.ofReal
          (measurableGainDiscountedCost x (measurablePolicySignal π) T s)
          ∂futureLebesgueMeasure T
      exact measurable_time_gain_cost_minimal x (measurablePolicySignal π) T
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false =>
      simpa [measurableMultiSourceRunningCost, lowerRunningCost] using
        lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : SourceAbstraction) ha).elim

theorem measurableMultiData_target_eq (T : ℝ) :
    theorem26ZeroValueTarget Set.univ
      (measurableMultiPolicyData.optimalValue (⊤ : SourceAbstraction)) T = zeroTarget T := by
  ext x
  simp [theorem26ZeroValueTarget, measurableMultiPolicyData,
    measurableMultiSourceValue, zeroTarget, value_eq_sq]

theorem measurableMultiTopPath_eq_flow (x T s : ℝ) (hT : 0 ≤ T) (hTs : T ≤ s) :
    measurableMultiSourceTrajectory true
      (measurableSignalPolicy maximalMeasurableGain) x T s = flow x T s := by
  simp only [measurableMultiSourceTrajectory.eq_def]
  rw [measurableMaxPolicy_future_orbit x T s hT hTs,
    maximalMeasurableGain_orbit]
  unfold orbit rate flow
  congr 1
  ring

/-- 有界可測な方策データは、定理26-A のすべての量的フィールドを満たす。最適フィードバックは、実際に方策族の元である。 -/
noncomputable def measurableMultiPolicyDynamics :
    Theorem26NonnegativeTimeDynamics measurableMultiPolicyData ℝ where
  policyEquiv := Equiv.refl _
  feedback := measurableSignalPolicy maximalMeasurableGain
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hfeedback : measurableSignalPolicy maximalMeasurableGain =
        measurableMultiSourceOptimalPolicy (⊤ : SourceAbstraction) x T := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hfeedback]
      exact measurableMultiPolicyData.optimal_policy_admissible
        (⊤ : SourceAbstraction) x T hT
    · rw [hfeedback]
      exact measurableMultiPolicyData.optimal_cost_integrable
        (⊤ : SourceAbstraction) x T hT
    · rw [hfeedback]
      exact measurableMultiPolicyData.optimal_value_attained
        (⊤ : SourceAbstraction) x T hT
  W := lyapunov
  ω := fun r => r ^ 2
  c₁ := 1
  c₂ := 1
  rate := 2
  c₁_pos := by norm_num
  c₂_pos := by norm_num
  rate_pos := by norm_num
  trajectory_alive := by intro x T s hT hx hTs; exact Set.mem_univ _
  target_nonempty := by
    intro T hT
    rw [measurableMultiData_target_eq, zeroTarget_eq_singleton]
    exact Set.singleton_nonempty 0
  target_closed := by
    intro T hT
    rw [measurableMultiData_target_eq, zeroTarget_eq_singleton]
    exact isClosed_singleton
  target_invariant := by
    intro x T s hT hmem hTs
    rw [measurableMultiData_target_eq] at hmem ⊢
    change measurableMultiSourceTrajectory true
      (measurableSignalPolicy maximalMeasurableGain) x T s ∈ zeroTarget s
    rw [measurableMultiTopPath_eq_flow x T s hT hTs]
    have hforward := model_forward_complete_and_target_invariant x T s hmem
    exact hforward.2.2 s
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    change AbsolutelyContinuousOnInterval
      (fun u => lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T u) u) T s
    apply (sourceDynamics.W_absolutelyContinuous x T s hT (Set.mem_univ x) hTs).congr
    intro u hu
    calc
      sourceDynamics.W (sourceData.trajectory ⊤ sourceDynamics.feedback x T u) u =
          WAlong x T u := rfl
      _ = lyapunov (measurableMultiSourceTrajectory true
          (measurableSignalPolicy maximalMeasurableGain) x T u) u := by
        rw [measurableMultiTopPath_eq_flow x T u hT (by
          rw [uIcc_of_le hTs] at hu
          exact hu.1)]
        rfl
  W_nonnegative := by
    intro x T s hT hx hTs
    change 0 ≤ lyapunov (measurableMultiSourceTrajectory true
      (measurableSignalPolicy maximalMeasurableGain) x T s) s
    rw [measurableMultiTopPath_eq_flow x T s hT hTs]
    exact sq_nonneg (flow x T s)
  W_rightSlope := by
    intro x T u hT hx hTu
    change Tomabechi.Theorem1.RightSlopeBound
      (fun s => lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T s) s) u
      (-2 * lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T u) u)
    have hEq : (fun s => lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T s) s) =ᶠ[
          nhdsWithin u (Set.Ioi u)]
        WAlong x T := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have huv : u < v := hv
      have hTv : T ≤ v := le_trans hTu huv.le
      rw [measurableMultiTopPath_eq_flow x T v hT hTv]
      rfl
    have huEq : lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T u) u = WAlong x T u := by
      rw [measurableMultiTopPath_eq_flow x T u hT hTu]
      rfl
    rw [huEq]
    intro r hr
    filter_upwards [sourceDynamics.W_rightSlope x T u hT (Set.mem_univ x) hTu r hr,
      hEq] with v hs hv
    have hbase : sourceDynamics.W
        (sourceData.trajectory ⊤ sourceDynamics.feedback x T u) u = WAlong x T u := rfl
    have hbaseV : sourceDynamics.W
        (sourceData.trajectory ⊤ sourceDynamics.feedback x T v) v = WAlong x T v := rfl
    have hs' : (v - u)⁻¹ * (WAlong x T v - WAlong x T u) < r := by
      simpa only [hbase, hbaseV] using hs
    calc
      (v - u)⁻¹ *
          (lyapunov (measurableMultiSourceTrajectory true
            (measurableSignalPolicy maximalMeasurableGain) x T v) v -
            lyapunov (measurableMultiSourceTrajectory true
              (measurableSignalPolicy maximalMeasurableGain) x T u) u) =
        (v - u)⁻¹ * (WAlong x T v - WAlong x T u) := by rw [hv, huEq]
      _ < r := hs'
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [measurableMultiData_target_eq s]
    change 1 * (Metric.infDist (measurableMultiSourceTrajectory true
      (measurableSignalPolicy maximalMeasurableGain) x T s) (zeroTarget s)) ^ 2 ≤
      lyapunov (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T s) s
    rw [measurableMultiTopPath_eq_flow x T s hT hTs]
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [measurableMultiData_target_eq s]
    change lyapunov (measurableMultiSourceTrajectory true
      (measurableSignalPolicy maximalMeasurableGain) x T s) s ≤
      1 * (Metric.infDist (measurableMultiSourceTrajectory true
        (measurableSignalPolicy maximalMeasurableGain) x T s) (zeroTarget s)) ^ 2
    rw [measurableMultiTopPath_eq_flow x T s hT hTs]
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ y ^ 2 ∧ y ^ 2 ≤
      (Metric.infDist y (theorem26ZeroValueTarget Set.univ
        (measurableMultiPolicyData.optimalValue (⊤ : SourceAbstraction)) t)) ^ 2
    rw [measurableMultiData_target_eq, zeroTarget_eq_singleton, Metric.infDist_singleton]
    constructor
    · positivity
    · simp [Real.dist_eq, sq_abs]

/-- 一般の 24→26 定理を、有界可測ゲイン族の全体に、すべての非負の初期時刻と状態について適用する。 -/
noncomputable def measurableMultiPolicy_model_24_26 (x T : ℝ) (hT : 0 ≤ T) :=
  theorem24_to26_from_nonnegativeTimeData measurableMultiPolicyData
    measurableMultiPolicyDynamics x T hT (Set.mem_univ x)

/-- 有界可測な方策データでは、PZS はちょうど零状態であり、したがって達成された価値の零集合と一致する。 -/
theorem measurableMultiPolicyPZS_iff_zero (x T : ℝ) (hT : 0 ≤ T) :
    FeedbackPZS (measurableMultiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => measurableMultiPolicyData.runningCost
        (⊤ : SourceAbstraction) π
        (measurableMultiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s)
      x T ↔ x = 0 := by
  have hgeneral := measurableMultiPolicy_model_24_26 x T hT
  have hpzs := hgeneral.2.1
  change FeedbackPZS (measurableMultiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => measurableMultiPolicyData.runningCost
        (⊤ : SourceAbstraction) π
        (measurableMultiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s)
      x T ↔ x ∈ theorem26ZeroValueTarget Set.univ
        (measurableMultiPolicyData.optimalValue (⊤ : SourceAbstraction)) T at hpzs
  rw [measurableMultiData_target_eq, zeroTarget_eq_singleton] at hpzs
  simpa using hpzs

/-- 有界可測ゲインの PZS の目標は、2 次元の定理27の例における運用上の無明の環と一致する。 -/
theorem measurableMultiPolicy_target_matches_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) :
    (¬ FeedbackPZS (measurableMultiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => measurableMultiPolicyData.runningCost
        (⊤ : SourceAbstraction) π
        (measurableMultiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s)
      (x 0) T) ↔ x ∉ Tomabechi.Examples.Theorem27Op.ringE T := by
  rw [measurableMultiPolicyPZS_iff_zero (x 0) T hT,
    Tomabechi.Examples.Theorem27Op.ringE_eq]
  simp

/-- 有界可測モデルの PZS の目標の外では、対応する運用上の定理27の軌道は、ほとんど至るところで正の行作動をもつ。 -/
theorem measurableMultiPolicy_ignorance_has_27_action
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T)
    (hnot : ¬ FeedbackPZS
      (measurableMultiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => measurableMultiPolicyData.runningCost
        (⊤ : SourceAbstraction) π
        (measurableMultiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s)
      (x 0) T) :
    (∀ t, Tomabechi.Examples.Theorem27Op.flowE x T t ∉
      Tomabechi.Examples.Theorem27Op.ringE t) ∧
      ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
        0 < -(inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            (Tomabechi.Examples.Theorem27Op.u0E x T t -
              Tomabechi.Examples.Theorem27Op.utrE x T t))) := by
  have hxnot : x 0 ≠ 0 := by
    intro hx0
    apply hnot
    apply (measurableMultiPolicyPZS_iff_zero (x 0) T hT).2
    simp [hx0]
  exact Tomabechi.Examples.Theorem27Op.ignorance_gives_action x T hT hxnot


/-! ### 定理24の多方策データ -/

abbrev ContinuousSignalPolicy :=
  NonnegativeTimeBorelMarkovFeedback ℝ ℝ

/-- 信号は、非負時間領域上の実際のマルコフ方策になる。 -/
def signalPolicy (k : ContinuousGainSignal) : ContinuousSignalPolicy :=
  ⟨fun q => -(k.1 q.1.1) * q.2, by fun_prop⟩

/-- Borel フィードバックが許容であるのは、有界連続ゲイン信号の 1 つから生成されるときに限る。 -/
def signalPolicyAdmissible (π : ContinuousSignalPolicy) : Prop :=
  ∃ k : ContinuousGainSignal, ∀ q : Set.Ici (0 : ℝ) × ℝ,
    π.action q = -(k.1 q.1.1) * q.2

/-- 許容方策を表す信号を選ぶ。許容でない方策には、軌道を全域的に保つためだけに最大信号を与える。 -/
noncomputable def policySignal (π : ContinuousSignalPolicy) : ContinuousGainSignal := by
  classical
  exact if hmax : π = signalPolicy maximalContinuousGain then maximalContinuousGain
    else if h : signalPolicyAdmissible π then Classical.choose h else maximalContinuousGain

/-- 選んだ代表は、状態 1 でのマルコフ作用を評価することにより、将来時刻においてちょうど方策のゲインをもつ。 -/
theorem policySignal_spec (π : ContinuousSignalPolicy)
    (hπ : signalPolicyAdmissible π) (t : ℝ) (ht : 0 ≤ t) :
    π.action (⟨⟨t, ht⟩, (1 : ℝ)⟩) = -(policySignal π).1 t := by
  classical
  by_cases hmax : π = signalPolicy maximalContinuousGain
  · have hmaxAction := congrArg (fun f : ContinuousSignalPolicy =>
      f.action (⟨⟨t, ht⟩, (1 : ℝ)⟩)) hmax
    simpa [policySignal, hmax, signalPolicy] using hmaxAction
  · have hrep := Classical.choose_spec hπ
    simp only [policySignal, hmax, dif_neg, hπ, dif_pos] at hrep ⊢
    have h := hrep ⟨⟨t, ht⟩, (1 : ℝ)⟩
    convert h using 1 <;> simp

/-- 24/26 定理のインターフェースが使う 2 層の抽象度。上層には、非自明な連続時間依存方策クラスを置く。 -/
abbrev MultiSourcePolicy (a : SourceAbstraction) : Type :=
  match a with
  | false => PUnit
  | true => ContinuousSignalPolicy

noncomputable def multiSourceTrajectory : (a : SourceAbstraction) →
    MultiSourcePolicy a → SourceState a → ℝ → ℝ → SourceState a
  | false, _, x, _, _ => x
  | true, π, x, T, s => timeVaryingOrbit x (policySignal π) T s

def multiSourceRunningCost : (a : SourceAbstraction) → MultiSourcePolicy a →
    SourceState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, x, _ => 3 * x ^ 2

def multiSourceAdmissible : (a : SourceAbstraction) → MultiSourcePolicy a →
    SourceState a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, _, _ => signalPolicyAdmissible π

def multiSourceValue : (a : SourceAbstraction) → SourceState a → ℝ → ℝ
  | false, _, T => lowerValue T
  | true, x, _ => x ^ 2

def multiSourceOptimalPolicy : (a : SourceAbstraction) → SourceState a → ℝ →
    MultiSourcePolicy a
  | false, _, _ => PUnit.unit
  | true, _, _ => signalPolicy maximalContinuousGain

/-- 最大ゲイン方策の閉ループ経路は、すべての将来区間でスカラーモデルと一致する。 -/
theorem maxPolicy_future_orbit (x T s : ℝ) (hT : 0 ≤ T) (hTs : T ≤ s) :
    timeVaryingOrbit x (policySignal (signalPolicy maximalContinuousGain)) T s =
      timeVaryingOrbit x maximalContinuousGain T s := by
  apply timeVaryingOrbit_eq_of_future_agreement x T s _ _ hT hTs
  intro t ht
  have hspec := policySignal_spec (signalPolicy maximalContinuousGain)
    ⟨maximalContinuousGain, fun _ => rfl⟩ t ht
  simpa [signalPolicy] using hspec.symm

theorem policySignal_eq_witness_future (π : ContinuousSignalPolicy)
    (k : ContinuousGainSignal)
    (hπ : ∀ q : Set.Ici (0 : ℝ) × ℝ,
      π.action q = -(k.1 q.1.1) * q.2)
    (t : ℝ) (ht : 0 ≤ t) : (policySignal π).1 t = k.1 t := by
  have hselected := policySignal_spec π ⟨k, hπ⟩ t ht
  have hw := hπ ⟨⟨t, ht⟩, (1 : ℝ)⟩
  linarith

theorem policyTrajectory_eq_signal_future (x T s : ℝ)
    (π : ContinuousSignalPolicy) (k : ContinuousGainSignal)
    (hπ : ∀ q : Set.Ici (0 : ℝ) × ℝ,
      π.action q = -(k.1 q.1.1) * q.2)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    timeVaryingOrbit x (policySignal π) T s = timeVaryingOrbit x k T s := by
  apply timeVaryingOrbit_eq_of_future_agreement x T s _ _ hT hTs
  intro t ht
  exact policySignal_eq_witness_future π k hπ t ht

/-- 将来時刻では、選ばれた最適の代表はいずれもスカラーモデルの軌道をもつ。0 より前の違いは、制限された測度には影響しない。 -/
theorem maxPolicy_trajectory_ae (x T : ℝ) (hT : 0 ≤ T) :
    (fun s => timeVaryingOrbit x
      (policySignal (signalPolicy maximalContinuousGain)) T s) =ᵐ[
        futureLebesgueMeasure T] (fun s => timeVaryingOrbit x maximalContinuousGain T s) := by
  filter_upwards [MeasureTheory.ae_restrict_mem
    (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
  exact maxPolicy_future_orbit x T s hT hs
/-- 最上位の抽象度に、有界連続信号の方策族をおいた、定理24の完全なデータ集合。 -/
noncomputable def multiPolicyData :
    Theorem24NonnegativeTimeData SourceState MultiSourcePolicy where
  rho := 1
  rho_pos := by norm_num
  trajectory := multiSourceTrajectory
  runningCost := multiSourceRunningCost
  admissible := multiSourceAdmissible
  optimalValue := multiSourceValue
  optimalPolicy := multiSourceOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true => exact timeVaryingOrbit_initial x (policySignal π) T
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [multiSourceRunningCost]
    | true => simp [multiSourceRunningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [multiSourceRunningCost, theorem26DiscountWeight]
    | true =>
      have hcont := timeVaryingOrbit_continuous x (policySignal π) T
      have hm : Measurable (fun s => theorem26DiscountWeight 1 T s *
          (3 * timeVaryingOrbit x (policySignal π) T s ^ 2)) := by
        fun_prop [theorem26DiscountWeight]
      exact ENNReal.measurable_ofReal.comp hm
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact lower_discounted_integrand_integrable T
    | true =>
      have hbase := discountedIntegrand_integrable x T
      have htraj := maxPolicy_trajectory_ae x T hT
      apply hbase.congr
      filter_upwards [htraj] with s hs
      simp only [multiSourceRunningCost, multiSourceTrajectory,
        multiSourceOptimalPolicy]
      rw [hs, maximalContinuousGain_orbit]
      simp [discountedIntegrand, runningCost, theorem26DiscountWeight,
        flow, orbit, rate]
      ring
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | false => trivial
    | true => exact ⟨maximalContinuousGain, fun _ => rfl⟩
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | false => exact (lower_policy_value_attained () T).2.1
    | true =>
      have hbase : value x T = ∫ s, theorem26DiscountWeight 1 T s *
          (3 * timeVaryingOrbit x maximalContinuousGain T s ^ 2)
            ∂futureLebesgueMeasure T := by
        unfold value
        apply MeasureTheory.integral_congr_ae
        filter_upwards with s
        rw [maximalContinuousGain_orbit]
        simp [discountedIntegrand, runningCost, orbit, rate,
          theorem26DiscountWeight, flow]
        ring
      have htraj := maxPolicy_trajectory_ae x T hT
      calc
        x ^ 2 = value x T := (value_eq_sq x T).symm
        _ = ∫ s, theorem26DiscountWeight 1 T s *
            (3 * timeVaryingOrbit x (policySignal
              (signalPolicy maximalContinuousGain)) T s ^ 2)
              ∂futureLebesgueMeasure T := by
          rw [hbase]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [htraj] with s hs
          rw [hs]
        _ = ∫ s, theorem26DiscountWeight 1 T s *
            multiSourceRunningCost true (multiSourceOptimalPolicy true x T)
              (multiSourceTrajectory true (multiSourceOptimalPolicy true x T)
                x T s) s ∂futureLebesgueMeasure T := by
          simp [multiSourceRunningCost, multiSourceOptimalPolicy,
            multiSourceTrajectory]
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
      apply le_of_eq
      simpa [multiSourceValue, multiSourceTrajectory, multiSourceRunningCost,
        lowerRunningCost] using source_lower_lintegral_eq T
    | true =>
      rcases hπ with ⟨k, hk⟩
      have htraj' : (fun s => timeVaryingOrbit x (policySignal π) T s) =ᵐ[
          futureLebesgueMeasure T] (fun s => timeVaryingOrbit x k T s) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
        exact policyTrajectory_eq_signal_future x T s π k hk hT hs
      have hcost_ae : (fun s => ENNReal.ofReal
          (theorem26DiscountWeight 1 T s * multiSourceRunningCost true π
            (multiSourceTrajectory true π x T s) s)) =ᵐ[
          futureLebesgueMeasure T] (fun s => ENNReal.ofReal
            (timeVaryingDiscountedCost x k T s)) := by
        filter_upwards [htraj'] with s hs
        simp only [multiSourceRunningCost, multiSourceTrajectory,
          timeVaryingDiscountedCost]
        rw [hs]
      have hcost := MeasureTheory.lintegral_congr_ae
        hcost_ae
      rw [multiSourceValue, hcost]
      exact continuous_time_gain_cost_minimal x k T
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false => simpa [multiSourceRunningCost, lowerRunningCost] using lower_condition24A () T
    | true => exact (lt_irrefl (⊤ : SourceAbstraction) ha).elim

local instance multiTopPseudoMetric :
    PseudoMetricSpace (SourceState (⊤ : SourceAbstraction)) :=
  Real.pseudoMetricSpace

local instance multiTopMeasurableSpace :
    MeasurableSpace (SourceState (⊤ : SourceAbstraction)) := by
  change MeasurableSpace ℝ
  infer_instance

local instance multiTopBorelSpace :
    BorelSpace (SourceState (⊤ : SourceAbstraction)) := by
  change BorelSpace ℝ
  infer_instance

local instance multiTopProductBorelSpace :
    BorelSpace (Set.Ici (0 : ℝ) × SourceState (⊤ : SourceAbstraction)) := by
  change BorelSpace (Set.Ici (0 : ℝ) × ℝ)
  infer_instance

theorem multiData_target_eq (T : ℝ) :
    theorem26ZeroValueTarget Set.univ
      (multiPolicyData.optimalValue (⊤ : SourceAbstraction)) T = zeroTarget T := by
  ext x
  simp [theorem26ZeroValueTarget, multiPolicyData, multiSourceValue,
    zeroTarget, value_eq_sq]

theorem multiTopPath_eq_flow (x T s : ℝ) :
    multiSourceTrajectory true (signalPolicy maximalContinuousGain)
      x T s = flow x T s := by
  simp only [multiSourceTrajectory.eq_def]
  have hsignal : policySignal (signalPolicy maximalContinuousGain) =
      maximalContinuousGain := by
    simp [policySignal, signalPolicy]
  rw [hsignal, maximalContinuousGain_orbit]
  unfold orbit rate flow
  congr 1
  ring

/-- 連続信号のデータも、定理26-A のすべての量的フィールドを満たす。選ばれた最適なマルコフフィードバックは、許容な多方策族の実際の元である。 -/
noncomputable def multiPolicyDynamics :
    Theorem26NonnegativeTimeDynamics multiPolicyData ℝ where
  policyEquiv := Equiv.refl _
  feedback := signalPolicy maximalContinuousGain
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hfeedback : signalPolicy maximalContinuousGain =
        multiSourceOptimalPolicy (⊤ : SourceAbstraction) x T := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hfeedback]
      exact multiPolicyData.optimal_policy_admissible (⊤ : SourceAbstraction) x T hT
    · rw [hfeedback]
      exact multiPolicyData.optimal_cost_integrable (⊤ : SourceAbstraction) x T hT
    · rw [hfeedback]
      exact multiPolicyData.optimal_value_attained (⊤ : SourceAbstraction) x T hT
  W := lyapunov
  ω := fun r => r ^ 2
  c₁ := 1
  c₂ := 1
  rate := 2
  c₁_pos := by norm_num
  c₂_pos := by norm_num
  rate_pos := by norm_num
  trajectory_alive := by intro x T s hT hx hTs; exact Set.mem_univ _
  target_nonempty := by
    intro T hT
    rw [multiData_target_eq, zeroTarget_eq_singleton]
    exact Set.singleton_nonempty 0
  target_closed := by
    intro T hT
    rw [multiData_target_eq, zeroTarget_eq_singleton]
    exact isClosed_singleton
  target_invariant := by
    intro x T s hT hmem hTs
    rw [multiData_target_eq] at hmem ⊢
    change multiSourceTrajectory true (signalPolicy maximalContinuousGain) x T s ∈
      zeroTarget s
    rw [multiTopPath_eq_flow]
    have hforward := model_forward_complete_and_target_invariant x T s hmem
    exact hforward.2.2 s
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    change AbsolutelyContinuousOnInterval
      (fun u => lyapunov (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T u) u) T s
    have hpath : (fun u => lyapunov (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T u) u) = WAlong x T := by
      funext u
      rw [multiTopPath_eq_flow]
      rfl
    rw [hpath]
    exact sourceDynamics.W_absolutelyContinuous x T s hT (Set.mem_univ x) hTs
  W_nonnegative := by
    intro x T s hT hx hTs
    change 0 ≤ lyapunov (multiSourceTrajectory true
      (signalPolicy maximalContinuousGain) x T s) s
    rw [multiTopPath_eq_flow]
    exact sq_nonneg (flow x T s)
  W_rightSlope := by
    intro x T u hT hx hTu
    change Tomabechi.Theorem1.RightSlopeBound
      (fun s => lyapunov (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T s) s) u
      (-2 * lyapunov (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T u) u)
    have hpath : (fun s => lyapunov (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T s) s) = WAlong x T := by
      funext v
      rw [multiTopPath_eq_flow]
      rfl
    rw [hpath]
    rw [multiTopPath_eq_flow]
    apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (WAlong x T) u (-2 * WAlong x T u) (-2 * WAlong x T u)
    · exact WAlong_hasDerivAt x T u
    · exact le_rfl
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    rw [multiData_target_eq s]
    change 1 * (Metric.infDist (multiSourceTrajectory true
      (signalPolicy maximalContinuousGain) x T s) (zeroTarget s)) ^ 2 ≤
      lyapunov (multiSourceTrajectory true (signalPolicy maximalContinuousGain) x T s) s
    rw [multiTopPath_eq_flow]
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    rw [multiData_target_eq s]
    change lyapunov (multiSourceTrajectory true
      (signalPolicy maximalContinuousGain) x T s) s ≤
      1 * (Metric.infDist (multiSourceTrajectory true
        (signalPolicy maximalContinuousGain) x T s) (zeroTarget s)) ^ 2
    rw [multiTopPath_eq_flow]
    rw [zeroTarget_eq_singleton, Metric.infDist_singleton]
    simp [lyapunov, Real.dist_eq, sq_abs]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ y ^ 2 ∧ y ^ 2 ≤
      (Metric.infDist y (theorem26ZeroValueTarget Set.univ
        (multiPolicyData.optimalValue (⊤ : SourceAbstraction)) t)) ^ 2
    rw [multiData_target_eq, zeroTarget_eq_singleton, Metric.infDist_singleton]
    constructor
    · positivity
    · simp [Real.dist_eq, sq_abs]

/-- 一般の定理24から26への結果を、すべての非負の初期対について、多方策データ集合全体に適用する。 -/
noncomputable def multiPolicy_model_24_26 (x T : ℝ) (hT : 0 ≤ T) :=
  theorem24_to26_from_nonnegativeTimeData multiPolicyData multiPolicyDynamics
    x T hT (Set.mem_univ x)

/-- この多方策モデルでは、永久苦痛ゼロはちょうど単集合の最適値目標 `{0}` である。 -/
theorem multiPolicyPZS_iff_zero (x T : ℝ) (hT : 0 ≤ T) :
    FeedbackPZS (multiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => multiPolicyData.runningCost (⊤ : SourceAbstraction) π
        (multiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s) x T ↔ x = 0 := by
  have hgeneral := multiPolicy_model_24_26 x T hT
  have hpzs := hgeneral.2.1
  change FeedbackPZS (multiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => multiPolicyData.runningCost (⊤ : SourceAbstraction) π
        (multiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s) x T ↔
    x ∈ theorem26ZeroValueTarget Set.univ
      (multiPolicyData.optimalValue (⊤ : SourceAbstraction)) T at hpzs
  rw [multiData_target_eq, zeroTarget_eq_singleton] at hpzs
  simpa using hpzs

/-- 動径の状態座標で評価すると、多方策の PZS の目標は、27-A のモデルと同じ運用上の環である。 -/
theorem multiPolicy_target_matches_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) :
    (¬ FeedbackPZS (multiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => multiPolicyData.runningCost (⊤ : SourceAbstraction) π
        (multiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s) (x 0) T) ↔
      x ∉ Tomabechi.Examples.Theorem27Op.ringE T := by
  rw [multiPolicyPZS_iff_zero (x 0) T hT,
    Tomabechi.Examples.Theorem27Op.ringE_eq]
  simp

/-- 許容な連続時間依存信号の族全体についての PZS。 -/
def continuousGainPZS (x T : ℝ) : Prop :=
  ∃ k : ContinuousGainSignal,
    timeVaryingDiscountedCost x k T =ᵐ[futureLebesgueMeasure T] 0

/-- 時間依存ゲイン族は、同じ価値ゼロの目標 `{x=0}` をもつ。 -/
theorem continuousGainPZS_iff_value_zero (x T : ℝ) :
    continuousGainPZS x T ↔ x ^ 2 = 0 := by
  constructor
  · rintro ⟨k, hzero⟩
    by_contra hx
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hx
      simp [hx0]
    have hμ : futureLebesgueMeasure T Set.univ ≠ 0 := by
      rw [futureLebesgueMeasure, MeasureTheory.Measure.restrict_apply
        MeasurableSet.univ]
      simp [Real.volume_Ici]
    have hpositive : ∀ᵐ s ∂futureLebesgueMeasure T,
        0 < timeVaryingDiscountedCost x k T s := by
      filter_upwards with s
      have hpath : timeVaryingOrbit x k T s ≠ 0 := by
        simp [timeVaryingOrbit, hx0, Real.exp_ne_zero]
      dsimp [timeVaryingDiscountedCost, theorem26DiscountWeight]
      positivity
    exact (not_ae_zero_of_ae_strictlyPositive
      (futureLebesgueMeasure T) (timeVaryingDiscountedCost x k T)
      hμ hpositive) hzero
  · intro hx
    have hx0 : x = 0 := (sq_eq_zero_iff).1 hx
    refine ⟨maximalContinuousGain, ?_⟩
    filter_upwards with s
    simp [timeVaryingDiscountedCost, timeVaryingOrbit, hx0]

/-- 時間依存ゲイン族の運用上の無明は、27-A のモデルで使った同じ零価値の環の外にいることとまったく同じである。 -/
theorem continuousGain_target_matches_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) :
    (¬ continuousGainPZS (x 0) T) ↔
      x ∉ Tomabechi.Examples.Theorem27Op.ringE T := by
  rw [continuousGainPZS_iff_value_zero,
    Tomabechi.Examples.Theorem27Op.ringE_eq]
  simp

/-- 族全体の非 PZS 判定は、選んだ最大信号を既存の 27-A の作動量の計算に入れ、その最適な閉ループ経路について a.e. で正の作動を証明する。 -/
theorem continuousGain_ignorance_has_27_action
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T)
    (hnot : ¬ continuousGainPZS (x 0) T) :
    (∀ t, Tomabechi.Examples.Theorem27Op.flowE x T t ∉
      Tomabechi.Examples.Theorem27Op.ringE t) ∧
      ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
        0 < -(inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            (Tomabechi.Examples.Theorem27Op.u0E x T t -
              Tomabechi.Examples.Theorem27Op.utrE x T t))) := by
  have hxnot : x 0 ≠ 0 := by
    intro hx0
    apply hnot
    apply (continuousGainPZS_iff_value_zero (x 0) T).2
    simp [hx0]
  exact Tomabechi.Examples.Theorem27Op.ignorance_gives_action x T hT hxnot

/-- データレベルの PZS の判定は、27-A の運用上の無明の判定と、その確立済みの正の作動量を保つ。 -/
theorem multiPolicy_ignorance_has_27_action
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T)
    (hnot : ¬ FeedbackPZS (multiPolicyData.admissible (⊤ : SourceAbstraction))
      futureLebesgueMeasure
      (fun π y t s => multiPolicyData.runningCost (⊤ : SourceAbstraction) π
        (multiPolicyData.trajectory (⊤ : SourceAbstraction) π y t s) s) (x 0) T) :
    (∀ t, Tomabechi.Examples.Theorem27Op.flowE x T t ∉
      Tomabechi.Examples.Theorem27Op.ringE t) ∧
      ∀ᵐ t ∂futureLebesgueMeasure T, T ≤ t →
        0 < -(inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE
            (Tomabechi.Examples.Theorem27Op.u0E x T t -
              Tomabechi.Examples.Theorem27Op.utrE x T t))) := by
  have hcontinuous : ¬ continuousGainPZS (x 0) T := by
    intro hpzs
    apply hnot
    apply (multiPolicyPZS_iff_zero (x 0) T hT).2
    exact sq_eq_zero_iff.mp
      ((continuousGainPZS_iff_value_zero (x 0) T).1 hpzs)
  exact continuousGain_ignorance_has_27_action x T hT hcontinuous



/-- 非負ゲインを無制限に許すと、費用は任意に小さくできる。 -/
theorem unbounded_gain_cost_below (r₀ μ T ε : ℝ)
    (hμ : 0 ≤ μ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ cost r₀ μ K T < ε := by
  by_cases hr : r₀ = 0
  · refine ⟨0, le_rfl, ?_⟩
    rw [cost_eq r₀ μ 0 T (by dsimp [rate]; nlinarith)]
    rw [hr]
    simpa [hr] using hε
  · let K := 3 * r₀ ^ 2 / ε
    refine ⟨K, by positivity, ?_⟩
    rw [cost_eq r₀ μ K T (by dsimp [rate]; positivity)]
    have hden : 1 + 2 * rate μ (3 * r₀ ^ 2 / ε) > 0 := by
      dsimp [rate]; positivity
    have hbound : 3 * r₀ ^ 2 / (1 + 2 * rate μ (3 * r₀ ^ 2 / ε)) < ε := by
      dsimp [rate]
      apply (div_lt_iff₀ hden).2
      have hs : 0 ≤ r₀ ^ 2 := sq_nonneg r₀
      dsimp [rate]
      field_simp [ne_of_gt hε]
      nlinarith [hμ, hε, hs]
    exact hbound

/-- 非零初期値では、各有限ゲインの割引費用は厳密に正。 -/
theorem finite_gain_cost_positive (r₀ μ K T : ℝ)
    (hμ : 0 ≤ μ) (hK : 0 ≤ K) (hr₀ : r₀ ≠ 0) :
    0 < cost r₀ μ K T := by
  have hden : 0 < 1 + 2 * rate μ K := by dsimp [rate]; positivity
  rw [cost_eq r₀ μ K T hden]
  positivity

/-- 無制限ゲイン族の下限は0だが、非零初期値ではどの有限ゲインも達成しない。 -/
theorem zero_infimum_not_attained (r₀ μ T : ℝ)
    (hμ : 0 ≤ μ) (hr₀ : r₀ ≠ 0) :
    (∀ ε > 0, ∃ K ≥ 0, cost r₀ μ K T < ε) ∧
      (∀ K ≥ 0, 0 < cost r₀ μ K T) := by
  constructor
  · intro ε hε
    obtain ⟨K, hK, hcost⟩ := unbounded_gain_cost_below r₀ μ T ε hμ hε
    exact ⟨K, hK, hcost⟩
  · intro K hK
    exact finite_gain_cost_positive r₀ μ K T hμ hK hr₀

/-- 有限定数ゲイン軌道を費用ごと含む連続経路族への適用。
埋め込み条件は、有限ゲインの軌道と拡張実数費用を保つことを表す。
ただし、この旧宣言の全実数ゲインへの費用一致は矛盾する。
適用には後続の非負ゲイン限定版を使う。 -/
theorem continuous_extension_of_finite_gains_zero_infimum_not_attained
    {P : Type*} (path : P → ℝ → ℝ) (T r₀ μ : ℝ)
    (familyCost : P → ENNReal) (embed : ℝ → P)
    (hcontinuous : ∀ p, Continuous (path p))
    (hinitial : ∀ p, path p T = r₀)
    (hr₀ : r₀ ≠ 0) (hμ : 0 ≤ μ)
    (hcost : ∀ p, familyCost p = ∫⁻ s,
      ENNReal.ofReal (Real.exp (-(s - T)) * (3 * path p s ^ 2))
        ∂futureLebesgueMeasure T)
    (hembed_path : ∀ K s, path (embed K) s = orbit r₀ μ K T s)
    (hembed_cost : ∀ K, familyCost (embed K) = ENNReal.ofReal (cost r₀ μ K T)) :
    (∀ ε : ℝ, 0 < ε → ∃ p, familyCost p < ENNReal.ofReal ε) ∧
      (∀ p, 0 < familyCost p) := by
  apply continuous_family_zero_infimum_not_attained path T familyCost hcontinuous
  · intro p
    rw [hinitial p]
    exact hr₀
  · exact hcost
  · intro ε hε
    obtain ⟨K, hK, hsmall⟩ := unbounded_gain_cost_below r₀ μ T ε hμ hε
    refine ⟨embed K, ?_⟩
    rw [hembed_cost K]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hsmall

/-- 負ゲイン `K=-μ-1/2` では割引被積分関数が定数となる。
非零初期値なら積分は発散するが、実数Bochner積分の値は0になる。
この値を拡張実数費用と同一視してはならない。 -/
theorem critical_negative_gain_bochner_cost_zero (r₀ μ T : ℝ) :
    cost r₀ μ (-μ - 1 / 2) T = 0 := by
  have hpoint (s : ℝ) : theorem26DiscountWeight 1 T s *
      (3 * orbit r₀ μ (-μ - 1 / 2) T s ^ 2) = 3 * r₀ ^ 2 := by
    simp only [theorem26DiscountWeight, orbit, rate, mul_pow]
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (2 : ℝ) * (-(μ + (-μ - 1 / 2)) * (s - T)) = s - T := by ring
    rw [he]
    calc
      Real.exp (-1 * (s - T)) * (3 * (r₀ ^ 2 * Real.exp (s - T))) =
          3 * r₀ ^ 2 * (Real.exp (-1 * (s - T)) * Real.exp (s - T)) := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  unfold cost
  simp_rw [hpoint]
  simp [integral_const, measureReal_def, futureLebesgueMeasure]

/-- 連続経路の非負拡張実数費用を、負ゲインを含む全実数ゲインの
実数Bochner費用に一致させる前提は矛盾する。旧埋め込み補題の量化の限界。 -/
theorem unrestricted_gain_cost_embedding_impossible
    {P : Type*} (path : P → ℝ → ℝ) (T r₀ μ : ℝ)
    (familyCost : P → ENNReal) (embed : ℝ → P)
    (hcontinuous : ∀ p, Continuous (path p))
    (hinitial : ∀ p, path p T = r₀) (hr₀ : r₀ ≠ 0)
    (hcost : ∀ p, familyCost p = ∫⁻ s,
      ENNReal.ofReal (Real.exp (-(s - T)) * (3 * path p s ^ 2))
        ∂futureLebesgueMeasure T)
    (hembed_cost : ∀ K, familyCost (embed K) = ENNReal.ofReal (cost r₀ μ K T)) :
    False := by
  let p := embed (-μ - 1 / 2)
  have hpos : 0 < familyCost p := by
    rw [hcost p]
    apply continuous_path_discounted_cost_pos (path p) T (hcontinuous p)
    rw [hinitial p]
    exact hr₀
  have hzero : familyCost p = 0 := by
    rw [hembed_cost, critical_negative_gain_bochner_cost_zero]
    simp
  rw [hzero] at hpos
  exact (lt_irrefl _ hpos)

/-- 非負有限ゲインの費用を保つ埋め込みだけで、連続経路族の費用下限0と
非達成を得る。負ゲインの発散Bochner費用との一致は要求しない。
全経路の連続性・共通初期値・拡張実数費用の定義は明示した条件である。 -/
theorem continuous_extension_of_nonnegative_gains_zero_infimum_not_attained
    {P : Type*} (path : P → ℝ → ℝ) (T r₀ μ : ℝ)
    (familyCost : P → ENNReal) (embed : {K : ℝ // 0 ≤ K} → P)
    (hcontinuous : ∀ p, Continuous (path p))
    (hinitial : ∀ p, path p T = r₀)
    (hr₀ : r₀ ≠ 0) (hμ : 0 ≤ μ)
    (hcost : ∀ p, familyCost p = ∫⁻ s,
      ENNReal.ofReal (Real.exp (-(s - T)) * (3 * path p s ^ 2))
        ∂futureLebesgueMeasure T)
    (hembed_cost : ∀ K, familyCost (embed K) = ENNReal.ofReal (cost r₀ μ K T)) :
    (∀ ε : ℝ, 0 < ε → ∃ p, familyCost p < ENNReal.ofReal ε) ∧
      (∀ p, 0 < familyCost p) := by
  apply continuous_family_zero_infimum_not_attained path T familyCost hcontinuous
  · intro p
    rw [hinitial p]
    exact hr₀
  · exact hcost
  · intro ε hε
    obtain ⟨K, hK, hsmall⟩ := unbounded_gain_cost_below r₀ μ T ε hμ hε
    refine ⟨embed ⟨K, hK⟩, ?_⟩
    rw [hembed_cost]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hsmall

/-- 非負有限ゲインの有限費用は、同じ軌道の拡張実数積分と一致する。
非零初期値では既存の正値評価からBochner可積分性も確認できる。 -/
theorem nonnegative_gain_extended_cost_eq (r₀ μ K T : ℝ)
    (hμ : 0 ≤ μ) (hK : 0 ≤ K) (hr₀ : r₀ ≠ 0) :
    (∫⁻ s, ENNReal.ofReal (Real.exp (-(s - T)) * (3 * orbit r₀ μ K T s ^ 2))
      ∂futureLebesgueMeasure T) = ENNReal.ofReal (cost r₀ μ K T) := by
  have hpos := finite_gain_cost_positive r₀ μ K T hμ hK hr₀
  have hInt : Integrable (fun s => theorem26DiscountWeight 1 T s *
      (3 * orbit r₀ μ K T s ^ 2)) (futureLebesgueMeasure T) := by
    by_contra h
    have hz : cost r₀ μ K T = 0 := integral_undef h
    exact (ne_of_gt hpos) hz
  have hnonneg : 0 ≤ᵐ[futureLebesgueMeasure T]
      (fun s => theorem26DiscountWeight 1 T s * (3 * orbit r₀ μ K T s ^ 2)) := by
    filter_upwards with s
    unfold theorem26DiscountWeight
    positivity
  simpa [cost, theorem26DiscountWeight] using
    (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm

/-- 共通の非零初期値を持つ全連続経路の族で、割引二次費用の下限0は非達成。
非負有限ゲイン軌道の埋め込みをここで実際に構成する。
任意のBorel方策についてODE解が存在するという主張は含まない。 -/
theorem continuous_paths_zero_infimum_not_attained (T r₀ μ : ℝ)
    (hμ : 0 ≤ μ) (hr₀ : r₀ ≠ 0) :
    let P := {r : ℝ → ℝ // Continuous r ∧ r T = r₀}
    let pathCost := fun p : P => ∫⁻ s,
      ENNReal.ofReal (Real.exp (-(s - T)) * (3 * p.1 s ^ 2))
        ∂futureLebesgueMeasure T
    (∀ ε : ℝ, 0 < ε → ∃ p : P, pathCost p < ENNReal.ofReal ε) ∧
      (∀ p : P, 0 < pathCost p) := by
  let P := {r : ℝ → ℝ // Continuous r ∧ r T = r₀}
  let embed : {K : ℝ // 0 ≤ K} → P := fun K =>
    ⟨orbit r₀ μ K.1 T, by unfold orbit; fun_prop, orbit_initial r₀ μ K.1 T⟩
  apply continuous_extension_of_nonnegative_gains_zero_infimum_not_attained
    (fun p : P => p.1) T r₀ μ _ embed (fun p => p.2.1) (fun p => p.2.2)
      hr₀ hμ (fun _ => rfl)
  intro K
  exact nonnegative_gain_extended_cost_eq r₀ μ K.1 T hμ K.2 hr₀

/-- ゼロから離れたところでは `b(x)=1`、`b(0)=0` となる不連続な作動場をもつ Borel フィードバック。 -/
def discontinuousBorelFeedback : BorelMarkovFeedback ℝ ℝ where
  action := fun p => if p.2 = 0 then 0 else 1
  measurable_action := by
    exact Measurable.ite
      (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const

def restPath : ℝ → ℝ := fun _ => 0
def departingPath : ℝ → ℝ := id

/-- 同じ Borel フィードバックが、0 から出る 2 つの異なる絶対的に滑らかな前向き軌道を許す：静止と、`x(t)=t` に沿った出発。それぞれの方程式はすべての正の時刻で成り立ち、初期時刻の 1 点は a.e. の ODE には影響しない。したがって、Borel 可測性だけでは一意な軌道は得られない。 -/
theorem borel_feedback_has_nonunique_forward_solutions :
    restPath 0 = departingPath 0 ∧
      (∀ t, 0 < t →
        HasDerivAt restPath
          (discontinuousBorelFeedback.action (t, restPath t)) t ∧
        HasDerivAt departingPath
          (discontinuousBorelFeedback.action (t, departingPath t)) t) ∧
      restPath 1 ≠ departingPath 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro t ht
    constructor
    · have hfield : discontinuousBorelFeedback.action (t, restPath t) = 0 := by
        simp [discontinuousBorelFeedback, restPath]
      rw [hfield]
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t
      exact hasDerivAt_const t 0
    · have hfield : discontinuousBorelFeedback.action (t, departingPath t) = 1 := by
        simp [discontinuousBorelFeedback, departingPath, ne_of_gt ht]
      rw [hfield]
      change HasDerivAt (fun s : ℝ => s) 1 t
      exact hasDerivAt_id t
  · norm_num [restPath, departingPath]

end Tomabechi.Examples.Theorem26_27ControlClasses
