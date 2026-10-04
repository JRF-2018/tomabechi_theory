import Theorem1

/-!
# 定理1の Python 例 (`examples/theorem01_receding_horizon.py`) の Lean 根拠

二重井戸 `V0(x)=(x²-1)²+0.3x`、閾値 `θ=0`、`TCZ={V0≤0}`（左の谷。`-1∈TCZ`、`V0(-1)=-0.3`）。

**Lean が検証する閉ループは2つで、Python の有限地平 argmin 反復そのものではない:**
* (A) 目標点フィードバック `ẋ=-(x+1)`（目標 `g=-1∈TCZ`）、初期点 `x0=-1/2`。補題0の前提
  （残差 `Φ=[V0]₊` のAC、a.e.下降 `Φ'≤-2cΦ`（`c=2/5`）、誤差境界 `dist²≤CΦ`（`C=1/6`）、TCZ非空）を
  証明し、定理1の一般結論 `dist(x(t),TCZ)≤√(CΦ(0)) e^{-ct}` を得る。
  （Python では (A)(C) の反復ホライズンが結果として目標側の谷へ向かうことを数値で見るだけで、
  その反復の下降条件は証明していない。）
* (B) 反例側: 局所谷の停留点 `x_loc∈(0.9,1)`（`V0'(x_loc)=0`、`V0(x_loc)>0`）では、定数軌道が閉ループ
  `ẋ=-V0'(x)`（零フィードバック）の解で、補題0の下降条件が破れ、TCZ への距離は正のまま。
  「argmin だから収束」は出ない、という原文の注意の具体例（反復ホライズン方策が実際にこの点に
  留まることは証明していない）。
-/

namespace Tomabechi.Examples.Theorem1DoubleWell

open Tomabechi.Theorem1 MeasureTheory

noncomputable def V0 (x : ℝ) : ℝ := (x ^ 2 - 1) ^ 2 + 3 / 10 * x
noncomputable def dV0 (x : ℝ) : ℝ := 4 * x ^ 3 - 4 * x + 3 / 10

theorem hasDerivAt_V0 (x : ℝ) : HasDerivAt V0 (dV0 x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * x) x := by
    have := (hasDerivAt_pow 2 x).sub_const 1
    exact this.congr_deriv (by simp)
  have h2 := h1.pow 2
  have h3 := (hasDerivAt_id x).const_mul (3 / 10 : ℝ)
  have h4 := h2.add h3
  unfold V0
  exact h4.congr_deriv (by unfold dV0; simp; ring)

theorem continuous_V0 : Continuous V0 := by unfold V0; fun_prop

/-- 目標側の谷 `[-1,-3/4]` では `V0<0`（TCZ 内）。 -/
theorem V0_neg_left (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ -3 / 4) : V0 x < 0 := by
  unfold V0
  nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (by linarith : 0 ≤ -3 / 4 - x),
    sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x + 3 / 4)]

/-- `[-3/4,-1/2]` で `V0' ≥ 3/2`。 -/
theorem dV0_ge (x : ℝ) (h1 : -3 / 4 ≤ x) (h2 : x ≤ -1 / 2) : 3 / 2 ≤ dV0 x := by
  unfold dV0
  nlinarith [mul_nonneg (by linarith : 0 ≤ x + 3 / 4) (by linarith : 0 ≤ -1 / 2 - x),
    sq_nonneg x, mul_nonneg (mul_nonneg (by linarith : 0 ≤ x + 3 / 4) (by linarith : 0 ≤ -1 / 2 - x)) (by linarith : 0 ≤ -x)]

/-- `[-3/4,-1/2]` で `V0 ≤ 33/80`。 -/
theorem V0_le_mid (x : ℝ) (h1 : -3 / 4 ≤ x) (h2 : x ≤ -1 / 2) : V0 x ≤ 33 / 80 := by
  unfold V0
  nlinarith [mul_nonneg (by linarith : 0 ≤ x + 3 / 4) (by linarith : 0 ≤ -1 / 2 - x),
    sq_nonneg (x ^ 2 - 9 / 16)]

/-- 下降の核: `[-3/4,-1/2]` で `(4/5) V0 ≤ V0'·(x+1)`。 -/
theorem desc_ineq (x : ℝ) (h1 : -3 / 4 ≤ x) (h2 : x ≤ -1 / 2) :
    4 / 5 * V0 x ≤ dV0 x * (x + 1) := by
  have h3 := dV0_ge x h1 h2
  have h4 := V0_le_mid x h1 h2
  nlinarith

/-- `[-1,-1/2]` で `V0' ≥ 3/10`（`V0` は狭義増加）。 -/
theorem dV0_pos (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ -1 / 2) : 3 / 10 ≤ dV0 x := by
  unfold dV0
  nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (by linarith : 0 ≤ -1 / 2 - x),
    mul_nonneg (by linarith : 0 ≤ -x) (by nlinarith : 0 ≤ 1 - x ^ 2)]

/-- 閉ループ `ẋ=-(x+1)`（目標 `g=-1`）の解、初期点 `x(0)=-1/2`。 -/
noncomputable def xA (t : ℝ) : ℝ := -1 + 1 / 2 * Real.exp (-t)

theorem hasDerivAt_xA (t : ℝ) : HasDerivAt xA (-(xA t + 1)) t := by
  have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t :=
    ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring)
  have h2 := (h.const_mul (1 / 2 : ℝ)).const_add (-1 : ℝ)
  unfold xA
  exact h2.congr_deriv (by ring)

theorem xA_zero : xA 0 = -1 / 2 := by norm_num [xA]

theorem xA_range (t : ℝ) (ht : 0 ≤ t) : -1 < xA t ∧ xA t ≤ -1 / 2 := by
  unfold xA
  have h1 : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  constructor <;> linarith

/-- `TCZ={V0≤0}`（定理1の `K=univ`、時刻不変）。 -/
def TCZset : Set ℝ := {x | x ∈ (Set.univ : Set ℝ) ∧ V0 x ≤ 0}

theorem TCZ_nonempty : TCZset.Nonempty := ⟨-1, trivial, by norm_num [V0]⟩

/-- 誤差境界 `dist(x,TCZ)² ≤ (1/6)[V0 x]₊`（`x∈[-1,-1/2]`）。 -/
theorem error_bound (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ -1 / 2) :
    Metric.infDist x TCZset ^ 2 ≤ 1 / 6 * max (V0 x - 0) 0 := by
  by_cases hV : V0 x ≤ 0
  · have hx : x ∈ TCZset := ⟨trivial, hV⟩
    rw [Metric.infDist_zero_of_mem hx]
    have := le_max_right (V0 x - 0) 0
    nlinarith
  · have hV' : 0 < V0 x := not_le.mp hV
    have hx34 : -3 / 4 < x := by
      by_contra h
      exact hV (V0_neg_left x h1 (not_lt.mp h)).le
    obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc (le_of_lt hx34) continuous_V0.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (V0 (-3 / 4)) (V0 x) from
        ⟨(V0_neg_left (-3 / 4) (by norm_num) le_rfl).le, hV'.le⟩)
    have hqS : q ∈ TCZset := ⟨trivial, hq0.le⟩
    have hdist : Metric.infDist x TCZset ≤ x - q := by
      have := Metric.infDist_le_dist_of_mem (x := x) hqS
      rwa [Real.dist_eq, abs_of_nonneg (by linarith [hq.2])] at this
    have hmvt : 3 / 2 * (x - q) ≤ V0 x - V0 q := by
      refine (convex_Icc q x).mul_sub_le_image_sub_of_le_deriv (f := V0)
        continuous_V0.continuousOn (fun y _ => (hasDerivAt_V0 y).differentiableAt.differentiableWithinAt)
        (fun y hy => ?_) q (Set.left_mem_Icc.2 hq.2) x (Set.right_mem_Icc.2 hq.2) hq.2
      rw [interior_Icc] at hy
      rw [(hasDerivAt_V0 y).deriv]
      exact dV0_ge y (by linarith [hq.1, hy.1]) (by linarith [hy.2])
    rw [hq0, sub_zero] at hmvt
    have hbig : x - q ≤ 1 / 4 := by linarith [hq.1]
    have h0 : 0 ≤ x - q := by linarith [hq.2]
    have hd0 : 0 ≤ Metric.infDist x TCZset := Metric.infDist_nonneg
    rw [show max (V0 x - 0) 0 = V0 x by simp [hV'.le]]
    nlinarith

/-- `g(s)=V0(x(s))` は滑らか。 -/
theorem contDiff_g : ContDiff ℝ 1 (fun s => V0 (xA s)) := by
  unfold V0 xA; fun_prop

/-- 残差 `Φ(s)=[V0(x(s))]₊` は絶対連続。 -/
theorem residual_ac (t : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => Tomabechi.Theorem1.residual1 (V0 (xA s)) 0) 0 t := by
  have hg : AbsolutelyContinuousOnInterval (fun s => V0 (xA s)) 0 t :=
    contDiff_g.contDiffOn.absolutelyContinuousOnInterval
  have hf : LipschitzWith 1 (fun r : ℝ => Tomabechi.Theorem1.residual1 r 0) := by
    unfold Tomabechi.Theorem1.residual1
    simpa using LipschitzWith.id.max_const (0 : ℝ)
  exact hf.comp_absolutelyContinuousOnInterval hg

/-- `V0∘x` は `t≥0` で狭義減少（`V0` は `[-1,-1/2]` で狭義増加、`x` は減少）。 -/
theorem g_strictAnti {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : V0 (xA b) < V0 (xA a) := by
  have hb := xA_range b (ha.trans hab.le)
  have ha' := xA_range a ha
  have hxlt : xA b < xA a := by
    unfold xA
    have := Real.exp_lt_exp.2 (show -b < -a by linarith)
    linarith
  have hmono : StrictMonoOn V0 (Set.Icc (-1 : ℝ) (-1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_V0.continuousOn ?_
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_V0 y).deriv]
    have := dV0_pos y hy.1.le hy.2.le
    linarith
  exact hmono ⟨hb.1.le, hb.2⟩ ⟨ha'.1.le, ha'.2⟩ hxlt

/-- `V0(x(s))=0` となる `s≥0` は高々1点。 -/
theorem zero_set_subsingleton : {s : ℝ | 0 ≤ s ∧ V0 (xA s) = 0}.Subsingleton := by
  intro a ha b hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := g_strictAnti ha.1 h
    rw [ha.2, hb.2] at this; exact lt_irrefl _ this
  · have := g_strictAnti hb.1 h
    rw [ha.2, hb.2] at this; exact lt_irrefl _ this

/-- a.e. 下降 `Φ' ≤ -(4/5)Φ`（すなわち `c=2/5`）。 -/
theorem residual_decay_ae (t : ℝ) :
    ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t),
      deriv (fun r => Tomabechi.Theorem1.residual1 (V0 (xA r)) 0) s ≤
        -2 * (2 / 5) * Tomabechi.Theorem1.residual1 (V0 (xA s)) 0 := by
  have hnull : volume {s : ℝ | 0 ≤ s ∧ V0 (xA s) = 0} = 0 :=
    zero_set_subsingleton.measure_zero _
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hsI
  have hs0 : 0 ≤ s := hsI.1
  have hne : V0 (xA s) ≠ 0 := fun h => hs ⟨hs0, h⟩
  have hrange := xA_range s hs0
  have hg : HasDerivAt (fun r => V0 (xA r)) (dV0 (xA s) * (-(xA s + 1))) s :=
    (hasDerivAt_V0 (xA s)).comp s (hasDerivAt_xA s)
  have hcont : Continuous (fun r => V0 (xA r)) := contDiff_g.continuous
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- V0∘x < 0 の近傍: Φ ≡ 0
    have hev : ∀ᶠ r in nhds s, V0 (xA r) < 0 := hcont.continuousAt.eventually (gt_mem_nhds hneg)
    have hEq : (fun r => Tomabechi.Theorem1.residual1 (V0 (xA r)) 0) =ᶠ[nhds s] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with r hr
      simp [Tomabechi.Theorem1.residual1, max_eq_right hr.le]
    rw [hEq.deriv_eq]
    simp [Tomabechi.Theorem1.residual1, max_eq_right hneg.le]
  · have hev : ∀ᶠ r in nhds s, 0 < V0 (xA r) := hcont.continuousAt.eventually (lt_mem_nhds hpos)
    have hEq : (fun r => Tomabechi.Theorem1.residual1 (V0 (xA r)) 0) =ᶠ[nhds s] fun r => V0 (xA r) := by
      filter_upwards [hev] with r hr
      simp [Tomabechi.Theorem1.residual1, max_eq_left hr.le]
    rw [hEq.deriv_eq, hg.deriv]
    have hx34 : -3 / 4 ≤ xA s := by
      by_contra h
      exact absurd hpos (not_lt.2 (V0_neg_left (xA s) hrange.1.le (by linarith [not_le.1 h])).le)
    have := desc_ineq (xA s) hx34 hrange.2
    simp [Tomabechi.Theorem1.residual1, max_eq_left hpos.le]
    nlinarith

/-- (A) 定理1の一般結論: `dist(x(t),TCZ) ≤ √(C Φ(0)) e^{-ct}`（`c=2/5`, `C=1/6`）。 -/
theorem theoremA (t : ℝ) (ht : 0 ≤ t) :
    Metric.infDist (xA t) TCZset ≤
      Real.sqrt (1 / 6 * Tomabechi.Theorem1.residual1 (V0 (xA 0)) 0) * Real.exp (-(2 / 5) * (t - 0)) := by
  have := theorem1_closed_loop_tcz_exponential_decay (X := ℝ) xA Set.univ (fun x _ => V0 x) 0 (2 / 5) (1 / 6)
    0 t (fun s _ => TCZ_nonempty) (residual_ac t) (residual_decay_ae t)
    (fun s hs => by
      have hr := xA_range s hs.1
      simpa [TCZset, Tomabechi.Theorem1.residual1] using error_bound (xA s) hr.1.le hr.2)
    (by norm_num) (by norm_num) ht
  simpa [TCZset] using this

/-! ## (B) 反例側: 局所谷の停留点 -/

theorem TCZ_closed : IsClosed TCZset := by
  have : TCZset = V0 ⁻¹' Set.Iic 0 := by ext x; simp [TCZset]
  rw [this]; exact isClosed_Iic.preimage continuous_V0

/-- `V0' ` は `(9/10,1)` に零点（局所谷の停留点）をもつ。 -/
theorem exists_local_stationary : ∃ x ∈ Set.Ioo (9 / 10 : ℝ) 1, dV0 x = 0 := by
  have hcont : Continuous dV0 := by unfold dV0; fun_prop
  obtain ⟨x, hx, h0⟩ := intermediate_value_Ioo (by norm_num : (9 / 10 : ℝ) ≤ 1) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (dV0 (9 / 10)) (dV0 1) from ⟨by norm_num [dV0], by norm_num [dV0]⟩)
  exact ⟨x, hx, h0⟩

/-- 停留点 `x_loc∈(9/10,1)` では `V0(x_loc) ≥ 27/100>0`（`θ=0` を超える）。 -/
theorem V0_pos_at_stationary (x : ℝ) (hx : x ∈ Set.Ioo (9 / 10 : ℝ) 1) : 27 / 100 ≤ V0 x := by
  unfold V0
  nlinarith [sq_nonneg (x ^ 2 - 1), hx.1]

/-- (B) 停留点 `x_loc` での定数軌道は閉ループ `ẋ=-V0'(x)` の解（`V0'(x_loc)=0`）で、
補題0の下降条件 `Φ'≤-2cΦ`（`c>0`）が破れ、TCZ への距離は正で一定のまま（収束しない）。 -/
theorem caseB (xloc : ℝ) (hx : xloc ∈ Set.Ioo (9 / 10 : ℝ) 1) (hstat : dV0 xloc = 0) :
    (∀ r : ℝ, HasDerivAt (fun _ : ℝ => xloc) (-dV0 xloc) r) ∧
    (∀ c : ℝ, 0 < c → ∀ s : ℝ, ¬ (deriv (fun _ : ℝ => Tomabechi.Theorem1.residual1 (V0 xloc) 0) s ≤
        -2 * c * Tomabechi.Theorem1.residual1 (V0 xloc) 0)) ∧
    0 < Metric.infDist xloc TCZset ∧
    ¬ Filter.Tendsto (fun _ : ℝ => Metric.infDist xloc TCZset) Filter.atTop (nhds 0) := by
  have hV := V0_pos_at_stationary xloc hx
  have hpos : 0 < Metric.infDist xloc TCZset := by
    refine (TCZ_closed.notMem_iff_infDist_pos TCZ_nonempty).1 ?_
    intro hmem; have := hmem.2; linarith
  refine ⟨fun r => by rw [hstat]; simpa using hasDerivAt_const r xloc, ?_, hpos, ?_⟩
  · intro c hc s h
    have hres : Tomabechi.Theorem1.residual1 (V0 xloc) 0 = V0 xloc := by
      simp [Tomabechi.Theorem1.residual1, max_eq_left (by linarith : (0 : ℝ) ≤ V0 xloc)]
    rw [hres] at h
    simp at h
    nlinarith
  · intro hT
    exact hpos.ne' (tendsto_nhds_unique tendsto_const_nhds hT)

end Tomabechi.Examples.Theorem1DoubleWell
