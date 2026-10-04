import Theorem4
import Tomabechi.Dynamics.GlobalFlow

/-!
# 定理4の Python 例 (`examples/theorem04_presence_weight.py`) の Lean 根拠

`Ṽ(x)=V0(x)-κ P(x) Q`、`V0(x)=½(x-1)²`、`P(x)=exp(-(x+1)²)`、`κ=2`、`Q∈{+1,0,-1}`。

* (a) `∂Ṽ/∂P=-κQ`（独立変数 `p,q` に対する偏微分）と、`Q>0` で臨場感増大が実効コストを下げ、
  `Q<0` で上げること。
* (b) 介入変数 `r` が `P=r`, `Q=1-2r` を同時に動かすと `dṼ/dr=-κ(1-4r)` で、
  `P↑`でも `r>1/4` では `Ṽ` が上がる（原文: 総変化の符号には追加条件が要る）。
* (c) `Ṽ_Q'(x)=(x-1)+4Q(x+1)e^{-(x+1)²}` の臨界点: `Q=+1` では `(-0.6,-0.4)` に、
  `Q=-1` では `(1,1.5)` に存在する。`x=-0.8` では両方とも `Ṽ'<0`（右へ流れる）で、
  `Q=+1` の左側区間 `[-0.8,-0.6]` は `Ṽ'<0`、`x=-0.4` では `Ṽ'>0`（閉区間 `[-0.8,-0.4]` が
  右端で流れが区間内向き）、`Q=-1` では `[-0.8,1)` 全域で `Ṽ'<0`（`x=-0.4` を通過する）。
* (d) `Q=0` の初期値 `-0.8` からの厳密勾配流と、`Q=±1` の大域前向きODE解の存在。
  二つの符号で局所谷区間の曲率が1より大きく、その区間内の臨界点が一意である。
* (e) `Q=±1` の指定初期値 `-0.8` から各谷入口への有限時間到達、局所残差のPL評価と指数減衰、
  初期時刻からの距離の指数評価を示す。`Q=1` は閾値0の原TCZへ到達して留まり、`Q=-1` では
  そのTCZが空である。

範囲外: 一般の非凸ポテンシャルから定理4の補題0に必要な下降条件・誤差境界を導くこと。
ここでの定量収束は指定した一変数モデルに限る。
-/

namespace Tomabechi.Examples.Theorem4

/-! ## (a) -/

/-- 独立変数 `p` について `∂/∂p [V0 - κ p q] = -κ q`。 -/
theorem partial_P (V0 κ q p : ℝ) :
    HasDerivAt (fun p => V0 - κ * p * q) (-κ * q) p := by
  have := ((hasDerivAt_id p).const_mul κ).mul_const q |>.const_sub V0
  exact this.congr_deriv (by ring)

theorem sign_of_partial (κ q : ℝ) (hκ : 0 < κ) :
    (0 < q → -κ * q < 0) ∧ (q < 0 → 0 < -κ * q) := by
  constructor <;> intro h <;> nlinarith

/-! ## (b) -/

/-- 介入 `r`: `Ṽ(r)=1-κ r(1-2r)`（`V0≡1`, `P=r`, `Q=1-2r`）。 -/
noncomputable def Vr (κ r : ℝ) : ℝ := 1 - κ * r * (1 - 2 * r)

theorem hasDerivAt_Vr (κ r : ℝ) : HasDerivAt (Vr κ) (-κ * (1 - 4 * r)) r := by
  have h := (((hasDerivAt_id r).const_mul κ).mul
    (((hasDerivAt_id r).const_mul 2).const_sub 1)).const_sub 1
  convert h using 1
  · funext x; simp [Vr]
  · simp; ring

/-- `r>1/4`（かつ `κ>0`）で `P=r` が増えても `Ṽ` は上がる。 -/
theorem Vr_increases_after_quarter (κ r : ℝ) (hκ : 0 < κ) (hr : 1 / 4 < r) :
    0 < -κ * (1 - 4 * r) := by nlinarith

theorem Vr_decreases_before_quarter (κ r : ℝ) (hκ : 0 < κ) (hr : r < 1 / 4) :
    -κ * (1 - 4 * r) < 0 := by nlinarith

/-! ## (c) 臨界点 -/

/-- `V0(x)=½(x-1)²`, `P(x)=exp(-(x+1)²)`, `κ=2`。 -/
noncomputable def Vt (Q x : ℝ) : ℝ := 1 / 2 * (x - 1) ^ 2 - 2 * Real.exp (-(x + 1) ^ 2) * Q
/-- `Ṽ_Q'(x)=(x-1)+4Q(x+1)e^{-(x+1)²}`。 -/
noncomputable def dVt (Q x : ℝ) : ℝ := (x - 1) + 4 * Q * (x + 1) * Real.exp (-(x + 1) ^ 2)

theorem hasDerivAt_Vt (Q x : ℝ) : HasDerivAt (Vt Q) (dVt Q x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 / 2 * (x - 1) ^ 2) (x - 1) x := by
    have := ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul (1 / 2))
    exact this.congr_deriv (by norm_num [id] <;> ring)
  have h2 : HasDerivAt (fun x : ℝ => -(x + 1) ^ 2) (-(2 * (x + 1))) x := by
    have := ((((hasDerivAt_id x).add_const 1).pow 2).neg)
    exact this.congr_deriv (by norm_num [id] <;> ring)
  have h3 := ((h2.exp).const_mul 2).mul_const Q
  have := h1.sub h3
  convert this using 1
  · funext y; simp [Vt]
  · simp [dVt]; ring

theorem continuous_dVt (Q : ℝ) : Continuous (dVt Q) := by unfold dVt; fun_prop

/-- Q=+1: `Ṽ'(-0.6)<0<Ṽ'(-0.4)`、したがって `(-0.6,-0.4)` に臨界点がある。 -/
theorem dVt_one_signs : dVt 1 (-(3 / 5)) < 0 ∧ 0 < dVt 1 (-(2 / 5)) := by
  constructor
  · unfold dVt
    have h : Real.exp (-(-(3 / 5) + 1) ^ 2) < 1 := by
      rw [Real.exp_lt_one_iff]; norm_num
    nlinarith [Real.exp_pos (-(-(3 / 5) + 1 : ℝ) ^ 2)]
  · unfold dVt
    have h : (16 / 25 : ℝ) ≤ Real.exp (-(-(2 / 5) + 1) ^ 2) := by
      have := Real.add_one_le_exp (-(-(2 / 5) + 1 : ℝ) ^ 2)
      norm_num at this ⊢; linarith
    nlinarith

theorem exists_critical_Q_pos : ∃ x ∈ Set.Ioo (-(3 / 5) : ℝ) (-(2 / 5)), dVt 1 x = 0 := by
  obtain ⟨x, hx, h0⟩ := intermediate_value_Ioo (by norm_num : (-(3 / 5) : ℝ) ≤ -(2 / 5))
    (continuous_dVt 1).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (dVt 1 (-(3 / 5))) (dVt 1 (-(2 / 5))) from
      ⟨by simpa using dVt_one_signs.1, by simpa using dVt_one_signs.2⟩)
  exact ⟨x, hx, h0⟩

/-- Q=-1: `Ṽ'(1)<0<Ṽ'(3/2)`、したがって `(1,3/2)` に臨界点がある。 -/
theorem exists_critical_Q_neg : ∃ x ∈ Set.Ioo (1 : ℝ) (3 / 2), dVt (-1) x = 0 := by
  have h1 : dVt (-1) 1 < 0 := by
    unfold dVt; norm_num; positivity
  have h2 : 0 < dVt (-1) (3 / 2) := by
    unfold dVt
    have h : (Real.exp (-(3 / 2 + 1) ^ 2))⁻¹ ≥ 1 + 25 / 4 + (25 / 4) ^ 2 / 2 := by
      rw [← Real.exp_neg, neg_neg]
      have := Real.quadratic_le_exp_of_nonneg (x := (25 / 4 : ℝ)) (by norm_num)
      norm_num at this ⊢; linarith
    have hpos := Real.exp_pos (-(3 / 2 + 1 : ℝ) ^ 2)
    have : Real.exp (-(3 / 2 + 1) ^ 2) ≤ 1 / (1 + 25 / 4 + (25 / 4) ^ 2 / 2) := by
      rw [le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_left h hpos.le
      rw [mul_inv_cancel₀ hpos.ne'] at this
      nlinarith
    norm_num at this ⊢; nlinarith
  obtain ⟨x, hx, h0⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 3 / 2)
    (continuous_dVt (-1)).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (dVt (-1) 1) (dVt (-1) (3 / 2)) from ⟨h1, h2⟩)
  exact ⟨x, hx, h0⟩

/-- 開始点 `x=-0.8` では `Q=±1` のどちらでも `Ṽ'<0`（右へ流れる）。 -/
theorem start_flows_right : dVt 1 (-(4 / 5)) < 0 ∧ dVt (-1) (-(4 / 5)) < 0 := by
  have hexp := Real.exp_pos (-(-(4 / 5) + 1 : ℝ) ^ 2)
  have hlt : Real.exp (-(-(4 / 5) + 1 : ℝ) ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  constructor <;> (unfold dVt; norm_num; nlinarith)

/-- Q=+1: `[-0.8,-0.6]` で `Ṽ'<0`（左端から右へ進み、最初の臨界点は `(-0.6,-0.4)` 内）。 -/
theorem Qpos_negative_on_left (x : ℝ) (hx1 : -(4 / 5) ≤ x) (hx2 : x ≤ -(3 / 5)) : dVt 1 x < 0 := by
  unfold dVt
  have hexp := Real.exp_pos (-(x + 1) ^ 2)
  have hlt : Real.exp (-(x + 1) ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < (x + 1) ^ 2 := by nlinarith
    linarith
  nlinarith

/-- Q=-1: `[-0.8,1)` 全域で `Ṽ'<0`（`x=-0.4` を含む区間を通過する）。 -/
theorem Qneg_negative_on_path (x : ℝ) (hx1 : -(4 / 5) ≤ x) (hx2 : x < 1) : dVt (-1) x < 0 := by
  unfold dVt
  have hexp := Real.exp_pos (-(x + 1) ^ 2)
  nlinarith

/-- Q=+1 の勾配は、開始点より左側でも右向きである。 -/
theorem Qpos_negative_left_of_start (x : ℝ) (hx : x ≤ -(4 / 5)) :
    dVt 1 x < 0 := by
  by_cases hxminus : x ≤ -1
  · unfold dVt
    have hfactor : x + 1 ≤ 0 := by linarith
    have hexp := Real.exp_pos (-(x + 1) ^ 2)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hfactor hexp.le]
  · have hxlo : -1 < x := lt_of_not_ge hxminus
    unfold dVt
    have hfactor : 0 < x + 1 := by linarith
    have hupper : x + 1 ≤ 1 / 5 := by linarith
    have hexple : Real.exp (-(x + 1) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (x + 1)]
    nlinarith

/-- Q=-1 では `dVt` は全域 `x≤-4/5` で負。-/
theorem Qneg_negative_left_of_start (x : ℝ) (hx : x ≤ -(4 / 5)) :
    dVt (-1) x < 0 := by
  by_cases hxminus : x ≤ -1
  · let u : ℝ := -(x + 1)
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hexp := Real.exp_pos (u ^ 2)
    have hquad := Real.add_one_le_exp (u ^ 2)
    have hlinear : 2 * u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    have hmul := mul_le_mul_of_nonneg_right
      (hlinear.trans (by simpa [add_comm] using hquad)) (Real.exp_pos (-(u ^ 2))).le
    have hexpcancel : Real.exp (u ^ 2) * Real.exp (-(u ^ 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hbound : 2 * u * Real.exp (-(u ^ 2)) < 1 := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · have hstrict := Real.add_one_lt_exp (pow_ne_zero 2 hu0)
        have htwou : 2 * u < Real.exp (u ^ 2) := by nlinarith [hlinear]
        have hmulstrict := mul_lt_mul_of_pos_right htwou (Real.exp_pos (-(u ^ 2)))
        rw [hexpcancel] at hmulstrict
        exact hmulstrict
    unfold dVt
    have hxbase : x - 1 ≤ -2 := by linarith
    have hterm : 4 * u * Real.exp (-(u ^ 2)) < 2 := by nlinarith [hbound]
    have hxeq : x + 1 = -u := by dsimp [u]; ring
    rw [hxeq]
    have hexpeq : Real.exp (-(-u) ^ 2) = Real.exp (-(u ^ 2)) := by congr 1 <;> ring
    rw [hexpeq]
    nlinarith
  · have hxlo : -1 < x := lt_of_not_ge hxminus
    unfold dVt
    have hfactor : 0 ≤ x + 1 := by linarith
    have hexp := Real.exp_pos (-(x + 1) ^ 2)
    nlinarith [mul_nonneg hfactor hexp.le]

/-- Q=-1 の導関数は初期値の左側を含め、`x<1` で負。 -/
theorem Qneg_negative_for_all_x_lt_one (x : ℝ) (hx : x < 1) : dVt (-1) x < 0 := by
  by_cases hstart : x ≤ -(4 / 5)
  · exact Qneg_negative_left_of_start x hstart
  · exact Qneg_negative_on_path x (le_of_not_ge hstart) hx

/-- Q=+1 の導関数は `x≤-3/5` で負。 -/
theorem Qpos_negative_for_all_x_le_neg_three_fifths (x : ℝ)
    (hx : x ≤ -(3 / 5)) : dVt 1 x < 0 := by
  by_cases hstart : x ≤ -(4 / 5)
  · exact Qpos_negative_left_of_start x hstart
  · exact Qpos_negative_on_left x (le_of_not_ge hstart) hx

/-- Q=+1 の `x=-0.4` では `Ṽ'>0`（`[-0.8,-0.4]` の右端で内向き）。 -/
theorem Qpos_inward_at_right : 0 < dVt 1 (-(2 / 5)) := dVt_one_signs.2

/-! ## (d) Q=0 の厳密な勾配流

この場合は重み付き項が消え、勾配流を閉形式で書ける。Q=±1 の非線形流については
この計算を流用せず、後続のODE評価で別に扱う。
-/

/-- 初期値 `-4/5` から出発する、Q=0 の明示的な勾配流。 -/
noncomputable def flowQ0 (t : ℝ) : ℝ := 1 + (-(9 / 5)) * Real.exp (-t)

/-- 明示流は指定初期値を取る。 -/
theorem flowQ0_initial : flowQ0 0 = -(4 / 5) := by
  norm_num [flowQ0]

/-- 明示流の微分は、Q=0 の負の勾配 `1-x` に一致する。 -/
theorem flowQ0_hasDerivAt (t : ℝ) :
    HasDerivAt flowQ0 ((9 / 5) * Real.exp (-t)) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
  have hexp := hneg.exp
  have h := (hexp.const_mul (-(9 / 5))).const_add 1
  convert h using 1
  · funext s
    simp [flowQ0]
  · ring

/-- Q=0 の流れ方程式 `x'=-dVt(0,x)`。 -/
theorem flowQ0_gradient_flow (t : ℝ) :
    deriv flowQ0 t = -dVt 0 (flowQ0 t) := by
  have hd := (flowQ0_hasDerivAt t).deriv
  rw [hd]
  simp [dVt, flowQ0]

/-- Q=0 の状態誤差は全ての時刻で厳密に `9/5 · exp(-t)`。 -/
theorem flowQ0_error (t : ℝ) :
  |flowQ0 t - 1| = (9 / 5) * Real.exp (-t) := by
  rw [flowQ0]
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have harg : 1 + -(9 / 5) * Real.exp (-t) - 1 = -(9 / 5 * Real.exp (-t)) := by ring
  rw [harg]
  rw [abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) he.le)]

/-- Q=0 のポテンシャル残差は、初期値込みで率2の指数減衰をする。 -/
theorem flowQ0_residual (t : ℝ) :
  Vt 0 (flowQ0 t) = (81 / 50) * Real.exp (-2 * t) := by
  rw [Vt, flowQ0]
  have harg : 1 + -(9 / 5) * Real.exp (-t) - 1 = -(9 / 5 * Real.exp (-t)) := by ring
  have hexp : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [show -2 * t = (-t) + (-t) by ring, Real.exp_add]
    ring
  rw [harg, hexp]
  ring

/-! ### 谷候補の一意性を支える曲率

以下の曲率評価は、存在定理で得た臨界点が指定区間内で一意であることを示す。
-/

/-- 一階導関数 `dVt` の導関数を明示する。 -/
theorem hasDerivAt_dVt (Q x : ℝ) :
    HasDerivAt (dVt Q)
      (1 + 4 * Q * Real.exp (-(x + 1) ^ 2) * (1 - 2 * (x + 1) ^ 2)) x := by
  have hbase : HasDerivAt (fun z : ℝ => z - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have harg : HasDerivAt (fun z : ℝ => -(z + 1) ^ 2) (-2 * (x + 1)) x := by
    have h := (((hasDerivAt_id x).add_const 1).pow 2).neg
    convert h using 1
    · funext z
      change -(z + 1) ^ 2 = -(z + 1) ^ 2
      rfl
    · change -2 * (x + 1) = -(2 * (x + 1) ^ (2 - 1) * 1)
      norm_num
  have hexp := harg.exp
  have hmul := (((hasDerivAt_id x).add_const 1).const_mul (4 * Q)).mul hexp
  have h := hbase.add hmul
  convert h using 1
  · funext z
    simp [dVt, id]
  · simp
    ring_nf
/-- Q=+1 の指定谷区間では二階微分が1より大きく、導関数は厳密増加する。 -/
theorem dVt_deriv_gt_one_Q_pos (x : ℝ)
    (hx₁ : -(3 / 5) ≤ x) (hx₂ : x ≤ -(2 / 5)) :
    1 < deriv (dVt 1) x := by
  have hd := (hasDerivAt_dVt 1 x).deriv
  rw [hd]
  have hu₁ : 0 < x + 1 := by linarith
  have hu₂ : x + 1 < 1 := by linarith
  have hexp := Real.exp_pos (-(x + 1) ^ 2)
  have hfactor : 0 < 1 - 2 * (x + 1) ^ 2 := by nlinarith
  nlinarith [mul_pos hexp hfactor]

/-- Q=-1 の指定谷区間でも二階微分が1より大きい。 -/
theorem dVt_deriv_gt_one_Q_neg (x : ℝ)
    (hx₁ : 1 ≤ x) (hx₂ : x ≤ 3 / 2) :
    1 < deriv (dVt (-1)) x := by
  have hd := (hasDerivAt_dVt (-1) x).deriv
  rw [hd]
  have hu : 2 ≤ x + 1 := by linarith
  have huhi : x + 1 ≤ 5 / 2 := by linarith
  have hexp := Real.exp_pos (-(x + 1) ^ 2)
  have hfactor : 0 < 2 * (x + 1) ^ 2 - 1 := by nlinarith [hu, huhi]
  nlinarith [mul_pos hexp hfactor]

/-- Q=+1 の臨界点は `(-3/5,-2/5)` にただ一つ存在する。 -/
theorem exists_unique_critical_Q_pos :
    ∃! x ∈ Set.Ioo (-(3 / 5) : ℝ) (-(2 / 5)), dVt 1 x = 0 := by
  obtain ⟨x, hx, hzero⟩ := exists_critical_Q_pos
  refine ⟨x, ⟨hx, hzero⟩, ?_⟩
  intro y hy
  have hmono : StrictMonoOn (dVt 1) (Set.Icc (-(3 / 5 : ℝ)) (-(2 / 5))) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    · exact (continuous_dVt 1).continuousOn
    · intro z hz
      have hmem := interior_subset hz
      have h := dVt_deriv_gt_one_Q_pos z hmem.1 hmem.2
      exact lt_trans (by norm_num : (0 : ℝ) < 1) h
  have hxy : dVt 1 x = dVt 1 y := hzero.trans hy.2.symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy'
  · have hlt' := hmono ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩ hyx
    rw [hxy] at hlt'
    exact (lt_irrefl _ hlt')
  · have hgt' := hmono ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ hxy'
    rw [hxy] at hgt'
    exact (lt_irrefl _ hgt')

/-- Q=-1 の臨界点も `(1,3/2)` にただ一つ存在する。 -/
theorem exists_unique_critical_Q_neg :
    ∃! x ∈ Set.Ioo (1 : ℝ) (3 / 2), dVt (-1) x = 0 := by
  obtain ⟨x, hx, hzero⟩ := exists_critical_Q_neg
  refine ⟨x, ⟨hx, hzero⟩, ?_⟩
  intro y hy
  have hmono : StrictMonoOn (dVt (-1)) (Set.Icc (1 : ℝ) (3 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    · exact (continuous_dVt (-1)).continuousOn
    · intro z hz
      have hmem := interior_subset hz
      have h := dVt_deriv_gt_one_Q_neg z hmem.1 hmem.2
      exact lt_trans (by norm_num : (0 : ℝ) < 1) h
  have hxy : dVt (-1) x = dVt (-1) y := hzero.trans hy.2.symm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy'
  · have hlt' := hmono ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩ hyx
    rw [hxy] at hlt'
    exact lt_irrefl _ hlt'
  · have hgt' := hmono ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ hxy'
    rw [hxy] at hgt'
    exact lt_irrefl _ hgt'

/-- 指定した負側の谷における、`Q=1` の一意な臨界点。 -/
noncomputable def criticalPointQpos : ℝ := Classical.choose exists_critical_Q_pos

/-- 選んだ `Q=1` の臨界点は `(-3/5,-2/5)` に属し、停留点である。 -/
theorem criticalPointQpos_spec :
    criticalPointQpos ∈ Set.Ioo (-(3 / 5) : ℝ) (-(2 / 5)) ∧
      dVt 1 criticalPointQpos = 0 := by
  exact Classical.choose_spec exists_critical_Q_pos

/-- 指定した正側の谷における、`Q=-1` の一意な臨界点。 -/
noncomputable def criticalPointQneg : ℝ := Classical.choose exists_critical_Q_neg

/-- 選んだ `Q=-1` の臨界点は `(1,3/2)` に属し、停留点である。 -/
theorem criticalPointQneg_spec :
    criticalPointQneg ∈ Set.Ioo (1 : ℝ) (3 / 2) ∧
      dVt (-1) criticalPointQneg = 0 := by
  exact Classical.choose_spec exists_critical_Q_neg

/-- `Q=1` の導関数は、局所谷の区間で厳密に増加する。 -/
theorem dVt_Qpos_strictMonoOn :
    StrictMonoOn (dVt 1) (Set.Icc (-(3 / 5 : ℝ)) (-(2 / 5))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ..)
  · exact (continuous_dVt 1).continuousOn
  · intro z hz
    have hmem := interior_subset hz
    have h := dVt_deriv_gt_one_Q_pos z hmem.1 hmem.2
    exact lt_trans (by norm_num : (0 : ℝ) < 1) h

/-- `Q=-1` の導関数は、局所谷の区間で厳密に増加する。 -/
theorem dVt_Qneg_strictMonoOn :
    StrictMonoOn (dVt (-1)) (Set.Icc (1 : ℝ) (3 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ..)
  · exact (continuous_dVt (-1)).continuousOn
  · intro z hz
    have hmem := interior_subset hz
    have h := dVt_deriv_gt_one_Q_neg z hmem.1 hmem.2
    exact lt_trans (by norm_num : (0 : ℝ) < 1) h

/-- `Q=1` では、負の勾配は局所最小点までは右向きである。 -/
theorem dVt_Qpos_negative_before_minimum (x : ℝ)
    (hx : x < criticalPointQpos) : dVt 1 x < 0 := by
  by_cases hleft : x ≤ -(3 / 5)
  · exact Qpos_negative_for_all_x_le_neg_three_fifths x hleft
  · have hxlo : -(3 / 5) < x := lt_of_not_ge hleft
    have hxhi : x < -(2 / 5) := lt_trans hx criticalPointQpos_spec.1.2
    have hstrict := dVt_Qpos_strictMonoOn
      ⟨le_of_lt hxlo, le_of_lt hxhi⟩
      ⟨le_of_lt criticalPointQpos_spec.1.1, le_of_lt criticalPointQpos_spec.1.2⟩ hx
    rw [criticalPointQpos_spec.2] at hstrict
    exact hstrict

/-- `Q=-1` では、負の勾配は局所最小点までは右向きである。 -/
theorem dVt_Qneg_negative_before_minimum (x : ℝ)
    (hx : x < criticalPointQneg) : dVt (-1) x < 0 := by
  by_cases hleft : x < 1
  · exact Qneg_negative_for_all_x_lt_one x hleft
  · have hxlo : 1 ≤ x := le_of_not_gt hleft
    have hxhi : x < 3 / 2 := lt_trans hx criticalPointQneg_spec.1.2
    have hstrict := dVt_Qneg_strictMonoOn
      ⟨hxlo, le_of_lt hxhi⟩
      ⟨le_of_lt criticalPointQneg_spec.1.1, le_of_lt criticalPointQneg_spec.1.2⟩ hx
    rw [criticalPointQneg_spec.2] at hstrict
    exact hstrict

/-- Q=±1 の勾配ベクトル場。 -/
noncomputable def gradientField4 (Q x : ℝ) : ℝ := -dVt Q x

/-- 正負いずれの価値符号でも、指定初期値のエネルギーは4未満。 -/
theorem initial_energy_lt_four (Q : ℝ) (hQ : Q = 1 ∨ Q = -1) :
    Vt Q (-(4 / 5)) < 4 := by
  have hexp : 0 < Real.exp (-( -(4 / 5) + 1 : ℝ) ^ 2) := Real.exp_pos _
  have hexple : Real.exp (-( -(4 / 5) + 1 : ℝ) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  rcases hQ with hQ | hQ
  · rw [hQ]
    norm_num [Vt]
    nlinarith [hexp]
  · rw [hQ]
    norm_num [Vt]
    nlinarith [hexple]

/-- 勾配流上では `Vt` は単調非増加である。 -/
theorem potential_antitone_along_gradient_flow4
    (Q : ℝ) (t₀ t : ℝ) (orbit : ℝ → ℝ) (ht : t₀ ≤ t)
    (hflow : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt orbit (gradientField4 Q (orbit s)) s) :
    Vt Q (orbit t) ≤ Vt Q (orbit t₀) := by
  let along : ℝ → ℝ := fun s => Vt Q (orbit s)
  have hanti : AntitoneOn along (Set.Icc t₀ t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t)
    · intro s hs
      have h := (hasDerivAt_Vt Q (orbit s)).comp s (hflow s hs)
      exact h.continuousAt.continuousWithinAt
    · intro s hs
      have h := (hasDerivAt_Vt Q (orbit s)).comp s
        (hflow s (interior_subset hs))
      exact h.differentiableAt.differentiableWithinAt
    · intro s hs
      have h := (hasDerivAt_Vt Q (orbit s)).comp s
        (hflow s (interior_subset hs))
      have hd := h.deriv
      change deriv along s ≤ 0
      change deriv (fun r => Vt Q (orbit r)) s = _ at hd
      rw [hd]
      simp [gradientField4]
      nlinarith [sq_nonneg (dVt Q (orbit s))]
  have ht₀ : t₀ ∈ Set.Icc t₀ t := ⟨le_rfl, ht⟩
  have htmem : t ∈ Set.Icc t₀ t := ⟨ht, le_rfl⟩
  simpa [along] using hanti ht₀ htmem ht

/-- Q=±1 の実際の勾配流は、初期値を含むコンパクトなエネルギー部分準位内に存在する。
この段階では収束先・収束率をまだ主張しない。 -/
theorem exists_global_gradient_flow4 (Q : ℝ) (hQ : Q = 1 ∨ Q = -1) :
    ∃ orbit : ℝ → ℝ, ∃ ε : ℝ, 0 < ε ∧ orbit 0 = -(4 / 5) ∧
      (∀ t ∈ Set.Ici (0 : ℝ), Vt Q (orbit t) ≤ Vt Q (-(4 / 5))) ∧
      (∀ t ∈ Set.Ioi (-ε),
        HasDerivAt orbit (gradientField4 Q (orbit t)) t) ∧
      (∀ t ∈ Set.Ioi (-ε), orbit t ∈ Metric.ball (1 : ℝ) 6) := by
  let level : ℝ := Vt Q (-(4 / 5))
  let K : Set ℝ := {x | Vt Q x ≤ level}
  have hlevel : level < 4 := by exact initial_energy_lt_four Q hQ
  have hclosed : IsClosed K := by
    apply isClosed_le
    · fun_prop [Vt]
    · exact continuous_const
  have hKbound : K ⊆ Metric.closedBall (1 : ℝ) 4 := by
    intro x hx
    have hpotential := hx
    change Vt Q x ≤ level at hpotential
    have hexp := Real.exp_pos (-(x + 1) ^ 2)
    have hexple : Real.exp (-(x + 1) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (x + 1)]
    have hterm : -2 ≤ -2 * Real.exp (-(x + 1) ^ 2) * Q := by
      rcases hQ with hQ | hQ
      · rw [hQ]
        nlinarith [hexple]
      · rw [hQ]
        nlinarith [hexp]
    have hsq : (x - 1) ^ 2 ≤ 12 := by
      unfold Vt at hpotential
      dsimp [level] at hpotential
      nlinarith [hlevel, hterm]
    have habs : |x - 1| ≤ 4 := by
      nlinarith [sq_abs (x - 1), sq_nonneg (|x - 1| - 4)]
    simpa [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] using habs
  have hKcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      ((Metric.isBounded_iff_subset_closedBall (1 : ℝ)).2 ⟨4, hKbound⟩)
  have hKsubset : K ⊆ Metric.closedBall (1 : ℝ) 6 := by
    intro x hx
    have hdist := Metric.mem_closedBall.mp (hKbound hx)
    apply Metric.mem_closedBall.mpr
    linarith
  have hKinterior : K ⊆ Metric.ball (1 : ℝ) 6 := by
    intro x hx
    have hdist := Metric.mem_closedBall.mp (hKbound hx)
    exact Metric.mem_ball.mpr (by
      simpa [Real.dist_eq, Real.norm_eq_abs] using
        lt_of_le_of_lt hdist (by norm_num : (4 : ℝ) < 6))
  have hregular : ∀ x ∈ Metric.closedBall (1 : ℝ) 6,
      ContDiffAt ℝ 1 (gradientField4 Q) x := by
    intro x hx
    fun_prop [gradientField4, dVt]
  have hinvariant : ∀ (t₀ d : ℝ) (orbit : ℝ → ℝ) (x : ℝ),
      0 ≤ d → orbit t₀ = x → x ∈ K →
      (∀ t ∈ Set.Icc t₀ (t₀ + d),
        HasDerivAt orbit (gradientField4 Q (orbit t)) t) →
      ∀ t ∈ Set.Icc t₀ (t₀ + d), orbit t ∈ K := by
    intro t₀ d orbit x hd horbit hx hflow t ht
    change Vt Q (orbit t) ≤ level
    have htupper : t ≤ t₀ + d := ht.2
    have hdec := potential_antitone_along_gradient_flow4 Q t₀ t orbit ht.1
      (fun s hs => hflow s ⟨hs.1, le_trans hs.2 htupper⟩)
    have hinit : Vt Q (orbit t₀) ≤ level := by
      change Vt Q x ≤ level at hx
      simpa [horbit] using hx
    exact hdec.trans hinit
  have hx0 : (-(4 / 5) : ℝ) ∈ K := by
    change Vt Q (-(4 / 5)) ≤ level
    rfl
  obtain ⟨orbit, ε, hε, hinit, hforward, hflow, hball⟩ :=
    Tomabechi.Theorem21.exists_global_forward_trajectory_of_compact_forward_invariant_set
      (gradientField4 Q) K (1 : ℝ) 6 (by norm_num) hregular hKcompact hKsubset
      hKinterior hinvariant (-(4 / 5)) hx0 0
  exact ⟨orbit, ε, hε, hinit, hforward, by simpa using hflow, by simpa using hball⟩

/-- 定数でない勾配軌道は、有限時刻に平衡点へ到達できない。時間を反転すると、到達したと仮定した場合に同じ初期状態をもつ 2 つの解ができ、局所一意性により元の軌道は最初から平衡点にいたことになる。 -/
theorem gradientFlow4_ne_stationary_at_finite_time
    (Q ε : ℝ) (orbit : ℝ → ℝ) (T a : ℝ)
    (hε : 0 < ε) (hT : 0 ≤ T) (hinit : orbit 0 = -(4 / 5))
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hball : ∀ t ∈ Set.Ioi (-ε), orbit t ∈ Metric.ball (1 : ℝ) 6)
    (ha : gradientField4 Q a = 0) (haBall : a ∈ Metric.ball (1 : ℝ) 6)
    (hane : a ≠ -(4 / 5)) : orbit T ≠ a := by
  intro hhit
  let reverseField : ℝ → ℝ := fun x => -gradientField4 Q x
  let reverseOrbit : ℝ → ℝ := fun s => orbit (T - s)
  let stationary : ℝ → ℝ := fun _ => a
  have hregular : ∀ x ∈ Metric.closedBall (1 : ℝ) 6,
      ContDiffAt ℝ 1 reverseField x := by
    intro x hx
    change ContDiffAt ℝ 1 (fun y => - -dVt Q y) x
    fun_prop [dVt]
  let b : ℝ := T + ε / 2
  have hTb : T < b := by dsimp [b]; linarith
  have hreverseFlow : ∀ s ∈ Set.Ico (0 : ℝ) b,
      HasDerivAt reverseOrbit (reverseField (reverseOrbit s)) s := by
    intro s hs
    have hslt : s < T + ε / 2 := by simpa [b] using hs.2
    have htime : -ε < T - s := by linarith
    have hflow' := hflow (T - s) (Set.mem_Ioi.mpr htime)
    have harg' := (hasDerivAt_const s T).sub (hasDerivAt_id s)
    have harg : HasDerivAt (fun u : ℝ => T - u) (-1) s := by
      convert harg' using 1
      · funext u
        rfl
      · ring
    have hcomp := hflow'.comp s harg
    convert hcomp using 1
    · funext u
      rfl
    · simp [reverseField, gradientField4]
      ring
  have hreverseBall : ∀ s ∈ Set.Ico (0 : ℝ) b,
      reverseOrbit s ∈ Metric.closedBall (1 : ℝ) 6 := by
    intro s hs
    have hslt : s < T + ε / 2 := by simpa [b] using hs.2
    have htime : -ε < T - s := by linarith
    exact Metric.ball_subset_closedBall (hball (T - s) (Set.mem_Ioi.mpr htime))
  have hstationaryFlow : ∀ s ∈ Set.Ico (0 : ℝ) b,
      HasDerivAt stationary (reverseField (stationary s)) s := by
    intro s hs
    simpa [stationary, reverseField, ha] using (hasDerivAt_const s a)
  have hstationaryBall : ∀ s ∈ Set.Ico (0 : ℝ) b,
      stationary s ∈ Metric.closedBall (1 : ℝ) 6 := by
    intro s hs
    exact Metric.ball_subset_closedBall haBall
  have hinitial : reverseOrbit 0 = stationary 0 := by
    simp [reverseOrbit, stationary, hhit]
  have heq := Tomabechi.Theorem21.ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall
    reverseField (1 : ℝ) 6 0 b hregular reverseOrbit stationary
    hreverseBall hstationaryBall hreverseFlow hstationaryFlow hinitial
  have hTmem : T ∈ Set.Ico (0 : ℝ) b := ⟨hT, hTb⟩
  have hzero : orbit 0 = a := by
    have := heq hTmem
    simpa [reverseOrbit, stationary] using this
  exact hane (by simpa [hinit] using hzero.symm)

/-- 平衡点より下から出発した前向き解は、厳密にその下に留まる。越えれば有限時間到達になり、ODE の一意性で排除される。 -/
theorem gradientFlow4_stays_below_equilibrium
    (Q ε : ℝ) (orbit : ℝ → ℝ) (a : ℝ)
    (hε : 0 < ε) (hinit : orbit 0 = -(4 / 5)) (hinit_lt : orbit 0 < a)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hball : ∀ t ∈ Set.Ioi (-ε), orbit t ∈ Metric.ball (1 : ℝ) 6)
    (hstationary : gradientField4 Q a = 0)
    (haBall : a ∈ Metric.ball (1 : ℝ) 6) :
    ∀ t, 0 ≤ t → orbit t < a := by
  intro t ht
  have hane : a ≠ -(4 / 5) := by
    intro h
    rw [hinit, h] at hinit_lt
    norm_num at hinit_lt
  have hnotHit := gradientFlow4_ne_stationary_at_finite_time Q ε orbit t a
    hε ht hinit hflow hball hstationary haBall hane
  by_contra hlt
  have hge : a ≤ orbit t := le_of_not_gt hlt
  rcases lt_or_eq_of_le hge with hgt | heq
  · have hcont : ContinuousOn orbit (Set.Icc (0 : ℝ) t) := by
      intro s hs
      have htime : -ε < s := by linarith [hs.1]
      exact (hflow s (Set.mem_Ioi.mpr htime)).continuousAt.continuousWithinAt
    have hbetween : a ∈ Set.Icc (orbit 0) (orbit t) := ⟨hinit_lt.le, hgt.le⟩
    have himage : a ∈ orbit '' Set.Icc (0 : ℝ) t :=
      intermediate_value_Icc ht hcont hbetween
    obtain ⟨s, hs, hhit⟩ := himage
    have hnohitS := gradientFlow4_ne_stationary_at_finite_time Q ε orbit s a
      hε hs.1 hinit hflow hball hstationary haBall hane
    exact hnohitS (by simpa using hhit)
  · exact hnotHit heq.symm

/-- ベクトル場が平衡点の下側で右向きなら、対応する前向き軌道は、有限の未来区間のどこでも厳密に増加する。 -/
theorem gradientFlow4_strictMonoOn
    (Q ε : ℝ) (orbit : ℝ → ℝ) (a t : ℝ)
    (hε : 0 < ε) (ht : 0 ≤ t)
    (hflow : ∀ s ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit s)) s)
    (hbelow : ∀ s, 0 ≤ s → orbit s < a)
    (hgradientSign : ∀ x, x < a → dVt Q x < 0) :
    StrictMonoOn orbit (Set.Icc (0 : ℝ) t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
  · intro s hs
    have htime : -ε < s := by linarith [hs.1]
    exact (hflow s (Set.mem_Ioi.mpr htime)).continuousAt.continuousWithinAt
  · intro s hs
    have hspos : 0 < s := by
      have hs' : s ∈ Set.Ioo (0 : ℝ) t := by simpa [interior_Icc] using hs
      exact hs'.1
    have htime : -ε < s := by linarith
    have hd := (hflow s (Set.mem_Ioi.mpr htime)).deriv
    rw [hd]
    unfold gradientField4
    exact neg_pos.mpr (hgradientSign (orbit s) (hbelow s hspos.le))

/-- 連続な正のベクトル場は、初期状態から入口境界までのコンパクト区間上で、正の最小値をもつ。 -/
theorem gradientField4_positive_minimum
    (Q ε : ℝ) (orbit : ℝ → ℝ) (boundary equilibrium : ℝ)
    (hinitial : orbit 0 < boundary) (hboundary : boundary < equilibrium)
    (hgradientSign : ∀ x, x < equilibrium → dVt Q x < 0) :
    ∃ speed, 0 < speed ∧ ∀ x ∈ Set.Icc (orbit 0) boundary,
      speed ≤ gradientField4 Q x := by
  have hpositive : ∀ x ∈ Set.Icc (orbit 0) boundary,
      0 < gradientField4 Q x := by
    intro x hx
    unfold gradientField4
    exact neg_pos.mpr (hgradientSign x (lt_of_le_of_lt hx.2 hboundary))
  have hcontinuousField : ContinuousOn (gradientField4 Q) (Set.Icc (orbit 0) boundary) := by
    fun_prop [gradientField4, dVt]
  have hJne : (Set.Icc (orbit 0) boundary).Nonempty :=
    ⟨orbit 0, ⟨le_rfl, hinitial.le⟩⟩
  obtain ⟨z, hz, hzmin⟩ := isCompact_Icc.exists_isMinOn hJne hcontinuousField
  refine ⟨gradientField4 Q z, hpositive z hz, ?_⟩
  intro x hx
  exact hzmin hx

/-- 正の速度下限があれば、有限時間での横断が保証される。明示的な上界は、区間の長さを速度で割ったものに 1 時間単位を加えたもの。 -/
theorem gradientFlow4_enters_right_of
    (Q ε : ℝ) (orbit : ℝ → ℝ) (boundary equilibrium speed : ℝ)
    (hε : 0 < ε) (hinitial : orbit 0 < boundary) (hboundary : boundary < equilibrium)
    (hspeed : 0 < speed)
    (hspeed_le : ∀ x ∈ Set.Icc (orbit 0) boundary,
      speed ≤ gradientField4 Q x)
    (hflow : ∀ s ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit s)) s)
    (hbelow : ∀ s, 0 ≤ s → orbit s < equilibrium)
    (hgradientSign : ∀ x, x < equilibrium → dVt Q x < 0) :
    ∃ T, 0 ≤ T ∧ T ≤ (boundary - orbit 0) / speed + 1 ∧ boundary ≤ orbit T := by
  let T : ℝ := (boundary - orbit 0) / speed + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmono : StrictMonoOn orbit (Set.Icc (0 : ℝ) T) :=
    gradientFlow4_strictMonoOn Q ε orbit equilibrium T hε hT hflow hbelow hgradientSign
  have hcross : boundary ≤ orbit T := by
    by_contra hnot
    have hTlt : orbit T < boundary := lt_of_not_ge hnot
    have hstate : ∀ s ∈ Set.Icc (0 : ℝ) T,
        orbit s ∈ Set.Icc (orbit 0) boundary := by
      intro s hs
      have hlow : orbit 0 ≤ orbit s := by
        by_cases hzero : s = 0
        · simp [hzero]
        · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
          exact le_of_lt (hmono ⟨le_rfl, hT⟩ hs hspos)
      have hhigh : orbit s ≤ orbit T := by
        rcases lt_or_eq_of_le hs.2 with hlt | heq
        · exact (hmono hs ⟨hT, le_rfl⟩ hlt).le
        · simpa [heq]
      exact ⟨hlow, le_trans hhigh hTlt.le⟩
    have hcont : ContinuousOn orbit (Set.Icc (0 : ℝ) T) := by
      intro s hs
      have htime : -ε < s := by linarith [hs.1]
      exact (hflow s (Set.mem_Ioi.mpr htime)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ orbit (interior (Set.Icc (0 : ℝ) T)) := by
      intro s hs
      have htime : -ε < s := by linarith [(interior_subset hs).1]
      exact (hflow s (Set.mem_Ioi.mpr htime)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ s ∈ interior (Set.Icc (0 : ℝ) T),
        speed ≤ deriv orbit s := by
      intro s hs
      have htime : -ε < s := by linarith [(interior_subset hs).1]
      have hd := (hflow s (Set.mem_Ioi.mpr htime)).deriv
      rw [hd]
      have hmem := hstate s (interior_subset hs)
      exact hspeed_le (orbit s) hmem
    have hlinear := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hderiv
    have hlinear' := hlinear (0 : ℝ) (by exact ⟨le_rfl, hT⟩)
      T (by exact ⟨hT, le_rfl⟩) hT
    have hexpand : speed * T = boundary - orbit 0 + speed := by
      dsimp [T]
      field_simp [hspeed.ne']
    have hflowLower : speed * T ≤ orbit T - orbit 0 := by simpa using hlinear'
    nlinarith [hflowLower, hTlt, hinitial]
  refine ⟨T, hT, ?_, hcross⟩
  dsimp [T]
  linarith

/-- 指定した `Q=1` の軌道は、明示的な有限時間で、局所強凸谷の左端に到達する。 -/
theorem exists_Qpos_flow_reaches_valley_entry :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧
      0 ≤ T ∧ T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (-(3 / 5)) ≤ orbit T ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) ∧
      (∀ t, 0 ≤ t → orbit t < criticalPointQpos) := by
  obtain ⟨orbit, ε, hε, hinit, henergy, hflow, hball⟩ :=
    exists_global_gradient_flow4 1 (Or.inl rfl)
  have hbelow : ∀ t, 0 ≤ t → orbit t < criticalPointQpos := by
    apply gradientFlow4_stays_below_equilibrium 1 ε orbit criticalPointQpos
      hε hinit ?_ hflow hball ?_ ?_
    · linarith [criticalPointQpos_spec.1.1]
    · simp [gradientField4, criticalPointQpos_spec.2]
    · have hroot := criticalPointQpos_spec.1
      change |criticalPointQpos - 1| < 6
      rw [abs_lt]
      constructor <;> linarith [hroot.1, hroot.2]
  obtain ⟨speed, hspeed, hspeed_le⟩ :=
    gradientField4_positive_minimum 1 ε orbit (-(3 / 5)) criticalPointQpos
      (by rw [hinit]; norm_num) (by linarith [criticalPointQpos_spec.1.1])
      dVt_Qpos_negative_before_minimum
  obtain ⟨T, hT, hTbound, hreach⟩ :=
    gradientFlow4_enters_right_of 1 ε orbit (-(3 / 5)) criticalPointQpos speed
      hε (by rw [hinit]; norm_num) (by linarith [criticalPointQpos_spec.1.1])
      hspeed hspeed_le hflow hbelow dVt_Qpos_negative_before_minimum
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hreach, hflow, hbelow⟩

/-- 指定した `Q=-1` の軌道は、局所強凸谷より手前の `x=1` を、有限時間の明示的な上界つきで横断する。 -/
theorem exists_Qneg_flow_reaches_valley_entry :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧
      0 ≤ T ∧ T ≤ (1 - orbit 0) / speed + 1 ∧ 1 ≤ orbit T ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 (-1) (orbit t)) t) ∧
      (∀ t, 0 ≤ t → orbit t < criticalPointQneg) := by
  obtain ⟨orbit, ε, hε, hinit, henergy, hflow, hball⟩ :=
    exists_global_gradient_flow4 (-1) (Or.inr rfl)
  have hbelow : ∀ t, 0 ≤ t → orbit t < criticalPointQneg := by
    apply gradientFlow4_stays_below_equilibrium (-1) ε orbit criticalPointQneg
      hε hinit ?_ hflow hball ?_ ?_
    · linarith [criticalPointQneg_spec.1.1]
    · simp [gradientField4, criticalPointQneg_spec.2]
    · have hroot := criticalPointQneg_spec.1
      change |criticalPointQneg - 1| < 6
      rw [abs_lt]
      constructor <;> linarith [hroot.1, hroot.2]
  obtain ⟨speed, hspeed, hspeed_le⟩ :=
    gradientField4_positive_minimum (-1) ε orbit 1 criticalPointQneg
      (by rw [hinit]; norm_num) (by linarith [criticalPointQneg_spec.1.1])
      dVt_Qneg_negative_before_minimum
  obtain ⟨T, hT, hTbound, hreach⟩ :=
    gradientFlow4_enters_right_of (-1) ε orbit 1 criticalPointQneg speed
      hε (by rw [hinit]; norm_num) (by linarith [criticalPointQneg_spec.1.1])
      hspeed hspeed_le hflow hbelow dVt_Qneg_negative_before_minimum
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hreach, hflow, hbelow⟩

/-- 停留点の左側の強凸区間では、ポテンシャルの傾きは、その点までの距離の符号反転以下に抑えられる。 -/
theorem dVt_le_neg_distance_of_curvature
    (Q boundary root x : ℝ)
    (hboundary : boundary ≤ root)
    (hcurvature : ∀ z ∈ Set.Icc boundary root, 1 < deriv (dVt Q) z)
    (hstationary : dVt Q root = 0)
    (hx : x ∈ Set.Icc boundary root) :
    dVt Q x ≤ -(root - x) := by
  have hcontinuous : ContinuousOn (dVt Q) (Set.Icc boundary root) :=
    (continuous_dVt Q).continuousOn
  have hdifferentiable : DifferentiableOn ℝ (dVt Q)
      (interior (Set.Icc boundary root)) := by
    intro z hz
    have hz' : z ∈ Set.Icc boundary root := interior_subset hz
    exact (hasDerivAt_dVt Q z).differentiableAt.differentiableWithinAt
  have hderivative : ∀ z ∈ interior (Set.Icc boundary root),
      1 ≤ deriv (dVt Q) z := by
    intro z hz
    exact le_of_lt (hcurvature z (interior_subset hz))
  have hlinear := (convex_Icc boundary root).mul_sub_le_image_sub_of_le_deriv
    hcontinuous hdifferentiable hderivative
  have hcompare := hlinear x hx root ⟨hboundary, le_rfl⟩ hx.2
  rw [hstationary] at hcompare
  linarith

/-- 谷の区間では、停留した最小点とのポテンシャル差は勾配の 2 乗で抑えられる（局所 Polyak–Łojasiewicz 評価）。 -/
theorem gradientPotentialGap_le_grad_sq
    (Q boundary root x : ℝ) (hboundary : boundary ≤ root)
    (hcurvature : ∀ z ∈ Set.Icc boundary root, 1 < deriv (dVt Q) z)
    (hmono : StrictMonoOn (dVt Q) (Set.Icc boundary root))
    (hstationary : dVt Q root = 0) (hx : x ∈ Set.Icc boundary root) :
    0 ≤ Vt Q x - Vt Q root ∧ Vt Q x - Vt Q root ≤ (dVt Q x) ^ 2 := by
  by_cases hxr : x = root
  · rw [hxr, hstationary]
    simp
  · have hlt : x < root := lt_of_le_of_ne hx.2 hxr
    have hpositive : 0 < root - x := by linarith
    have hdistance := dVt_le_neg_distance_of_curvature Q boundary root x
      hboundary hcurvature hstationary hx
    have hcontinuous : ContinuousOn (Vt Q) (Set.Icc x root) := by
      fun_prop [Vt]
    have hdifferentiable : DifferentiableOn ℝ (Vt Q) (Set.Ioo x root) := by
      intro z hz
      exact (hasDerivAt_Vt Q z).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hmean⟩ :=
      exists_deriv_eq_slope (Vt Q) hlt hcontinuous hdifferentiable
    have hcIcc : c ∈ Set.Icc boundary root :=
      ⟨le_trans hx.1 hc.1.le, hc.2.le⟩
    have hdc : deriv (Vt Q) c = dVt Q c := (hasDerivAt_Vt Q c).deriv
    rw [hdc] at hmean
    have hmon := hmono hcIcc ⟨hboundary, le_rfl⟩ hc.2
    rw [hstationary] at hmon
    have hmonx := hmono hx hcIcc hc.1
    have hnegative : dVt Q x < 0 := by linarith [hdistance]
    have hgap_slope : Vt Q x - Vt Q root = -(dVt Q c) * (root - x) := by
      have hmul : dVt Q c * (root - x) = Vt Q root - Vt Q x := by
        have htmp := hmean
        field_simp [ne_of_gt hpositive] at htmp
        linarith
      nlinarith [hmul]
    have hgap_nonneg : 0 ≤ Vt Q x - Vt Q root := by
      rw [hgap_slope]
      exact mul_nonneg (neg_nonneg.mpr hmon.le) hpositive.le
    have hfirst : Vt Q x - Vt Q root ≤ -(dVt Q x) * (root - x) := by
      rw [hgap_slope]
      exact mul_le_mul_of_nonneg_right (by linarith [hmonx]) hpositive.le
    have hquad : (-(dVt Q x)) * (root - x) ≤ (dVt Q x) ^ 2 := by
      have hprod := mul_le_mul_of_nonneg_left
        (show root - x ≤ -(dVt Q x) by linarith [hdistance])
        (neg_nonneg.mpr hnegative.le)
      nlinarith [hprod]
    exact ⟨hgap_nonneg, le_trans hfirst hquad⟩

/-- 強凸谷へ左端から入った後、勾配軌道は少なくとも率 `exp(-t)` で停留点に近づく。 -/
theorem gradientFlow4_exponential_after_entry
    (Q ε boundary root T : ℝ) (orbit : ℝ → ℝ)
    (hboundary : boundary ≤ root)
    (hε : 0 < ε) (hT : 0 ≤ T) (hentry : boundary ≤ orbit T)
    (hbelow : ∀ t, 0 ≤ t → orbit t < root)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hgradientSign : ∀ x, x < root → dVt Q x < 0)
    (hcurvature : ∀ x ∈ Set.Icc boundary root, 1 < deriv (dVt Q) x)
    (hstationary : dVt Q root = 0) :
    ∀ t, T ≤ t → root - orbit t ≤ (root - orbit T) * Real.exp (-(t - T)) := by
  intro t ht
  have hmono : StrictMonoOn orbit (Set.Icc (0 : ℝ) t) :=
    gradientFlow4_strictMonoOn Q ε orbit root t hε (le_trans hT ht) hflow hbelow
      hgradientSign
  have hstate : ∀ s ∈ Set.Icc T t, orbit s ∈ Set.Icc boundary root := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hT hs.1
    have hTle : orbit T ≤ orbit s := by
      by_cases heq : T = s
      · simpa [heq]
      · have hts : T < s := by
          by_contra hnot
          have hsT : s ≤ T := le_of_not_gt hnot
          exact heq (le_antisymm hs.1 hsT)
        exact (hmono ⟨hT, ht⟩ ⟨le_trans hT hs.1, hs.2⟩ hts).le
    exact ⟨le_trans hentry hTle, (hbelow s hs0).le⟩
  let scaled : ℝ → ℝ := fun s => (root - orbit s) * Real.exp (s - T)
  have hscaledAnti : AntitoneOn scaled (Set.Icc T t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc T t)
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT hs.1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have harg := (hasDerivAt_id s).sub_const T
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s harg
      have hfun : scaled = ((fun x : ℝ => root) - orbit) *
          (fun u => Real.exp (u - T)) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          ((-gradientField4 Q (orbit s)) * Real.exp (s - T) +
            (root - orbit s) * Real.exp (s - T)) s := by
        rw [hfun]
        simpa [Pi.sub_apply, zero_sub] using
          ((hasDerivAt_const s root).sub horbit).mul hexp
      change ContinuousWithinAt scaled (Set.Icc T t) s
      exact hscaled.continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT (interior_subset hs).1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have harg := (hasDerivAt_id s).sub_const T
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s harg
      have hfun : scaled = ((fun x : ℝ => root) - orbit) *
          (fun u => Real.exp (u - T)) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          ((-gradientField4 Q (orbit s)) * Real.exp (s - T) +
            (root - orbit s) * Real.exp (s - T)) s := by
        rw [hfun]
        simpa [Pi.sub_apply, zero_sub] using
          ((hasDerivAt_const s root).sub horbit).mul hexp
      change DifferentiableWithinAt ℝ scaled (interior (Set.Icc T t)) s
      exact hscaled.differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT (interior_subset hs).1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have harg := (hasDerivAt_id s).sub_const T
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s harg
      have hfun : scaled = ((fun x : ℝ => root) - orbit) *
          (fun u => Real.exp (u - T)) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          ((-gradientField4 Q (orbit s)) * Real.exp (s - T) +
            (root - orbit s) * Real.exp (s - T)) s := by
        rw [hfun]
        simpa [Pi.sub_apply, zero_sub] using
          ((hasDerivAt_const s root).sub horbit).mul hexp
      have hd := hscaled.deriv
      change deriv scaled s ≤ 0
      rw [hd]
      simp only [gradientField4]
      have hpoint := hstate s (interior_subset hs)
      have hslope := dVt_le_neg_distance_of_curvature Q boundary root (orbit s)
        hboundary hcurvature hstationary hpoint
      have hexppos := Real.exp_pos (s - T)
      have hsum : dVt Q (orbit s) + (root - orbit s) ≤ 0 := by linarith
      have hproduct := mul_nonpos_of_nonneg_of_nonpos hexppos.le hsum
      nlinarith [hproduct]
  have hanti := hscaledAnti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hscaled : (root - orbit t) * Real.exp (t - T) ≤ root - orbit T := by
    simpa [scaled] using hanti
  have hexp_id : Real.exp (t - T) * Real.exp (-(t - T)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right hscaled (le_of_lt (Real.exp_pos (-(t - T))))
  calc
    root - orbit t = ((root - orbit t) * Real.exp (t - T)) * Real.exp (-(t - T)) := by
      rw [mul_assoc, hexp_id, mul_one]
    _ ≤ (root - orbit T) * Real.exp (-(t - T)) := hmul

/-- 局所 PL 不等式により、軌道が谷に入った後のポテンシャル差は指数的に減衰する。 -/
theorem gradientFlow4_residual_exponential_after_entry
    (Q ε boundary root T : ℝ) (orbit : ℝ → ℝ)
    (hboundary : boundary ≤ root)
    (hε : 0 < ε) (hT : 0 ≤ T) (hentry : boundary ≤ orbit T)
    (hbelow : ∀ t, 0 ≤ t → orbit t < root)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hgradientSign : ∀ x, x < root → dVt Q x < 0)
    (hpl : ∀ x ∈ Set.Icc boundary root,
      0 ≤ Vt Q x - Vt Q root ∧ Vt Q x - Vt Q root ≤ (dVt Q x) ^ 2) :
    ∀ t, T ≤ t →
      0 ≤ Vt Q (orbit t) - Vt Q root ∧
      Vt Q (orbit t) - Vt Q root ≤
        (Vt Q (orbit T) - Vt Q root) * Real.exp (-(t - T)) := by
  intro t ht
  have hmono : StrictMonoOn orbit (Set.Icc (0 : ℝ) t) :=
    gradientFlow4_strictMonoOn Q ε orbit root t hε (le_trans hT ht) hflow hbelow
      hgradientSign
  have hstate : ∀ s ∈ Set.Icc T t, orbit s ∈ Set.Icc boundary root := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hT hs.1
    have hTle : orbit T ≤ orbit s := by
      by_cases heq : T = s
      · simpa [heq]
      · have hts : T < s := by
          by_contra hnot
          exact heq (le_antisymm hs.1 (le_of_not_gt hnot))
        exact (hmono ⟨hT, ht⟩ ⟨le_trans hT hs.1, hs.2⟩ hts).le
    exact ⟨le_trans hentry hTle, (hbelow s hs0).le⟩
  let gap : ℝ → ℝ := fun s => Vt Q (orbit s) - Vt Q root
  let scaled : ℝ → ℝ := fun s => gap s * Real.exp (s - T)
  have hscaledAnti : AntitoneOn scaled (Set.Icc T t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc T t)
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT hs.1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s ((hasDerivAt_id s).sub_const T)
      have hgap := ((hasDerivAt_Vt Q (orbit s)).comp s horbit).sub_const
        (Vt Q root)
      have hfun : gap = (fun u => Vt Q (orbit u) - Vt Q root) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          (-(dVt Q (orbit s)) ^ 2 * Real.exp (s - T) +
            (Vt Q (orbit s) - Vt Q root) * Real.exp (s - T)) s := by
        rw [show scaled = gap * (fun u => Real.exp (u - T)) by
          funext u
          rfl]
        rw [hfun]
        convert hgap.mul hexp using 1 <;> simp [gradientField4] <;> ring
      exact hscaled.continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT (interior_subset hs).1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s ((hasDerivAt_id s).sub_const T)
      have hgap := ((hasDerivAt_Vt Q (orbit s)).comp s horbit).sub_const
        (Vt Q root)
      have hfun : gap = (fun u => Vt Q (orbit u) - Vt Q root) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          (-(dVt Q (orbit s)) ^ 2 * Real.exp (s - T) +
            (Vt Q (orbit s) - Vt Q root) * Real.exp (s - T)) s := by
        rw [show scaled = gap * (fun u => Real.exp (u - T)) by
          funext u
          rfl]
        rw [hfun]
        convert hgap.mul hexp using 1 <;> simp [gradientField4] <;> ring
      exact hscaled.differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := le_trans hT (interior_subset hs).1
      have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) hs0
      have horbit := hflow s (Set.mem_Ioi.mpr htime)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (u - T))
          (Real.exp (s - T)) s := by
        simpa [Function.comp_def, mul_one] using
          (Real.hasDerivAt_exp (s - T)).comp s ((hasDerivAt_id s).sub_const T)
      have hgap := ((hasDerivAt_Vt Q (orbit s)).comp s horbit).sub_const
        (Vt Q root)
      have hfun : gap = (fun u => Vt Q (orbit u) - Vt Q root) := by
        funext u
        rfl
      have hscaled : HasDerivAt scaled
          (-(dVt Q (orbit s)) ^ 2 * Real.exp (s - T) +
            (Vt Q (orbit s) - Vt Q root) * Real.exp (s - T)) s := by
        rw [show scaled = gap * (fun u => Real.exp (u - T)) by
          funext u
          rfl]
        rw [hfun]
        convert hgap.mul hexp using 1 <;> simp [gradientField4] <;> ring
      have hd := hscaled.deriv
      change deriv scaled s ≤ 0
      rw [hd]
      have hpoint := hstate s (interior_subset hs)
      have hPL := hpl (orbit s) hpoint
      have hsum : -(dVt Q (orbit s)) ^ 2 +
          (Vt Q (orbit s) - Vt Q root) ≤ 0 := by linarith [hPL.2]
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (Real.exp_pos (s - T)).le hsum
      nlinarith [hprod]
  have hanti := hscaledAnti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hscaled : (Vt Q (orbit t) - Vt Q root) * Real.exp (t - T) ≤
      Vt Q (orbit T) - Vt Q root := by
    simpa [scaled, gap] using hanti
  have hexp_id : Real.exp (t - T) * Real.exp (-(t - T)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right hscaled
    (le_of_lt (Real.exp_pos (-(t - T))))
  refine ⟨(hpl (orbit t) (hstate t ⟨ht, le_rfl⟩)).1, ?_⟩
  calc
    Vt Q (orbit t) - Vt Q root =
        ((Vt Q (orbit t) - Vt Q root) * Real.exp (t - T)) *
          Real.exp (-(t - T)) := by rw [mul_assoc, hexp_id, mul_one]
    _ ≤ (Vt Q (orbit T) - Vt Q root) * Real.exp (-(t - T)) := hmul

/-- 実際の `Q=1` 軌道は、強凸区間に入った後、単位指数率をもつ。入口時刻は先の明示的な上界をもつ。 -/
theorem exists_Qpos_flow_exponential_after_entry :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t → criticalPointQpos - orbit t ≤
        (criticalPointQpos - orbit T) * Real.exp (-(t - T))) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) ∧
      (∀ t, 0 ≤ t → orbit t < criticalPointQpos) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hentry, hflow, hbelow⟩ :=
    exists_Qpos_flow_reaches_valley_entry
  have hcurvature : ∀ x ∈ Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos,
      1 < deriv (dVt 1) x := by
    intro x hx
    apply dVt_deriv_gt_one_Q_pos x hx.1
    exact le_trans hx.2 (le_of_lt criticalPointQpos_spec.1.2)
  have hdecay := gradientFlow4_exponential_after_entry 1 ε (-(3 / 5))
    criticalPointQpos T orbit (by linarith [criticalPointQpos_spec.1.1])
    hε hT hentry hbelow hflow dVt_Qpos_negative_before_minimum hcurvature
    criticalPointQpos_spec.2
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
    hdecay, hflow, hbelow⟩

/-- 実際の `Q=-1` 軌道は、`x=1` を越えた後に単位指数率で収束する。横断時刻は正の最小速度で抑えられる。 -/
theorem exists_Qneg_flow_exponential_after_entry :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t → criticalPointQneg - orbit t ≤
        (criticalPointQneg - orbit T) * Real.exp (-(t - T))) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 (-1) (orbit t)) t) ∧
      (∀ t, 0 ≤ t → orbit t < criticalPointQneg) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hentry, hflow, hbelow⟩ :=
    exists_Qneg_flow_reaches_valley_entry
  have hcurvature : ∀ x ∈ Set.Icc (1 : ℝ) criticalPointQneg,
      1 < deriv (dVt (-1)) x := by
    intro x hx
    apply dVt_deriv_gt_one_Q_neg x hx.1
    exact le_trans hx.2 (le_of_lt criticalPointQneg_spec.1.2)
  have hdecay := gradientFlow4_exponential_after_entry (-1) ε 1
    criticalPointQneg T orbit (by linarith [criticalPointQneg_spec.1.1])
    hε hT hentry hbelow hflow dVt_Qneg_negative_before_minimum hcurvature
    criticalPointQneg_spec.2
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
    hdecay, hflow, hbelow⟩

/-- 明示的な入口時刻以降の局所的な単位率評価を、初期時刻から有効な評価に変換する。入口時刻は定数に吸収される。 -/
theorem gradientFlow4_global_exponential_from_entry
    (Q ε : ℝ) (orbit : ℝ → ℝ) (root T : ℝ)
    (hε : 0 < ε) (hT : 0 ≤ T) (hinit : orbit 0 < root)
    (hbelow : ∀ t, 0 ≤ t → orbit t < root)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hgradientSign : ∀ x, x < root → dVt Q x < 0)
    (hafter : ∀ t, T ≤ t → root - orbit t ≤
      (root - orbit T) * Real.exp (-(t - T))) :
    ∀ t, 0 ≤ t → |orbit t - root| ≤
      (root - orbit 0) * Real.exp T * Real.exp (-t) := by
  intro t ht
  have hmono : StrictMonoOn orbit (Set.Icc (0 : ℝ) t) :=
    gradientFlow4_strictMonoOn Q ε orbit root t hε ht hflow hbelow hgradientSign
  rw [abs_of_nonpos (by linarith [hbelow t ht] : orbit t - root ≤ 0)]
  rw [neg_sub]
  by_cases htime : t ≤ T
  · have hstate : orbit 0 ≤ orbit t := by
      by_cases htzero : t = 0
      · simp [htzero]
      · exact le_of_lt (hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩
          (lt_of_le_of_ne ht (Ne.symm htzero)))
    have hgap : root - orbit 0 ≤
        (root - orbit 0) * Real.exp T * Real.exp (-t) := by
      have hexp : 1 ≤ Real.exp (T - t) := Real.one_le_exp_iff.mpr (by linarith)
      have hident : Real.exp T * Real.exp (-t) = Real.exp (T - t) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      calc
        root - orbit 0 = (root - orbit 0) * 1 := by ring
        _ ≤ (root - orbit 0) * Real.exp (T - t) :=
          mul_le_mul_of_nonneg_left hexp (sub_nonneg.mpr hinit.le)
        _ = (root - orbit 0) * Real.exp T * Real.exp (-t) := by
          rw [← hident]
          ring
    calc
      root - orbit t ≤ root - orbit 0 := by linarith
      _ ≤ (root - orbit 0) * Real.exp T * Real.exp (-t) := hgap
  · have hTt : T ≤ t := le_of_not_ge htime
    have hstate : orbit 0 ≤ orbit T := by
      by_cases hTzero : T = 0
      · simp [hTzero]
      · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
        exact le_of_lt (hmono ⟨le_rfl, ht⟩ ⟨hT, hTt⟩ hTpos)
    have hafter' := hafter t hTt
    have hexppos := Real.exp_pos (-(t - T))
    have hgap : root - orbit T ≤ root - orbit 0 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hgap (le_of_lt hexppos)
    have hident : Real.exp T * Real.exp (-t) = Real.exp (-(t - T)) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    calc
      root - orbit t ≤ (root - orbit T) * Real.exp (-(t - T)) := hafter'
      _ ≤ (root - orbit 0) * Real.exp (-(t - T)) := hmul
      _ = (root - orbit 0) * Real.exp T * Real.exp (-t) := by
        rw [← hident]
        ring

/-- 入口時刻以降の局所ポテンシャル差の減衰を、初期時刻からの評価に拡張する。有限の過渡区間は `exp T` に吸収される。 -/
theorem gradientFlow4_global_local_gap_exponential
    (Q ε : ℝ) (orbit : ℝ → ℝ) (root T : ℝ)
    (hε : 0 < ε) (hT : 0 ≤ T)
    (hflow : ∀ t ∈ Set.Ioi (-ε),
      HasDerivAt orbit (gradientField4 Q (orbit t)) t)
    (hlocal : ∀ t, T ≤ t →
      0 ≤ Vt Q (orbit t) - Vt Q root ∧
      Vt Q (orbit t) - Vt Q root ≤
        (Vt Q (orbit T) - Vt Q root) * Real.exp (-(t - T))) :
    ∀ t, 0 ≤ t →
      0 ≤ Vt Q (orbit t) - Vt Q root ∧
      Vt Q (orbit t) - Vt Q root ≤
        (Vt Q (orbit 0) - Vt Q root) * Real.exp T * Real.exp (-t) := by
  intro t ht
  have henergy (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Vt Q (orbit b) ≤ Vt Q (orbit a) := by
    apply potential_antitone_along_gradient_flow4 Q a b orbit hab
    intro s hs
    have htime : -ε < s := lt_of_lt_of_le (neg_lt_zero.mpr hε) (le_trans ha hs.1)
    exact hflow s (Set.mem_Ioi.mpr htime)
  have hgapT : 0 ≤ Vt Q (orbit T) - Vt Q root := (hlocal T le_rfl).1
  have hgap0 : 0 ≤ Vt Q (orbit 0) - Vt Q root := by
    have hdec := henergy 0 T (by norm_num) hT
    linarith
  by_cases htime : t ≤ T
  · have hdec1 := henergy t T ht htime
    have hdec2 := henergy 0 t (by norm_num) ht
    have hgap_t : 0 ≤ Vt Q (orbit t) - Vt Q root := by linarith
    have hexp : 1 ≤ Real.exp (T - t) := Real.one_le_exp_iff.mpr (by linarith)
    have hident : Real.exp T * Real.exp (-t) = Real.exp (T - t) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    refine ⟨hgap_t, ?_⟩
    calc
      Vt Q (orbit t) - Vt Q root ≤ Vt Q (orbit 0) - Vt Q root := by linarith
      _ = (Vt Q (orbit 0) - Vt Q root) * 1 := by ring
      _ ≤ (Vt Q (orbit 0) - Vt Q root) * Real.exp (T - t) :=
        mul_le_mul_of_nonneg_left hexp hgap0
      _ = (Vt Q (orbit 0) - Vt Q root) * Real.exp T * Real.exp (-t) := by
        rw [← hident]
        ring
  · have hTt : T ≤ t := le_of_not_ge htime
    have hlocal' := hlocal t hTt
    have hdec := henergy 0 T (by norm_num) hT
    have hexppos := Real.exp_pos (-(t - T))
    have hmul := mul_le_mul_of_nonneg_right (by linarith :
      Vt Q (orbit T) - Vt Q root ≤ Vt Q (orbit 0) - Vt Q root) hexppos.le
    have hident : Real.exp T * Real.exp (-t) = Real.exp (-(t - T)) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    refine ⟨hlocal'.1, ?_⟩
    calc
      Vt Q (orbit t) - Vt Q root ≤
          (Vt Q (orbit T) - Vt Q root) * Real.exp (-(t - T)) := hlocal'.2
      _ ≤ (Vt Q (orbit 0) - Vt Q root) * Real.exp (-(t - T)) := hmul
      _ = (Vt Q (orbit 0) - Vt Q root) * Real.exp T * Real.exp (-t) := by
        rw [← hident]
        ring

/-- `Q=1` では、指定初期値からの状態誤差が、有限の入口時間を含めて、大域的な明示的指数評価を満たす。 -/
theorem exists_Qpos_flow_global_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t → |orbit t - criticalPointQpos| ≤
        (criticalPointQpos - orbit 0) * Real.exp T * Real.exp (-t)) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hafter, hflow, hbelow⟩ := exists_Qpos_flow_exponential_after_entry
  have hglobal := gradientFlow4_global_exponential_from_entry 1 ε orbit
    criticalPointQpos T hε hT
    (by rw [hinit]; linarith [criticalPointQpos_spec.1.1])
    hbelow hflow dVt_Qpos_negative_before_minimum hafter
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal⟩

/-- `Q=-1` では、指定初期値からの状態誤差が、有限の入口時間を定数に含む大域的な明示的指数評価を満たす。 -/
theorem exists_Qneg_flow_global_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t → |orbit t - criticalPointQneg| ≤
        (criticalPointQneg - orbit 0) * Real.exp T * Real.exp (-t)) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hafter, hflow, hbelow⟩ := exists_Qneg_flow_exponential_after_entry
  have hglobal := gradientFlow4_global_exponential_from_entry (-1) ε orbit
    criticalPointQneg T hε hT
    (by rw [hinit]; linarith [criticalPointQneg_spec.1.1])
    hbelow hflow dVt_Qneg_negative_before_minimum hafter
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal⟩

/-- `Q=1` の局所ポテンシャル差も、入口後に指数的に減衰する。これは局所最小点との切り詰めのない差で、論文の閾値 0 における正部分残差とは別物である。 -/
theorem exists_Qpos_flow_local_residual_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t →
        0 ≤ Vt 1 (orbit t) - Vt 1 criticalPointQpos ∧
        Vt 1 (orbit t) - Vt 1 criticalPointQpos ≤
          (Vt 1 (orbit T) - Vt 1 criticalPointQpos) * Real.exp (-(t - T))) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hentry, hflow, hbelow⟩ := exists_Qpos_flow_reaches_valley_entry
  have hcurvature : ∀ x ∈ Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos,
      1 < deriv (dVt 1) x := by
    intro x hx
    apply dVt_deriv_gt_one_Q_pos x hx.1
    exact le_trans hx.2 (le_of_lt criticalPointQpos_spec.1.2)
  have hmono : StrictMonoOn (dVt 1)
      (Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    · exact (continuous_dVt 1).continuousOn
    · intro x hx
      exact lt_trans (by norm_num : (0 : ℝ) < 1)
        (hcurvature x (interior_subset hx))
  have hpl : ∀ x ∈ Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos,
      0 ≤ Vt 1 x - Vt 1 criticalPointQpos ∧
      Vt 1 x - Vt 1 criticalPointQpos ≤ (dVt 1 x) ^ 2 := by
    intro x hx
    exact gradientPotentialGap_le_grad_sq 1 (-(3 / 5)) criticalPointQpos x
      (by linarith [criticalPointQpos_spec.1.1]) hcurvature hmono
      criticalPointQpos_spec.2 hx
  have hres := gradientFlow4_residual_exponential_after_entry 1 ε (-(3 / 5))
    criticalPointQpos T orbit (by linarith [criticalPointQpos_spec.1.1])
    hε hT hentry hbelow hflow dVt_Qpos_negative_before_minimum hpl
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hres, hflow⟩

/-- `Q=-1` の局所ポテンシャル差は入口後に指数減衰するが、元の閾値 0 の残差は消えるとは限らない。 -/
theorem exists_Qneg_flow_local_residual_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t →
        0 ≤ Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ∧
        Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ≤
          (Vt (-1) (orbit T) - Vt (-1) criticalPointQneg) * Real.exp (-(t - T))) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 (-1) (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hentry, hflow, hbelow⟩ := exists_Qneg_flow_reaches_valley_entry
  have hcurvature : ∀ x ∈ Set.Icc (1 : ℝ) criticalPointQneg,
      1 < deriv (dVt (-1)) x := by
    intro x hx
    apply dVt_deriv_gt_one_Q_neg x hx.1
    exact le_trans hx.2 (le_of_lt criticalPointQneg_spec.1.2)
  have hmono : StrictMonoOn (dVt (-1)) (Set.Icc (1 : ℝ) criticalPointQneg) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..)
    · exact (continuous_dVt (-1)).continuousOn
    · intro x hx
      exact lt_trans (by norm_num : (0 : ℝ) < 1)
        (hcurvature x (interior_subset hx))
  have hpl : ∀ x ∈ Set.Icc (1 : ℝ) criticalPointQneg,
      0 ≤ Vt (-1) x - Vt (-1) criticalPointQneg ∧
      Vt (-1) x - Vt (-1) criticalPointQneg ≤ (dVt (-1) x) ^ 2 := by
    intro x hx
    exact gradientPotentialGap_le_grad_sq (-1) 1 criticalPointQneg x
      (by linarith [criticalPointQneg_spec.1.1]) hcurvature hmono
      criticalPointQneg_spec.2 hx
  have hres := gradientFlow4_residual_exponential_after_entry (-1) ε 1
    criticalPointQneg T orbit (by linarith [criticalPointQneg_spec.1.1])
    hε hT hentry hbelow hflow dVt_Qneg_negative_before_minimum hpl
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hres, hflow⟩

/-- 指定初期状態から、`Q=1` の局所ポテンシャル差は、有限の入口時間を定数に吸収した大域的な指数評価に従う。 -/
theorem exists_Qpos_flow_global_local_gap_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t →
        0 ≤ Vt 1 (orbit t) - Vt 1 criticalPointQpos ∧
        Vt 1 (orbit t) - Vt 1 criticalPointQpos ≤
          (Vt 1 (orbit 0) - Vt 1 criticalPointQpos) * Real.exp T * Real.exp (-t)) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hlocal, hflow⟩ :=
    exists_Qpos_flow_local_residual_exponential
  have hglobal := gradientFlow4_global_local_gap_exponential 1 ε orbit
    criticalPointQpos T hε hT hflow hlocal
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal⟩

/-- 指定初期状態から、`Q=-1` の局所ポテンシャル差にも大域的な指数評価がある。元の TCZ 残差は正のまま残る。 -/
theorem exists_Qneg_flow_global_local_gap_exponential :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t →
        0 ≤ Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ∧
        Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ≤
          (Vt (-1) (orbit 0) - Vt (-1) criticalPointQneg) * Real.exp T * Real.exp (-t)) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hlocal, hflow⟩ :=
    exists_Qneg_flow_local_residual_exponential
  have hglobal := gradientFlow4_global_local_gap_exponential (-1) ε orbit
    criticalPointQneg T hε hT hflow hlocal
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal⟩

/-- 具体的な定理4の例の、時間に依らない成分。論文の重み付き TCZ の定義と同じ形に並べてある。 -/
noncomputable def presenceWeightBaseline4 (x t : ℝ) : ℝ := 1 / 2 * (x - 1) ^ 2

noncomputable def presenceWeightP4 (x t : ℝ) : ℝ := Real.exp (-(x + 1) ^ 2)

noncomputable def presenceWeightQpos4 (x t : ℝ) : ℝ := 1

noncomputable def presenceWeightQneg4 (x t : ℝ) : ℝ := -1

noncomputable def presenceWeightTCZQpos4 (t : ℝ) : Set ℝ :=
  Tomabechi.Theorem4.weightedTCZ Set.univ presenceWeightBaseline4
    presenceWeightP4 presenceWeightQpos4 2 0 t

noncomputable def presenceWeightTCZQneg4 (t : ℝ) : Set ℝ :=
  Tomabechi.Theorem4.weightedTCZ Set.univ presenceWeightBaseline4
    presenceWeightP4 presenceWeightQneg4 2 0 t

/-- 閾値 0 では、正符号の重み付き TCZ への所属は、元の実効ポテンシャルの不等式そのものである。 -/
theorem mem_presenceWeightTCZQpos4_iff (x t : ℝ) :
    x ∈ presenceWeightTCZQpos4 t ↔ Vt 1 x ≤ 0 := by
  simp [presenceWeightTCZQpos4, Tomabechi.Theorem4.weightedTCZ,
    Tomabechi.Theorem4.effectivePotential, presenceWeightBaseline4,
    presenceWeightP4, presenceWeightQpos4, Vt]

/-- 閾値 0 では、負符号の重み付き TCZ への所属は、対応する実効ポテンシャルの不等式である。 -/
theorem mem_presenceWeightTCZQneg4_iff (x t : ℝ) :
    x ∈ presenceWeightTCZQneg4 t ↔ Vt (-1) x ≤ 0 := by
  simp [presenceWeightTCZQneg4, Tomabechi.Theorem4.weightedTCZ,
    Tomabechi.Theorem4.effectivePotential, presenceWeightBaseline4,
    presenceWeightP4, presenceWeightQneg4, Vt]

/-- 元の実効ポテンシャルは、`Q=1` の強凸谷の左端ですでに厳密に負である。 -/
theorem Vt_Qpos_left_valley_entry_negative : Vt 1 (-(3 / 5)) < 0 := by
  have hexp : (21 / 25 : ℝ) ≤ Real.exp (-(4 / 25)) := by
    have h := Real.add_one_le_exp (-(4 / 25 : ℝ))
    nlinarith
  unfold Vt
  norm_num
  nlinarith [hexp]

/-- `Q=1` の谷の区間では、ポテンシャルは臨界点に向かって減少する。 -/
theorem Vt_Qpos_antitoneOn_valley :
    AntitoneOn (Vt 1) (Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc ..)
  · fun_prop [Vt]
  · intro x hx
    exact (hasDerivAt_Vt 1 x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (-(3 / 5 : ℝ)) criticalPointQpos := by
      simpa [interior_Icc] using hx
    rw [(hasDerivAt_Vt 1 x).deriv]
    exact le_of_lt (dVt_Qpos_negative_before_minimum x
      hx'.2)

/-- 実際の `Q=1` 勾配流は、元の閾値 0 の論文の重み付き TCZ に到達し、エネルギーの減少によってその後も TCZ に留まる。 -/
theorem exists_Qpos_flow_enters_original_TCZ :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t → orbit t ∈ presenceWeightTCZQpos4 t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hentry, hflow, hbelow⟩ :=
    exists_Qpos_flow_reaches_valley_entry
  have hstateT : orbit T ∈ Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos :=
    ⟨hentry, (hbelow T hT).le⟩
  have hnegativeT : Vt 1 (orbit T) < 0 := by
    have hdecrease := Vt_Qpos_antitoneOn_valley
      ⟨le_rfl, le_of_lt criticalPointQpos_spec.1.1⟩ hstateT hentry
    exact lt_of_le_of_lt hdecrease Vt_Qpos_left_valley_entry_negative
  have hstay : ∀ t, T ≤ t → Vt 1 (orbit t) < 0 := by
    intro t ht
    have hdec := potential_antitone_along_gradient_flow4 1 T t orbit ht
      (fun s hs => hflow s (Set.mem_Ioi.mpr
        (lt_of_lt_of_le (neg_lt_zero.mpr hε) (le_trans hT hs.1))))
    exact lt_of_le_of_lt hdec hnegativeT
  refine ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, ?_⟩
  intro t ht
  rw [mem_presenceWeightTCZQpos4_iff]
  exact (hstay t ht).le

/-- `Q=-1` では、元の閾値 0 の重み付き TCZ は空である。実効ポテンシャルは、非負の 2 乗と正のガウスの和になっているため。 -/
theorem presenceWeightTCZQneg4_empty (t : ℝ) :
    presenceWeightTCZQneg4 t = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [mem_presenceWeightTCZQneg4_iff] at hx
  have hpositive : 0 < Vt (-1) x := by
    unfold Vt
    have hsquare : 0 ≤ 1 / 2 * (x - 1) ^ 2 := by positivity
    have hexp : 0 < 2 * Real.exp (-(x + 1) ^ 2) := by positivity
    linarith
  linarith


/-! ## 監査用：評価とODEを同じ軌道について保持する入口 -/

/-- 既存の評価と同じ軌道が指定された勾配流のODEを満たすことを、結論の型に保持する。
指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。 -/
theorem exists_Qpos_flow_global_exponential_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t → |orbit t - criticalPointQpos| ≤
        (criticalPointQpos - orbit 0) * Real.exp T * Real.exp (-t)) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hafter, hflow, hbelow⟩ := exists_Qpos_flow_exponential_after_entry
  have hglobal := gradientFlow4_global_exponential_from_entry 1 ε orbit
    criticalPointQpos T hε hT
    (by rw [hinit]; linarith [criticalPointQpos_spec.1.1])
    hbelow hflow dVt_Qpos_negative_before_minimum hafter
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal, hflow⟩

/-- 既存の評価と同じ軌道が指定された勾配流のODEを満たすことを、結論の型に保持する。
指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。 -/
theorem exists_Qneg_flow_global_exponential_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t → |orbit t - criticalPointQneg| ≤
        (criticalPointQneg - orbit 0) * Real.exp T * Real.exp (-t)) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 (-1) (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound,
      hafter, hflow, hbelow⟩ := exists_Qneg_flow_exponential_after_entry
  have hglobal := gradientFlow4_global_exponential_from_entry (-1) ε orbit
    criticalPointQneg T hε hT
    (by rw [hinit]; linarith [criticalPointQneg_spec.1.1])
    hbelow hflow dVt_Qneg_negative_before_minimum hafter
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal, hflow⟩

/-- 既存の評価と同じ軌道が指定された勾配流のODEを満たすことを、結論の型に保持する。
指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。 -/
theorem exists_Qpos_flow_global_local_gap_exponential_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t →
        0 ≤ Vt 1 (orbit t) - Vt 1 criticalPointQpos ∧
        Vt 1 (orbit t) - Vt 1 criticalPointQpos ≤
          (Vt 1 (orbit 0) - Vt 1 criticalPointQpos) * Real.exp T * Real.exp (-t)) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hlocal, hflow⟩ :=
    exists_Qpos_flow_local_residual_exponential
  have hglobal := gradientFlow4_global_local_gap_exponential 1 ε orbit
    criticalPointQpos T hε hT hflow hlocal
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal, hflow⟩

/-- 既存の評価と同じ軌道が指定された勾配流のODEを満たすことを、結論の型に保持する。
指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。 -/
theorem exists_Qneg_flow_global_local_gap_exponential_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (1 - orbit 0) / speed + 1 ∧
      (∀ t, 0 ≤ t →
        0 ≤ Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ∧
        Vt (-1) (orbit t) - Vt (-1) criticalPointQneg ≤
          (Vt (-1) (orbit 0) - Vt (-1) criticalPointQneg) * Real.exp T * Real.exp (-t)) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 (-1) (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hlocal, hflow⟩ :=
    exists_Qneg_flow_local_residual_exponential
  have hglobal := gradientFlow4_global_local_gap_exponential (-1) ε orbit
    criticalPointQneg T hε hT hflow hlocal
  exact ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hglobal, hflow⟩

/-- 既存の評価と同じ軌道が指定された勾配流のODEを満たすことを、結論の型に保持する。
指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。 -/
theorem exists_Qpos_flow_enters_original_TCZ_with_ode :
    ∃ (orbit : ℝ → ℝ) (ε speed T : ℝ),
      0 < ε ∧ orbit 0 = -(4 / 5) ∧ 0 < speed ∧ 0 ≤ T ∧
      T ≤ (-(3 / 5) - orbit 0) / speed + 1 ∧
      (∀ t, T ≤ t → orbit t ∈ presenceWeightTCZQpos4 t) ∧
      (∀ t ∈ Set.Ioi (-ε), HasDerivAt orbit (gradientField4 1 (orbit t)) t) := by
  obtain ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, hentry, hflow, hbelow⟩ :=
    exists_Qpos_flow_reaches_valley_entry
  have hstateT : orbit T ∈ Set.Icc (-(3 / 5 : ℝ)) criticalPointQpos :=
    ⟨hentry, (hbelow T hT).le⟩
  have hnegativeT : Vt 1 (orbit T) < 0 := by
    have hdecrease := Vt_Qpos_antitoneOn_valley
      ⟨le_rfl, le_of_lt criticalPointQpos_spec.1.1⟩ hstateT hentry
    exact lt_of_le_of_lt hdecrease Vt_Qpos_left_valley_entry_negative
  have hstay : ∀ t, T ≤ t → Vt 1 (orbit t) < 0 := by
    intro t ht
    have hdec := potential_antitone_along_gradient_flow4 1 T t orbit ht
      (fun s hs => hflow s (Set.mem_Ioi.mpr
        (lt_of_lt_of_le (neg_lt_zero.mpr hε) (le_trans hT hs.1))))
    exact lt_of_le_of_lt hdec hnegativeT
  refine ⟨orbit, ε, speed, T, hε, hinit, hspeed, hT, hTbound, ?_, hflow⟩
  intro t ht
  rw [mem_presenceWeightTCZQpos4_iff]
  exact (hstay t ht).le

end Tomabechi.Examples.Theorem4
