import Mathlib

/-!
# ガウス谷 `well A σ c x = -A exp(-(x-c)²/(2σ²))` の微分補題（定理21・22の Python 例で共有）

`dwell` は 1 階微分、`ddwell` は 2 階微分。`|x-c|≤r<σ` の球上で `ddwell>0`（局所強凸）。
-/

namespace Tomabechi.Examples.Gaussian

noncomputable def well (A σ c x : ℝ) : ℝ := -A * Real.exp (-(x - c) ^ 2 / (2 * σ ^ 2))
noncomputable def dwell (A σ c x : ℝ) : ℝ :=
  A * (x - c) / σ ^ 2 * Real.exp (-(x - c) ^ 2 / (2 * σ ^ 2))
noncomputable def ddwell (A σ c x : ℝ) : ℝ :=
  A / σ ^ 2 * (1 - (x - c) ^ 2 / σ ^ 2) * Real.exp (-(x - c) ^ 2 / (2 * σ ^ 2))

theorem hasDerivAt_expArg (σ c x : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (fun x => -(x - c) ^ 2 / (2 * σ ^ 2)) (-(x - c) / σ ^ 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - c) 1 x := (hasDerivAt_id x).sub_const c
  have h2 : HasDerivAt (fun x : ℝ => (x - c) ^ 2) (2 * (x - c)) x := by
    have h := (hasDerivAt_pow 2 (x - c)).comp x h1
    rw [show (2 * (x - c) : ℝ) = (↑(2 : ℕ) * (x - c) ^ (2 - 1) * 1) by norm_num]
    exact h
  have h3 := (h2.neg).div_const (2 * σ ^ 2)
  refine h3.congr_deriv ?_
  field_simp

theorem hasDerivAt_well (A σ c x : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (well A σ c) (dwell A σ c x) x := by
  have h := ((hasDerivAt_expArg σ c x hσ).exp).const_mul (-A)
  refine h.congr_deriv ?_
  unfold dwell
  field_simp

theorem hasDerivAt_dwell (A σ c x : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (dwell A σ c) (ddwell A σ c x) x := by
  have h1 : HasDerivAt (fun x => A * (x - c) / σ ^ 2) (A / σ ^ 2) x := by
    have := (((hasDerivAt_id x).sub_const c).const_mul A).div_const (σ ^ 2)
    simpa using this
  have h := h1.mul (hasDerivAt_expArg σ c x hσ).exp
  refine h.congr_deriv ?_
  unfold ddwell
  field_simp
  ring

/-- `|x-c|≤r<σ` の球上で `Ṽ''>0`（局所強凸）。 -/
theorem ddwell_pos {A σ c r x : ℝ} (hA : 0 < A) (hσ : 0 < σ) (hr : r < σ)
    (hx : |x - c| ≤ r) : 0 < ddwell A σ c x := by
  unfold ddwell
  have h0 : |x - c| ^ 2 < σ ^ 2 := by
    have : |x - c| < σ := lt_of_le_of_lt hx hr
    exact pow_lt_pow_left₀ this (abs_nonneg _) (by norm_num)
  have h1 : 0 < 1 - (x - c) ^ 2 / σ ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    rwa [sq_abs] at h0
  positivity


end Tomabechi.Examples.Gaussian
