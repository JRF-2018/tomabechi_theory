import Mathlib

open Real

-- 1. 基本定義
-- 力学系: xの時間発展 x(t) = x₀ * exp(-λ * t)
noncomputable def x_traj (x0 lam t : ℝ) : ℝ := x0 * Real.exp (-(lam * t))

-- 評価関数 V(x) = 0.5 * x^2
noncomputable def V (x : ℝ) : ℝ := 0.5 * x^2

-- 制御方策 πc(t, x) := -λ * x
noncomputable def pi_c (lam x : ℝ) : ℝ := -(lam * x)

-- TCZ (Target Constraint Zone): V(x) ≤ θ を満たす集合
def TCZ (theta : ℝ) : Set ℝ := {x | V x ≤ theta}

-- 定量的収束（TCZ への距離の指数減衰）の定義
def ExponentiallyConvergesToTCZ (x : ℝ → ℝ) (TCZ : Set ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∃ C > 0, ∀ t ≥ 0, Metric.infDist (x t) TCZ ≤ C * exp (-(lam * t))

-- 2. πc と x_traj の解関係の代入検証 (ẋ = πc(x) であることの証明)
theorem x_traj_is_sol (x0 lam t : ℝ) :
    HasDerivAt (x_traj x0 lam) (pi_c lam (x_traj x0 lam t)) t := by
  unfold x_traj pi_c
  have h1 : HasDerivAt (fun t => -(lam * t)) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have h2 : HasDerivAt (fun t => Real.exp (-(lam * t))) (Real.exp (-(lam * t)) * -lam) t :=
    HasDerivAt.exp h1
  have h3 : HasDerivAt (fun t => x0 * Real.exp (-(lam * t))) (x0 * (Real.exp (-(lam * t)) * -lam)) t :=
    h2.const_mul x0
  convert h3 using 1
  ring

-- 初期値条件 x(0) = x0 の検証
theorem x_traj_init (x0 lam : ℝ) : x_traj x0 lam 0 = x0 := by
  unfold x_traj
  simp

-- 3. V が条件に合うことを証明
-- 条件1: Vは正定値
theorem V_pos_def (x : ℝ) : V x ≥ 0 ∧ (V x = 0 ↔ x = 0) := by
  unfold V
  constructor
  · positivity
  · constructor
    · intro h
      have h1 : x^2 = 0 := by linarith
      exact sq_eq_zero_iff.mp h1
    · intro h
      subst h
      ring

-- 条件2: 軌道に沿ってVが指数的に減衰する
theorem V_exp_decay (x0 lam t : ℝ) (_hlam : lam > 0) :
    V (x_traj x0 lam t) = V x0 * Real.exp (-(2 * lam * t)) := by
  unfold V x_traj
  have h_exp : (Real.exp (-(lam * t)))^2 = Real.exp (-(2 * lam * t)) := by
    have h1 : (Real.exp (-(lam * t)))^2 = Real.exp (2 * (-(lam * t))) := by
      exact (Real.exp_nat_mul (-(lam * t)) 2).symm
    have h2 : 2 * (-(lam * t)) = -(2 * lam * t) := by ring
    rw [h1, h2]
  have h_alg : 0.5 * (x0 * Real.exp (-(lam * t)))^2 = (0.5 * x0^2) * (Real.exp (-(lam * t)))^2 := by ring
  rw [h_alg, h_exp]

/-- 4. 具体例を代入した convergence_to_TCZ の完全証明 -/
theorem convergence_to_TCZ
    (x0 lam theta : ℝ)
    (hlam : 0 < lam)
    (htheta : 0 ≤ theta) :
    ExponentiallyConvergesToTCZ (x_traj x0 lam) (TCZ theta) lam := by
  constructor
  · exact hlam
  · refine ⟨|x0| + 1, add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one, ?_⟩
    intro t ht
    have h0_in_TCZ : (0 : ℝ) ∈ TCZ theta := by
      change V 0 ≤ theta
      dsimp [V]
      ring_nf
      exact htheta
    have h_le_dist : Metric.infDist (x_traj x0 lam t) (TCZ theta) ≤ dist (x_traj x0 lam t) 0 :=
      Metric.infDist_le_dist_of_mem h0_in_TCZ
    rw [Real.dist_eq, sub_zero] at h_le_dist
    dsimp [x_traj] at h_le_dist
    rw [abs_mul, abs_of_pos (exp_pos _)] at h_le_dist
    -- h_upper および nlinarith も -(lam * t) に統一
    have h_upper : |x0| * exp (-(lam * t)) ≤ (|x0| + 1) * exp (-(lam * t)) := by
      nlinarith [exp_pos (-(lam * t))]
    exact h_le_dist.trans h_upper
