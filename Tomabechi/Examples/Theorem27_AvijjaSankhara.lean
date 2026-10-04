import Tomabechi.Theorem27.Actuator
import Tomabechi.Examples.Theorem27_Operational
import Tomabechi.Examples.Theorem26_27_ControlClasses

/-!
# 定理27の Python 例 (`examples/theorem27_avijja_sankhara.py`) の Lean 根拠

状態 `x=(r,φ)∈ℝ²`（輪 `𝒩={r=0}`、`W=½r²`）、自然ドリフト `f0=(-μr,0)`、`G=id`、指定入力 `u0=(-κr,ω)`、
基準入力 A: `utr=(μr,ω)`、B: `utr=(0,ω)`。Python が数値で確認する各項目を、一般補題
`Tomabechi.Theorem27.Actuator.actuator_identity_from_reference_cancellation` と
`positive_actuator_contribution`（(27.7)・(27.8) の代数核）のインスタンスとして証明する。

* A（27-A2 成立）: 基準閉ループが `W` を変えず、`Des=(μ+κ)r²=-⟪∇W,Gη27⟫`（行の帰属が完全）。
* B（27-A2 破れ）: 27-A2 の左辺が `-μr²≠0`、帰属が `κr²` で `Des` と `μr²` だけずれる（自然ドリフト分）。
* 寂静内 `r=0`: `∇W=0` なので行の寄与は 0、ただし `φ'=ω` は残る（動的寂静）。

軌道と ODE の微分可能性・Dini 微分・再始動は一般定理側に接続する。固定パラメータ
`μ=κ=1/2, ω=3/2` では `Theorem27Op` の実軌道に一致する。任意パラメータの代数式は維持し、
Dini・再始動も `μ≥0, κ>0, ω∈ℝ` のもとで示す。値関数は割引費用の最適値
`V=3r²/(1+2(μ+κ))` とし、`W=V` の距離比較・指数減衰を定理27の一般軌道カーネルへ
接続する。制御クラスは `0≤k(t)≤κ` の有界可測ゲイン族であり、最大ゲインが費用を達成する。
-/

namespace Tomabechi.Examples.Theorem27

open Tomabechi.Theorem27.Actuator
open MeasureTheory

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def vec (a b : ℝ) : E2 := !₂[a, b]

theorem inner_vec (a b c d : ℝ) : inner ℝ (vec a b) (vec c d) = a * c + b * d := by
  simp [vec, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- `∇W = (r, 0)`（W=½r²）。 -/
noncomputable def gradW (r : ℝ) : E2 := vec r 0
/-- 自然ドリフト `f0=(-μr,0)`。 -/
noncomputable def drift (μ r : ℝ) : E2 := vec (-μ * r) 0
/-- 指定入力 `u0=(-κr,ω)`。 -/
noncomputable def u0 (κ ω r : ℝ) : E2 := vec (-κ * r) ω
/-- 基準入力 A `(μr,ω)`（27-A2 を満たす）。 -/
noncomputable def utrA (μ ω r : ℝ) : E2 := vec (μ * r) ω
/-- 基準入力 B `(0,ω)`（自然ドリフトを無視。27-A2 を破る）。 -/
noncomputable def utrB (ω : ℝ) : E2 := vec 0 ω

/-- 実アクチュエータ `G=id`。 -/
noncomputable def G : E2 →L[ℝ] E2 := ContinuousLinearMap.id ℝ E2

/-- Python の `Des = -(gradW @ (f0+u0))`。 -/
theorem descent_rate (μ κ ω r : ℝ) :
    -(0 + inner ℝ (gradW r) (drift μ r + G (u0 κ ω r))) = (μ + κ) * r ^ 2 := by
  simp only [gradW, drift, u0, G, ContinuousLinearMap.id_apply, vec, zero_add]
  have : (!₂[-μ * r, (0 : ℝ)] + !₂[-κ * r, ω] : E2) = !₂[-μ * r + -κ * r, ω] := by
    ext i; fin_cases i <;> simp
  rw [this]
  change -(inner ℝ (vec r 0) (vec (-μ * r + -κ * r) ω)) = _
  rw [inner_vec]; ring

/-- A: 27-A2 の左辺 `∂tW + ⟪∇W, f0+G utr⟫ = 0`。 -/
theorem A2_residual_A (μ ω r : ℝ) :
    0 + inner ℝ (gradW r) (drift μ r + G (utrA μ ω r)) = 0 := by
  simp only [gradW, drift, utrA, G, ContinuousLinearMap.id_apply, vec, zero_add]
  have : (!₂[-μ * r, (0 : ℝ)] + !₂[μ * r, ω] : E2) = !₂[-μ * r + μ * r, ω] := by
    ext i; fin_cases i <;> simp
  rw [this]
  change inner ℝ (vec r 0) (vec (-μ * r + μ * r) ω) = 0
  rw [inner_vec]; ring

/-- B: 27-A2 の左辺は `-μ r²`（基準だけで W が下がる）。 -/
theorem A2_residual_B (μ ω r : ℝ) :
    0 + inner ℝ (gradW r) (drift μ r + G (utrB ω)) = -μ * r ^ 2 := by
  simp only [gradW, drift, utrB, G, ContinuousLinearMap.id_apply, vec, zero_add]
  have : (!₂[-μ * r, (0 : ℝ)] + !₂[0, ω] : E2) = !₂[-μ * r + 0, ω] := by
    ext i; fin_cases i <;> simp
  rw [this]
  change inner ℝ (vec r 0) (vec (-μ * r + 0) ω) = _
  rw [inner_vec]; ring

/-- A: 行の帰属 `-⟪∇W, Gη27⟫ = (μ+κ) r² = Des`（一般補題 (27.7) の代数核）。 -/
theorem attribution_A (μ κ ω r : ℝ) :
    (μ + κ) * r ^ 2 = -(inner ℝ (gradW r) (G (u0 κ ω r - utrA μ ω r))) := by
  have h := actuator_identity_from_reference_cancellation (gradW r) (drift μ r)
    (u0 κ ω r) (utrA μ ω r) G 0 ((μ + κ) * r ^ 2) (A2_residual_A μ ω r)
    (by rw [← descent_rate μ κ ω r])
  exact h

/-- B: 帰属は `κ r²` で、`Des` との差（取りこぼし）は自然ドリフト分 `μ r²`。 -/
theorem attribution_B (μ κ ω r : ℝ) :
    -(inner ℝ (gradW r) (G (u0 κ ω r - utrB ω))) = κ * r ^ 2 ∧
      (μ + κ) * r ^ 2 - κ * r ^ 2 = μ * r ^ 2 := by
  refine ⟨?_, by ring⟩
  simp only [gradW, u0, utrB, G, ContinuousLinearMap.id_apply, vec]
  have : (!₂[-κ * r, ω] - !₂[0, ω] : E2) = !₂[-κ * r, 0] := by
    ext i; fin_cases i <;> simp
  rw [this]
  change -(inner ℝ (vec r 0) (vec (-κ * r) 0)) = _
  rw [inner_vec]; ring

/-- (27.6)-(27.7)-(27.8) の正値部分: 無明 `r≠0`（W=½r²>0）で行の寄与は正、`η27≠0`、`Gη27≠0`。
Des = λW が等号で成り立つ（λ=2(μ+κ)）。 -/
theorem ignorance_implies_action (μ κ ω r : ℝ) (hμ : 0 ≤ μ) (hκ : 0 < κ) (hr : r ≠ 0) :
    0 < -(inner ℝ (gradW r) (G (u0 κ ω r - utrA μ ω r))) ∧
      u0 κ ω r - utrA μ ω r ≠ 0 ∧ G (u0 κ ω r - utrA μ ω r) ≠ 0 := by
  have hW : 0 < r ^ 2 / 2 := by positivity
  have hdecay : 2 * (μ + κ) * (r ^ 2 / 2) ≤ (μ + κ) * r ^ 2 := by nlinarith
  exact positive_actuator_contribution (gradW r) _ G (2 * (μ + κ)) (r ^ 2 / 2)
    ((μ + κ) * r ^ 2) (by positivity) hW hdecay (attribution_A μ κ ω r)

/-- 寂静内 `r=0`: 行の寄与も `Des` も 0。 -/
theorem quiescence_zero_contribution (μ κ ω : ℝ) :
    -(inner ℝ (gradW 0) (G (u0 κ ω 0 - utrA μ ω 0))) = 0 ∧ (μ + κ) * (0 : ℝ) ^ 2 = 0 := by
  refine ⟨?_, by ring⟩
  have h0 : gradW 0 = 0 := by
    ext i; fin_cases i <;> simp [gradW, vec]
  rw [h0, inner_zero_left]; ring

/-- 寂静後も接線成分は動き続ける: 位相 `φ(t)=φ0+ωt` は `φ'=ω`。 -/
theorem tangential_motion_persists (φ0 ω t : ℝ) :
    HasDerivAt (fun s : ℝ => φ0 + ω * s) ω t := by
  simpa using ((hasDerivAt_id t).const_mul ω).const_add φ0

/-- 半径方向の厳密解 `r(t)=r0 e^{-(μ+κ)t}` は `ṙ=-(μ+κ)r` を解く（Python の Euler 積分の連続極限）。 -/
theorem radial_exact_solution (μ κ r0 t : ℝ) :
    HasDerivAt (fun s : ℝ => r0 * Real.exp (-(μ + κ) * s))
      (-(μ + κ) * (r0 * Real.exp (-(μ + κ) * t))) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(μ + κ) * s) (-(μ + κ)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(μ + κ))
  have h2 := (HasDerivAt.exp h1).const_mul r0
  convert h2 using 1
  ring

/-! ## 固定パラメータでのOperational軌道接続

小例の任意パラメータ公式のうち `μ=κ=1/2, ω=3/2` を選ぶと、原点時刻からの半径解は
Operationalモデルの `flow` と一致する。この範囲ではODE、一般定理27のDini下降・行同値、
および流れの再始動をそのまま利用できる。
-/

theorem radial_exact_solution_operational (r0 φ0 t : ℝ) :
    vec (r0 * Real.exp (-t)) (φ0 + (3/2) * t) =
      Tomabechi.Examples.Theorem27Op.flowE
        (r0 • Tomabechi.Examples.Theorem27Op.e0 + φ0 • Tomabechi.Examples.Theorem27Op.e1) 0 t := by
  ext i
  fin_cases i
  · simp [vec, Tomabechi.Examples.Theorem27Op.flowE,
      Tomabechi.Theorem24_26_Model.flow, Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1]
  · simp [vec, Tomabechi.Examples.Theorem27Op.flowE,
      Tomabechi.Theorem24_26_Model.flow, Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1, Tomabechi.Examples.Theorem27Op.omg]

theorem operational_restart_connected
    (r0 φ0 a s t : ℝ) :
    Tomabechi.Examples.Theorem27Op.flowE
      (Tomabechi.Examples.Theorem27Op.flowE
        (r0 • Tomabechi.Examples.Theorem27Op.e0 + φ0 • Tomabechi.Examples.Theorem27Op.e1) a s) s t =
      Tomabechi.Examples.Theorem27Op.flowE
        (r0 • Tomabechi.Examples.Theorem27Op.e0 + φ0 • Tomabechi.Examples.Theorem27Op.e1) a t :=
  Tomabechi.Examples.Theorem27Op.flowE_semigroup _ _ _ _

/-! ## A2: パラメータ一般化の解析核

ここでは固定値モデルを変更せず、`μ ≥ 0`, `κ > 0`, `ω ∈ ℝ` の別モデルを定義する。
減衰率 `λ=μ+κ` は正で、Lyapunov 関数 `W=r²/2` の減衰率は `2λ`。
最適化データ全体への接続は後続の補題で行い、この節の軌道計算だけを一般化証明とする。
-/

/-- A2 の減衰率。仮定 `μ≥0`, `κ>0` から正となる。 -/
def parameterRate (μ κ : ℝ) : ℝ := μ + κ

theorem parameterRate_pos (μ κ : ℝ) (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    0 < parameterRate μ κ := by
  dsimp [parameterRate]
  linarith

/-- 初期半径 `r₀` を時刻 `T` から指数率 `μ+κ` で減衰させる半径軌道。 -/
noncomputable def parameterRadius (μ κ r₀ T s : ℝ) : ℝ :=
  r₀ * Real.exp (-parameterRate μ κ * (s - T))

/-- 位相座標は任意の速度 `ω` で一様に動く。 -/
noncomputable def parameterPhase (ω φ₀ T s : ℝ) : ℝ := φ₀ + ω * (s - T)

/-- 一般パラメータの二次元状態軌道。 -/
noncomputable def parameterOrbit (μ κ ω r₀ φ₀ T s : ℝ) : E2 :=
  parameterRadius μ κ r₀ T s • Tomabechi.Examples.Theorem27Op.e0 +
    parameterPhase ω φ₀ T s • Tomabechi.Examples.Theorem27Op.e1

/-- A2 の自然ドリフト、指定入力、27-A2 を満たす参照入力。 -/
noncomputable def parameterDrift (μ r : ℝ) : E2 := vec (-μ * r) 0
noncomputable def parameterActionInput (κ ω r : ℝ) : E2 := vec (-κ * r) ω
noncomputable def parameterReferenceInput (μ ω r : ℝ) : E2 := vec (μ * r) ω

/-- 一般パラメータに対応する最適値/Lyapunov関数
`V(r)=3r²/(1+2(μ+κ))`。 -/
noncomputable def parameterValue (μ κ r : ℝ) : ℝ :=
  (3 / (1 + 2 * (μ + κ))) * r ^ 2

/-- 状態勾配 `∇V=(2cr,0)`。 -/
noncomputable def parameterValueGradient (μ κ r : ℝ) : E2 :=
  vec (2 * (3 / (1 + 2 * (μ + κ))) * r) 0

/-- 時空微分の候補。Vは時間に陽には依存しない。 -/
noncomputable def parameterValueDerivative (μ κ r : ℝ) : ℝ × E2 →L[ℝ] ℝ :=
  (2 * (3 / (1 + 2 * (μ + κ))) * r) •
    ((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ E2))

/-- Lyapunov関数Vの値を二次元状態の第0成分から得る。 -/
noncomputable def parameterW (μ κ : ℝ) (x : E2) (_t : ℝ) : ℝ :=
  parameterValue μ κ (x 0)

theorem parameterValueDerivative_apply (μ κ r a : ℝ) (z : E2) :
    parameterValueDerivative μ κ r (a, z) =
      2 * (3 / (1 + 2 * (μ + κ))) * r * z 0 := by
  simp [parameterValueDerivative]

/-- Vは時間・状態の組に関してFréchet微分可能で、微分はparameterValueDerivative。 -/
theorem parameterW_hasFDerivAt (μ κ : ℝ) (x : E2) (t : ℝ) :
    HasFDerivAt (fun p : ℝ × E2 => parameterW μ κ p.2 p.1)
      (parameterValueDerivative μ κ (x 0)) (t, x) := by
  let proj := (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ E2)
  have h1 : HasFDerivAt (fun p : ℝ × E2 => p.2 0) proj (t, x) :=
    ContinuousLinearMap.hasFDerivAt proj
  have h2 := h1.pow 2
  have hc := h2.const_mul (3 / (1 + 2 * (μ + κ)))
  have hfun : (fun p : ℝ × E2 => parameterW μ κ p.2 p.1) =
      fun p : ℝ × E2 => (3 / (1 + 2 * (μ + κ))) * (p.2 0) ^ 2 := by
    funext p
    simp [parameterW, parameterValue]
  rw [hfun]
  refine hc.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro p
  rcases p with ⟨a, z⟩
  simp [parameterValueDerivative, proj]
  ring

theorem parameterValue_state_gradient (μ κ r : ℝ) (z : E2) :
    parameterValueDerivative μ κ r (0, z) =
      inner ℝ (parameterValueGradient μ κ r) z := by
  have hz : z = vec (z 0) (z 1) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [parameterValueDerivative_apply, parameterValueGradient, hz, inner_vec]
  simp [vec]

/-- 27-A2の基準入力相殺。Vの正の比例係数を含めて成立する。 -/
theorem parameterValue_reference_cancellation (μ κ ω r : ℝ) :
    parameterValueDerivative μ κ r (1, 0) +
      inner ℝ (parameterValueGradient μ κ r)
        (parameterDrift μ r + parameterReferenceInput μ ω r) = 0 := by
  rw [parameterValueDerivative_apply]
  have hsum : parameterDrift μ r + parameterReferenceInput μ ω r = vec 0 ω := by
    ext i
    fin_cases i <;> simp [parameterDrift, parameterReferenceInput, vec] <;> ring
  rw [hsum, parameterValueGradient, inner_vec]
  simp [vec]

/-- 指定入力・参照入力から作るアクチュエータ差は、Vの全下降量を帰属させる。 -/
theorem parameterValue_action_attribution (μ κ ω r : ℝ) :
    2 * (3 / (1 + 2 * (μ + κ))) * (μ + κ) * r ^ 2 =
      -(inner ℝ (parameterValueGradient μ κ r)
        (parameterActionInput κ ω r - parameterReferenceInput μ ω r)) := by
  have hdiff : parameterActionInput κ ω r - parameterReferenceInput μ ω r =
      vec (-(κ + μ) * r) 0 := by
    ext i
    fin_cases i <;> simp [parameterActionInput, parameterReferenceInput, vec] <;> ring
  rw [parameterValueGradient, hdiff, inner_vec]
  ring

/-- 無明 `r≠0` なら、`κ>0` のもとでこのモデルの行作用は厳密に正。 -/
theorem parameterValue_ignorance_implies_action
    (μ κ ω r : ℝ) (hμ : 0 ≤ μ) (hκ : 0 < κ) (hr : r ≠ 0) :
    0 < -(inner ℝ (parameterValueGradient μ κ r)
      (parameterActionInput κ ω r - parameterReferenceInput μ ω r)) := by
  rw [← parameterValue_action_attribution]
  have hrate : 0 < μ + κ := by linarith
  have hcoef : 0 < 3 / (1 + 2 * (μ + κ)) := by positivity
  have hsq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  positivity

/-- 最適値関数の零集合は原点半径の超平面である。 -/
theorem parameterValue_eq_zero_iff (μ κ r : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    parameterValue μ κ r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have hc : 0 < 3 / (1 + 2 * (μ + κ)) := by positivity
    have hs : r ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt hc)
    exact (sq_eq_zero_iff.mp hs)
  · rintro rfl
    simp [parameterValue]

/-- 24/26の零価値目標は、このモデルでも半径0の円（一次元では超平面）。 -/
noncomputable def parameterZeroTarget (μ κ T : ℝ) : Set E2 :=
  Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
    (fun y (_ : ℝ) => parameterValue μ κ (y 0)) T

theorem parameterZeroTarget_eq_ring (μ κ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    parameterZeroTarget μ κ T = Tomabechi.Examples.Theorem27Op.ringE T := by
  ext y
  simp [parameterZeroTarget,
    Tomabechi.Theorem24_26.theorem26ZeroValueTarget,
    parameterValue_eq_zero_iff μ κ (y 0) hμ hκ,
    Tomabechi.Examples.Theorem27Op.ringE_eq]

/-- 目標集合までの距離は半径の絶対値なので、Vとの距離比較は係数cで厳密。 -/
theorem parameterW_eq_value_distance (μ κ : ℝ) (x : E2) (t : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    parameterW μ κ x t =
      (3 / (1 + 2 * (μ + κ))) *
        (Metric.infDist x (parameterZeroTarget μ κ t)) ^ 2 := by
  rw [parameterW, parameterValue, parameterZeroTarget_eq_ring μ κ t hμ hκ,
    Tomabechi.Examples.Theorem27Op.infDist_ringE]
  simp [parameterValue, sq_abs]

/-- 半径軌道は指定入力と自然ドリフトの合成方程式を満たす。 -/
theorem parameterRadius_ode (μ κ r₀ T t : ℝ) :
    HasDerivAt (parameterRadius μ κ r₀ T)
      (-(μ + κ) * parameterRadius μ κ r₀ T t) t := by
  have harg : HasDerivAt (fun s : ℝ => -parameterRate μ κ * (s - T))
      (-parameterRate μ κ) t := by
    convert ((hasDerivAt_id t).sub_const T).const_mul (-parameterRate μ κ) using 1 <;>
      simp
  have hexp := (HasDerivAt.exp harg).const_mul r₀
  change HasDerivAt (fun s => r₀ * Real.exp (-parameterRate μ κ * (s - T)))
    (-(μ + κ) * (r₀ * Real.exp (-parameterRate μ κ * (t - T)))) t
  convert hexp using 1 <;> dsimp [parameterRate] <;> ring

/-- 位相座標の速度は `ω`。 -/
theorem parameterPhase_ode (ω φ₀ T t : ℝ) :
    HasDerivAt (parameterPhase ω φ₀ T) ω t := by
  change HasDerivAt (fun s => φ₀ + ω * (s - T)) ω t
  convert (((hasDerivAt_id t).sub_const T).const_mul ω).const_add φ₀ using 1 <;> simp

/-- 二次元軌道は同一の `μ,κ,ω` を使う制御アファインODEを満たす。 -/
theorem parameterOrbit_ode (μ κ ω r₀ φ₀ T t : ℝ) :
    HasDerivAt (parameterOrbit μ κ ω r₀ φ₀ T)
      (parameterDrift μ (parameterRadius μ κ r₀ T t) +
        parameterActionInput κ ω (parameterRadius μ κ r₀ T t)) t := by
  have hr := parameterRadius_ode μ κ r₀ T t
  have hp := parameterPhase_ode ω φ₀ T t
  have h := (hr.smul_const Tomabechi.Examples.Theorem27Op.e0).add
    (hp.smul_const Tomabechi.Examples.Theorem27Op.e1)
  change HasDerivAt (fun s => parameterRadius μ κ r₀ T s •
    Tomabechi.Examples.Theorem27Op.e0 + parameterPhase ω φ₀ T s •
      Tomabechi.Examples.Theorem27Op.e1) _ t
  refine h.congr_deriv ?_
  unfold parameterDrift parameterActionInput
  ext i
  fin_cases i
  · simp [vec, Tomabechi.Examples.Theorem27Op.e0_apply0,
      Tomabechi.Examples.Theorem27Op.e1_apply0]
    ring
  · simp [vec, Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1]

@[simp] theorem parameterOrbit_radius (μ κ ω r₀ φ₀ T s : ℝ) :
    parameterOrbit μ κ ω r₀ φ₀ T s 0 = parameterRadius μ κ r₀ T s := by
  simp [parameterOrbit, Tomabechi.Examples.Theorem27Op.e0_apply0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]

@[simp] theorem parameterOrbit_phase (μ κ ω r₀ φ₀ T s : ℝ) :
    parameterOrbit μ κ ω r₀ φ₀ T s 1 = parameterPhase ω φ₀ T s := by
  simp [parameterOrbit, Tomabechi.Examples.Theorem27Op.e0_apply1,
    Tomabechi.Examples.Theorem27Op.e1_apply1]

/-- ODEの半径変数は実際のベクトル軌道の第0座標そのもの。 -/
theorem parameterOrbit_ode_on_state (μ κ ω r₀ φ₀ T t : ℝ) :
    HasDerivAt (parameterOrbit μ κ ω r₀ φ₀ T)
      (parameterDrift μ (parameterOrbit μ κ ω r₀ φ₀ T t 0) +
        parameterActionInput κ ω (parameterOrbit μ κ ω r₀ φ₀ T t 0)) t := by
  simpa [parameterOrbit_radius] using parameterOrbit_ode μ κ ω r₀ φ₀ T t

/-- A2の同じ状態軌道上で、27-AのODE・時空微分・状態勾配・基準相殺が揃う。 -/
theorem parameterModel_27A_on_orbit (μ κ ω r₀ φ₀ T t : ℝ) :
    HasDerivAt (parameterOrbit μ κ ω r₀ φ₀ T)
      (parameterDrift μ (parameterOrbit μ κ ω r₀ φ₀ T t 0) +
        parameterActionInput κ ω (parameterOrbit μ κ ω r₀ φ₀ T t 0)) t ∧
    HasFDerivAt (fun p : ℝ × E2 => parameterW μ κ p.2 p.1)
      (parameterValueDerivative μ κ (parameterOrbit μ κ ω r₀ φ₀ T t 0))
      (t, parameterOrbit μ κ ω r₀ φ₀ T t) ∧
    (∀ z, parameterValueDerivative μ κ
        (parameterOrbit μ κ ω r₀ φ₀ T t 0) (0, z) =
      inner ℝ (parameterValueGradient μ κ
        (parameterOrbit μ κ ω r₀ φ₀ T t 0)) z) ∧
    parameterValueDerivative μ κ (parameterOrbit μ κ ω r₀ φ₀ T t 0) (1, 0) +
      inner ℝ (parameterValueGradient μ κ
        (parameterOrbit μ κ ω r₀ φ₀ T t 0))
        (parameterDrift μ (parameterOrbit μ κ ω r₀ φ₀ T t 0) +
          parameterReferenceInput μ ω (parameterOrbit μ κ ω r₀ φ₀ T t 0)) = 0 := by
  refine ⟨parameterOrbit_ode_on_state μ κ ω r₀ φ₀ T t,
    parameterW_hasFDerivAt μ κ (parameterOrbit μ κ ω r₀ φ₀ T t) t, ?_, ?_⟩
  · intro z
    exact parameterValue_state_gradient μ κ
      (parameterOrbit μ κ ω r₀ φ₀ T t 0) z
  · exact parameterValue_reference_cancellation μ κ ω
      (parameterOrbit μ κ ω r₀ φ₀ T t 0)

/-- Lyapunov 関数 `W=r²/2` は厳密に `W'=-2(μ+κ)W` で減衰する。 -/
theorem parameter_lyapunov_exact_decay (μ κ r₀ T t : ℝ) :
    HasDerivAt (fun s => (parameterRadius μ κ r₀ T s) ^ 2 / 2)
      (-2 * (μ + κ) * ((parameterRadius μ κ r₀ T t) ^ 2 / 2)) t := by
  have hr := parameterRadius_ode μ κ r₀ T t
  have hsq := (hr.pow 2).div_const 2
  change HasDerivAt (fun s => (parameterRadius μ κ r₀ T s) ^ 2 / 2) _ t at hsq
  convert hsq using 1 <;> ring

/-- 一般パラメータのLyapunov関数を軌道に沿って微分すると、率 `2λ` で減衰する。 -/
theorem parameterValue_along_ode (μ κ r₀ T t : ℝ) :
    HasDerivAt (fun s => parameterValue μ κ (parameterRadius μ κ r₀ T s))
      (-2 * (μ + κ) * parameterValue μ κ (parameterRadius μ κ r₀ T t)) t := by
  have hr := parameter_lyapunov_exact_decay μ κ r₀ T t
  have hc := hr.const_mul (2 * (3 / (1 + 2 * (μ + κ))))
  convert hc using 1 <;> dsimp [parameterValue] <;> ring

/-- 同じLyapunov軌道の上右Dini微分も `-2λV` と一致する。 -/
theorem parameterValue_along_dini (μ κ r₀ T t : ℝ) :
    Tomabechi.Theorem27.Actuator.upperRightDiniDerivative
      (fun s => parameterValue μ κ (parameterRadius μ κ r₀ T s)) t =
      -2 * (μ + κ) * parameterValue μ κ (parameterRadius μ κ r₀ T t) :=
  Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_eq_of_hasDerivAt _ _ _
    (parameterValue_along_ode μ κ r₀ T t)

/-- 二次元状態軌道上での27-A Lyapunov量のDini微分は、最適値Vの指数率と一致する。 -/
theorem parameterModel_dini_on_orbit (μ κ ω r₀ φ₀ T t : ℝ) :
    Tomabechi.Theorem27.Actuator.upperRightDiniDerivative
      (fun s => parameterW μ κ (parameterOrbit μ κ ω r₀ φ₀ T s) s) t =
      -2 * (μ + κ) *
        parameterW μ κ (parameterOrbit μ κ ω r₀ φ₀ T t) t := by
  have hfun : (fun s => parameterW μ κ
      (parameterOrbit μ κ ω r₀ φ₀ T s) s) =
      (fun s => parameterValue μ κ (parameterRadius μ κ r₀ T s)) := by
    funext s
    simp [parameterW, parameterValue, parameterOrbit_radius]
  rw [hfun]
  simpa [parameterW, parameterOrbit_radius] using
    parameterValue_along_dini μ κ r₀ T t

/-! ### A2から定理27の軌道カーネルへの接続

閉形式の最適軌道について、距離二乗の下界・目標不変性・厳密Dini減衰と
27-Aの入力条件を一つの一般カーネルへ渡す。 -/

noncomputable def parameter_orbit_theorem27_kernel
    (μ κ ω r₀ φ₀ T : ℝ) (hμ : 0 ≤ μ) (hκ : 0 < κ) (hT : 0 ≤ T) := by
  let x : ℝ → E2 := fun t => parameterOrbit μ κ ω r₀ φ₀ T t
  let N : ℝ → Set E2 := fun _ => Tomabechi.Examples.Theorem27Op.ringE 0
  let W : ℝ × E2 → ℝ := fun p => parameterW μ κ p.2 p.1
  let dW : ℝ → (ℝ × E2 →L[ℝ] ℝ) := fun t =>
    parameterValueDerivative μ κ (x t 0)
  let grad : ℝ → E2 := fun t => parameterValueGradient μ κ (x t 0)
  let drift : ℝ → E2 := fun t => parameterDrift μ (x t 0)
  let u0 : ℝ → E2 := fun t => parameterActionInput κ ω (x t 0)
  let utr : ℝ → E2 := fun t => parameterReferenceInput μ ω (x t 0)
  let actuator : ℝ → E2 →L[ℝ] E2 := fun _ => ContinuousLinearMap.id ℝ E2
  have hc : 0 < 3 / (1 + 2 * (μ + κ)) := by positivity
  have hmodel : ∀ t, HasDerivAt x (drift t + actuator t (u0 t)) t ∧
      (∀ z, dW t (0, z) = inner ℝ (grad t) z) ∧
      dW t (1, 0) + inner ℝ (grad t) (drift t + actuator t (utr t)) = 0 := by
    intro t
    have h := parameterModel_27A_on_orbit μ κ ω r₀ φ₀ T t
    refine ⟨?_, ?_, ?_⟩
    · simpa [x, drift, u0, actuator, parameterActionInput] using h.1
    · intro z
      simpa [dW, grad, x] using h.2.2.1 z
    · simpa [dW, grad, drift, utr, x, actuator, parameterReferenceInput] using h.2.2.2
  have hW : ∀ t, HasFDerivAt W (dW t) (t, x t) := by
    intro t
    exact parameterW_hasFDerivAt μ κ (x t) t
  have hlower : ∀ t, T ≤ t →
      (3 / (1 + 2 * (μ + κ))) * (Metric.infDist (x t) (N t)) ^ 2 ≤ W (t, x t) := by
    intro t ht
    rw [show N t = parameterZeroTarget μ κ t from by
      simp [N, parameterZeroTarget, Tomabechi.Theorem24_26.theorem26ZeroValueTarget,
        parameterValue_eq_zero_iff μ κ _ hμ hκ,
        Tomabechi.Examples.Theorem27Op.ringE_eq]]
    exact le_of_eq (parameterW_eq_value_distance μ κ (x t) t hμ hκ).symm
  have hDini : ∀ t, T ≤ t →
      2 * (μ + κ) * W (t, x t) ≤
        -Tomabechi.Theorem27.Actuator.upperRightDiniDerivative
          (fun s => W (s, x s)) t := by
    intro t ht
    change 2 * (μ + κ) * parameterW μ κ (parameterOrbit μ κ ω r₀ φ₀ T t) t ≤
      -Tomabechi.Theorem27.Actuator.upperRightDiniDerivative
        (fun s => parameterW μ κ (parameterOrbit μ κ ω r₀ φ₀ T s) s) t
    rw [parameterModel_dini_on_orbit]
    nlinarith
  have hLip : LocallyLipschitzOn (Set.Ici T) (fun s => W (s, x s)) := by
    have heq : (fun s => W (s, x s)) =
        (fun s => parameterValue μ κ (parameterRadius μ κ r₀ T s)) := by
      funext s
      simp [W, x, parameterW, parameterValue, parameterOrbit_radius]
    rw [heq]
    have hcont : ContDiff ℝ 1
        (fun s : ℝ => parameterValue μ κ (parameterRadius μ κ r₀ T s)) := by
      unfold parameterValue parameterRadius parameterRate
      fun_prop
    exact hcont.locallyLipschitz.locallyLipschitzOn.mono (Set.subset_univ _)
  exact Tomabechi.Theorem27.theorem27_operational_ignorance_iff_descent_and_action_ae_after_time
    T N (by intro t ht; exact Tomabechi.Examples.Theorem27Op.ringE_closed 0)
    (by intro t ht; exact ⟨0, by simp [N,
      Tomabechi.Examples.Theorem27Op.ringE_eq]⟩) W x
    (3 / (1 + 2 * (μ + κ))) (2 * (μ + κ)) hc (by linarith)
    hlower hDini
    (by
      intro s t hs hst hmem
      have hr0 : r₀ = 0 := by
        have hzero : parameterOrbit μ κ ω r₀ φ₀ T s 0 = 0 := by
          simpa [x, N, Tomabechi.Examples.Theorem27Op.ringE_eq] using hmem
        have hrad : parameterRadius μ κ r₀ T s = 0 := by
          simpa [parameterOrbit_radius] using hzero
        dsimp [parameterRadius] at hrad
        exact (mul_eq_zero.mp hrad).resolve_right (ne_of_gt (Real.exp_pos _))
      change x t ∈ N t
      have hzero : parameterOrbit μ κ ω r₀ φ₀ T t 0 = 0 := by
        rw [parameterOrbit_radius, parameterRadius]
        simp [hr0]
      simpa [N, x, Tomabechi.Examples.Theorem27Op.ringE_eq] using hzero
      )
    (by
      intro s hs y hy
      have hy0 : y 0 = 0 := by
        simpa [N, Tomabechi.Examples.Theorem27Op.ringE_eq] using hy
      simp [W, parameterW, parameterValue, hy0])
    dW grad drift u0 utr actuator
    (Filter.Eventually.of_forall fun t => hW t)
    (Filter.Eventually.of_forall fun t => hmodel t)
    hLip (fun t => x t ∉ N t)
    (by intro t ht; rfl)

/-- 半径の二乗は初期二乗に `exp(-2λ(s-T))` を掛けたもの。 -/
theorem parameterRadius_sq (μ κ r₀ T s : ℝ) :
    (parameterRadius μ κ r₀ T s) ^ 2 =
      r₀ ^ 2 * Real.exp (-2 * (μ + κ) * (s - T)) := by
  calc
    (parameterRadius μ κ r₀ T s) ^ 2 =
        r₀ ^ 2 * Real.exp (-parameterRate μ κ * (s - T)) ^ 2 := by
          simp [parameterRadius]; ring
    _ = r₀ ^ 2 * Real.exp (-2 * (μ + κ) * (s - T)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp [parameterRate]
          ring

/-- Vの実際の数値は初期値に正の係数 `3/(1+2λ)` を掛けたもの。 -/
theorem parameterValue_along_exact (μ κ r₀ T s : ℝ) :
    parameterValue μ κ (parameterRadius μ κ r₀ T s) =
      parameterValue μ κ r₀ * Real.exp (-2 * (μ + κ) * (s - T)) := by
  rw [parameterValue, parameterValue, parameterRadius_sq]
  ring

/-- A2 の半径流は時刻をずらしても同じ軌道になる（再始動性）。 -/
theorem parameterRadius_restart (μ κ r₀ T u s : ℝ) :
    parameterRadius μ κ (parameterRadius μ κ r₀ T u) u s =
      parameterRadius μ κ r₀ T s := by
  simp only [parameterRadius]
  calc
    r₀ * Real.exp (-parameterRate μ κ * (u - T)) *
        Real.exp (-parameterRate μ κ * (s - u)) =
      r₀ * (Real.exp (-parameterRate μ κ * (u - T)) *
        Real.exp (-parameterRate μ κ * (s - u))) := by ring
    _ = r₀ * Real.exp (-parameterRate μ κ * (u - T) +
        -parameterRate μ κ * (s - u)) := by rw [← Real.exp_add]
    _ = r₀ * Real.exp (-parameterRate μ κ * (s - T)) := by
      congr 2
      dsimp [parameterRate]
      ring

/-- 二次元状態そのものも時刻再始動則を満たす。 -/
theorem parameterOrbit_restart (μ κ ω r₀ φ₀ T u s : ℝ) :
    parameterOrbit μ κ ω
        (parameterRadius μ κ r₀ T u) (parameterPhase ω φ₀ T u) u s =
      parameterOrbit μ κ ω r₀ φ₀ T s := by
  ext i
  fin_cases i
  · simp [parameterOrbit, parameterRadius_restart,
      Tomabechi.Examples.Theorem27Op.e0_apply0,
      Tomabechi.Examples.Theorem27Op.e1_apply0]
  · simp [parameterOrbit, parameterPhase,
      Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1]
    ring

/-- Lyapunov量は同一の一般パラメータ率 `2(μ+κ)` で指数評価できる。 -/
theorem parameter_lyapunov_exponential (μ κ r₀ T s : ℝ) :
    (parameterRadius μ κ r₀ T s) ^ 2 / 2 =
      (r₀ ^ 2 / 2) * Real.exp (-2 * (μ + κ) * (s - T)) := by
  rw [parameterRadius_sq]
  ring

/-- 微分式は上右Dini微分にもそのまま引き継がれる。 -/
theorem parameter_lyapunov_dini (μ κ r₀ T t : ℝ) :
    Tomabechi.Theorem27.Actuator.upperRightDiniDerivative
      (fun s => (parameterRadius μ κ r₀ T s) ^ 2 / 2) t =
      -2 * (μ + κ) * ((parameterRadius μ κ r₀ T t) ^ 2 / 2) := by
  exact Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_eq_of_hasDerivAt
    _ _ _ (parameter_lyapunov_exact_decay μ κ r₀ T t)

/-- 割引率1・走行費用 `3r²` の候補軌道費用の係数。
この式が `r₀²` ではなく `3r₀²/(1+2λ)` となる点を明示する。 -/
theorem parameter_running_value_coefficient (μ κ r₀ : ℝ) :
    (3 * r₀ ^ 2) / (1 + 2 * (μ + κ)) =
      r₀ ^ 2 * (3 / (1 + 2 * (μ + κ))) := by ring

/-- 走行費用 `3r²`・割引率1の最大ゲイン軌道の厳密積分値。
`μ≥0, κ>0` のため分母は正であり、固定例以外では一般に `r₀²` ではない。 -/
theorem parameter_candidate_cost_exact (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    Tomabechi.Examples.Theorem26_27ControlClasses.cost r₀ μ κ T =
      3 * r₀ ^ 2 / (1 + 2 * (μ + κ)) := by
  have hden : 0 < 1 + 2 * (μ + κ) := by linarith
  simpa [Tomabechi.Examples.Theorem26_27ControlClasses.rate] using
    (Tomabechi.Examples.Theorem26_27ControlClasses.cost_eq r₀ μ κ T hden)

/-- `parameterRadius` に沿って評価した実際の積分費用。既存の 26/27 の例と同じ割引・走行費用を使う。 -/
noncomputable def parameterOrbitCost (μ κ r₀ T : ℝ) : ℝ :=
  ∫ s, Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
    (3 * (parameterRadius μ κ r₀ T s) ^ 2)
    ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T

/-- 明示的な A2 の軌道は、代数的な係数が一致するだけでなく、主張どおりの割引走行費用をもつ。 -/
theorem parameterOrbitCost_exact (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    parameterOrbitCost μ κ r₀ T = 3 * r₀ ^ 2 / (1 + 2 * (μ + κ)) := by
  have h := parameter_candidate_cost_exact μ κ r₀ T hμ hκ
  simpa [parameterOrbitCost,
    Tomabechi.Examples.Theorem26_27ControlClasses.cost,
    parameterRadius, parameterRate,
    Tomabechi.Examples.Theorem26_27ControlClasses.orbit,
    Tomabechi.Examples.Theorem26_27ControlClasses.rate] using h

/-- 費用最小値と27で使うLyapunov関数の初期値は一致する。 -/
theorem parameterOrbitCost_eq_parameterValue (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    parameterOrbitCost μ κ r₀ T = parameterValue μ κ r₀ := by
  rw [parameterOrbitCost_exact μ κ r₀ T hμ hκ, parameterValue]
  ring

/-- A2の最大ゲイン軌道は、割引区間上で有限なBochner費用を持つ。 -/
theorem parameterOrbitCost_integrable (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    Integrable (fun s => Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
      (3 * (parameterRadius μ κ r₀ T s) ^ 2))
      (Tomabechi.Theorem24_26.futureLebesgueMeasure T) := by
  let c := 1 + 2 * (μ + κ)
  have hc : 0 < c := by dsimp [c]; linarith
  change Integrable _ (MeasureTheory.volume.restrict (Set.Ici T))
  have hbase : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi (by linarith) T
  have hbaseIci : IntegrableOn (fun s : ℝ => Real.exp (-c * s)) (Set.Ici T) :=
    integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hbase
  have hscaled : IntegrableOn
      (fun s : ℝ => (3 * r₀ ^ 2 * Real.exp (c * T)) * Real.exp (-c * s))
      (Set.Ici T) := hbaseIci.const_mul _
  have heq : (fun s : ℝ =>
      Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (3 * (parameterRadius μ κ r₀ T s) ^ 2)) =ᵐ[
          MeasureTheory.volume.restrict (Set.Ici T)]
      (fun s => (3 * r₀ ^ 2 * Real.exp (c * T)) * Real.exp (-c * s)) := by
    filter_upwards with s
    rw [Tomabechi.Theorem24_26.theorem26DiscountWeight, parameterRadius_sq]
    rw [show -1 * (s - T) = -(s - T) by ring]
    calc
      Real.exp (-(s - T)) *
          (3 * (r₀ ^ 2 * Real.exp (-2 * (μ + κ) * (s - T)))) =
        3 * r₀ ^ 2 * (Real.exp (-(s - T)) *
          Real.exp (-2 * (μ + κ) * (s - T))) := by ring
      _ = 3 * r₀ ^ 2 * Real.exp (-(s - T) +
          -2 * (μ + κ) * (s - T)) := by rw [← Real.exp_add]
      _ = 3 * r₀ ^ 2 * Real.exp (-c * (s - T)) := by
        congr 2
        dsimp [c]
        ring
      _ = (3 * r₀ ^ 2 * Real.exp (c * T)) * Real.exp (-c * s) := by
        rw [show -c * (s - T) = c * T + (-c * s) by ring, Real.exp_add]
        ring
  exact hscaled.congr heq.symm

/-! ### A2の可測ゲイン族に対する最適性

許容ゲインは時間可測で、各時刻に `0≤k(t)≤κ` を満たす。累積ゲインの積分上界から、
最大定数ゲイン軌道は各未来時刻で半径二乗を最小にする。この比較は候補ごとの有限費用を
仮定せず、拡張実数積分で表す。
-/

abbrev ParameterBoundedMeasurableGain (κ : ℝ) :=
  {k : ℝ → ℝ // Measurable k ∧ ∀ t, 0 ≤ k t ∧ k t ≤ κ}

theorem parameterGain_intervalIntegrable (κ : ℝ) (hκ : 0 ≤ κ)
    (k : ParameterBoundedMeasurableGain κ) (T s : ℝ) :
    IntervalIntegrable k.1 MeasureTheory.volume T s := by
  rw [intervalIntegrable_iff]
  let μ := MeasureTheory.volume.restrict (Set.uIoc T s)
  have hfinite : MeasureTheory.volume (Set.uIoc T s) < ⊤ := by
    apply lt_of_le_of_lt (MeasureTheory.measure_mono Set.uIoc_subset_uIcc)
    exact isCompact_uIcc.measure_lt_top
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hfinite
  have hconst : Integrable (fun _ : ℝ => κ) μ := integrable_const _
  refine hconst.mono' k.2.1.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(k.2.2 t).1], (k.2.2 t).2⟩

/-- 時刻Tからの累積ゲイン。 -/
noncomputable def parameterAccumulatedGain (κ : ℝ) (k : ParameterBoundedMeasurableGain κ)
    (T s : ℝ) : ℝ := ∫ u in T..s, k.1 u

/-- 可測ゲインの累積量は `0` と `κ(s-T)` の間にある。 -/
theorem parameterAccumulatedGain_bounds (κ : ℝ) (hκ : 0 ≤ κ)
    (k : ParameterBoundedMeasurableGain κ) (T s : ℝ) (hTs : T ≤ s) :
    0 ≤ parameterAccumulatedGain κ k T s ∧
      parameterAccumulatedGain κ k T s ≤ κ * (s - T) := by
  have hkint := parameterGain_intervalIntegrable κ hκ k T s
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hmax : IntervalIntegrable (fun _ : ℝ => κ) MeasureTheory.volume T s :=
    continuous_const.intervalIntegrable T s
  have hlo := intervalIntegral.integral_mono_on hTs hzero hkint
    (fun u _ => (k.2.2 u).1)
  have hhi := intervalIntegral.integral_mono_on hTs hkint hmax
    (fun u _ => (k.2.2 u).2)
  constructor
  · simpa [parameterAccumulatedGain] using hlo
  · calc
      parameterAccumulatedGain κ k T s ≤ (s - T) * κ := by
        simpa [parameterAccumulatedGain, intervalIntegral.integral_const] using hhi
      _ = κ * (s - T) := by ring

theorem parameterAccumulatedGain_add (κ : ℝ) (hκ : 0 ≤ κ)
    (k : ParameterBoundedMeasurableGain κ) (T u s : ℝ) :
    parameterAccumulatedGain κ k T s =
      parameterAccumulatedGain κ k T u + parameterAccumulatedGain κ k u s := by
  symm
  exact intervalIntegral.integral_add_adjacent_intervals
    (parameterGain_intervalIntegrable κ hκ k T u)
    (parameterGain_intervalIntegrable κ hκ k u s)

theorem parameterAccumulatedGain_eq_of_future_agreement (κ : ℝ) (hκ : 0 ≤ κ)
    (k₁ k₂ : ParameterBoundedMeasurableGain κ) (T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    parameterAccumulatedGain κ k₁ T s = parameterAccumulatedGain κ k₂ T s := by
  unfold parameterAccumulatedGain
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hTs] at ht
  exact hfuture t (le_trans hT ht.1)

/-- 累積ゲインの原始関数はκ-Lipschitz。 -/
theorem parameterAccumulatedGain_lipschitz (κ : ℝ) (hκ : 0 ≤ κ)
    (k : ParameterBoundedMeasurableGain κ) (T : ℝ) :
    LipschitzWith (Real.toNNReal κ)
      (parameterAccumulatedGain κ k T) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hdiff : parameterAccumulatedGain κ k T s - parameterAccumulatedGain κ k T t =
      parameterAccumulatedGain κ k t s := by
    have hsplit := parameterAccumulatedGain_add κ hκ k T t s
    dsimp [parameterAccumulatedGain] at hsplit ⊢
    linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := k.1) (a := t) (b := s) (C := κ) (fun u _ => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(k.2.2 u).1], (k.2.2 u).2⟩)
  have hreal : |parameterAccumulatedGain κ k T s -
      parameterAccumulatedGain κ k T t| ≤ κ * |s - t| := by
    rw [hdiff, ← Real.norm_eq_abs]
    exact hnorm
  rw [Real.dist_eq, Real.dist_eq]
  have hcoef : ((Real.toNNReal κ : NNReal) : ℝ) = κ :=
    Real.coe_toNNReal κ hκ
  rw [hcoef]
  exact hreal

/-- 時間依存ゲイン `k(t)` による半径軌道。 -/
noncomputable def parameterGainRadius (μ κ : ℝ)
    (k : ParameterBoundedMeasurableGain κ) (r₀ T s : ℝ) : ℝ :=
  r₀ * Real.exp (-(μ * (s - T) + parameterAccumulatedGain κ k T s))

/-- 任意の有界可測ゲインで作った半径軌道は連続である。 -/
theorem parameterGainRadius_continuous (μ κ r₀ T : ℝ)
    (hκ : 0 ≤ κ) (k : ParameterBoundedMeasurableGain κ) :
    Continuous (parameterGainRadius μ κ k r₀ T) := by
  have hacc : Continuous (parameterAccumulatedGain κ k T) :=
    (parameterAccumulatedGain_lipschitz κ hκ k T).continuous
  have hlin : Continuous (fun s : ℝ => μ * (s - T)) := by fun_prop
  have hexp : Continuous (fun s : ℝ =>
      Real.exp (-(μ * (s - T) + parameterAccumulatedGain κ k T s))) :=
    Real.continuous_exp.comp (hlin.add hacc).neg
  convert hexp.const_mul r₀ using 1
  ext s
  simp [parameterGainRadius]

/-- ゲイン上限κを常に使う軌道より、どの許容ゲイン軌道も半径二乗が小さくならない。 -/
theorem parameterGainRadius_sq_lower_bound (μ κ : ℝ) (hκ : 0 ≤ κ)
    (k : ParameterBoundedMeasurableGain κ) (r₀ T s : ℝ) (hTs : T ≤ s) :
    (parameterRadius μ κ r₀ T s) ^ 2 ≤
      (parameterGainRadius μ κ k r₀ T s) ^ 2 := by
  have hacc := (parameterAccumulatedGain_bounds κ hκ k T s hTs).2
  have hexponent : -(μ * (s - T) + κ * (s - T)) ≤
      -(μ * (s - T) + parameterAccumulatedGain κ k T s) := by
    have hgap : 0 ≤ s - T := sub_nonneg.mpr hTs
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hsquare := (sq_le_sq₀ (Real.exp_nonneg _) (Real.exp_nonneg _)).2 hexp
  have hmul := mul_le_mul_of_nonneg_left hsquare (sq_nonneg r₀)
  have hmax : -(μ * (s - T) + κ * (s - T)) =
      -parameterRate μ κ * (s - T) := by
    dsimp [parameterRate]
    ring
  rw [parameterRadius, parameterGainRadius]
  calc
    (r₀ * Real.exp (-parameterRate μ κ * (s - T))) ^ 2 =
        r₀ ^ 2 * Real.exp (-parameterRate μ κ * (s - T)) ^ 2 := by ring
    _ ≤ r₀ ^ 2 * Real.exp (-(μ * (s - T) +
          parameterAccumulatedGain κ k T s)) ^ 2 := by
      simpa [parameterRate, hmax, add_comm, add_left_comm, add_assoc] using hmul
    _ = (r₀ * Real.exp (-(μ * (s - T) +
          parameterAccumulatedGain κ k T s))) ^ 2 := by ring

/-- 割引と走行費用を含めた可測ゲイン軌道の被積分関数。 -/
noncomputable def parameterGainCostIntegrand (μ κ : ℝ)
    (k : ParameterBoundedMeasurableGain κ) (r₀ T s : ℝ) : ℝ :=
  Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
    (3 * (parameterGainRadius μ κ k r₀ T s) ^ 2)

/-- 可測時間依存ゲイン `0≤k≤κ` の全体で、最大ゲイン費用が最小値を与える。
この主張はBochner可積分性を個々の競合ゲインに要求せず、拡張実数費用で述べる。 -/
theorem parameterGainCost_minimal (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ)
    (k : ParameterBoundedMeasurableGain κ) :
    ENNReal.ofReal (parameterValue μ κ r₀) ≤
      ∫⁻ s, ENNReal.ofReal (parameterGainCostIntegrand μ κ k r₀ T s)
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
  have hbaseInt := parameterOrbitCost_integrable μ κ r₀ T hμ hκ
  have hbaseNonneg : 0 ≤ᵐ[Tomabechi.Theorem24_26.futureLebesgueMeasure T]
      (fun s => Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (3 * (parameterRadius μ κ r₀ T s) ^ 2)) := by
    filter_upwards with s
    unfold Tomabechi.Theorem24_26.theorem26DiscountWeight
    positivity
  have hbaseLin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hbaseInt hbaseNonneg
  have hbaseValue : ENNReal.ofReal (parameterValue μ κ r₀) =
      ∫⁻ s, ENNReal.ofReal
        (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * (parameterRadius μ κ r₀ T s) ^ 2))
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
    rw [← parameterOrbitCost_eq_parameterValue μ κ r₀ T hμ hκ]
    exact hbaseLin
  have hpoint : ∀ᵐ s ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (3 * (parameterRadius μ κ r₀ T s) ^ 2) ≤
      parameterGainCostIntegrand μ κ k r₀ T s := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
    have hsq := parameterGainRadius_sq_lower_bound μ κ hκ.le k r₀ T s hs
    have hdiscount : 0 ≤ Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s := by
      rw [Tomabechi.Theorem24_26.theorem26DiscountWeight]
      positivity
    rw [parameterGainCostIntegrand]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq (by norm_num : 0 ≤ (3 : ℝ))) hdiscount
  calc
    ENNReal.ofReal (parameterValue μ κ r₀) =
        ∫⁻ s, ENNReal.ofReal
          (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
            (3 * (parameterRadius μ κ r₀ T s) ^ 2))
          ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := hbaseValue
    _ ≤ ∫⁻ s, ENNReal.ofReal (parameterGainCostIntegrand μ κ k r₀ T s)
          ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hpoint] with s hs
      exact ENNReal.ofReal_le_ofReal hs

/-- `[0,κ]` に入る定数の最大可測ゲイン。 -/
def parameterMaximalGain (κ : ℝ) (hκ : 0 ≤ κ) : ParameterBoundedMeasurableGain κ :=
  ⟨fun _ => κ, measurable_const, fun _ => ⟨hκ, le_rfl⟩⟩

theorem parameterAccumulatedGain_maximal (κ : ℝ) (hκ : 0 ≤ κ) (T s : ℝ) :
    parameterAccumulatedGain κ (parameterMaximalGain κ hκ) T s = κ * (s - T) := by
  simp [parameterAccumulatedGain, parameterMaximalGain,
    intervalIntegral.integral_const]
  ring

/-- 最大定数ゲインの半径軌道は、A2の閉形式軌道そのもの。 -/
theorem parameterGainRadius_maximal (μ κ r₀ T s : ℝ) (hκ : 0 ≤ κ) :
    parameterGainRadius μ κ (parameterMaximalGain κ hκ) r₀ T s =
      parameterRadius μ κ r₀ T s := by
  rw [parameterGainRadius, parameterAccumulatedGain_maximal κ hκ]
  congr 2
  dsimp [parameterRate]
  ring

/-- 最大ゲインは一般有界可測ゲイン族で最小値を達成する。 -/
theorem parameter_maximal_gain_attains_value (μ κ r₀ T : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) :
    ENNReal.ofReal (parameterValue μ κ r₀) =
      ∫⁻ s, ENNReal.ofReal (parameterGainCostIntegrand μ κ
        (parameterMaximalGain κ hκ.le) r₀ T s)
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
  have hInt := parameterOrbitCost_integrable μ κ r₀ T hμ hκ
  have hNonneg : 0 ≤ᵐ[Tomabechi.Theorem24_26.futureLebesgueMeasure T]
      (fun s => Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
        (3 * (parameterRadius μ κ r₀ T s) ^ 2)) := by
    filter_upwards with s
    unfold Tomabechi.Theorem24_26.theorem26DiscountWeight
    positivity
  have hlin := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg
  calc
    ENNReal.ofReal (parameterValue μ κ r₀) =
        ENNReal.ofReal (parameterOrbitCost μ κ r₀ T) := by
      rw [parameterOrbitCost_eq_parameterValue μ κ r₀ T hμ hκ]
    _ = ∫⁻ s, ENNReal.ofReal
        (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * (parameterRadius μ κ r₀ T s) ^ 2))
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := hlin
    _ = ∫⁻ s, ENNReal.ofReal (parameterGainCostIntegrand μ κ
          (parameterMaximalGain κ hκ.le) r₀ T s)
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards with s
      simp [parameterGainCostIntegrand, parameterGainRadius_maximal μ κ r₀ T s hκ.le]


/-- フィードバックの表示の選択と軌道の公式をつなぐ：非負の未来で入力が同じなら、状態軌道も同じ。 -/
theorem parameterGainRadius_eq_of_future_agreement (μ κ r₀ T s : ℝ)
    (hκ : 0 ≤ κ) (k₁ k₂ : ParameterBoundedMeasurableGain κ)
    (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    parameterGainRadius μ κ k₁ r₀ T s = parameterGainRadius μ κ k₂ r₀ T s := by
  unfold parameterGainRadius
  rw [parameterAccumulatedGain_eq_of_future_agreement κ hκ k₁ k₂ T s hT hTs hfuture]

/-- 有界可测ゲインで定める二次元軌道。 -/
noncomputable def parameterGainVectorOrbit (μ κ ω : ℝ)
    (k : ParameterBoundedMeasurableGain κ) (x : Tomabechi.Examples.Theorem27Op.E2)
    (T s : ℝ) : Tomabechi.Examples.Theorem27Op.E2 :=
  parameterGainRadius μ κ k (x 0) T s • Tomabechi.Examples.Theorem27Op.e0 +
    (x 1 + ω * (s - T)) • Tomabechi.Examples.Theorem27Op.e1

theorem parameterGainRadius_initial (μ κ : ℝ)
    (k : ParameterBoundedMeasurableGain κ) (r₀ T : ℝ) :
    parameterGainRadius μ κ k r₀ T T = r₀ := by
  simp [parameterGainRadius, parameterAccumulatedGain]

theorem parameterGainRadius_maximal_eq (μ κ r₀ T s : ℝ) (hκ : 0 ≤ κ) :
    parameterGainRadius μ κ (parameterMaximalGain κ hκ) r₀ T s =
      parameterRadius μ κ r₀ T s :=
  parameterGainRadius_maximal μ κ r₀ T s hκ

@[simp] theorem parameterGainVectorOrbit_radius (μ κ ω : ℝ)
    (k : ParameterBoundedMeasurableGain κ) (x : Tomabechi.Examples.Theorem27Op.E2)
    (T s : ℝ) :
    parameterGainVectorOrbit μ κ ω k x T s 0 =
      parameterGainRadius μ κ k (x 0) T s := by
  simp [parameterGainVectorOrbit, Tomabechi.Examples.Theorem27Op.e0_apply0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]

theorem parameterGainVectorOrbit_eq_of_future_agreement (μ κ ω : ℝ)
    (k₁ k₂ : ParameterBoundedMeasurableGain κ) (x : Tomabechi.Examples.Theorem27Op.E2)
    (T s : ℝ) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hTs : T ≤ s)
    (hfuture : ∀ t, 0 ≤ t → k₁.1 t = k₂.1 t) :
    parameterGainVectorOrbit μ κ ω k₁ x T s =
      parameterGainVectorOrbit μ κ ω k₂ x T s := by
  ext i
  fin_cases i
  · simp [parameterGainVectorOrbit,
      parameterGainRadius_eq_of_future_agreement μ κ (x 0) T s hκ k₁ k₂ hT hTs hfuture,
      Tomabechi.Examples.Theorem27Op.e0_apply0,
      Tomabechi.Examples.Theorem27Op.e1_apply0]
  · simp [parameterGainVectorOrbit,
      Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1]

theorem parameterGainVectorOrbit_maximal_eq (μ κ ω : ℝ) (x : Tomabechi.Examples.Theorem27Op.E2)
    (T s : ℝ) (hκ : 0 ≤ κ) :
    parameterGainVectorOrbit μ κ ω (parameterMaximalGain κ hκ) x T s =
      parameterOrbit μ κ ω (x 0) (x 1) T s := by
  ext i
  fin_cases i
  · simp [parameterGainVectorOrbit, parameterOrbit,
      parameterGainRadius_maximal μ κ (x 0) T s hκ,
      Tomabechi.Examples.Theorem27Op.e0_apply0,
      Tomabechi.Examples.Theorem27Op.e1_apply0]
  · simp [parameterGainVectorOrbit, parameterOrbit,
      parameterPhase,
      Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1] <;> ring

/-- パラメータ付き時間可測ゲインから作るBorel Markovフィードバック。 -/
noncomputable def parameterGainVectorPolicy (ω κ : ℝ)
    (k : ParameterBoundedMeasurableGain κ) :
    Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2 where
  action q :=
    (-(k.1 q.1.1) * q.2 0) • Tomabechi.Examples.Theorem27Op.e0 +
      ω • Tomabechi.Examples.Theorem27Op.e1
  measurable_action := by
    have hk := k.2.1
    fun_prop

/-- 各フィードバックが上のゲイン族に属するときだけ許容とする。 -/
def parameterGainPolicyAdmissible (ω κ : ℝ)
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2) : Prop :=
  ∃ k : ParameterBoundedMeasurableGain κ,
    ∀ q : Set.Ici (0 : ℝ) × Tomabechi.Examples.Theorem27Op.E2,
      π.action q = (parameterGainVectorPolicy ω κ k).action q

/-- 許容方策に対応するゲインを選ぶ。 -/
noncomputable def selectedParameterGain (ω κ : ℝ)
    (hκ : 0 ≤ κ)
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2) :
    ParameterBoundedMeasurableGain κ := by
  classical
  exact if h : parameterGainPolicyAdmissible ω κ π then Classical.choose h
    else parameterMaximalGain κ hκ

theorem selectedParameterGain_spec (ω κ : ℝ) (hκ : 0 ≤ κ)
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2)
    (hπ : parameterGainPolicyAdmissible ω κ π)
    (t : Set.Ici (0 : ℝ)) (x : Tomabechi.Examples.Theorem27Op.E2) :
    π.action (t, x) =
      (parameterGainVectorPolicy ω κ (selectedParameterGain ω κ hκ π)).action (t, x) := by
  classical
  have hrep := Classical.choose_spec hπ
  have h := hrep (t, x)
  simpa [selectedParameterGain, hπ] using h

theorem selectedParameterGain_eq_witness_future (ω κ : ℝ) (hκ : 0 ≤ κ)
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2)
    (k : ParameterBoundedMeasurableGain κ)
    (hπ : ∀ q : Set.Ici (0 : ℝ) × Tomabechi.Examples.Theorem27Op.E2,
      π.action q = (parameterGainVectorPolicy ω κ k).action q)
    (t : ℝ) (ht : 0 ≤ t) :
    (selectedParameterGain ω κ hκ π).1 t = k.1 t := by
  let x : Tomabechi.Examples.Theorem27Op.E2 := Tomabechi.Examples.Theorem27Op.e0
  have hselected := selectedParameterGain_spec ω κ hκ π ⟨k, hπ⟩ ⟨t, ht⟩ x
  have hwitness := hπ (⟨t, ht⟩, x)
  have hrad := congrArg (fun z : Tomabechi.Examples.Theorem27Op.E2 => z 0)
    (hselected.symm.trans hwitness)
  simpa [x, parameterGainVectorPolicy, Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e0_apply0] using hrad

abbrev ParameterSourceState (κ : ℝ) :
    Tomabechi.Theorem24_26_Model.SourceAbstraction → Type
  | false => Unit
  | true => Tomabechi.Examples.Theorem27Op.E2

abbrev ParameterSourcePolicy (κ : ℝ)
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) : Type :=
  match a with
  | false => PUnit
  | true => Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2

noncomputable def parameterSourceTrajectory (μ κ ω : ℝ) (hκ : 0 ≤ κ) :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      ParameterSourcePolicy κ a → ParameterSourceState κ a → ℝ → ℝ → ParameterSourceState κ a
  | false, _, x, _, _ => x
  | true, π, x, T, s => parameterGainVectorOrbit μ κ ω
      (selectedParameterGain ω κ hκ π) x T s

def parameterSourceRunningCost (κ : ℝ) :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      ParameterSourcePolicy κ a → ParameterSourceState κ a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, x, _ => 3 * (x 0) ^ 2

def parameterSourceAdmissible (ω κ : ℝ) :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      ParameterSourcePolicy κ a → ParameterSourceState κ a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, _, _ => parameterGainPolicyAdmissible ω κ π

noncomputable def parameterSourceOptimalValue (μ κ : ℝ) :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      ParameterSourceState κ a → ℝ → ℝ
  | false, _, T => Tomabechi.Theorem24_26_Model.lowerValue T
  | true, x, _ => parameterValue μ κ (x 0)

noncomputable def parameterSourceOptimalPolicy (ω κ : ℝ) (hκ : 0 ≤ κ) :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      (x : ParameterSourceState κ a) → ℝ → ParameterSourcePolicy κ a
  | false, _, _ => PUnit.unit
  | true, _, _ => parameterGainVectorPolicy ω κ (parameterMaximalGain κ hκ)

noncomputable def parameterSourceMaximalPolicy (ω κ : ℝ) (hκ : 0 ≤ κ) :
    ParameterSourcePolicy κ true :=
  parameterGainVectorPolicy ω κ (parameterMaximalGain κ hκ)

/-- 制御族の最適フィードバックが生成する軌道は、A2の閉形式解そのもの。 -/
theorem parameterSourceTrajectory_maximal_eq_orbit (μ κ ω : ℝ)
    (hκ : 0 ≤ κ)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    parameterSourceTrajectory μ κ ω hκ true
      (parameterSourceMaximalPolicy ω κ hκ) x T s =
        parameterOrbit μ κ ω (x 0) (x 1) T s := by
  change parameterGainVectorOrbit μ κ ω
      (selectedParameterGain ω κ hκ (parameterSourceMaximalPolicy ω κ hκ)) x T s = _
  rw [parameterGainVectorOrbit_eq_of_future_agreement μ κ ω
    (selectedParameterGain ω κ hκ (parameterSourceMaximalPolicy ω κ hκ))
    (parameterMaximalGain κ hκ) x T s hκ hT hTs ?_]
  · exact parameterGainVectorOrbit_maximal_eq μ κ ω x T s hκ
  · intro t ht
    exact selectedParameterGain_eq_witness_future ω κ hκ
      (parameterSourceMaximalPolicy ω κ hκ)
      (parameterMaximalGain κ hκ) (fun _ => rfl) t ht


/-- A2 の最適値係数 `c=3/(1+2λ)` は正で、初期半径が非零なら値も正。 -/
theorem parameter_candidate_value_positive (μ κ r₀ : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) (hr₀ : r₀ ≠ 0) :
    0 < (3 / (1 + 2 * (μ + κ))) * r₀ ^ 2 := by
  have hden : 0 < 1 + 2 * (μ + κ) := by linarith
  have hc : 0 < 3 / (1 + 2 * (μ + κ)) := by positivity
  have hr : 0 < r₀ ^ 2 := sq_pos_of_ne_zero hr₀
  exact mul_pos hc hr

/-- 一般の `μ≥0` のもとで、許容定数ゲイン `0≤K≤κ` では最大ゲインが
割引費用を最小化する。ここでの許容族は定数ゲイン族である。 -/
theorem parameter_maximal_constant_gain_optimal
    (r₀ μ κ K T : ℝ) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ)
    (hK : 0 ≤ K) (hKκ : K ≤ κ) :
    Tomabechi.Examples.Theorem26_27ControlClasses.cost r₀ μ κ T ≤
      Tomabechi.Examples.Theorem26_27ControlClasses.cost r₀ μ K T :=
  Tomabechi.Examples.Theorem26_27ControlClasses.bounded_constant_gain_optimal
    r₀ μ κ K T hμ hκ hK hKκ

/-- 基準入力 `(μr,ω)` は、時間微分と基準閉ループの半径変化を相殺する。 -/
theorem parameter_reference_cancellation (μ ω r : ℝ) :
    0 + inner ℝ (gradW r) (drift μ r + G (utrA μ ω r)) = 0 := by
  exact A2_residual_A μ ω r

/-- 指定入力 `(-κr,ω)` の行の寄与は、減衰量 `(μ+κ)r²` と一致する。 -/
theorem parameter_attribution (μ κ ω r : ℝ) :
    (μ + κ) * r ^ 2 =
      -(inner ℝ (gradW r) (G (u0 κ ω r - utrA μ ω r))) := by
  exact attribution_A μ κ ω r

/-! ## A1: 有界可測ゲインと27-A指定入力の座標接続

有界可測ゲインの最大値 `1/2` は、27-Aの指定入力と軌道を座標ごとに一致させる。
ここでは等式を `E2` 上で証明し、零集合上の一致だけに依存しない。
-/

/-- 可測ゲイン `k(t)` による二次元入力 `(-k(t)r, 3/2)`。 -/
noncomputable def measurableGainInput (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (t r : ℝ) : Tomabechi.Examples.Theorem27Op.E2 :=
  vec (-(k.1 t) * r) (3 / 2 : ℝ)

/-- 状態 `x` を受け取る形にした可測ゲイン入力 `u_k(t,x)`。 -/
noncomputable def measurableGainInputOnState
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (t : ℝ) (x : Tomabechi.Examples.Theorem27Op.E2) :
    Tomabechi.Examples.Theorem27Op.E2 := measurableGainInput k t (x 0)

/-- 状態空間上の自然ドリフト `f₀(x)=vec(-x₀/2,0)`。 -/
noncomputable def measurableGainNaturalDrift
    (x : Tomabechi.Examples.Theorem27Op.E2) : Tomabechi.Examples.Theorem27Op.E2 :=
  vec (-((1 / 2 : ℝ) * x 0)) 0

/-- 二次元制御空間から状態空間への作用素 `G` は恒等写像。 -/
def measurableGainActuator :
    Tomabechi.Examples.Theorem27Op.E2 →L[ℝ] Tomabechi.Examples.Theorem27Op.E2 :=
  ContinuousLinearMap.id ℝ _

@[simp] theorem measurableGainActuator_eq_GE :
    measurableGainActuator = Tomabechi.Examples.Theorem27Op.GE := rfl

/-- 状態で定義した自然ドリフトは、指定軌道上ではOperational版の
ドリフトと一致する。 -/
theorem measurableGainNaturalDrift_eq_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    measurableGainNaturalDrift (Tomabechi.Examples.Theorem27Op.flowE x T t) =
      Tomabechi.Examples.Theorem27Op.driftE x T t := by
  ext i
  fin_cases i <;> simp [measurableGainNaturalDrift, vec,
    Tomabechi.Examples.Theorem27Op.driftE,
    Tomabechi.Examples.Theorem27Op.flowE_0,
    Tomabechi.Examples.Theorem27Op.mu,
    Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e1] <;> ring

/-- 最大有界可測ゲインの入力は、27-Aの指定入力そのものになる。 -/
theorem maximal_measurable_input_eq_operational (r : ℝ) :
    measurableGainInput Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain 0 r =
      (-(1 / 2) * r) • Tomabechi.Examples.Theorem27Op.e0 +
      Tomabechi.Examples.Theorem27Op.omg • Tomabechi.Examples.Theorem27Op.e1 := by
  ext i
  fin_cases i <;>
    simp [measurableGainInput, vec,
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
      Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1,
      Tomabechi.Examples.Theorem27Op.omg] <;> ring

/-- 最大ゲインの時刻別入力をOperationalの指定入力へ直接同定する。 -/
theorem maximal_measurable_input_eq_u0E (x : Tomabechi.Examples.Theorem27Op.E2)
    (T t : ℝ) :
    measurableGainInput Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain t
      (Tomabechi.Examples.Theorem27Op.flowE x T t 0) =
      Tomabechi.Examples.Theorem27Op.u0E x T t := by
  ext i
  fin_cases i <;> simp [measurableGainInput, vec,
    Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
    Tomabechi.Examples.Theorem27Op.u0E, Tomabechi.Examples.Theorem27Op.flowE_0,
    Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1,
    Tomabechi.Examples.Theorem27Op.kap, Tomabechi.Examples.Theorem27Op.omg]

/-- 27-Aの基準入力を状態半径から作る。 -/
noncomputable def measurableGainReferenceInput (r : ℝ) : Tomabechi.Examples.Theorem27Op.E2 :=
  vec ((1 / 2 : ℝ) * r) (3 / 2 : ℝ)

/-- 半径射影で作った基準入力はOperationalの `utrE` とベクトルとして一致する。 -/
theorem measurable_reference_input_eq_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    measurableGainReferenceInput (Tomabechi.Examples.Theorem27Op.flowE x T t 0) =
      Tomabechi.Examples.Theorem27Op.utrE x T t := by
  ext i
  fin_cases i <;> simp [measurableGainReferenceInput, vec,
    Tomabechi.Examples.Theorem27Op.utrE, Tomabechi.Examples.Theorem27Op.flowE_0,
    Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1,
    Tomabechi.Examples.Theorem27Op.mu, Tomabechi.Examples.Theorem27Op.omg]

/-- 同じ半径状態上で、基準入力が27-A2の `W` 不変性条件を満たす。 -/
theorem measurable_reference_input_satisfies_27A2
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    Tomabechi.Examples.Theorem27Op.dWE x T t (1, 0) +
      inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
        (Tomabechi.Examples.Theorem27Op.driftE x T t +
          Tomabechi.Examples.Theorem27Op.GE
            (measurableGainReferenceInput
              (Tomabechi.Examples.Theorem27Op.flowE x T t 0))) = 0 := by
  rw [measurable_reference_input_eq_operational]
  exact Tomabechi.Examples.Theorem27Op.reference_cancellation x T t

/-- 1 つの有界可測な動径ゲインから作る、Borel マルコフの 2 次元フィードバック。 -/
noncomputable def measurableGainVectorPolicy
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) :
    Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback Tomabechi.Examples.Theorem27Op.E2
      Tomabechi.Examples.Theorem27Op.E2 where
  action q :=
    (-(k.1 q.1.1) * q.2 0) • Tomabechi.Examples.Theorem27Op.e0 +
      (3 / 2 : ℝ) • Tomabechi.Examples.Theorem27Op.e1
  measurable_action := by
    have hk := k.2.1
    fun_prop

/-- このフィードバックの作用は、ちょうど `u_k(t,x)=vec(-k(t)x₀,3/2)` である。 -/
theorem measurableGainVectorPolicy_action
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (t : Set.Ici (0 : ℝ)) (x : Tomabechi.Examples.Theorem27Op.E2) :
    (measurableGainVectorPolicy k).action (t, x) = measurableGainInput k t.1 (x 0) := by
  ext i
  fin_cases i <;> simp [measurableGainVectorPolicy, measurableGainInput, vec,
    Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1]

/-- 完全な可測フィードバックは、その動径入力が有界可測ゲイン族のゲインで表されるときに限り許容である。 -/
def measurableGainVectorPolicyAdmissible
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback Tomabechi.Examples.Theorem27Op.E2
      Tomabechi.Examples.Theorem27Op.E2) : Prop :=
  ∃ k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal,
    ∀ q : Set.Ici (0 : ℝ) × Tomabechi.Examples.Theorem27Op.E2,
      π.action q = (measurableGainVectorPolicy k).action q

/-- 許容な 2 次元マルコフ方策を表すゲインを選ぶ。 -/
noncomputable def selectedMeasurableVectorGain
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback Tomabechi.Examples.Theorem27Op.E2
      Tomabechi.Examples.Theorem27Op.E2) :
    Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal := by
  classical
  exact if h : measurableGainVectorPolicyAdmissible π then Classical.choose h
    else Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain

/-- 選んだゲインは、すべての非負時刻とすべての状態で、方策のベクトル作用を実現する。 -/
theorem selectedMeasurableVectorGain_spec
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback Tomabechi.Examples.Theorem27Op.E2
      Tomabechi.Examples.Theorem27Op.E2)
    (hπ : measurableGainVectorPolicyAdmissible π)
    (t : Set.Ici (0 : ℝ)) (x : Tomabechi.Examples.Theorem27Op.E2) :
    π.action (t, x) =
      (measurableGainVectorPolicy (selectedMeasurableVectorGain π)).action (t, x) := by
  classical
  have hrep := Classical.choose_spec hπ
  have h := hrep (t, x)
  simpa [selectedMeasurableVectorGain, hπ] using h

/-- 許容性の証拠と、選んだ代表は、すべての非負時刻で一致する。単位半径状態でベクトルフィードバックを評価する。 -/
theorem selectedMeasurableVectorGain_eq_witness_future
    (π : Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (hπ : ∀ q : Set.Ici (0 : ℝ) × Tomabechi.Examples.Theorem27Op.E2,
      π.action q = (measurableGainVectorPolicy k).action q)
    (t : ℝ) (ht : 0 ≤ t) :
    (selectedMeasurableVectorGain π).1 t = k.1 t := by
  let x : Tomabechi.Examples.Theorem27Op.E2 :=
    Tomabechi.Examples.Theorem27Op.e0
  have hselected := selectedMeasurableVectorGain_spec π ⟨k, hπ⟩ ⟨t, ht⟩ x
  have hwitness := hπ (⟨t, ht⟩, x)
  have hrad := congrArg (fun z : Tomabechi.Examples.Theorem27Op.E2 => z 0)
    (hselected.symm.trans hwitness)
  simpa [x, measurableGainVectorPolicy, Tomabechi.Examples.Theorem27Op.e0,
    Tomabechi.Examples.Theorem27Op.e0_apply0] using hrad

/-- 半径解と線形位相を組にした軌道。 -/
noncomputable def measurableGainVectorOrbit (r0 φ0 T s : ℝ)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) :
    Tomabechi.Examples.Theorem27Op.E2 :=
  (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T s) •
      Tomabechi.Examples.Theorem27Op.e0 +
    (φ0 + (3 / 2 : ℝ) * (s - T)) • Tomabechi.Examples.Theorem27Op.e1

/-- 下層・上層の源の層。上層の状態は 2 次元。 -/
abbrev VectorSourceState : Tomabechi.Theorem24_26_Model.SourceAbstraction → Type
  | false => Unit
  | true => Tomabechi.Examples.Theorem27Op.E2

abbrev VectorSourcePolicy (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) : Type :=
  match a with
  | false => PUnit
  | true => Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback
      Tomabechi.Examples.Theorem27Op.E2 Tomabechi.Examples.Theorem27Op.E2

noncomputable def vectorSourceTrajectory :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      VectorSourcePolicy a → VectorSourceState a → ℝ → ℝ → VectorSourceState a
  | false, _, x, _, _ => x
  | true, π, x, T, s => measurableGainVectorOrbit (x 0) (x 1) T s
      (selectedMeasurableVectorGain π)

def vectorSourceRunningCost :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      VectorSourcePolicy a → VectorSourceState a → ℝ → ℝ
  | false, _, _, _ => 1
  | true, _, x, _ => 3 * (x 0) ^ 2

def vectorSourceAdmissible :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      VectorSourcePolicy a → VectorSourceState a → ℝ → Prop
  | false, _, _, _ => True
  | true, π, _, _ => measurableGainVectorPolicyAdmissible π

noncomputable def vectorSourceOptimalValue :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      VectorSourceState a → ℝ → ℝ
  | false, _, T => Tomabechi.Theorem24_26_Model.lowerValue T
  | true, x, _ => (x 0) ^ 2

noncomputable def vectorSourceOptimalPolicy :
    (a : Tomabechi.Theorem24_26_Model.SourceAbstraction) →
      (x : VectorSourceState a) → ℝ → VectorSourcePolicy a
  | false, _, _ => PUnit.unit
  | true, _, _ => measurableGainVectorPolicy
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain

noncomputable def vectorMaximalPolicy : VectorSourcePolicy true :=
  measurableGainVectorPolicy
    Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain

theorem vectorSourceTrajectory_radial (π : VectorSourcePolicy true)
    (x : Tomabechi.Examples.Theorem27Op.E2) (T s : ℝ) :
    (vectorSourceTrajectory true π x T s) 0 =
      Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit
        (x 0) (selectedMeasurableVectorGain π) T s := by
  simp [vectorSourceTrajectory, measurableGainVectorOrbit,
    Tomabechi.Examples.Theorem27Op.e0_apply0,
    Tomabechi.Examples.Theorem27Op.e1_apply0]

theorem vectorMaximalTrajectory_radial_eq_flow (x : Tomabechi.Examples.Theorem27Op.E2)
    (T s : ℝ) (hT : 0 ≤ T) (hTs : T ≤ s) :
    (vectorSourceTrajectory true
      (vectorSourceOptimalPolicy true x T) x T s) 0 =
        Tomabechi.Theorem24_26_Model.flow (x 0) T s := by
  rw [vectorSourceTrajectory_radial]
  have hk := selectedMeasurableVectorGain_eq_witness_future
    (measurableGainVectorPolicy
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain)
    Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain
      (fun _ => rfl) s (le_trans hT hTs)
  change Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0)
      (selectedMeasurableVectorGain
        (measurableGainVectorPolicy
          Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain)) T s =
    Tomabechi.Theorem24_26_Model.flow (x 0) T s
  rw [Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_eq_of_future_agreement
    (x 0) T s (selectedMeasurableVectorGain
      (measurableGainVectorPolicy
        Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain))
    Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain hT hTs]
  · rw [Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain_orbit]
    unfold Tomabechi.Examples.Theorem26_27ControlClasses.orbit
      Tomabechi.Examples.Theorem26_27ControlClasses.rate
      Tomabechi.Theorem24_26_Model.flow
    congr 1
    norm_num
  · intro t ht
    exact selectedMeasurableVectorGain_eq_witness_future
      (measurableGainVectorPolicy
        Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain)
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain
      (fun _ => rfl) t ht

set_option maxHeartbeats 2000000

/- The policy family, discounted cost, value, and PZS inputs in two dimensions.
The running value and optimal value depend only on the radial coordinate. -/
noncomputable def vectorSourceData :
    Tomabechi.Theorem24_26.Theorem24NonnegativeTimeData
      VectorSourceState VectorSourcePolicy where
  rho := 1
  rho_pos := by norm_num
  trajectory := vectorSourceTrajectory
  runningCost := vectorSourceRunningCost
  admissible := vectorSourceAdmissible
  optimalValue := vectorSourceOptimalValue
  optimalPolicy := vectorSourceOptimalPolicy
  trajectory_initial := by
    intro a π x T hT hπ
    cases a with
    | false => rfl
    | true =>
      ext i
      fin_cases i <;> simp [vectorSourceTrajectory, measurableGainVectorOrbit,
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_initial,
        Tomabechi.Examples.Theorem27Op.e0_apply0,
        Tomabechi.Examples.Theorem27Op.e0_apply1,
        Tomabechi.Examples.Theorem27Op.e1_apply0,
        Tomabechi.Examples.Theorem27Op.e1_apply1]
  runningCost_nonnegative := by
    intro a π x t
    cases a with
    | false => norm_num [vectorSourceRunningCost]
    | true => simp [vectorSourceRunningCost]; positivity
  measurable_cost := by
    intro a x T π hT hπ
    cases a with
    | false => fun_prop [vectorSourceRunningCost,
        Tomabechi.Theorem24_26.theorem26DiscountWeight]
    | true =>
      have hc := Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_continuous
        (x 0) (selectedMeasurableVectorGain π) T
      change Measurable (fun s => ENNReal.ofReal
        (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          vectorSourceRunningCost true π
            (vectorSourceTrajectory true π x T s) s))
      simp only [vectorSourceRunningCost]
      have hrad : (fun s => (vectorSourceTrajectory true π x T s) 0) =
          Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit
            (x 0) (selectedMeasurableVectorGain π) T := by
        funext s
        exact vectorSourceTrajectory_radial π x T s
      have hcRad : Continuous (fun s => (vectorSourceTrajectory true π x T s) 0) := by
        rw [hrad]
        exact hc
      have hw : Continuous (fun s : ℝ =>
          Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s) := by
        unfold Tomabechi.Theorem24_26.theorem26DiscountWeight
        fun_prop
      have hm : Measurable (fun s => Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * ((vectorSourceTrajectory true π x T s) 0) ^ 2)) := by
        have hcont : Continuous (fun s : ℝ =>
            Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
              (3 * ((vectorSourceTrajectory true π x T s) 0) ^ 2)) := by
          exact hw.mul (continuous_const.mul (hcRad.pow 2))
        exact hcont.measurable
      exact ENNReal.measurable_ofReal.comp hm
  optimal_cost_integrable := by
    intro a x T hT
    cases a with
    | false => exact Tomabechi.Theorem24_26_Model.lower_discounted_integrand_integrable T
    | true =>
      have hbase := Tomabechi.Theorem24_26_Model.discountedIntegrand_integrable
        (x 0) T
      have hpath : ∀ᵐ s ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
          (vectorSourceTrajectory true (vectorSourceOptimalPolicy true x T) x T s) 0 =
            Tomabechi.Theorem24_26_Model.flow (x 0) T s := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
        exact vectorMaximalTrajectory_radial_eq_flow x T s hT hs
      change MeasureTheory.Integrable
        (fun s => Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * ((vectorSourceTrajectory true (vectorSourceOptimalPolicy true x T)
            x T s) 0) ^ 2)) (Tomabechi.Theorem24_26.futureLebesgueMeasure T)
      apply hbase.congr
      filter_upwards [hpath] with s hs
      rw [hs]
      rfl
  optimal_policy_admissible := by
    intro a x T hT
    cases a with
    | false => trivial
    | true => exact ⟨Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain,
        fun _ => rfl⟩
  optimal_value_attained := by
    intro a x T hT
    cases a with
    | false => exact (Tomabechi.Theorem24_26_Model.lower_policy_value_attained () T).2.1
    | true =>
      change (x 0) ^ 2 = ∫ s,
        Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * ((vectorSourceTrajectory true (vectorSourceOptimalPolicy true x T)
            x T s) 0) ^ 2)
        ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T
      rw [← Tomabechi.Theorem24_26_Model.value_eq_sq]
      unfold Tomabechi.Theorem24_26_Model.value
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
      rw [vectorMaximalTrajectory_radial_eq_flow x T s hT hs]
      rfl
  optimal_value_minimal := by
    intro a x T π hT hπ
    cases a with
    | false =>
      apply le_of_eq
      simpa [vectorSourceOptimalValue, vectorSourceTrajectory,
        vectorSourceRunningCost, Tomabechi.Theorem24_26_Model.lowerValue,
        Tomabechi.Theorem24_26_Model.lowerRunningCost] using
        Tomabechi.Theorem24_26_Model.source_lower_lintegral_eq T
    | true =>
      rcases hπ with ⟨k, hk⟩
      have hmin := Tomabechi.Examples.Theorem26_27ControlClasses.measurable_time_gain_cost_minimal
        (x 0) k T
      change ENNReal.ofReal ((x 0) ^ 2) ≤
        ∫⁻ s, ENNReal.ofReal (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
          (3 * ((vectorSourceTrajectory true π x T s) 0) ^ 2))
          ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T
      calc
        _ ≤ ∫⁻ s, ENNReal.ofReal
            (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainDiscountedCost
              (x 0) k T s)
            ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := hmin
        _ = ∫⁻ s, ENNReal.ofReal (Tomabechi.Theorem24_26.theorem26DiscountWeight 1 T s *
              (3 * ((vectorSourceTrajectory true π x T s) 0) ^ 2))
              ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (μ := MeasureTheory.volume) measurableSet_Ici] with s hs
          rw [vectorSourceTrajectory_radial,
            Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_eq_of_future_agreement
              (x 0) T s (selectedMeasurableVectorGain π) k hT hs
              (fun t ht => selectedMeasurableVectorGain_eq_witness_future π k hk t
                ht)]
          rfl
  condition24A := by
    intro a ha x T hT π hπ
    cases a with
    | false =>
      simpa [vectorSourceRunningCost, vectorSourceTrajectory,
        Tomabechi.Theorem24_26_Model.lowerRunningCost] using
        Tomabechi.Theorem24_26_Model.lower_condition24A x T
    | true => exact (lt_irrefl ⊤ ha).elim

set_option maxHeartbeats 200000

set_option maxHeartbeats 2000000 in
/-- 各有限区間で二次元軌道は絶対連続。半径座標は可測ゲイン軌道、位相座標は affine。 -/
theorem measurableGainVectorOrbit_absolutelyContinuousOnInterval (r0 φ0 T s : ℝ)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal)
    (hTs : T ≤ s) :
    AbsolutelyContinuousOnInterval (fun u => measurableGainVectorOrbit r0 φ0 T u k) T s := by
  let r := fun u => Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T u
  let p := fun u : ℝ => φ0 + (3 / 2 : ℝ) * (u - T)
  have hr : AbsolutelyContinuousOnInterval r T s := by
    change AbsolutelyContinuousOnInterval
      (fun u => Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T u) T s
    exact Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_absolutelyContinuousOnInterval
      r0 k T s hTs
  have hp : AbsolutelyContinuousOnInterval p T s := by
    have hpcont : ContDiff ℝ 1 p := by
      dsimp [p]
      fun_prop
    exact hpcont.contDiffOn.absolutelyContinuousOnInterval
  have he0 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => Tomabechi.Examples.Theorem27Op.e0) T s := by
    have hc : ContDiff ℝ 1 (fun _ : ℝ => Tomabechi.Examples.Theorem27Op.e0) := contDiff_const
    exact hc.contDiffOn.absolutelyContinuousOnInterval
  have he1 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => Tomabechi.Examples.Theorem27Op.e1) T s := by
    have hc : ContDiff ℝ 1 (fun _ : ℝ => Tomabechi.Examples.Theorem27Op.e1) := contDiff_const
    exact hc.contDiffOn.absolutelyContinuousOnInterval
  have hfirst : AbsolutelyContinuousOnInterval
      (fun u => r u • Tomabechi.Examples.Theorem27Op.e0) T s := hr.smul he0
  have hsecond : AbsolutelyContinuousOnInterval
      (fun u => p u • Tomabechi.Examples.Theorem27Op.e1) T s := hp.smul he1
  have hsum : AbsolutelyContinuousOnInterval
      (fun u => r u • Tomabechi.Examples.Theorem27Op.e0 +
        p u • Tomabechi.Examples.Theorem27Op.e1) T s := hfirst.add hsecond
  change AbsolutelyContinuousOnInterval
    (fun u => r u • Tomabechi.Examples.Theorem27Op.e0 +
      p u • Tomabechi.Examples.Theorem27Op.e1) T s
  exact hsum

/-- 任意有界可測ゲインのベクトル軌道は、再始動時刻で同じ軌道に接続する。 -/
theorem measurableGainVectorOrbit_restart (r0 φ0 T u s : ℝ)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) :
    measurableGainVectorOrbit
      (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T u)
      (φ0 + (3 / 2 : ℝ) * (u - T)) u s k =
      measurableGainVectorOrbit r0 φ0 T s k := by
  simp only [measurableGainVectorOrbit]
  rw [Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_restart]
  congr 1
  ring

/-- 任意の有限区間でベクトル軌道は絶対連続。始点で再始動した表式に置き換える。 -/
theorem measurableGainVectorOrbit_ac_all (r0 φ0 T a b : ℝ)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) :
    AbsolutelyContinuousOnInterval (fun u => measurableGainVectorOrbit r0 φ0 T u k) a b := by
  by_cases hab : a ≤ b
  · let ra := Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T a
    let pa := φ0 + (3 / 2 : ℝ) * (a - T)
    have hbase : AbsolutelyContinuousOnInterval
        (fun u => measurableGainVectorOrbit ra pa a u k) a b :=
      measurableGainVectorOrbit_absolutelyContinuousOnInterval ra pa a b k hab
    have heq : Set.EqOn (fun u => measurableGainVectorOrbit ra pa a u k)
        (fun u => measurableGainVectorOrbit r0 φ0 T u k) (Set.uIcc a b) := by
      intro u _
      simpa [ra, pa] using measurableGainVectorOrbit_restart r0 φ0 T a u k
    exact hbase.congr heq
  · have hba : b ≤ a := le_of_not_ge hab
    let rb := Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T b
    let pb := φ0 + (3 / 2 : ℝ) * (b - T)
    have hbase : AbsolutelyContinuousOnInterval
        (fun u => measurableGainVectorOrbit rb pb b u k) b a :=
      measurableGainVectorOrbit_absolutelyContinuousOnInterval rb pb b a k hba
    have heq : Set.EqOn (fun u => measurableGainVectorOrbit rb pb b u k)
        (fun u => measurableGainVectorOrbit r0 φ0 T u k) (Set.uIcc b a) := by
      intro u _
      simpa [rb, pb] using measurableGainVectorOrbit_restart r0 φ0 T b u k
    exact (hbase.congr heq).symm

/-- 有界可測ゲイン軌道は、ベクトル自然ドリフトと指定入力からなるODEをa.e.満たす。 -/
theorem measurableGainVectorOrbit_ae_ode (r0 φ0 T : ℝ)
    (k : Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal) :
    ∀ᵐ s : ℝ, HasDerivAt (fun u => measurableGainVectorOrbit r0 φ0 T u k)
      (vec (-((1 / 2) *
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T s)) 0 +
        measurableGainInput k s
          (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T s)) s := by
  have hrad := Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_ae_ode
    r0 k T
  filter_upwards [hrad] with s hs
  let r := fun u => Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit r0 k T u
  let p := fun u : ℝ => φ0 + (3 / 2 : ℝ) * (u - T)
  have hp : HasDerivAt p (3 / 2 : ℝ) s := by
    have h := (((hasDerivAt_id s).sub_const T).const_mul (3 / 2 : ℝ)).const_add φ0
    simpa [p, mul_comm] using h
  have hvec : HasDerivAt (fun u => r u • Tomabechi.Examples.Theorem27Op.e0 +
      p u • Tomabechi.Examples.Theorem27Op.e1)
      ((-(1 / 2 + k.1 s) * r s) • Tomabechi.Examples.Theorem27Op.e0 +
        (3 / 2 : ℝ) • Tomabechi.Examples.Theorem27Op.e1) s := by
    have hr' : HasDerivAt r (-(1 / 2 + k.1 s) * r s) s := by
      simpa [r] using hs
    convert (hr'.smul_const Tomabechi.Examples.Theorem27Op.e0).add
      (hp.smul_const Tomabechi.Examples.Theorem27Op.e1) using 1 <;> rfl
  have heq : (-(1 / 2 + k.1 s) * r s) • Tomabechi.Examples.Theorem27Op.e0 +
      (3 / 2 : ℝ) • Tomabechi.Examples.Theorem27Op.e1 =
      vec (-((1 / 2) * r s)) 0 + measurableGainInput k s (r s) := by
    ext i
    fin_cases i <;> simp [measurableGainInput, vec,
      Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1] <;> ring
  have hpath : (fun u => measurableGainVectorOrbit r0 φ0 T u k) =
      (fun u => r u • Tomabechi.Examples.Theorem27Op.e0 +
        p u • Tomabechi.Examples.Theorem27Op.e1) := by
    funext u
    rfl
  rw [hpath]
  exact hvec.congr_deriv heq

/-- 最大ゲインのベクトル軌道はOperationalの実軌道に座標ごとに一致する。 -/
theorem maximal_measurable_vector_orbit_eq_operational (r0 φ0 T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    measurableGainVectorOrbit r0 φ0 T s
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain =
    Tomabechi.Examples.Theorem27Op.flowE
      (r0 • Tomabechi.Examples.Theorem27Op.e0 + φ0 • Tomabechi.Examples.Theorem27Op.e1) T s := by
  ext i
  fin_cases i
  · simp [measurableGainVectorOrbit, vec, Tomabechi.Examples.Theorem27Op.flowE,
      Tomabechi.Examples.Theorem27Op.e0, Tomabechi.Examples.Theorem27Op.e1,
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain_orbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.orbit,
      Tomabechi.Examples.Theorem26_27ControlClasses.rate,
      Tomabechi.Theorem24_26_Model.flow]
    congr 1 <;> norm_num <;> ring
  · simp [measurableGainVectorOrbit, vec, Tomabechi.Examples.Theorem27Op.flowE_1,
      Tomabechi.Examples.Theorem27Op.omg, Tomabechi.Examples.Theorem27Op.e0,
      Tomabechi.Examples.Theorem27Op.e1]

/-- 持ち上げた 2 層モデルの指定された最適フィードバックは、将来半直線の全体で Operational のベクトル流に点ごとに従う。 -/
theorem vectorSourceOptimalTrajectory_eq_flowE
    (x : Tomabechi.Examples.Theorem27Op.E2) (T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    vectorSourceTrajectory true (vectorSourceOptimalPolicy true x T) x T s =
      Tomabechi.Examples.Theorem27Op.flowE x T s := by
  ext i
  fin_cases i
  · simpa [Tomabechi.Examples.Theorem27Op.flowE_0] using
      vectorMaximalTrajectory_radial_eq_flow x T s hT hTs
  · simp [vectorSourceTrajectory, measurableGainVectorOrbit,
      vectorSourceOptimalPolicy,
      Tomabechi.Examples.Theorem27Op.flowE_1,
      Tomabechi.Examples.Theorem27Op.omg,
      Tomabechi.Examples.Theorem27Op.e0_apply1,
      Tomabechi.Examples.Theorem27Op.e1_apply1]

local instance vectorTopBorelProduct :
    BorelSpace (Set.Ici (0 : ℝ) × VectorSourceState true) := by
  change BorelSpace (Set.Ici (0 : ℝ) × Tomabechi.Examples.Theorem27Op.E2)
  infer_instance

theorem vectorSourceTarget_eq_ring (T : ℝ) :
    Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceData.optimalValue true) T =
        Tomabechi.Examples.Theorem27Op.ringE T := by
  change Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceOptimalValue true) T = Tomabechi.Examples.Theorem27Op.ringE T
  rw [Tomabechi.Examples.Theorem27Op.ringE_eq]
  ext x
  simp [Tomabechi.Theorem24_26.theorem26ZeroValueTarget,
    vectorSourceOptimalValue]

theorem vectorSourceDataTrajectory_eq_flowE
    (x : Tomabechi.Examples.Theorem27Op.E2) (T s : ℝ)
    (hT : 0 ≤ T) (hTs : T ≤ s) :
    vectorSourceData.trajectory true vectorMaximalPolicy x T s =
      Tomabechi.Examples.Theorem27Op.flowE x T s := by
  change vectorSourceTrajectory true vectorMaximalPolicy x T s = _
  have h := vectorSourceOptimalTrajectory_eq_flowE x T s hT hTs
  simpa [vectorMaximalPolicy, vectorSourceOptimalPolicy] using h

/-- 持ち上げた最適軌道上の状態から作る参照入力。 -/
noncomputable def vectorSourceReferenceInput
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ) :
    Tomabechi.Examples.Theorem27Op.E2 :=
  measurableGainReferenceInput
    ((vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) 0)

theorem vectorSourceReferenceInput_eq_operational
    (x : Tomabechi.Examples.Theorem27Op.E2) (T t : ℝ)
    (hT : 0 ≤ T) (hTt : T ≤ t) :
    vectorSourceReferenceInput x T t = Tomabechi.Examples.Theorem27Op.utrE x T t := by
  unfold vectorSourceReferenceInput
  change measurableGainReferenceInput
      ((vectorSourceTrajectory true vectorMaximalPolicy x T t) 0) = _
  have hpath : vectorSourceTrajectory true vectorMaximalPolicy x T t =
      Tomabechi.Examples.Theorem27Op.flowE x T t := by
    simpa [vectorMaximalPolicy, vectorSourceOptimalPolicy] using
      vectorSourceOptimalTrajectory_eq_flowE x T t hT hTt
  rw [hpath]
  exact measurable_reference_input_eq_operational x T t

theorem vectorSourceTargetTop_eq_ring (T : ℝ) :
    Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceData.optimalValue
        (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction)) T =
      Tomabechi.Examples.Theorem27Op.ringE T := by
  change Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceOptimalValue true) T = Tomabechi.Examples.Theorem27Op.ringE T
  exact vectorSourceTarget_eq_ring T

/-- 持ち上げたデータが定理26の力学インターフェースを満たすことを示す。
選ぶフィードバックは最大可測ゲインで、その二次元軌道は27-Aで使う
Operationalの流れと一致する。 -/
noncomputable def vectorSourceDynamics :
    Tomabechi.Theorem24_26.Theorem26NonnegativeTimeDynamics
      vectorSourceData Tomabechi.Examples.Theorem27Op.E2 where
  policyEquiv := Equiv.refl _
  feedback := vectorMaximalPolicy
  alive := Set.univ
  feedback_attains_optimum := by
    intro x T hT hx
    have hAdm := vectorSourceData.optimal_policy_admissible true x T hT
    have hInt := vectorSourceData.optimal_cost_integrable true x T hT
    have hVal := vectorSourceData.optimal_value_attained true x T hT
    exact ⟨by simpa [vectorSourceData, vectorSourceOptimalPolicy, vectorMaximalPolicy] using hAdm,
      by simpa [vectorSourceData, vectorSourceOptimalPolicy, vectorMaximalPolicy] using hInt,
      by simpa [vectorSourceData, vectorSourceOptimalPolicy, vectorMaximalPolicy] using hVal⟩
  W := Tomabechi.Examples.Theorem27Op.W3
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
    change (Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceData.optimalValue true) T).Nonempty
    rw [vectorSourceTarget_eq_ring, Tomabechi.Examples.Theorem27Op.ringE_eq]
    exact ⟨0, by simp⟩
  target_closed := by
    intro T hT
    change IsClosed (Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
      (vectorSourceData.optimalValue true) T)
    rw [vectorSourceTarget_eq_ring]
    exact Tomabechi.Examples.Theorem27Op.ringE_closed T
  target_invariant := by
    intro x T s hT hmem hTs
    change x ∈ Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (vectorSourceData.optimalValue true) T at hmem
    change vectorSourceData.trajectory true vectorMaximalPolicy x T s ∈
      Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (vectorSourceData.optimalValue true) s
    rw [vectorSourceTarget_eq_ring, Tomabechi.Examples.Theorem27Op.ringE_eq] at hmem ⊢
    have hx0 : x 0 = 0 := hmem
    rw [vectorSourceDataTrajectory_eq_flowE x T s hT hTs]
    change (Tomabechi.Examples.Theorem27Op.flowE x T s) 0 = 0
    rw [Tomabechi.Examples.Theorem27Op.flowE_0]
    simp [Tomabechi.Theorem24_26_Model.flow, hx0]
  W_absolutelyContinuous := by
    intro x T s hT hx hTs
    change AbsolutelyContinuousOnInterval
      (fun u => Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceTrajectory true vectorMaximalPolicy x T u) u) T s
    have hac := Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_absolutelyContinuousOnInterval
      (x 0) (selectedMeasurableVectorGain vectorMaximalPolicy) T s hTs
    have hsq := hac.mul hac
    have hEq : (fun u => Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceTrajectory true vectorMaximalPolicy x T u) u) =
          (fun u => Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0)
              (selectedMeasurableVectorGain vectorMaximalPolicy) T u) *
            (fun u => Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0)
              (selectedMeasurableVectorGain vectorMaximalPolicy) T u) := by
      funext u
      simp [vectorSourceTrajectory, Tomabechi.Examples.Theorem27Op.W3,
        Tomabechi.Theorem24_26_Model.lyapunov, measurableGainVectorOrbit,
        Tomabechi.Examples.Theorem27Op.e0_apply0,
        Tomabechi.Examples.Theorem27Op.e1_apply0] <;> ring
    rw [hEq]
    exact hsq
  W_nonnegative := by
    intro x T s hT hx hTs
    change 0 ≤ ((vectorSourceData.trajectory true vectorMaximalPolicy x T s) 0) ^ 2
    exact sq_nonneg _
  W_rightSlope := by
    intro x T u hT hx hTu
    change Tomabechi.Theorem1.RightSlopeBound
      (fun s => Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceData.trajectory true vectorMaximalPolicy x T s) s) u
      (-2 * Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceData.trajectory true vectorMaximalPolicy x T u) u)
    have hfun : (fun s => Tomabechi.Examples.Theorem27Op.W3
        (Tomabechi.Examples.Theorem27Op.flowE x T s) s) =
          Tomabechi.Theorem24_26_Model.WAlong (x 0) T :=
      Tomabechi.Examples.Theorem27Op.W3_along x T
    have hderRaw := Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
      (Tomabechi.Theorem24_26_Model.WAlong (x 0) T) u
      (-2 * Tomabechi.Theorem24_26_Model.WAlong (x 0) T u)
      (-2 * Tomabechi.Theorem24_26_Model.WAlong (x 0) T u)
      (Tomabechi.Theorem24_26_Model.WAlong_hasDerivAt (x 0) T u) le_rfl
    have hpath : ∀ s, T ≤ s → vectorSourceData.trajectory true
        vectorMaximalPolicy x T s = Tomabechi.Examples.Theorem27Op.flowE x T s := by
      intro s hs
      exact vectorSourceDataTrajectory_eq_flowE x T s hT hs
    have hu : Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceData.trajectory true vectorMaximalPolicy x T u) u =
          Tomabechi.Theorem24_26_Model.WAlong (x 0) T u := by
      rw [hpath u hTu]
      exact congrFun hfun u
    have hder : Tomabechi.Theorem1.RightSlopeBound
        (Tomabechi.Theorem24_26_Model.WAlong (x 0) T) u
        (-2 * Tomabechi.Examples.Theorem27Op.W3
          (vectorSourceData.trajectory true vectorMaximalPolicy x T u) u) := by
      apply Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le
        (Tomabechi.Theorem24_26_Model.WAlong (x 0) T) u
        (-2 * Tomabechi.Theorem24_26_Model.WAlong (x 0) T u)
      · exact Tomabechi.Theorem24_26_Model.WAlong_hasDerivAt (x 0) T u
      · rw [hu]
    intro r hr
    filter_upwards [hder r hr, self_mem_nhdsWithin] with z hz hzu
    have hzT : T ≤ z := le_trans hTu hzu.le
    have hzFlow : (z - u)⁻¹ *
        (Tomabechi.Examples.Theorem27Op.W3
          (Tomabechi.Examples.Theorem27Op.flowE x T z) z -
         Tomabechi.Examples.Theorem27Op.W3
          (Tomabechi.Examples.Theorem27Op.flowE x T u) u) < r := by
      simpa only [← hfun] using hz
    simpa only [hpath z hzT, hpath u hTu] using hzFlow
  W_lower_distance_bound := by
    intro x T s hT hx hTs
    change 1 * Metric.infDist
        (vectorSourceData.trajectory true vectorMaximalPolicy x T s)
        (Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (vectorSourceData.optimalValue
            true) s) ^ 2 ≤
      Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceData.trajectory true vectorMaximalPolicy x T s) s
    rw [vectorSourceTarget_eq_ring s,
      vectorSourceDataTrajectory_eq_flowE x T s hT hTs]
    change 1 * Metric.infDist (Tomabechi.Examples.Theorem27Op.flowE x T s)
      (Tomabechi.Examples.Theorem27Op.ringE s) ^ 2 ≤
        Tomabechi.Examples.Theorem27Op.W3
          (Tomabechi.Examples.Theorem27Op.flowE x T s) s
    rw [Tomabechi.Examples.Theorem27Op.infDist_ringE_sq]
    simp [Tomabechi.Examples.Theorem27Op.W3,
      Tomabechi.Theorem24_26_Model.lyapunov]
  W_upper_distance_bound := by
    intro x T s hT hx hTs
    change Tomabechi.Examples.Theorem27Op.W3
        (vectorSourceData.trajectory true vectorMaximalPolicy x T s) s ≤
      1 * Metric.infDist
        (vectorSourceData.trajectory true vectorMaximalPolicy x T s)
        (Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
        (vectorSourceData.optimalValue
            true) s) ^ 2
    rw [vectorSourceTarget_eq_ring s,
      vectorSourceDataTrajectory_eq_flowE x T s hT hTs]
    change Tomabechi.Examples.Theorem27Op.W3
        (Tomabechi.Examples.Theorem27Op.flowE x T s) s ≤
      1 * Metric.infDist (Tomabechi.Examples.Theorem27Op.flowE x T s)
        (Tomabechi.Examples.Theorem27Op.ringE s) ^ 2
    rw [Tomabechi.Examples.Theorem27Op.infDist_ringE_sq]
    simp [Tomabechi.Examples.Theorem27Op.W3,
      Tomabechi.Theorem24_26_Model.lyapunov]
  ω_continuous := by fun_prop
  ω_zero := by norm_num
  ω_nonnegative := by intro r hr; positivity
  ω_monotone_on_nonnegative := by
    intro r₁ r₂ hr₁ hr₁₂
    nlinarith [sq_nonneg (r₂ - r₁)]
  value_distance_bound := by
    intro y t ht hy
    change 0 ≤ vectorSourceData.optimalValue
        (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction) y t ∧
      vectorSourceData.optimalValue
        (⊤ : Tomabechi.Theorem24_26_Model.SourceAbstraction) y t ≤
        (Metric.infDist y (Tomabechi.Theorem24_26.theorem26ZeroValueTarget Set.univ
          (vectorSourceData.optimalValue
            true) t)) ^ 2
    rw [vectorSourceTarget_eq_ring t,
      Tomabechi.Examples.Theorem27Op.infDist_ringE_sq]
    change 0 ≤ (y 0) ^ 2 ∧ (y 0) ^ 2 ≤ (y 0) ^ 2
    exact ⟨sq_nonneg _, le_rfl⟩

/-- 持ち上げた最適化データと力学から、定理27の一般カーネルを適用した結論を得る。
ドリフト、指定入力、参照入力はいずれも実際のベクトル軌道上で結び付ける。 -/
noncomputable def vectorSourceData_theorem27_kernel
    (x : Tomabechi.Examples.Theorem27Op.E2) (T : ℝ) (hT : 0 ≤ T) := by
  let k := selectedMeasurableVectorGain vectorMaximalPolicy
  have hraw := measurableGainVectorOrbit_ae_ode (x 0) (x 1) T k
  have hODE : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasDerivAt (fun s => vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T s)
        (Tomabechi.Examples.Theorem27Op.driftE x T t +
          Tomabechi.Examples.Theorem27Op.GE (Tomabechi.Examples.Theorem27Op.u0E x T t)) t := by
    rw [Tomabechi.Theorem24_26.futureLebesgueMeasure,
      MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [hraw] with t hraw ht
    have hgain0 := selectedMeasurableVectorGain_eq_witness_future vectorMaximalPolicy
      Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain
      (fun _ => rfl) t (le_trans hT (Set.mem_Ici.mp ht))
    have hgain : k.1 t =
        Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain.1 t := by
      change (selectedMeasurableVectorGain vectorMaximalPolicy).1 t = _
      exact hgain0
    have htraj := vectorSourceDataTrajectory_eq_flowE x T t hT (Set.mem_Ici.mp ht)
    have hradius := vectorSourceTrajectory_radial vectorMaximalPolicy x T t
    have htraj' : vectorSourceTrajectory true vectorMaximalPolicy x T t =
        Tomabechi.Examples.Theorem27Op.flowE x T t := by
      simpa [vectorSourceData] using htraj
    have hradiusFlow :
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit
          (x 0) (selectedMeasurableVectorGain vectorMaximalPolicy) T t =
          Tomabechi.Examples.Theorem27Op.flowE x T t 0 := by
      calc
        _ = (vectorSourceTrajectory true vectorMaximalPolicy x T t) 0 := hradius.symm
        _ = Tomabechi.Examples.Theorem27Op.flowE x T t 0 := congrArg (fun y => y 0) htraj'
    have hinput : measurableGainInput (selectedMeasurableVectorGain vectorMaximalPolicy) t
        (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit
          (x 0) (selectedMeasurableVectorGain vectorMaximalPolicy) T t) =
          Tomabechi.Examples.Theorem27Op.u0E x T t := by
      simp only [measurableGainInput, hgain0]
      rw [← maximal_measurable_input_eq_u0E x T t]
      congr 1
      rw [hradiusFlow]
    have hdrift : vec (-((1 / 2 : ℝ) *
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0) k T t)) 0 =
          Tomabechi.Examples.Theorem27Op.driftE x T t := by
      rw [← hradius, htraj']
      ext i
      fin_cases i <;> simp [vec, Tomabechi.Examples.Theorem27Op.driftE,
        Tomabechi.Examples.Theorem27Op.flowE_0,
        Tomabechi.Examples.Theorem27Op.mu,
        Tomabechi.Examples.Theorem27Op.e0,
        Tomabechi.Examples.Theorem27Op.e1] <;> ring
    have heq : vec (-((1 / 2 : ℝ) *
        Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0) k T t)) 0 +
          measurableGainInput (selectedMeasurableVectorGain vectorMaximalPolicy) t
            (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0) k T t) =
        Tomabechi.Examples.Theorem27Op.driftE x T t +
          Tomabechi.Examples.Theorem27Op.GE (Tomabechi.Examples.Theorem27Op.u0E x T t) := by
      rw [hdrift, hinput]
      rfl
    have hpathDeriv : HasDerivAt
        (fun s => vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T s)
        (vec (-((1 / 2 : ℝ) *
          Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0) k T t)) 0 +
            measurableGainInput k t
              (Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit (x 0) k T t)) t := by
      change HasDerivAt (fun s => vectorSourceTrajectory true vectorMaximalPolicy x T s) _ t
      simpa [vectorSourceTrajectory, measurableGainVectorOrbit, k] using hraw
    exact hpathDeriv.congr_deriv heq
  have hODEdirect : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasDerivAt (fun s => vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T s)
        (measurableGainNaturalDrift
          (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) +
          Tomabechi.Examples.Theorem27Op.GE (Tomabechi.Examples.Theorem27Op.u0E x T t)) t := by
    filter_upwards [hODE,
      MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t hode ht
    have hpath : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t =
        Tomabechi.Examples.Theorem27Op.flowE x T t :=
      vectorSourceDataTrajectory_eq_flowE x T t hT (Set.mem_Ici.mp ht)
    have hdrift : measurableGainNaturalDrift
        (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) =
          Tomabechi.Examples.Theorem27Op.driftE x T t := by
      rw [hpath]
      exact measurableGainNaturalDrift_eq_operational x T t
    rw [← hdrift] at hode
    exact hode
  have hStateGrad : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      ∀ z, (Tomabechi.Examples.Theorem27Op.dWE x T t) (0, z) =
        inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t) z :=
    Filter.Eventually.of_forall fun t z =>
      Tomabechi.Examples.Theorem27Op.stateGrad x T t z
  have hReference : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      (Tomabechi.Examples.Theorem27Op.dWE x T t) (1, 0) +
        inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.driftE x T t +
            Tomabechi.Examples.Theorem27Op.GE
              (Tomabechi.Examples.Theorem27Op.utrE x T t)) = 0 :=
    Filter.Eventually.of_forall fun t =>
      Tomabechi.Examples.Theorem27Op.reference_cancellation x T t
  have hReferenceOnVectorPath : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      (Tomabechi.Examples.Theorem27Op.dWE x T t) (1, 0) +
        inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (measurableGainNaturalDrift
            (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) +
            Tomabechi.Examples.Theorem27Op.GE (vectorSourceReferenceInput x T t)) = 0 := by
    filter_upwards [hReference,
      MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t href ht
    have hpath : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t =
        Tomabechi.Examples.Theorem27Op.flowE x T t :=
      vectorSourceDataTrajectory_eq_flowE x T t hT (Set.mem_Ici.mp ht)
    have hdrift := measurableGainNaturalDrift_eq_operational x T t
    have hreference := vectorSourceReferenceInput_eq_operational x T t hT
      (Set.mem_Ici.mp ht)
    rw [hpath, hreference, hdrift]
    exact href
  have hW : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      HasFDerivAt (fun p : ℝ × Tomabechi.Examples.Theorem27Op.E2 =>
        vectorSourceDynamics.W p.2 p.1)
        (Tomabechi.Examples.Theorem27Op.dWE x T t)
        (t, vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t ht
    change HasFDerivAt (fun p : ℝ × Tomabechi.Examples.Theorem27Op.E2 =>
      Tomabechi.Examples.Theorem27Op.W3 p.2 p.1)
      (Tomabechi.Examples.Theorem27Op.dWE x T t)
      (t, vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t)
    have hpath : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t =
        Tomabechi.Examples.Theorem27Op.flowE x T t := by
      change vectorSourceTrajectory true vectorMaximalPolicy x T t = _
      exact vectorSourceOptimalTrajectory_eq_flowE x T t hT (Set.mem_Ici.mp ht)
    rw [hpath]
    exact Tomabechi.Examples.Theorem27Op.hasFDerivAt_W x T t
  have hAdjoint : ∀ᵐ t ∂Tomabechi.Theorem24_26.futureLebesgueMeasure T,
      (¬ Tomabechi.Theorem24_26.FeedbackPZS
        (vectorSourceData.admissible (⊤ : _))
        Tomabechi.Theorem24_26.futureLebesgueMeasure
        (fun π y a s => vectorSourceData.runningCost (⊤ : _) π
          (vectorSourceData.trajectory (⊤ : _) π y a s) s)
        (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t) t) →
      ∀ v : Tomabechi.Examples.Theorem27Op.E2,
        |inner ℝ (Tomabechi.Examples.Theorem27Op.gradWE x T t)
          (Tomabechi.Examples.Theorem27Op.GE v)| ≤ (2 * |x 0| + 1) * ‖v‖ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Ici : MeasurableSet (Set.Ici T))] with t ht _ v
    rw [show Tomabechi.Examples.Theorem27Op.GE v = v from rfl,
      Tomabechi.Examples.Theorem27Op.inner_gradWE]
    have hr : |Tomabechi.Theorem24_26_Model.flow (x 0) T t| ≤ |x 0| := by
      unfold Tomabechi.Theorem24_26_Model.flow
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (T - t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact sub_nonpos.2 ht
      nlinarith [abs_nonneg (x 0)]
    have hv : |v 0| ≤ ‖v‖ := by
      have h := PiLp.norm_apply_le v 0
      simpa [Real.norm_eq_abs] using h
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg (v 0), abs_nonneg (Tomabechi.Theorem24_26_Model.flow (x 0) T t),
      norm_nonneg v, mul_le_mul hr hv (abs_nonneg _) (abs_nonneg _)]
  have hKernel := Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae
    (A := Tomabechi.Theorem24_26_Model.SourceAbstraction)
    (State := VectorSourceState) (Feedback := VectorSourcePolicy)
    (Control := Tomabechi.Examples.Theorem27Op.E2) rfl rfl
    vectorSourceData vectorSourceDynamics x T hT (Set.mem_univ x)
    (fun y a s t ha has hst hadm => by
      change vectorSourceData.trajectory true vectorMaximalPolicy
          (vectorSourceData.trajectory true vectorMaximalPolicy y a s) s t =
        vectorSourceData.trajectory true vectorMaximalPolicy y a t
      rw [vectorSourceDataTrajectory_eq_flowE y a s ha has,
        vectorSourceDataTrajectory_eq_flowE
          (Tomabechi.Examples.Theorem27Op.flowE y a s) s t (le_trans ha has) hst,
        vectorSourceDataTrajectory_eq_flowE y a t ha (le_trans has hst)]
      exact Tomabechi.Examples.Theorem27Op.flowE_semigroup y a s t)
    (fun t => Tomabechi.Examples.Theorem27Op.dWE x T t)
    (fun t => Tomabechi.Examples.Theorem27Op.gradWE x T t)
    (fun t => measurableGainNaturalDrift
      (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t))
    (fun t => Tomabechi.Examples.Theorem27Op.u0E x T t)
    (fun t => vectorSourceReferenceInput x T t)
    (fun _ => Tomabechi.Examples.Theorem27Op.GE)
    hODEdirect hStateGrad hReferenceOnVectorPath
    (by
      intro t ht
      obtain ⟨K, U, hU, hLip⟩ := Tomabechi.Examples.Theorem27Op.locallyLipschitz_W x T ht
      refine ⟨K, U ∩ Set.Ici T, Filter.inter_mem hU self_mem_nhdsWithin, ?_⟩
      intro a ha b hb
      change edist
        (Tomabechi.Examples.Theorem27Op.W3
          (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T a) a)
        (Tomabechi.Examples.Theorem27Op.W3
          (vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T b) b) ≤
          (↑K : ENNReal) * edist a b
      have hpathA : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T a =
          Tomabechi.Examples.Theorem27Op.flowE x T a := by
        change vectorSourceTrajectory true vectorMaximalPolicy x T a = _
        exact vectorSourceOptimalTrajectory_eq_flowE x T a hT ha.2
      have hpathB : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T b =
          Tomabechi.Examples.Theorem27Op.flowE x T b := by
        change vectorSourceTrajectory true vectorMaximalPolicy x T b = _
        exact vectorSourceOptimalTrajectory_eq_flowE x T b hT hb.2
      rw [hpathA, hpathB]
      exact hLip ha.1 hb.1)
    hW
    (fun t htt => by
      have hpath : vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t =
          Tomabechi.Examples.Theorem27Op.flowE x T t := by
        change vectorSourceTrajectory true vectorMaximalPolicy x T t = _
        exact vectorSourceOptimalTrajectory_eq_flowE x T t hT htt
      change Tomabechi.Examples.Theorem27Op.u0E x T t =
        vectorMaximalPolicy.action ⟨⟨t, hT.trans htt⟩,
          vectorSourceData.trajectory (⊤ : _) vectorMaximalPolicy x T t⟩
      rw [hpath]
      calc
        _ = measurableGainInput
            Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain t
              (Tomabechi.Examples.Theorem27Op.flowE x T t 0) :=
          (maximal_measurable_input_eq_u0E x T t).symm
        _ = (measurableGainVectorPolicy
            Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain).action
              ⟨⟨t, hT.trans htt⟩, Tomabechi.Examples.Theorem27Op.flowE x T t⟩ :=
          (measurableGainVectorPolicy_action
            Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain
            ⟨t, hT.trans htt⟩ (Tomabechi.Examples.Theorem27Op.flowE x T t)).symm)
    (2 * |x 0| + 1) (by positivity) hAdjoint
  exact hKernel

end Tomabechi.Examples.Theorem27
