import Theorem1
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# 定理20：象徴臨場感による指定LUB方向への条件付き核

指定LUB `uσ = ⨆ Wσ` は束の最大元と同一視しない。ここでは原文 (20.A/B)
の微分計算をスカラー化した核を置く。基礎地形・臨場感の交差項を `a`、
計量勾配ノルム二乗を `g²` とすると、(20.A) は `a ≤ b g²`、(20.B) の
寄与は `symbolTerm ≤ -(b+c)g²` である。これらから (20.1) の厳密下降を得る。
PL条件からの微分不等式も示すが、一般の軌道に沿う指数評価 (20.2) は別の
微分不等式から指数重み付き関数の単調性を経て形式化する。距離誤差境界
から距離の指数評価も得る。ベクトル場から各仮定を導くモデル構成は別課題。
-/

namespace Tomabechi.Theorem20

open Filter
open scoped Gradient Topology

/-- 空間上で勾配を持つスカラー関数を微分可能な状態軌道に沿って評価した
ときの連鎖律。これにより、`Ḋ=⟪∇D,ẋ⟫` を別の数理仮定にせず導ける。 -/
theorem distance_derivative_along_gradient_path
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : E → ℝ) (x : ℝ → E) (grad velocity : E) (t : ℝ)
    (hD : HasGradientAt D grad (x t)) (hx : HasDerivAt x velocity t) :
    HasDerivAt (fun s => D (x s)) (inner ℝ grad velocity) t := by
  have hcomp := hD.hasFDerivAt.comp t hx.hasFDerivAt
  have hderiv := hcomp.hasDerivAt
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply] using hderiv

/-- 積と合成の微分則から、実効ポテンシャル
`V₀ - κq P s(D)` の勾配を構成する。`s′(D)` は指定点での導関数である。 -/
theorem effective_potential_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V₀ P D : E → ℝ) (s : ℝ → ℝ) (x gradV gradP gradD : E)
    (sDeriv κq : ℝ)
    (hV : HasGradientAt V₀ gradV x)
    (hP : HasGradientAt P gradP x)
    (hD : HasGradientAt D gradD x)
    (hs : HasDerivAt s sDeriv (D x)) :
    HasGradientAt (fun y => V₀ y - κq * (P y * s (D y)))
      (gradV - κq • (s (D x) • gradP + (P x * sDeriv) • gradD)) x := by
  let S : E → ℝ := fun y => s (D y)
  have hSdiff : DifferentiableAt ℝ S x := by
    apply hs.differentiableAt.comp x
    exact hD.differentiableAt
  have hSderiv : fderiv ℝ S x = sDeriv • InnerProductSpace.toDual ℝ E gradD := by
    rw [show S = s ∘ D by rfl, fderiv_comp x hs.differentiableAt hD.differentiableAt]
    ext y
    simp [hs.hasFDerivAt.fderiv, hD.hasFDerivAt.fderiv,
      ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    ring
  have hSfd : HasFDerivAt S (InnerProductSpace.toDual ℝ E (sDeriv • gradD)) x := by
    have hbase := hSdiff.hasFDerivAt
    rw [hSdiff.hasFDerivAt.fderiv, hSderiv] at hbase
    have hdual : InnerProductSpace.toDual ℝ E (sDeriv • gradD) =
        sDeriv • InnerProductSpace.toDual ℝ E gradD := by
      ext y
      simp [InnerProductSpace.toDual_apply_apply]
    rw [hdual]
    exact hbase
  have hS : HasGradientAt S (sDeriv • gradD) x :=
    by simpa using (hasFDerivAt_iff_hasGradientAt).1 hSfd
  let R : E → ℝ := fun y => P y * S y
  have hRderiv : fderiv ℝ R x =
      InnerProductSpace.toDual ℝ E
        (S x • gradP + (P x * sDeriv) • gradD) := by
    rw [show R = P * S by rfl, fderiv_mul hP.differentiableAt hSdiff]
    ext y
    simp [hP.fderiv_apply, hS.fderiv_apply, InnerProductSpace.toDual_apply_apply,
      inner_smul_left]
    ring_nf
  have hRdiff : DifferentiableAt ℝ R x := hP.differentiableAt.mul hSdiff
  have hRfd : HasFDerivAt R
      (InnerProductSpace.toDual ℝ E (S x • gradP + (P x * sDeriv) • gradD)) x := by
    convert hRdiff.hasFDerivAt using 1
    rw [hRdiff.hasFDerivAt.fderiv, hRderiv]
  have hR : HasGradientAt R (S x • gradP + (P x * sDeriv) • gradD) x :=
    by simpa using (hasFDerivAt_iff_hasGradientAt).1 hRfd
  have hscaledfd : HasFDerivAt (fun y => κq * R y)
      (InnerProductSpace.toDual ℝ E
        (κq • (S x • gradP + (P x * sDeriv) • gradD))) x := by
    convert hRfd.const_mul κq using 1
    have hdual : InnerProductSpace.toDual ℝ E
        (κq • (S x • gradP + (P x * sDeriv) • gradD)) =
        κq • InnerProductSpace.toDual ℝ E (S x • gradP + (P x * sDeriv) • gradD) := by
      ext y
      simp [InnerProductSpace.toDual_apply_apply]
    rw [hdual]
  have hscaled : HasGradientAt (fun y => κq * R y)
      (κq • (S x • gradP + (P x * sDeriv) • gradD)) x :=
    by simpa using (hasFDerivAt_iff_hasGradientAt).1 hscaledfd
  have heffectivefd := hV.hasFDerivAt.sub hscaledfd
  have hfunction : V₀ - (fun y => κq * R y) =
      (fun y => V₀ y - κq * (P y * s (D y))) := by
    funext y
    simp [S, R]
  have hdualEffective : InnerProductSpace.toDual ℝ E
      (gradV - κq • (s (D x) • gradP + (P x * sDeriv) • gradD)) =
      InnerProductSpace.toDual ℝ E gradV -
        InnerProductSpace.toDual ℝ E
          (κq • (S x • gradP + (P x * sDeriv) • gradD)) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, S]
  have heffective : HasFDerivAt (fun y => V₀ y - κq * (P y * s (D y)))
      (InnerProductSpace.toDual ℝ E
        (gradV - κq • (s (D x) • gradP + (P x * sDeriv) • gradD))) x := by
    rw [hfunction, ← hdualEffective] at heffectivefd
    exact heffectivefd
  simpa using (hasFDerivAt_iff_hasGradientAt).1 heffective

/-- ベクトル場上での距離微分の展開。`hEffectiveGradient` は実効ポテンシャル
`V₀-κqP s(D)` の勾配に対する積・合成則を表す。仮定されたODE
`velocity=-M∇Ṽ` に代入すると、(20.A/B) に現れる項と最後の
`κqP s′‖∇D‖²_M` が正確に得られる。 -/
theorem gradient_flow_distance_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (gradD gradV gradP gradEffective : E)
    (κ q P S sDeriv : ℝ) (velocity : E)
    (hEffectiveGradient : gradEffective =
      gradV - (κ * q) • (S • gradP + (P * sDeriv) • gradD))
    (hFlow : velocity = -M gradEffective) :
    inner ℝ gradD velocity =
      -inner ℝ gradD (M gradV) + κ * q * S * inner ℝ gradD (M gradP) +
        κ * q * P * sDeriv * inner ℝ gradD (M gradD) := by
  rw [hFlow, hEffectiveGradient]
  simp only [map_sub, map_add, map_smul, inner_neg_right, inner_sub_right,
    inner_add_right, inner_smul_right]
  ring_nf

/-- 自己共役な移動度とその逆を用いると、実効勾配流の方向成分は距離の
減少率の負号に一致する。 `inner (M⁻¹ velocity) direction` は
`M⁻¹`計量内積を表す。 -/
theorem inverse_metric_direction_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M Minv : E →L[ℝ] E) (gradD gradEffective velocity direction : E)
    (hleft : ∀ x, Minv (M x) = x)
    (hsymmetric : ∀ x y, inner ℝ x (M y) = inner ℝ (M x) y)
    (hFlow : velocity = -M gradEffective)
    (hDirection : direction = -M gradD) :
    inner ℝ (Minv velocity) direction = -inner ℝ gradD velocity := by
  rw [hFlow, hDirection]
  simp only [map_neg, hleft, inner_neg_left, inner_neg_right, neg_neg]
  rw [hsymmetric gradEffective gradD]
  rw [real_inner_comm]

/-- 原文の一適用区間における方向結論 (20.1)。ここでは `hEffectiveGradient`
が実効ポテンシャルの勾配積・合成則、`hFlow` が閉ループODEを表す。
`hA` と `hB` は論文の一様条件を現在状態で評価したもの、正の `g2` は
移動度の正定値性と目標外での非零勾配に対応する。 -/
theorem theorem20_directional_conclusion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M Minv : E →L[ℝ] E) (gradD gradV gradP gradEffective velocity direction : E)
    (κ q P S sDeriv b c : ℝ)
    (hEffectiveGradient : gradEffective =
      gradV - (κ * q) • (S • gradP + (P * sDeriv) • gradD))
    (hFlow : velocity = -M gradEffective)
    (hDirection : direction = -M gradD)
    (hleft : ∀ x, Minv (M x) = x)
    (hsymmetric : ∀ x y, inner ℝ x (M y) = inner ℝ (M x) y)
    (hA : -inner ℝ gradD (M gradV) + κ * q * S * inner ℝ gradD (M gradP) ≤
      b * inner ℝ gradD (M gradD))
    (hB : κ * q * P * (-sDeriv) ≥ b + c)
    (hg2 : 0 < inner ℝ gradD (M gradD))
    (_hb : 0 < b) (hc : 0 < c) :
    inner ℝ gradD velocity ≤ -c * inner ℝ gradD (M gradD) ∧
      0 < inner ℝ (Minv velocity) direction := by
  have hderiv := gradient_flow_distance_derivative M gradD gradV gradP
    gradEffective κ q P S sDeriv velocity hEffectiveGradient hFlow
  have hsymbol : κ * q * P * sDeriv * inner ℝ gradD (M gradD) ≤
      -(b + c) * inner ℝ gradD (M gradD) := by
    have hcoeff : -(κ * q * P * (-sDeriv)) ≤ -(b + c) := neg_le_neg hB
    have hmul := mul_le_mul_of_nonneg_right hcoeff hg2.le
    calc
      κ * q * P * sDeriv * inner ℝ gradD (M gradD) =
          -(κ * q * P * (-sDeriv)) * inner ℝ gradD (M gradD) := by ring
      _ ≤ -(b + c) * inner ℝ gradD (M gradD) := hmul
  have hdecrease :
      -inner ℝ gradD (M gradV) + κ * q * S * inner ℝ gradD (M gradP) +
        κ * q * P * sDeriv * inner ℝ gradD (M gradD) ≤
          -c * inner ℝ gradD (M gradD) := by
    have := add_le_add hA hsymbol
    nlinarith
  have hbound : inner ℝ gradD velocity ≤ -c * inner ℝ gradD (M gradD) := by
    calc
      inner ℝ gradD velocity =
          -inner ℝ gradD (M gradV) + κ * q * S * inner ℝ gradD (M gradP) +
            κ * q * P * sDeriv * inner ℝ gradD (M gradD) := hderiv
      _ ≤ -c * inner ℝ gradD (M gradD) := hdecrease
  constructor
  · exact hbound
  · rw [inverse_metric_direction_identity M Minv gradD gradEffective velocity direction
      hleft hsymmetric hFlow hDirection]
    have hstrict : inner ℝ gradD velocity < 0 := by
      calc
        inner ℝ gradD velocity ≤ -c * inner ℝ gradD (M gradD) := hbound
        _ < 0 := mul_neg_of_neg_of_pos (by linarith) hg2
    linarith

/-- 原文の実効ポテンシャルを関数として与え、各項の勾配が存在するときの
方向結論。積・合成則で実効勾配を構成してから、閉ループ方程式と(20.A/B)
を適用する。 -/
theorem theorem20_directional_from_potential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M Minv : E →L[ℝ] E) (V₀ P D : E → ℝ) (s : ℝ → ℝ)
    (x gradV gradP gradD velocity direction : E)
    (κ q sDeriv b c : ℝ)
    (hV : HasGradientAt V₀ gradV x)
    (hP : HasGradientAt P gradP x)
    (hD : HasGradientAt D gradD x)
    (hs : HasDerivAt s sDeriv (D x))
    (hFlow : velocity = -M (∇ (fun y => V₀ y - κ * q * (P y * s (D y))) x))
    (hDirection : direction = -M gradD)
    (hleft : ∀ y, Minv (M y) = y)
    (hsymmetric : ∀ y z, inner ℝ y (M z) = inner ℝ (M y) z)
    (hA : -inner ℝ gradD (M gradV) + κ * q * s (D x) *
      inner ℝ gradD (M gradP) ≤ b * inner ℝ gradD (M gradD))
    (hB : κ * q * P x * (-sDeriv) ≥ b + c)
    (hg2 : 0 < inner ℝ gradD (M gradD))
    (hb : 0 < b) (hc : 0 < c) :
    inner ℝ gradD velocity ≤ -c * inner ℝ gradD (M gradD) ∧
      0 < inner ℝ (Minv velocity) direction := by
  let Veff : E → ℝ := fun y => V₀ y - κ * q * (P y * s (D y))
  have hVeff := effective_potential_hasGradientAt V₀ P D s x gradV gradP gradD
    sDeriv (κ * q) hV hP hD hs
  have hgrad := hVeff.gradient
  have hresult := theorem20_directional_conclusion M Minv gradD gradV gradP
    (∇ Veff x) velocity direction κ q (P x) (s (D x)) sDeriv b c
    (by simpa [Veff] using hgrad) (by simpa [Veff] using hFlow) hDirection
    hleft hsymmetric hA hB hg2 hb hc
  simpa [Veff] using hresult

/-- (20.A/B) の代数核。`g2` は `‖∇D‖_M²`、`baseTerm` は (20.A) 左辺、
`symbolTerm` は `κqP s′(D) g2` に当たる。 -/
theorem strict_distance_descent
    (baseTerm symbolTerm g2 b c : ℝ)
    (hA : baseTerm ≤ b * g2)
    (hB : symbolTerm ≤ -(b + c) * g2) :
    baseTerm + symbolTerm ≤ -c * g2 := by
  have hsum := add_le_add hA hB
  nlinarith

/-- PL型条件を追加すると、距離関数の軌道微分は指数評価に必要な
微分不等式 `Ḋ ≤ -2 μ c D` を満たす。 -/
theorem pl_yields_rate_differential
    (distanceDeriv g2 distance mu c : ℝ)
    (hdescent : distanceDeriv ≤ -c * g2)
    (hPL : 2 * mu * distance ≤ g2)
    (hc : 0 ≤ c) :
    distanceDeriv ≤ -(2 * mu * c) * distance := by
  have hmul := mul_le_mul_of_nonneg_left hPL hc
  nlinarith

/-- `d_u = -M∇D` と `ẋ = -M∇Ṽ` の定義から得る方向成分の符号。
原文の計量内積恒等式を、`distanceDeriv = Ḋ` として明示する。 -/
theorem positive_direction_component
    (directionComponent distanceDeriv : ℝ)
    (hidentity : directionComponent = -distanceDeriv)
    (hdescent : distanceDeriv < 0) :
    0 < directionComponent := by
  rw [hidentity]
  linarith

/-- PL境界を使ったとき、軌道上の距離微分が負となる。 -/
theorem pl_strict_descent
    (distanceDeriv g2 distance mu c : ℝ)
    (hdescent : distanceDeriv ≤ -c * g2)
    (hPL : 2 * mu * distance ≤ g2)
    (hc : 0 < c) (_hμ : 0 < mu) (hdistance : 0 < distance) :
    distanceDeriv < 0 := by
  have hrate := pl_yields_rate_differential distanceDeriv g2 distance mu c
    hdescent hPL hc.le
  have hprod : 0 < 2 * mu * c * distance := by positivity
  nlinarith

/-- C¹な非負距離関数がPL微分不等式を満たすなら、指数重みを掛けた関数は
非増加となり、原文 (20.2) の距離関数の定量評価を得る。原文のC¹仮定に
合わせ、a.e.微分ではなく各時刻での微分不等式を用いる。 -/
theorem exponential_distance_bound
    (D : ℝ → ℝ) (rate t₀ t : ℝ)
    (hD : Differentiable ℝ D)
    (hdecay : ∀ s, deriv D s ≤ -rate * D s)
    (ht : t₀ ≤ t) :
    D t ≤ D t₀ * Real.exp (-rate * (t - t₀)) := by
  let weighted : ℝ → ℝ := fun s => D s * Real.exp (rate * (s - t₀))
  have hweighted : Differentiable ℝ weighted := by
    apply Differentiable.mul hD
    fun_prop
  have hderiv : ∀ s, deriv weighted s ≤ 0 := by
    intro s
    have hformula : deriv weighted s =
        deriv D s * Real.exp (rate * (s - t₀)) +
          D s * (rate * Real.exp (rate * (s - t₀))) := by
      change deriv (D * fun z : ℝ => Real.exp (rate * (z - t₀))) s = _
      rw [deriv_mul (hD.differentiableAt) (by fun_prop)]
      rw [deriv_exp (by fun_prop)]
      have hlin : deriv (fun z : ℝ => rate * (z - t₀)) s = rate := by
        simp
      rw [hlin]
      ring_nf
    rw [hformula]
    have hexp : 0 ≤ Real.exp (rate * (s - t₀)) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right (hdecay s) hexp
    nlinarith
  have hanti := antitone_of_deriv_nonpos hweighted hderiv
  have hweighted_le := hanti ht
  have hmul := hweighted_le
  have hexp_pos : 0 < Real.exp (rate * (t - t₀)) := Real.exp_pos _
  have hrewrite : weighted t = D t * Real.exp (rate * (t - t₀)) := rfl
  have hstart : weighted t₀ = D t₀ := by simp [weighted]
  rw [hrewrite, hstart] at hmul
  have hresult := (le_div_iff₀ hexp_pos).2 hmul
  calc
    D t ≤ D t₀ * (Real.exp (rate * (t - t₀)))⁻¹ := by
      simpa only [div_eq_mul_inv] using hresult
    _ = D t₀ * Real.exp (-rate * (t - t₀)) := by
      congr 1
      rw [← Real.exp_neg]
      ring_nf

/-- Interval version of the exponential comparison lemma. It asks for
derivatives only on `[t₀,t]`, so applications need no regularity or decay
assumptions at earlier times. -/
theorem exponential_distance_bound_on_interval
    (D : ℝ → ℝ) (rate t₀ t : ℝ)
    (hD : ∀ s, s ∈ Set.Icc t₀ t → HasDerivAt D (deriv D s) s)
    (hdecay : ∀ s, s ∈ Set.Icc t₀ t → deriv D s ≤ -rate * D s)
    (ht : t₀ ≤ t) :
    D t ≤ D t₀ * Real.exp (-rate * (t - t₀)) := by
  let weighted : ℝ → ℝ := fun s => D s * Real.exp (rate * (s - t₀))
  have hDdiff : DifferentiableOn ℝ D (Set.Icc t₀ t) := by
    intro s hs
    exact (hD s hs).differentiableAt.differentiableWithinAt
  have hExpDiff : DifferentiableOn ℝ (fun s : ℝ => Real.exp (rate * (s - t₀)))
      (Set.Icc t₀ t) := by
    intro s hs
    exact (by fun_prop : DifferentiableAt ℝ
      (fun s : ℝ => Real.exp (rate * (s - t₀))) s).differentiableWithinAt
  have hweightedDiff : DifferentiableOn ℝ weighted (Set.Icc t₀ t) := by
    change DifferentiableOn ℝ (D * fun s : ℝ => Real.exp (rate * (s - t₀)))
      (Set.Icc t₀ t)
    exact hDdiff.mul hExpDiff
  have hweightedContinuous : ContinuousOn weighted (Set.Icc t₀ t) :=
    hweightedDiff.continuousOn
  have hweightedDerivative : ∀ s, s ∈ Set.Icc t₀ t → deriv weighted s ≤ 0 := by
    intro s hs
    have harg : HasDerivAt (fun z : ℝ => rate * (z - t₀)) rate s := by
      simpa [mul_comm] using (hasDerivAt_id s).sub_const t₀ |>.const_mul rate
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (rate * (z - t₀)))
        (rate * Real.exp (rate * (s - t₀))) s := by
      simpa [mul_comm] using (HasDerivAt.exp harg)
    have hmul := (hD s hs).mul hexp
    have hformula : deriv weighted s =
        deriv D s * Real.exp (rate * (s - t₀)) +
          D s * (rate * Real.exp (rate * (s - t₀))) := by
      change deriv (D * (fun z : ℝ => Real.exp (rate * (z - t₀)))) s = _
      exact hmul.deriv
    rw [hformula]
    have hmul := mul_le_mul_of_nonneg_right (hdecay s hs)
      (Real.exp_nonneg (rate * (s - t₀)))
    nlinarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc t₀ t)
    hweightedContinuous (hweightedDiff.mono interior_subset)
    (by
      intro s hs
      exact hweightedDerivative s (interior_subset hs))
  have hweightedDrop := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hmul := hweightedDrop
  have hexp_pos : 0 < Real.exp (rate * (t - t₀)) := Real.exp_pos _
  have hstart : weighted t₀ = D t₀ := by simp [weighted]
  rw [show weighted t = D t * Real.exp (rate * (t - t₀)) by rfl,
    hstart] at hmul
  have hresult := (le_div_iff₀ hexp_pos).2 hmul
  calc
    D t ≤ D t₀ * (Real.exp (rate * (t - t₀)))⁻¹ := by
      simpa only [div_eq_mul_inv] using hresult
    _ = D t₀ * Real.exp (-rate * (t - t₀)) := by
      congr 1
      rw [← Real.exp_neg]
      ring_nf

/-- 距離誤差境界 `dist ≤ C√D` を加えると、状態距離も指数率 `rate/2`
で減衰する。原文では `rate=2μc` を代入する。 -/
theorem distance_error_exponential_bound
    (D distanceToTarget : ℝ → ℝ) (C rate t₀ t : ℝ)
    (hdecay : D t ≤ D t₀ * Real.exp (-rate * (t - t₀)))
    (herror : distanceToTarget t ≤ C * Real.sqrt (D t))
    (hD₀ : 0 ≤ D t₀) (hC : 0 ≤ C) :
    distanceToTarget t ≤ C * Real.sqrt (D t₀) *
      Real.exp (-rate * (t - t₀) / 2) := by
  calc
    distanceToTarget t ≤ C * Real.sqrt (D t) := herror
    _ ≤ C * Real.sqrt (D t₀ * Real.exp (-rate * (t - t₀))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.sqrt_le_sqrt hdecay
    _ = C * Real.sqrt (D t₀) * Real.exp (-rate * (t - t₀) / 2) := by
      rw [Real.sqrt_mul hD₀, ← Real.exp_half]
      ring_nf

/-- 全適用時間でPL型条件が保たれる一つの軌道について、(20.1) と
PL境界・距離誤差境界を合成し、原文 (20.2) の指数率 `μc` を得る。
原文のコンパクト前向き不変集合は、これらの一様軌道条件を保証する場として
解釈される。 -/
theorem theorem20_exponential_conclusion
    (D distanceToTarget g2 : ℝ → ℝ) (C μ c t₀ t : ℝ)
    (hD : Differentiable ℝ D)
    (hdescent : ∀ s, deriv D s ≤ -c * g2 s)
    (hPL : ∀ s, 2 * μ * D s ≤ g2 s)
    (herror : ∀ s, distanceToTarget s ≤ C * Real.sqrt (D s))
    (hD₀ : 0 ≤ D t₀) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (ht : t₀ ≤ t) :
    D t ≤ D t₀ * Real.exp (-(2 * μ * c) * (t - t₀)) ∧
      distanceToTarget t ≤ C * Real.sqrt (D t₀) * Real.exp (-μ * c * (t - t₀)) := by
  have hrate : ∀ s, deriv D s ≤ -(2 * μ * c) * D s := by
    intro s
    exact pl_yields_rate_differential (deriv D s) (g2 s) (D s) μ c
      (hdescent s) (hPL s) hc
  have hDdecay := exponential_distance_bound D (2 * μ * c) t₀ t hD hrate ht
  have hdist := distance_error_exponential_bound D distanceToTarget C
    (2 * μ * c) t₀ t hDdecay (herror t) hD₀ hC
  refine ⟨?_, ?_⟩
  · simpa only [neg_mul, mul_assoc] using hDdecay
  · convert hdist using 1
    congr 1
    ring_nf

/-- 一様な指数距離評価と距離の非負性から、`t→∞` の極限も得る。
指数率は正であり、評価はある開始時刻以降に成立すれば十分。 -/
theorem distance_tendsto_zero_of_exponential_bound
    (distanceToTarget : ℝ → ℝ) (A rate t₀ : ℝ)
    (hbound : ∀ t, t₀ ≤ t →
      distanceToTarget t ≤ A * Real.exp (-rate * (t - t₀)))
    (hnonneg : ∀ t, 0 ≤ distanceToTarget t)
    (hrate : 0 < rate) :
    Tendsto distanceToTarget atTop (𝓝 0) := by
  have hmul : Tendsto (fun t : ℝ => -rate * t) atTop atBot := by
    apply (Filter.tendsto_const_mul_atBot_of_neg (l := atTop)
      (f := id) (r := -rate) (by linarith)).2
    exact Filter.tendsto_id
  have harg : Tendsto (fun t : ℝ => -rate * (t - t₀)) atTop atBot := by
    have hshift := Filter.tendsto_atBot_add_const_right atTop (rate * t₀) hmul
    convert hshift using 1 <;> ext t <;> ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (-rate * (t - t₀))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmajor : Tendsto (fun t : ℝ => A * Real.exp (-rate * (t - t₀)))
      atTop (𝓝 0) := by simpa using hexp.const_mul A
  apply squeeze_zero' (Filter.Eventually.of_forall hnonneg) ?_ hmajor
  filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => hbound t ht⟩]
  exact fun t ht => ht

/-- 全未来時刻の勾配非零性を置く強い十分条件版。原文の目標外条件だけを
要求する入口には `theorem20_full_trajectory_conclusion_of_original_conditions` を使う。
空間上のポテンシャル・勾配・閉ループ軌道を、(20.1) と (20.2) に
一続きに接続する条件付き定理。距離微分は勾配連鎖律から導出し、実効勾配は
積・合成則から構成する。仮定は初期時刻以後に限り、方向評価・指数評価・距離極限を返す。 -/
theorem theorem20_full_trajectory_conclusion_everywhere_strict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M Minv : ℝ → E →L[ℝ] E) (V₀ P D : E → ℝ) (s : ℝ → ℝ)
    (x velocity : ℝ → E) (Z : Set E) (g2 sDeriv : ℝ → ℝ)
    (κ q b c μ C t₀ : ℝ)
    (gradV gradP gradD : ℝ → E)
    (hV : ∀ r, t₀ ≤ r → HasGradientAt V₀ (gradV r) (x r))
    (hP : ∀ r, t₀ ≤ r → HasGradientAt P (gradP r) (x r))
    (hD : ∀ r, t₀ ≤ r → HasGradientAt D (gradD r) (x r))
    (hs : ∀ r, t₀ ≤ r → HasDerivAt s (sDeriv r) (D (x r)))
    (hPath : ∀ r, t₀ ≤ r → HasDerivAt x (velocity r) r)
    (hFlow : ∀ r, t₀ ≤ r → velocity r =
      -(M r) (∇ (fun y => V₀ y - κ * q * (P y * s (D y))) (x r)))
    (hleft : ∀ r, t₀ ≤ r → ∀ y, Minv r (M r y) = y)
    (hsymmetric : ∀ r, t₀ ≤ r → ∀ y z, inner ℝ y (M r z) = inner ℝ (M r y) z)
    (hA : ∀ r, t₀ ≤ r → -inner ℝ (gradD r) (M r (gradV r)) +
      κ * q * s (D (x r)) * inner ℝ (gradD r) (M r (gradP r)) ≤
      b * inner ℝ (gradD r) (M r (gradD r)))
    (hB : ∀ r, t₀ ≤ r → κ * q * P (x r) * (-sDeriv r) ≥ b + c)
    (hg2 : ∀ r, t₀ ≤ r → 0 < inner ℝ (gradD r) (M r (gradD r)))
    (hPL : ∀ r, t₀ ≤ r → 2 * μ * D (x r) ≤ g2 r)
    (hg2_eq : ∀ r, t₀ ≤ r → g2 r = inner ℝ (gradD r) (M r (gradD r)))
    (herror : ∀ r, t₀ ≤ r → Metric.infDist (x r) Z ≤ C * Real.sqrt (D (x r)))
    (hD₀ : 0 ≤ D (x t₀)) (hC : 0 ≤ C) (hμ : 0 < μ)
    (hb : 0 < b) (hc : 0 < c) :
    (∀ t, t₀ ≤ t →
      ((D (x t) ≤ D (x t₀) * Real.exp (-(2 * μ * c) * (t - t₀)) ∧
        Metric.infDist (x t) Z ≤ C * Real.sqrt (D (x t₀)) * Real.exp (-μ * c * (t - t₀))) ∧
        deriv (fun r => D (x r)) t ≤ -c * g2 t)) ∧
      Tendsto (fun r => Metric.infDist (x r) Z) atTop (𝓝 0) := by
  let distanceToTarget : ℝ → ℝ := fun r => Metric.infDist (x r) Z
  let Dpath : ℝ → ℝ := fun r => D (x r)
  have hDpath_deriv : ∀ r, t₀ ≤ r → HasDerivAt Dpath
      (inner ℝ (gradD r) (velocity r)) r := by
    intro r hr
    simpa [Dpath] using distance_derivative_along_gradient_path D x
      (gradD r) (velocity r) r (hD r hr) (hPath r hr)
  have hdescent : ∀ r, t₀ ≤ r → deriv Dpath r ≤ -c * g2 r := by
    intro r hr
    have hdir := theorem20_directional_from_potential (M r) (Minv r) V₀ P D s (x r)
      (gradV r) (gradP r) (gradD r) (velocity r) (-(M r) (gradD r)) κ q
      (sDeriv r) b c (hV r hr) (hP r hr) (hD r hr) (hs r hr) (hFlow r hr) rfl
      (hleft r hr) (hsymmetric r hr) (hA r hr) (hB r hr)
      (by simpa [hg2_eq r hr] using hg2 r hr) hb hc
    calc
      deriv Dpath r = inner ℝ (gradD r) (velocity r) := (hDpath_deriv r hr).deriv
      _ ≤ -c * g2 r := by simpa [hg2_eq r hr] using hdir.1
  have hrate : ∀ r, t₀ ≤ r → deriv Dpath r ≤ -(2 * μ * c) * Dpath r := by
    intro r hr
    have hPLr : 2 * μ * Dpath r ≤ g2 r := by simpa [Dpath] using hPL r hr
    have hdescentr : deriv Dpath r ≤ -c * g2 r := hdescent r hr
    have hmul := mul_le_mul_of_nonneg_left hPLr hc.le
    dsimp [Dpath]
    nlinarith
  have hDpath_regular : ∀ r, t₀ ≤ r → HasDerivAt Dpath (deriv Dpath r) r := by
    intro r hr
    have h := hDpath_deriv r hr
    convert h using 1
    exact h.deriv
  have hpointwise : ∀ t, t₀ ≤ t →
      (D (x t) ≤ D (x t₀) * Real.exp (-(2 * μ * c) * (t - t₀)) ∧
        distanceToTarget t ≤ C * Real.sqrt (D (x t₀)) * Real.exp (-μ * c * (t - t₀))) ∧
        deriv (fun r => D (x r)) t ≤ -c * g2 t := by
    intro t ht
    have hDdecay := exponential_distance_bound_on_interval Dpath (2 * μ * c) t₀ t
      (fun r hr => hDpath_regular r hr.1) (fun r hr => hrate r hr.1) ht
    have hdist := distance_error_exponential_bound Dpath distanceToTarget C
      (2 * μ * c) t₀ t (by simpa [Dpath, neg_mul, mul_assoc] using hDdecay)
      (by simpa [Dpath] using herror t ht) (by simpa [Dpath] using hD₀) hC
    constructor
    · constructor
      · simpa [Dpath, neg_mul, mul_assoc] using hDdecay
      · convert hdist using 1 <;> congr 1 <;> ring_nf
    · exact hdescent t ht
  have hlim := distance_tendsto_zero_of_exponential_bound distanceToTarget
    (C * Real.sqrt (D (x t₀))) (μ * c) t₀
    (fun τ hτ => by
      have h := (hpointwise τ hτ).1.2
      convert h using 1 <;> congr 2 <;> ring_nf)
    (fun r => Metric.infDist_nonneg)
    (mul_pos hμ hc)
  exact ⟨hpointwise, hlim⟩

/-- 非負関数の零点では、存在する勾配はゼロになる。定理20の目標上では
方向条件を仮定せず、この停留性から収支の零値を得る。 -/
theorem gradient_eq_zero_of_nonnegative_at_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : E → ℝ) (x grad : E)
    (hD : HasGradientAt D grad x)
    (hnonneg : ∀ y, 0 ≤ D y) (hzero : D x = 0) :
    grad = 0 := by
  have hmin : IsLocalMin D x := by
    filter_upwards with y
    rw [hzero]
    exact hnonneg y
  have hderiv := hmin.hasFDerivAt_eq_zero hD.hasFDerivAt
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa using hderiv

/-- 定理20の原文条件による全軌道接続。方向条件A/Bと勾配の非零性は
前向き不変集合K上の目標外にだけ課す。目標上は非負距離型関数の零点なので
勾配ゼロを導き、下降微分もゼロとする。逆計量恒等式は全時刻で、厳密下降は
目標外で返す。PL評価・距離誤差から指数率と極限を得る。 -/
theorem theorem20_full_trajectory_conclusion_of_original_conditions
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M Minv : ℝ → E →L[ℝ] E) (V₀ P D : E → ℝ) (s : ℝ → ℝ)
    (x velocity : ℝ → E) (K Z : Set E) (g2 sDeriv : ℝ → ℝ)
    (κ q b c μ C gamma t₀ : ℝ)
    (gradV gradP gradD : ℝ → E)
    (hK : ∀ r, t₀ ≤ r → x r ∈ K)
    (hV : ∀ r, t₀ ≤ r → HasGradientAt V₀ (gradV r) (x r))
    (hP : ∀ r, t₀ ≤ r → HasGradientAt P (gradP r) (x r))
    (hD : ∀ r, t₀ ≤ r → HasGradientAt D (gradD r) (x r))
    (hD_nonneg : ∀ y, 0 ≤ D y)
    (hD_zero : ∀ y, D y = 0 ↔ y ∈ Z)
    (hZ_nonempty : Z.Nonempty) (hZ_closed : IsClosed Z)
    (hs : ∀ r, t₀ ≤ r → HasDerivAt s (sDeriv r) (D (x r)))
    (hPath : ∀ r, t₀ ≤ r → HasDerivAt x (velocity r) r)
    (hFlow : ∀ r, t₀ ≤ r → velocity r =
      -(M r) (∇ (fun y => V₀ y - κ * q * (P y * s (D y))) (x r)))
    (hleft : ∀ r, t₀ ≤ r → ∀ y, Minv r (M r y) = y)
    (hsymmetric : ∀ r, t₀ ≤ r → ∀ y z, inner ℝ y (M r z) = inner ℝ (M r y) z)
    (hcoercive : ∀ r, t₀ ≤ r → ∀ y,
      gamma * ‖y‖ ^ 2 ≤ inner ℝ y (M r y))
    (hA : ∀ r, t₀ ≤ r → x r ∈ K → x r ∉ Z →
      -inner ℝ (gradD r) (M r (gradV r)) +
        κ * q * s (D (x r)) * inner ℝ (gradD r) (M r (gradP r)) ≤
          b * inner ℝ (gradD r) (M r (gradD r)))
    (hB : ∀ r, t₀ ≤ r → x r ∈ K → x r ∉ Z →
      κ * q * P (x r) * (-sDeriv r) ≥ b + c)
    (hPL : ∀ r, t₀ ≤ r → 2 * μ * D (x r) ≤ g2 r)
    (hg2_eq : ∀ r, t₀ ≤ r →
      g2 r = inner ℝ (gradD r) (M r (gradD r)))
    (herror : ∀ r, t₀ ≤ r →
      Metric.infDist (x r) Z ≤ C * Real.sqrt (D (x r)))
    (hC : 0 ≤ C) (hμ : 0 < μ) (_hq : 0 < q)
    (hb : 0 < b) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ t, t₀ ≤ t →
      D (x t) ≤ D (x t₀) * Real.exp (-(2 * μ * c) * (t - t₀)) ∧
      Metric.infDist (x t) Z ≤ C * Real.sqrt (D (x t₀)) *
        Real.exp (-μ * c * (t - t₀)) ∧
      deriv (fun r => D (x r)) t ≤ -c * g2 t ∧
      (x t ∉ Z → deriv (fun r => D (x r)) t < 0) ∧
      inner ℝ (Minv t (velocity t)) (-(M t (gradD t))) =
        -deriv (fun r => D (x r)) t) ∧
      Tendsto (fun r => Metric.infDist (x r) Z) atTop (𝓝 0) := by
  let Dpath : ℝ → ℝ := fun r => D (x r)
  let dist : ℝ → ℝ := fun r => Metric.infDist (x r) Z
  have hDpath_deriv : ∀ r, t₀ ≤ r → HasDerivAt Dpath
      (inner ℝ (gradD r) (velocity r)) r := by
    intro r hr
    simpa [Dpath] using distance_derivative_along_gradient_path D x
      (gradD r) (velocity r) r (hD r hr) (hPath r hr)
  have hidentity : ∀ r, t₀ ≤ r →
      inner ℝ (Minv r (velocity r)) (-(M r (gradD r))) = -deriv Dpath r := by
    intro r hr
    rw [inverse_metric_direction_identity (M r) (Minv r) (gradD r)
      (∇ (fun y => V₀ y - κ * q * (P y * s (D y))) (x r))
      (velocity r) (-(M r (gradD r))) (hleft r hr) (hsymmetric r hr)
      (hFlow r hr) rfl]
    rw [(hDpath_deriv r hr).deriv]
  have hdescent : ∀ r, t₀ ≤ r → deriv Dpath r ≤ -c * g2 r := by
    intro r hr
    by_cases htarget : x r ∈ Z
    · have hDzero : D (x r) = 0 := (hD_zero (x r)).2 htarget
      have hgrad := gradient_eq_zero_of_nonnegative_at_zero D (x r) (gradD r)
        (hD r hr) hD_nonneg hDzero
      have hgzero : g2 r = 0 := by simp [hg2_eq r hr, hgrad]
      have hderivzero : deriv Dpath r = 0 := by
        rw [(hDpath_deriv r hr).deriv]
        simp [hgrad]
      rw [hderivzero, hgzero]
      simp
    · have hgradne : gradD r ≠ 0 := by
        intro heq
        apply htarget
        apply (hD_zero (x r)).1
        have hpl := hPL r hr
        have hgzero : g2 r = 0 := by rw [hg2_eq r hr, heq]; simp
        rw [hgzero] at hpl
        nlinarith [hD_nonneg (x r)]
      have hgpositive : 0 < inner ℝ (gradD r) (M r (gradD r)) := by
        have hnormne : ‖gradD r‖ ≠ 0 := norm_ne_zero_iff.mpr hgradne
        have hnorm : 0 < ‖gradD r‖ ^ 2 := sq_pos_of_ne_zero hnormne
        have hquad := hcoercive r hr (gradD r)
        nlinarith
      have hdir := theorem20_directional_from_potential
        (M r) (Minv r) V₀ P D s (x r) (gradV r) (gradP r) (gradD r)
        (velocity r) (-(M r (gradD r))) κ q (sDeriv r) b c
        (hV r hr) (hP r hr) (hD r hr) (hs r hr) (hFlow r hr) rfl
        (hleft r hr) (hsymmetric r hr)
        (hA r hr (hK r hr) htarget) (hB r hr (hK r hr) htarget)
        hgpositive hb hc
      have hderiv := (hDpath_deriv r hr).deriv
      calc
        deriv Dpath r = inner ℝ (gradD r) (velocity r) := hderiv
        _ ≤ -c * inner ℝ (gradD r) (M r (gradD r)) := hdir.1
        _ = -c * g2 r := by rw [hg2_eq r hr]
  have hrate : ∀ r, t₀ ≤ r → deriv Dpath r ≤ -(2 * μ * c) * Dpath r := by
    intro r hr
    have hpl : 2 * μ * Dpath r ≤ g2 r := by simpa [Dpath] using hPL r hr
    have hmul := mul_le_mul_of_nonneg_left hpl hc.le
    have hdec := hdescent r hr
    dsimp [Dpath]
    nlinarith
  have hregular : ∀ r, t₀ ≤ r →
      HasDerivAt Dpath (deriv Dpath r) r := by
    intro r hr
    have h := hDpath_deriv r hr
    convert h using 1
    exact h.deriv
  have hpoint : ∀ t, t₀ ≤ t →
      D (x t) ≤ D (x t₀) * Real.exp (-(2 * μ * c) * (t - t₀)) ∧
      dist t ≤ C * Real.sqrt (D (x t₀)) * Real.exp (-μ * c * (t - t₀)) ∧
      deriv Dpath t ≤ -c * g2 t ∧
      (x t ∉ Z → deriv Dpath t < 0) ∧
      inner ℝ (Minv t (velocity t)) (-(M t (gradD t))) = -deriv Dpath t := by
    intro t ht
    have hDdecay := exponential_distance_bound_on_interval Dpath (2 * μ * c) t₀ t
      (fun r hr => hregular r hr.1) (fun r hr => hrate r hr.1) ht
    have hdist := distance_error_exponential_bound Dpath dist C
      (2 * μ * c) t₀ t (by simpa [Dpath, neg_mul, mul_assoc] using hDdecay)
      (by simpa [dist, Dpath] using herror t ht) (hD_nonneg (x t₀)) hC
    have hstrict : x t ∉ Z → deriv Dpath t < 0 := by
      intro hnot
      have hgradne : gradD t ≠ 0 := by
        intro heq
        apply hnot
        apply (hD_zero (x t)).1
        have hpl := hPL t ht
        have hgzero : g2 t = 0 := by rw [hg2_eq t ht, heq]; simp
        rw [hgzero] at hpl
        nlinarith [hD_nonneg (x t)]
      have hnormne : ‖gradD t‖ ≠ 0 := norm_ne_zero_iff.mpr hgradne
      have hnorm : 0 < ‖gradD t‖ ^ 2 := sq_pos_of_ne_zero hnormne
      have hquad := hcoercive t ht (gradD t)
      have hgpositive : 0 < inner ℝ (gradD t) (M t (gradD t)) := by nlinarith
      have hdir := theorem20_directional_from_potential
        (M t) (Minv t) V₀ P D s (x t) (gradV t) (gradP t) (gradD t)
        (velocity t) (-(M t (gradD t))) κ q (sDeriv t) b c
        (hV t ht) (hP t ht) (hD t ht) (hs t ht) (hFlow t ht) rfl
        (hleft t ht) (hsymmetric t ht)
        (hA t ht (hK t ht) hnot) (hB t ht (hK t ht) hnot)
        hgpositive hb hc
      have hderiv := (hDpath_deriv t ht).deriv
      rw [hderiv]
      have hnegative : 0 < -deriv Dpath t := by
        rw [← hidentity t ht]
        exact hdir.2
      linarith
    refine ⟨?_, ?_, hdescent t ht, hstrict, hidentity t ht⟩
    · simpa [Dpath, neg_mul, mul_assoc] using hDdecay
    · convert hdist using 1 <;> congr 1 <;> ring_nf
  have hlim := distance_tendsto_zero_of_exponential_bound dist
    (C * Real.sqrt (D (x t₀))) (μ * c) t₀
    (fun τ hτ => by
      have h := (hpoint τ hτ).2.1
      convert h using 1 <;> congr 1 <;> ring_nf)
    (fun r => Metric.infDist_nonneg) (mul_pos hμ hc)
  exact ⟨hpoint, hlim⟩

/-- H-flow adapter for the original-condition theorem 20 entry. It requires a
`DifferentiableClosedLoopPolicyFlow`, whose `solves` field gives an ordinary
derivative at every future time, including a two-sided derivative at the start.
This is an explicit regularity condition stronger than a forward AC+a.e.
Carathéodory solution; this adapter does not derive it from the Borel feedback
or restart law. The trajectory and velocity still come from one policy flow,
rather than unrelated functions. -/
theorem theorem20_policy_flow_original_condition_conclusion
    {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : Tomabechi.Theorem1.DifferentiableClosedLoopPolicyFlow E U)
    (M Minv : ℝ → E →L[ℝ] E) (V₀ P D : E → ℝ) (s : ℝ → ℝ)
    (κ q b c μ C gamma t₀ : ℝ)
    (ht₀ : 0 ≤ t₀)
    (initialSet : Set E) (x₀ : E) (hx₀ : x₀ ∈ initialSet) (Z : Set E)
    (g2 sDeriv : ℝ → ℝ)
    (gradV gradP gradD : ℝ → E)
    (hField : ∀ y r,
      F.vectorField y (F.feedback y r) r =
        -(M r) (∇ (fun z => V₀ z - κ * q * (P z * s (D z))) y))
    (_hKcompact : IsCompact (Tomabechi.Theorem1.closedLoopReachableSet
      (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀)))
    (_hKforwardInvariant : ∀ y ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀),
      ∀ r, t₀ ≤ r → F.flow t₀ y r ∈ Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀))
    (hV : ∀ r, t₀ ≤ r → HasGradientAt V₀ (gradV r) (F.flow t₀ x₀ r))
    (hP : ∀ r, t₀ ≤ r → HasGradientAt P (gradP r) (F.flow t₀ x₀ r))
    (hD : ∀ r, t₀ ≤ r → HasGradientAt D (gradD r) (F.flow t₀ x₀ r))
    (hD_nonneg : ∀ y, 0 ≤ D y)
    (hD_zero : ∀ y, D y = 0 ↔ y ∈ Z)
    (hZ_nonempty : Z.Nonempty) (hZ_closed : IsClosed Z)
    (hs : ∀ r, t₀ ≤ r → HasDerivAt s (sDeriv r) (D (F.flow t₀ x₀ r)))
    (hleft : ∀ r, t₀ ≤ r → ∀ y, Minv r (M r y) = y)
    (hsymmetric : ∀ r, t₀ ≤ r → ∀ y z,
      inner ℝ y (M r z) = inner ℝ (M r y) z)
    (hcoercive : ∀ r, t₀ ≤ r → ∀ y,
      gamma * ‖y‖ ^ 2 ≤ inner ℝ y (M r y))
    (hA : ∀ r, t₀ ≤ r → F.flow t₀ x₀ r ∈
        Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀) →
      F.flow t₀ x₀ r ∉ Z →
      -inner ℝ (gradD r) (M r (gradV r)) +
        κ * q * s (D (F.flow t₀ x₀ r)) * inner ℝ (gradD r) (M r (gradP r)) ≤
          b * inner ℝ (gradD r) (M r (gradD r)))
    (hB : ∀ r, t₀ ≤ r → F.flow t₀ x₀ r ∈
        Tomabechi.Theorem1.closedLoopReachableSet
        (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀) →
      F.flow t₀ x₀ r ∉ Z →
      κ * q * P (F.flow t₀ x₀ r) * (-sDeriv r) ≥ b + c)
    (hPL : ∀ r, t₀ ≤ r → 2 * μ * D (F.flow t₀ x₀ r) ≤ g2 r)
    (hg2_eq : ∀ r, t₀ ≤ r →
      g2 r = inner ℝ (gradD r) (M r (gradD r)))
    (herror : ∀ r, t₀ ≤ r →
      Metric.infDist (F.flow t₀ x₀ r) Z ≤ C * Real.sqrt (D (F.flow t₀ x₀ r)))
    (hC : 0 ≤ C) (hμ : 0 < μ) (hq : 0 < q)
    (hb : 0 < b) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ t, t₀ ≤ t →
      D (F.flow t₀ x₀ t) ≤ D (F.flow t₀ x₀ t₀) *
        Real.exp (-(2 * μ * c) * (t - t₀)) ∧
      Metric.infDist (F.flow t₀ x₀ t) Z ≤ C *
        Real.sqrt (D (F.flow t₀ x₀ t₀)) * Real.exp (-μ * c * (t - t₀)) ∧
      deriv (fun r => D (F.flow t₀ x₀ r)) t ≤ -c * g2 t ∧
      (F.flow t₀ x₀ t ∉ Z →
        deriv (fun r => D (F.flow t₀ x₀ r)) t < 0) ∧
      (inner ℝ (Minv t (F.vectorField (F.flow t₀ x₀ t)
          (F.feedback (F.flow t₀ x₀ t) t) t)) (-(M t (gradD t))) =
        -deriv (fun r => D (F.flow t₀ x₀ r)) t)) ∧
      Filter.Tendsto (fun r => Metric.infDist (F.flow t₀ x₀ r) Z)
        atTop (𝓝 0) := by
  let x : ℝ → E := F.flow t₀ x₀
  let velocity : ℝ → E := fun r => F.vectorField (x r) (F.feedback (x r) r) r
  let K : Set E := Tomabechi.Theorem1.closedLoopReachableSet
    (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀)
  have hK : ∀ r, t₀ ≤ r → x r ∈ K := by
    intro r hr
    exact Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt
      (Tomabechi.Theorem1.policyFlowReachableAt F.toClosedLoopPolicyFlow initialSet t₀)
      (le_trans ht₀ hr)
      (Tomabechi.Theorem1.mem_policyFlowReachableAt_of_flow
        F.toClosedLoopPolicyFlow initialSet t₀ r x₀ hx₀ hr)
  have hPath : ∀ r, t₀ ≤ r → HasDerivAt x (velocity r) r := by
    intro r hr
    simpa [x, velocity] using F.solves t₀ x₀ r hr
  have hFlow : ∀ r, t₀ ≤ r → velocity r =
      -(M r) (∇ (fun y => V₀ y - κ * q * (P y * s (D y))) (x r)) := by
    intro r hr
    exact hField (x r) r
  have hresult := theorem20_full_trajectory_conclusion_of_original_conditions
    M Minv V₀ P D s x velocity K Z g2 sDeriv κ q b c μ C gamma t₀
    gradV gradP gradD hK hV hP hD hD_nonneg hD_zero hZ_nonempty hZ_closed
    hs hPath hFlow hleft
    hsymmetric hcoercive hA hB hPL hg2_eq herror hC hμ hq hb hc hgamma
  simpa [x, velocity] using hresult

end Tomabechi.Theorem20

#print axioms Tomabechi.Theorem20.gradient_eq_zero_of_nonnegative_at_zero
#print axioms Tomabechi.Theorem20.theorem20_full_trajectory_conclusion_of_original_conditions
#print axioms Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion
