import Mathlib.Order.FixedPoints
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Theorem21
import Econlib.Math.Topology.FanGlicksberg

/-!
# 定理16・25の依存コア

このファイルでは、履歴ごとの逆極限状態と層別フィードバックの整合性を型で表し、
定理16の固定点存在・縮小写像による一意性と、定理25第1結論の論理的接続を分ける。

原文の定理16は、有限層族の整合性からなる逆極限と連続自己写像に対する固定点存在を
主張し、さらに完備距離上の縮小性を条件として一意性と幾何収束を述べる。有限層整合性は
有向性・各層の非空性・射影の合成則・TCZ像包含から導出し、別仮定にはしない。この縮小条件は
原文に明示されているが、局所凸コンパクト条件から導く証明は原文にない。Mathlib v4.34.1
には局所凸空間のコンパクト凸集合に対する固定点定理はないため、EconlibのFan–Glicksberg
証明依存をApache-2.0表示つきで移植し、定理16の存在部分を形式化する。存在と縮小条件下の
一意性・幾何収束を別々に扱う。元論文条件を受け取る統合定理は恒等射影則と最大元なしも
APIに残すが、有限整合性の導出と固定点存在の証明ではそれらを使用しない。

定理25第1結論は、異なる履歴に相対する固定点が異なるという条件25-A(1)と、
各履歴で固定点が一意であることから、全履歴共通固定点がないことを導く。
第2結論は条件25-Dの機能的完備性を「候補自性の介入が関係状態と将来出力の同時法則を
変えない」と読む操作的モデル上で形式化する。25-B・25-Cはモデルの層別・関係構造を
与えるが、それらだけから25-Dは導かれない。
-/

namespace Tomabechi.Theorem16_25

open Function
open scoped Convex
open scoped RealInnerProductSpace

universe u v

/-- 有限離散外生空間からの写像は可測であり、その確率法則pushforwardは通常の像測度になる。 -/
private theorem theorem25_finiteDomain_aemeasurable
    {U V : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    [Finite U] [MeasurableSpace V]
    (μ : MeasureTheory.Measure U) (f : U → V) : AEMeasurable f μ :=
  (measurable_of_finite f).aemeasurable

/-- 確率測度のpushforwardが、全ての像点を含む可測集合に確率1を与える。 -/
private theorem theorem25_probabilityMap_eq_one_of_forall_mem
    {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (μ : MeasureTheory.ProbabilityMeasure U) (f : U → V) (s : Set V)
    (hf : AEMeasurable f (MeasureTheory.ProbabilityMeasure.toMeasure μ))
    (hs : MeasurableSet s) (hmem : ∀ u, f u ∈ s) :
    MeasureTheory.ProbabilityMeasure.toMeasure (μ.map f) s = 1 := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure μ).map f s = 1
  rw [MeasureTheory.Measure.map_apply_of_aemeasurable hf hs]
  have hpre : f ⁻¹' s = Set.univ := by
    ext u
    simp [hmem u]
  rw [hpre]
  simp

/-- 強単調な勾配と勾配のLipschitz上界があれば、明示したステップ幅条件のもとで
陽的Euler勾配更新は縮小写像になる。定理21型ポテンシャル力学から定理16の
`ContractingWith` へ進むための有限次元・離散時間の橋渡し候補である。 -/
theorem gradientEulerStep_contracting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (η c L : ℝ) (K : NNReal)
    (hconvex : Tomabechi.Theorem21.StronglyConvexOn U potential gradient c)
    (hη : 0 < η) (hL : 0 ≤ L)
    (hK : K < 1)
    (hstep : 1 - 2 * η * c + η ^ 2 * L ^ 2 ≤ (K : ℝ) ^ 2)
    (hgradLip : ∀ x ∈ U, ∀ y ∈ U,
      ‖gradient y - gradient x‖ ≤ L * ‖y - x‖)
    (hmaps : ∀ x ∈ U, x - η • gradient x ∈ U) :
    ContractingWith K
      (fun x : {x : E // x ∈ U} =>
        (⟨x.1 - η • gradient x.1, hmaps x.1 x.2⟩ : {x : E // x ∈ U})) := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have hdiff : (x.1 - η • gradient x.1) - (y.1 - η • gradient y.1) =
      (x.1 - y.1) - η • (gradient x.1 - gradient y.1) := by module
  rw [hdiff]
  have hmono := Tomabechi.Theorem21.strongly_monotone_gradient
    potential gradient c U hconvex y.1 y.2 x.1 x.2
  have hgrad := hgradLip y.1 y.2 x.1 x.2
  have hgradSq : ‖gradient x.1 - gradient y.1‖ ^ 2 ≤
      L ^ 2 * ‖x.1 - y.1‖ ^ 2 := by
    have hprod : 0 ≤ (L * ‖x.1 - y.1‖ - ‖gradient x.1 - gradient y.1‖) *
        (L * ‖x.1 - y.1‖ + ‖gradient x.1 - gradient y.1‖) :=
      mul_nonneg (sub_nonneg.mpr hgrad) (by positivity)
    nlinarith [hprod]
  have hsq : ‖(x.1 - y.1) - η • (gradient x.1 - gradient y.1)‖ ^ 2 ≤
      (K : ℝ) ^ 2 * ‖x.1 - y.1‖ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη,
      inner_smul_right]
    have hmonoDiff : c * ‖x.1 - y.1‖ ^ 2 ≤
        inner ℝ (gradient x.1 - gradient y.1) (x.1 - y.1) := by
      simpa only [inner_sub_left] using hmono
    have hmonoSymm : c * ‖x.1 - y.1‖ ^ 2 ≤
        inner ℝ (x.1 - y.1) (gradient x.1 - gradient y.1) := by
      simpa only [real_inner_comm] using hmonoDiff
    have hmono' := mul_le_mul_of_nonneg_left hmonoSymm (le_of_lt hη)
    have hgradSq' := mul_le_mul_of_nonneg_left hgradSq (sq_nonneg η)
    have hstep' := mul_le_mul_of_nonneg_right hstep
      (sq_nonneg ‖x.1 - y.1‖)
    have hcross : -2 * (η * inner ℝ (x.1 - y.1)
        (gradient x.1 - gradient y.1)) ≤
        -2 * (η * (c * ‖x.1 - y.1‖ ^ 2)) := by
      exact mul_le_mul_of_nonpos_left hmono' (by norm_num)
    have hgradTerm : (η * ‖gradient x.1 - gradient y.1‖) ^ 2 =
        η ^ 2 * ‖gradient x.1 - gradient y.1‖ ^ 2 := by ring
    rw [hgradTerm]
    nlinarith [hcross, hgradSq', hstep']
  have hnonneg : 0 ≤ ‖(x.1 - y.1) - η • (gradient x.1 - gradient y.1)‖ := norm_nonneg _
  have htarget : 0 ≤ (K : ℝ) * ‖x.1 - y.1‖ := by positivity
  nlinarith [hsq]

/-- 強凸ポテンシャルに対する恒等移動度の自律勾配流 `x'=-∇V` は、二軌道間距離を
指数率 `c` で縮める。各軌道が凸領域に留まることは明示仮定。
これは定理21の状態依存移動度 `x'=-A(x)∇V` 一般を扱わず、また定理16の抽象的な
層別フィードバックとの同定も仮定からは導かない。 -/
theorem stronglyConvexGradientFlow_dist_contracting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (c a b : ℝ)
    (hconvex : Tomabechi.Theorem21.StronglyConvexOn U potential gradient c)
    (f g : ℝ → E)
    (hf : ∀ t, HasDerivAt f (-gradient (f t)) t)
    (hg : ∀ t, HasDerivAt g (-gradient (g t)) t)
    (hfU : ∀ t ∈ Set.Icc a b, f t ∈ U)
    (hgU : ∀ t ∈ Set.Icc a b, g t ∈ U) :
    ∀ t ∈ Set.Icc a b,
      dist (f t) (g t) ≤ Real.exp (-c * (t - a)) * dist (f a) (g a) := by
  let delta : ℝ → E := fun t => g t - f t
  let q : ℝ → ℝ := fun t => ‖delta t‖ ^ 2
  let phi : ℝ → ℝ := fun t => Real.exp (2 * c * (t - a)) * q t
  have hq_diff : Differentiable ℝ q := by
    intro t
    dsimp [q]
    simpa [delta] using ((hg t).sub (hf t)).norm_sq.differentiableAt
  have hphi_diff : Differentiable ℝ phi := by
    change Differentiable ℝ (fun t => Real.exp (2 * c * (t - a)) * q t)
    exact (Real.differentiable_exp.comp
      ((differentiable_id.sub_const a).const_mul (2 * c))).mul hq_diff
  have hphi_cont : ContinuousOn phi (Set.Icc a b) :=
    hphi_diff.continuous.continuousOn
  have hphi_deriv_nonpos : ∀ t ∈ interior (Set.Icc a b), deriv phi t ≤ 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have hdelta : HasDerivAt delta (gradient (f t) - gradient (g t)) t := by
      dsimp [delta]
      convert (hg t).sub (hf t) using 1 <;> module
    have hq : HasDerivAt q
        (2 * inner ℝ (delta t) (gradient (f t) - gradient (g t))) t := by
      simpa [q] using hdelta.norm_sq
    have hexpArg : HasDerivAt (fun r : ℝ => 2 * c * (r - a)) (2 * c) t := by
      simpa [Function.comp_def] using
        ((hasDerivAt_id t).sub_const a).const_mul (2 * c)
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (2 * c * (r - a)))
        (2 * c * Real.exp (2 * c * (t - a))) t := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (2 * c * (t - a))).comp t hexpArg
    have hphi : HasDerivAt phi
        (2 * c * Real.exp (2 * c * (t - a)) * q t +
          Real.exp (2 * c * (t - a)) *
            (2 * inner ℝ (delta t) (gradient (f t) - gradient (g t)))) t := by
      dsimp [phi]
      convert hexp.mul hq using 1
    have hmono := Tomabechi.Theorem21.strongly_monotone_gradient
      potential gradient c U hconvex (f t) (hfU t htIcc) (g t) (hgU t htIcc)
    have hinnerEq : inner ℝ (delta t) (gradient (f t) - gradient (g t)) =
        -(inner ℝ (gradient (g t)) (g t - f t) -
          inner ℝ (gradient (f t)) (g t - f t)) := by
      simp [delta, inner_sub_right, real_inner_comm]
    have hqdecay :
        2 * inner ℝ (delta t) (gradient (f t) - gradient (g t)) ≤
          -2 * c * q t := by
      rw [hinnerEq]
      dsimp [q, delta]
      nlinarith [hmono]
    have hexppos : 0 < Real.exp (2 * c * (t - a)) := Real.exp_pos _
    have hderiv := hphi.deriv
    rw [hderiv]
    calc
      2 * c * Real.exp (2 * c * (t - a)) * q t +
          Real.exp (2 * c * (t - a)) *
            (2 * inner ℝ (delta t) (gradient (f t) - gradient (g t)))
          = Real.exp (2 * c * (t - a)) *
              (2 * c * q t +
                2 * inner ℝ (delta t) (gradient (f t) - gradient (g t))) := by ring
      _ ≤ 0 := by
        have hsum : 2 * c * q t +
            2 * inner ℝ (delta t) (gradient (f t) - gradient (g t)) ≤ 0 := by
          nlinarith [hqdecay]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hexppos) hsum
  have hanti : AntitoneOn phi (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hphi_cont
      (hphi_diff.differentiableOn.mono interior_subset) hphi_deriv_nonpos
  intro t ht
  have hab : a ≤ b := le_trans ht.1 ht.2
  have haIcc : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hphi_le := hanti haIcc ht ht.1
  have hexpRelation : Real.exp (-c * (t - a)) ^ 2 *
      Real.exp (2 * c * (t - a)) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    ring
  have hdist0 : 0 ≤ dist (f a) (g a) := dist_nonneg
  have hdistt : 0 ≤ dist (f t) (g t) := dist_nonneg
  have htarget : 0 ≤ Real.exp (-c * (t - a)) * dist (f a) (g a) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hdist0
  have hqdist : q t = dist (f t) (g t) ^ 2 := by
    simp [q, delta, dist_eq_norm, norm_sub_rev]
  have hqdist0 : q a = dist (f a) (g a) ^ 2 := by
    simp [q, delta, dist_eq_norm, norm_sub_rev]
  have hphi_le' : Real.exp (2 * c * (t - a)) * dist (f t) (g t) ^ 2 ≤
      dist (f a) (g a) ^ 2 := by
    simpa [phi, hqdist, hqdist0] using hphi_le
  have hmul : dist (f t) (g t) ^ 2 * Real.exp (2 * c * (t - a)) ≤
      (Real.exp (-c * (t - a)) * dist (f a) (g a)) ^ 2 *
        Real.exp (2 * c * (t - a)) := by
    calc
      dist (f t) (g t) ^ 2 * Real.exp (2 * c * (t - a)) ≤
          dist (f a) (g a) ^ 2 := by simpa [mul_comm] using hphi_le'
      _ = (Real.exp (-c * (t - a)) * dist (f a) (g a)) ^ 2 *
          Real.exp (2 * c * (t - a)) := by
        rw [mul_pow]
        calc
          dist (f a) (g a) ^ 2 =
              dist (f a) (g a) ^ 2 * 1 := by ring
          _ = dist (f a) (g a) ^ 2 *
              (Real.exp (-c * (t - a)) ^ 2 * Real.exp (2 * c * (t - a))) := by
            rw [hexpRelation, mul_one]
          _ = _ := by ring
  have hsquare : dist (f t) (g t) ^ 2 ≤
      (Real.exp (-c * (t - a)) * dist (f a) (g a)) ^ 2 := by
    exact (le_of_mul_le_mul_right hmul (Real.exp_pos _))
  nlinarith [sq_nonneg (dist (f t) (g t) -
    Real.exp (-c * (t - a)) * dist (f a) (g a))]

/-- 座標変換後のドリフトが一様強単調なら、元の状態軌道の変換座標距離は指数収縮する。
距離は `dist (coordinate x) (coordinate y)` であり、原座標のユークリッド距離ではない。 -/
theorem coordinateFlow_dist_contracting
    (U : Set ℝ) (coordinate drift : ℝ → ℝ) (μ a b : ℝ)
    (_hμ : 0 < μ)
    (hmono : ∀ x ∈ U, ∀ y ∈ U,
      μ * (coordinate x - coordinate y) ^ 2 ≤
        (drift x - drift y) * (coordinate x - coordinate y))
    (f g : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s => coordinate (f s)) (-drift (f t)) t)
    (hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s => coordinate (g s)) (-drift (g t)) t)
    (hfU : ∀ t ∈ Set.Icc a b, f t ∈ U)
    (hgU : ∀ t ∈ Set.Icc a b, g t ∈ U) :
    ∀ t ∈ Set.Icc a b,
      dist (coordinate (f t)) (coordinate (g t)) ≤
        Real.exp (-μ * (t - a)) *
          dist (coordinate (f a)) (coordinate (g a)) := by
  let delta : ℝ → ℝ := fun t => coordinate (g t) - coordinate (f t)
  let q : ℝ → ℝ := fun t => delta t * delta t
  let phi : ℝ → ℝ := fun t => Real.exp (2 * μ * (t - a)) * q t
  have hq_diff : DifferentiableOn ℝ q (Set.Icc a b) := by
    intro t ht
    dsimp [q]
    exact (((hg t ht).sub (hf t ht)).mul
      ((hg t ht).sub (hf t ht))).differentiableAt.differentiableWithinAt
  have hphi_diff : DifferentiableOn ℝ phi (Set.Icc a b) := by
    change DifferentiableOn ℝ (fun t => Real.exp (2 * μ * (t - a)) * q t)
      (Set.Icc a b)
    exact (Real.differentiable_exp.comp
      ((differentiable_id.sub_const a).const_mul (2 * μ))).differentiableOn.mul hq_diff
  have hphi_cont : ContinuousOn phi (Set.Icc a b) :=
    hphi_diff.continuousOn
  have hphi_deriv_nonpos : ∀ t ∈ interior (Set.Icc a b), deriv phi t ≤ 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have hdelta : HasDerivAt delta (drift (f t) - drift (g t)) t := by
      dsimp [delta]
      convert (hg t htIcc).sub (hf t htIcc) using 1 <;> ring
    have hq : HasDerivAt q
        (2 * delta t * (drift (f t) - drift (g t))) t := by
      dsimp [q]
      convert hdelta.mul hdelta using 1 <;> ring
    have hexpArg : HasDerivAt (fun r : ℝ => 2 * μ * (r - a)) (2 * μ) t := by
      simpa [Function.comp_def] using
        ((hasDerivAt_id t).sub_const a).const_mul (2 * μ)
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (2 * μ * (r - a)))
        (2 * μ * Real.exp (2 * μ * (t - a))) t := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (2 * μ * (t - a))).comp t hexpArg
    have hphi : HasDerivAt phi
        (2 * μ * Real.exp (2 * μ * (t - a)) * q t +
          Real.exp (2 * μ * (t - a)) *
            (2 * delta t * (drift (f t) - drift (g t)))) t := by
      dsimp [phi]
      convert hexp.mul hq using 1
    have hmono' := hmono (g t) (hgU t htIcc) (f t) (hfU t htIcc)
    have hqdecay :
        2 * delta t * (drift (f t) - drift (g t)) ≤ -2 * μ * q t := by
      dsimp [q, delta]
      nlinarith [hmono']
    have hexppos : 0 < Real.exp (2 * μ * (t - a)) := Real.exp_pos _
    have hderiv := hphi.deriv
    rw [hderiv]
    calc
      2 * μ * Real.exp (2 * μ * (t - a)) * q t +
          Real.exp (2 * μ * (t - a)) *
            (2 * delta t * (drift (f t) - drift (g t)))
          = Real.exp (2 * μ * (t - a)) *
              (2 * μ * q t + 2 * delta t * (drift (f t) - drift (g t))) := by ring
      _ ≤ 0 := by
        have hsum : 2 * μ * q t +
            2 * delta t * (drift (f t) - drift (g t)) ≤ 0 := by
          nlinarith [hqdecay]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hexppos) hsum
  have hanti : AntitoneOn phi (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hphi_cont
      (hphi_diff.mono interior_subset) hphi_deriv_nonpos
  intro t ht
  have hab : a ≤ b := le_trans ht.1 ht.2
  have haIcc : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hphi_le := hanti haIcc ht ht.1
  have hexpRelation : Real.exp (-μ * (t - a)) ^ 2 *
      Real.exp (2 * μ * (t - a)) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    ring
  have hqdist : q t = dist (coordinate (f t)) (coordinate (g t)) ^ 2 := by
    simp [q, delta, dist_eq_norm, Real.norm_eq_abs, sq_abs]
    ring
  have hqdist0 : q a =
      dist (coordinate (f a)) (coordinate (g a)) ^ 2 := by
    simp [q, delta, dist_eq_norm, Real.norm_eq_abs, sq_abs]
    ring
  have hphi_le' :
      Real.exp (2 * μ * (t - a)) *
        dist (coordinate (f t)) (coordinate (g t)) ^ 2 ≤
      dist (coordinate (f a)) (coordinate (g a)) ^ 2 := by
    simpa [phi, hqdist, hqdist0] using hphi_le
  have htarget : 0 ≤ Real.exp (-μ * (t - a)) *
      dist (coordinate (f a)) (coordinate (g a)) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) dist_nonneg
  have hmul : dist (coordinate (f t)) (coordinate (g t)) ^ 2 *
      Real.exp (2 * μ * (t - a)) ≤
      (Real.exp (-μ * (t - a)) *
        dist (coordinate (f a)) (coordinate (g a))) ^ 2 *
        Real.exp (2 * μ * (t - a)) := by
    calc
      dist (coordinate (f t)) (coordinate (g t)) ^ 2 *
          Real.exp (2 * μ * (t - a)) ≤
          dist (coordinate (f a)) (coordinate (g a)) ^ 2 := by
            simpa [mul_comm] using hphi_le'
      _ = (Real.exp (-μ * (t - a)) *
          dist (coordinate (f a)) (coordinate (g a))) ^ 2 *
          Real.exp (2 * μ * (t - a)) := by
        rw [mul_pow]
        calc
          dist (coordinate (f a)) (coordinate (g a)) ^ 2 =
              dist (coordinate (f a)) (coordinate (g a)) ^ 2 * 1 := by ring
          _ = dist (coordinate (f a)) (coordinate (g a)) ^ 2 *
              (Real.exp (-μ * (t - a)) ^ 2 * Real.exp (2 * μ * (t - a))) := by
            rw [hexpRelation, mul_one]
          _ = _ := by ring
  have hsquare : dist (coordinate (f t)) (coordinate (g t)) ^ 2 ≤
      (Real.exp (-μ * (t - a)) *
        dist (coordinate (f a)) (coordinate (g a))) ^ 2 :=
    le_of_mul_le_mul_right hmul (Real.exp_pos _)
  nlinarith [sq_nonneg (dist (coordinate (f t)) (coordinate (g t)) -
    Real.exp (-μ * (t - a)) * dist (coordinate (f a)) (coordinate (g a)))]

/-- 恒等移動度の強凸勾配流の時間 `T>0` 写像は、全ての初期値からの軌道が領域内に
留まるなら縮小写像となる。これは定理16のBanach条件に対する十分条件の例である。
軌道の大域存在・領域不変性、および定理16の自己意識更新則との同定は別途必要で、
定理21にある状態依存移動度 `A(x)` を含む一般系への拡張も証明していない。 -/
theorem stronglyConvexGradientFlow_timeMap_contracting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (potential : E → ℝ) (gradient : E → E) (c T : ℝ)
    (hc : 0 < c)
    (hconvex : Tomabechi.Theorem21.StronglyConvexOn U potential gradient c)
    (hT : 0 < T)
    (trajectory : {x : E // x ∈ U} → ℝ → E)
    (hderiv : ∀ x t, HasDerivAt (trajectory x) (-gradient (trajectory x t)) t)
    (hstay : ∀ x t, t ∈ Set.Icc 0 T → trajectory x t ∈ U)
    (hstart : ∀ x, trajectory x 0 = x.1) :
    ContractingWith ⟨Real.exp (-c * T), le_of_lt (Real.exp_pos _)⟩
      (fun x : {x : E // x ∈ U} =>
        (⟨trajectory x T, hstay x T ⟨le_of_lt hT, le_rfl⟩⟩ : {x : E // x ∈ U})) := by
  have hK : (⟨Real.exp (-c * T), le_of_lt (Real.exp_pos _)⟩ : NNReal) < 1 := by
    change Real.exp (-c * T) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Subtype.dist_eq, Subtype.dist_eq]
  have hcontract := stronglyConvexGradientFlow_dist_contracting
    U potential gradient c 0 T hconvex
    (trajectory x) (trajectory y) (hderiv x) (hderiv y)
    (fun t ht => hstay x t ht) (fun t ht => hstay y t ht) T
    ⟨le_of_lt hT, le_rfl⟩
  change dist (trajectory x T) (trajectory y T) ≤
    Real.exp (-c * T) * dist (x : E) (y : E)
  simpa [sub_zero, hstart] using hcontract

/-- アフィン写像は係数和が1の凸結合を保つ。 -/
theorem affineMap_preserves_convexCombination
    {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ᵃ[ℝ] W) (x y : V) (a b : ℝ) (hab : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  have ha' : a = 1 - b := by linarith
  rw [ha']
  have hsource : (1 - b) • x + b • y = b • (y - x) + x := by
    module
  calc
    f ((1 - b) • x + b • y) = f (b • (y - x) + x) := congrArg f hsource
    _ = (1 - b) • f x + b • f y := by
      rw [← vadd_eq_add, f.map_vadd, map_smul, ← vsub_eq_sub,
        f.linearMap_vsub, vsub_eq_sub, vadd_eq_add]
      module

/-- 逆極限を定める射影方程式の添字。 -/
abbrev ProjectionConstraintIndex (I : Type u) [Preorder I] :=
  {p : I × I // p.1 ≤ p.2}

/-- 凸な層状態集合の逆極限は、層間射影がアフィンなら凸である。
これはSchauder–Tychonoff固定点定理へ渡す逆極限側の凸性を形式化する。 -/
def affineInverseLimitSet {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β) : Set (∀ i, E i) :=
  {x | (∀ i, x i ∈ K i) ∧
    ∀ ⦃β α : I⦄ (hβα : β ≤ α), project hβα (x α) = x β}

/-- 各層の局所凸性は積空間にも引き継がれ、Schauder–Tychonoffを適用するambientを与える。 -/
theorem product_locallyConvexSpace {I : Type u}
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, LocallyConvexSpace ℝ (E i)] :
    LocallyConvexSpace ℝ (∀ i, E i) := inferInstance

/-- Fan–Glicksbergを使うambientは単なる局所凸空間クラスでなく位相ベクトル空間である。
各層で加法とスカラー倍が連続なら、積空間でも両連続性が引き継がれる。 -/
theorem product_topologicalVectorSpaceOperations {I : Type u}
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] :
    IsTopologicalAddGroup (∀ i, E i) ∧ ContinuousSMul ℝ (∀ i, E i) :=
  ⟨inferInstance, inferInstance⟩

/-- 射影整合条件を積空間上の一つの閉候補として表す。 -/
def affineProjectionConstraint {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (j : ProjectionConstraintIndex I) : Set (∀ i, E i) :=
  {x | project j.2 (x j.1.2) = x j.1.1}

/-- 各射影がTCZ上でのみ連続でも、逆極限は非空かつコンパクト。
積TCZの部分型をambientとして等式制約の閉性を示すので、周囲空間全体への
連続延長は仮定しない。 -/
theorem affineInverseLimitSet_nonempty_compact_of_relativeContinuous
    {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectContinuousOn : ∀ (j : ProjectionConstraintIndex I),
      ContinuousOn (project j.2) (K j.1.2))
    (hfinite : ∀ t : Finset I,
      ∃ z : ∀ i, i ∈ t → E i,
        (∀ i (hi : i ∈ t), z i hi ∈ K i) ∧
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          project hβα (z α hα) = z β hβ) :
    (affineInverseLimitSet E K project).Nonempty ∧
      IsCompact (affineInverseLimitSet E K project) := by
  classical
  let productK : Set (∀ i, E i) := {x | ∀ i, x i ∈ K i}
  let P := {x : ∀ i, E i // x ∈ productK}
  let constraint (j : ProjectionConstraintIndex I) : Set P :=
    {x | project j.2 (x.1 j.1.2) = x.1 j.1.1}
  have hproductCompact : IsCompact productK := isCompact_pi_infinite hKcompact
  letI : CompactSpace P := (isCompact_iff_compactSpace).mp hproductCompact
  have hcoordinate (i : I) : Continuous (fun x : P =>
      (⟨x.1 i, x.2 i⟩ : {y : E i // y ∈ K i})) := by
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  have hconstraintClosed : ∀ j, IsClosed (constraint j) := by
    intro j
    apply isClosed_eq
    · exact (hprojectContinuousOn j).domRestrict.comp (hcoordinate j.1.2)
    · exact (continuous_apply j.1.1).comp continuous_subtype_val
  have hfiniteConstraints : ∀ s : Finset (ProjectionConstraintIndex I),
      (Set.univ ∩ ⋂ j ∈ s, constraint j).Nonempty := by
    intro s
    let layers : Finset I := s.biUnion (fun j => {j.1.1, j.1.2})
    obtain ⟨z, hzK, hzproj⟩ := hfinite layers
    let x : ∀ i, E i := fun i =>
      if hi : i ∈ layers then z i hi else Classical.choose (hKnonempty i)
    have hxK : ∀ i, x i ∈ K i := by
      intro i
      by_cases hi : i ∈ layers
      · simp only [x, dite_eq_left hi]
        exact hzK i hi
      · simp only [x, dite_eq_right hi]
        exact Classical.choose_spec (hKnonempty i)
    let xp : P := ⟨x, hxK⟩
    refine ⟨xp, ?_⟩
    constructor
    · simp
    simp only [Set.mem_iInter]
    intro j hj
    have hβ : j.1.1 ∈ layers := by
      simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨j, hj, Or.inl rfl⟩
    have hα : j.1.2 ∈ layers := by
      simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨j, hj, Or.inr rfl⟩
    change project j.2 (x j.1.2) = x j.1.1
    simp only [x, dite_eq_left hα, dite_eq_left hβ]
    exact hzproj j.2 hβ hα
  obtain ⟨x, hx⟩ := IsCompact.inter_iInter_nonempty
    (isCompact_univ : IsCompact (Set.univ : Set P)) constraint
    hconstraintClosed hfiniteConstraints
  have hsolutionsCompact : IsCompact (⋂ j, constraint j) := by
    exact isCompact_univ.of_isClosed_subset (isClosed_iInter hconstraintClosed)
      (Set.subset_univ _)
  have hset : affineInverseLimitSet E K project =
      Subtype.val '' (⋂ j, constraint j) := by
    ext y
    simp only [affineInverseLimitSet, Set.mem_ofPred_eq, Set.mem_image,
      Set.mem_iInter, constraint]
    constructor
    · rintro ⟨hyK, hyproj⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      intro j
      exact hyproj j.2
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      intro β α hβα
      exact hx ⟨(β, α), hβα⟩
  refine ⟨?_, ?_⟩
  · have hxsol : x ∈ ⋂ j, constraint j := hx.2
    refine ⟨x.1, ?_⟩
    rw [hset]
    exact ⟨x, hxsol, rfl⟩
  · rw [hset]
    exact hsolutionsCompact.image continuous_subtype_val

/-- コンパクト層の積の中で、アフィン射影方程式が閉なら逆極限はコンパクト。
Hausdorffな層と連続射影から閉性を得る条件も引数に明記する。 -/
theorem affineInverseLimitSet_isCompact {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectContinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ i, E i => project j.2 (x j.1.2))) :
    IsCompact (affineInverseLimitSet E K project) := by
  have hKprod : IsCompact {x : ∀ i, E i | ∀ i, x i ∈ K i} :=
    isCompact_pi_infinite hKcompact
  have hclosed : IsClosed (⋂ j, affineProjectionConstraint E project j) := by
    apply isClosed_iInter
    intro j
    exact isClosed_eq (hprojectContinuous j) (continuous_apply j.1.1)
  have hset : affineInverseLimitSet E K project =
      {x : ∀ i, E i | ∀ i, x i ∈ K i} ∩
        (⋂ j, affineProjectionConstraint E project j) := by
    ext x
    simp only [affineInverseLimitSet, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter, affineProjectionConstraint]
    constructor
    · rintro ⟨hK, hproj⟩
      refine ⟨hK, fun j => ?_⟩
      exact hproj j.2
    · rintro ⟨hK, hproj⟩
      refine ⟨hK, ?_⟩
      intro β α hβα
      exact hproj ⟨(β, α), hβα⟩
  rw [hset]
  exact hKprod.inter_right hclosed

/-- 原文の各層非空性と有限層整合性から、アフィン逆極限が非空である。
コンパクト層の積に閉じた射影等式を加える有限交叉論法を直接適用する。 -/
theorem affineInverseLimitSet_nonempty {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectContinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ i, E i => project j.2 (x j.1.2)))
    (hfinite : ∀ t : Finset I,
      ∃ z : ∀ i, i ∈ t → E i,
        (∀ i (hi : i ∈ t), z i hi ∈ K i) ∧
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          project hβα (z α hα) = z β hβ) :
    (affineInverseLimitSet E K project).Nonempty := by
  classical
  let productK : Set (∀ i, E i) := {x | ∀ i, x i ∈ K i}
  let constraint (j : ProjectionConstraintIndex I) :=
    affineProjectionConstraint E project j
  have hproductCompact : IsCompact productK := by
    exact isCompact_pi_infinite hKcompact
  have hconstraintsClosed : ∀ j, IsClosed (constraint j) := by
    intro j
    exact isClosed_eq (hprojectContinuous j) (continuous_apply j.1.1)
  have hfiniteConstraints : ∀ s : Finset (ProjectionConstraintIndex I),
      (productK ∩ ⋂ j ∈ s, constraint j).Nonempty := by
    intro s
    let layers : Finset I := s.biUnion (fun j => {j.1.1, j.1.2})
    obtain ⟨z, hzK, hzproj⟩ := hfinite layers
    let x : ∀ i, E i := fun i =>
      if hi : i ∈ layers then z i hi else Classical.choose (hKnonempty i)
    refine ⟨x, ?_⟩
    constructor
    · intro i
      by_cases hi : i ∈ layers
      · simp only [x, dite_eq_left hi]
        exact hzK i hi
      · simp only [x, dite_eq_right hi]
        exact Classical.choose_spec (hKnonempty i)
    · simp only [Set.mem_iInter]
      intro j hj
      have hβ : j.1.1 ∈ layers := by
        simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨j, hj, Or.inl rfl⟩
      have hα : j.1.2 ∈ layers := by
        simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨j, hj, Or.inr rfl⟩
      change project j.2 (x j.1.2) = x j.1.1
      simp only [x, dite_eq_left hα, dite_eq_left hβ]
      exact hzproj j.2 hβ hα
  obtain ⟨x, hx⟩ := hproductCompact.inter_iInter_nonempty
    constraint hconstraintsClosed hfiniteConstraints
  have hxK : ∀ i, x i ∈ K i := hx.1
  have hx' : ∀ j, x ∈ constraint j := by
    simpa only [Set.mem_iInter] using hx.2
  have hxproj : ∀ ⦃β α : I⦄ (hβα : β ≤ α), project hβα (x α) = x β := by
    intro β α hβα
    have hcoord := hx' ⟨(β, α), hβα⟩
    change project hβα (x α) = x β at hcoord
    exact hcoord
  exact ⟨x, hxK, hxproj⟩

theorem affineInverseLimitSet_convex {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (hKconvex : ∀ i, Convex ℝ (K i)) :
    Convex ℝ (affineInverseLimitSet E K project) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact (convex_iff_add_mem.mp (hKconvex i) (hx.1 i) (hy.1 i) ha hb hab)
  · intro β α hβα
    change project hβα (a • x α + b • y α) = a • x β + b • y β
    calc
      project hβα (a • x α + b • y α) =
          a • project hβα (x α) + b • project hβα (y α) :=
        hprojectAffineOnK hβα (x α) (y α) a b (hx.1 α) (hy.1 α) ha hb hab
      _ = a • x β + b • y β := by
        have hprojx : project hβα (x α) = x β := hx.2 hβα
        have hprojy : project hβα (y α) = y β := hy.2 hβα
        exact congrArg₂ (fun u v : E β => a • u + b • v) hprojx hprojy

/-- 逆極限の強条件版。射影の連続性をambient全体で仮定する。
原文条件に近い相対連続性版は `theorem16_inverseLimit_of_originalLayerConditions` を使う。 -/
theorem theorem16_inverseLimit_nonempty_compact_convex {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (hprojectContinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ i, E i => project j.2 (x j.1.2)))
    (hfinite : ∀ t : Finset I,
      ∃ z : ∀ i, i ∈ t → E i,
        (∀ i (hi : i ∈ t), z i hi ∈ K i) ∧
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          project hβα (z α hα) = z β hβ)
    (hKconvex : ∀ i, Convex ℝ (K i)) :
    (affineInverseLimitSet E K project).Nonempty ∧
      IsCompact (affineInverseLimitSet E K project) ∧
      Convex ℝ (affineInverseLimitSet E K project) := by
  exact ⟨affineInverseLimitSet_nonempty E K hKcompact hKnonempty project
      hprojectContinuous hfinite,
    affineInverseLimitSet_isCompact E K hKcompact project hprojectContinuous,
      affineInverseLimitSet_convex E K project hprojectAffineOnK hKconvex⟩

/-- 上向き有向な添字集合では、有限個の層の上界を取り、その層の任意の点を
すべての有限層へ射影できる。射影の合成則とTCZ像包含により、有限整合性は別仮定でなく導出される。 -/
theorem theorem16_finiteLayerConsistency_of_directedProjections
    {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKnonempty : ∀ i, (K i).Nonempty)
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectComp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β)) :
    ∀ t : Finset I,
      ∃ z : ∀ i, i ∈ t → E i,
        (∀ i (hi : i ∈ t), z i hi ∈ K i) ∧
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          project hβα (z α hα) = z β hβ := by
  classical
  have upperBound : ∀ t : Finset I, ∃ u : I, ∀ i, i ∈ t → i ≤ u := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact ⟨Classical.choice (inferInstance : Nonempty I), by simp⟩
    | @insert a t ha ih =>
        obtain ⟨u, hu⟩ := ih
        obtain ⟨v, hav, huv⟩ := exists_ge_ge a u
        refine ⟨v, ?_⟩
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hit
        · exact hav
        · exact (hu i hit).trans huv
  intro t
  obtain ⟨u, hu⟩ := upperBound t
  let x : E u := Classical.choose (hKnonempty u)
  have hx : x ∈ K u := Classical.choose_spec (hKnonempty u)
  refine ⟨fun i hi => project (hu i hi) x, ?_, ?_⟩
  · intro i hi
    exact hprojectMaps (hu i hi) hx
  · intro β α hβα hβ hα
    calc
      project hβα (project (hu α hα) x) =
          project (hβα.trans (hu α hα)) x :=
        hprojectComp hβα (hu α hα) ⟨x, hx⟩
      _ = project (hu β hβ) x := by
        congr 1

/-- 定理16の原文に列挙された逆系条件を入口に明示した統合結果。
原文対応のため最大元なしと射影の恒等則も受け取るが、この存在・コンパクト性の証明では
使わない。有限層整合性は別引数にせず、上界層の一点を有限個の層へ射影して導く。
したがって、以下の逆極限結論に最大元なしは位相論的には不要である。 -/
theorem theorem16_inverseLimit_of_originalLayerConditions
    {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (hKconvex : ∀ i, Convex ℝ (K i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (_hprojectRefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (hprojectContinuousOn : ∀ (j : ProjectionConstraintIndex I),
      ContinuousOn (project j.2) (K j.1.2))
    (_hnoMax : ∀ i : I, ∃ j, i < j) :
    (affineInverseLimitSet E K project).Nonempty ∧
      IsCompact (affineInverseLimitSet E K project) ∧
      Convex ℝ (affineInverseLimitSet E K project) := by
  have hfinite := theorem16_finiteLayerConsistency_of_directedProjections
    E K hKnonempty project hprojectComp hprojectMaps
  obtain ⟨hne, hcompact⟩ := affineInverseLimitSet_nonempty_compact_of_relativeContinuous
    E K hKcompact hKnonempty project hprojectContinuousOn hfinite
  exact ⟨hne, hcompact,
    affineInverseLimitSet_convex E K project hprojectAffineOnK hKconvex⟩

/-- TCZ間の層間射影を部分型上の写像として表す。 -/
def affineLayerProjection {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    {β α : I} (hβα : β ≤ α) :
    {x : E α // x ∈ K α} → {y : E β // y ∈ K β} :=
  fun x => ⟨project hβα x.1, hprojectMaps hβα x.2⟩

/-- 各層のTCZ上で定義されたフィードバックが射影と可換なら、
逆極限上に誘導される自己写像。周囲空間全体への延長は要求しない。 -/
def inducedAffineInverseLimitMap {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (f : ∀ i, {x : E i // x ∈ K i} → {x : E i // x ∈ K i})
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K α}),
      affineLayerProjection E K project hprojectMaps hβα (f α x) =
        f β (affineLayerProjection E K project hprojectMaps hβα x))
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project}) :
    {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} := by
  refine ⟨fun i => f i ⟨x.1 i, x.2.1 i⟩, ?_⟩
  constructor
  · intro i
    exact (f i ⟨x.1 i, x.2.1 i⟩).2
  · intro β α hβα
    have h := hcomm hβα ⟨x.1 α, x.2.1 α⟩
    apply congrArg Subtype.val at h
    have hargs : affineLayerProjection E K project hprojectMaps hβα
        ⟨x.1 α, x.2.1 α⟩ = ⟨x.1 β, x.2.1 β⟩ := by
      apply Subtype.ext
      exact x.2.2 hβα
    change project hβα (f α ⟨x.1 α, x.2.1 α⟩).1 =
      (f β ⟨x.1 β, x.2.1 β⟩).1
    simpa only [affineLayerProjection] using h.trans
      (congrArg (fun z : {y : E β // y ∈ K β} => (f β z).1)
        hargs)

/-- 層別連続フィードバックから逆極限上の誘導自己写像への連続性。 -/
theorem inducedAffineInverseLimitMap_continuous {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (f : ∀ i, {x : E i // x ∈ K i} → {x : E i // x ∈ K i})
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K α}),
      affineLayerProjection E K project hprojectMaps hβα (f α x) =
        f β (affineLayerProjection E K project hprojectMaps hβα x))
    (hf : ∀ i, Continuous (f i)) :
    Continuous (inducedAffineInverseLimitMap E K project hprojectMaps f hcomm) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hcoord : Continuous (fun x : {x : ∀ i, E i //
      x ∈ affineInverseLimitSet E K project} =>
        (⟨x.1 i, x.2.1 i⟩ : {y : E i // y ∈ K i})) := by
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  exact continuous_subtype_val.comp ((hf i).comp hcoord)

/-- 定理16の逆極限条件から、層別連続フィードバックが誘導する逆極限自己写像の固定点が
存在する。逆極限の非空・コンパクト・凸性とFan–Glicksbergを合成するため、縮小性は不要。
原文対応で最大元なし・射影恒等則も引数に含むが、この証明では不要。有限層整合性は、
上向き有向性・層ごとの非空性・射影の合成則・TCZ像包含から導き、独立仮定にしない。 -/
theorem theorem16_fixedPoint_exists_of_originalLayerConditions
    {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (hKconvex : ∀ i, Convex ℝ (K i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (hprojectRefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (hprojectContinuousOn : ∀ (j : ProjectionConstraintIndex I),
      ContinuousOn (project j.2) (K j.1.2))
    (hnoMax : ∀ i : I, ∃ j, i < j)
    (f : ∀ i, {x : E i // x ∈ K i} → {x : E i // x ∈ K i})
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K α}),
      affineLayerProjection E K project hprojectMaps hβα (f α x) =
        f β (affineLayerProjection E K project hprojectMaps hβα x))
    (hf : ∀ i, Continuous (f i)) :
    ∃ x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project},
      inducedAffineInverseLimitMap E K project hprojectMaps f hcomm x = x := by
  obtain ⟨hne, hcompact, hconvex⟩ := theorem16_inverseLimit_of_originalLayerConditions
    E K hKcompact hKnonempty hKconvex project hprojectAffineOnK hprojectRefl
    hprojectComp hprojectMaps hprojectContinuousOn hnoMax
  let F := inducedAffineInverseLimitMap E K project hprojectMaps f hcomm
  have hfixedContinuous : Continuous F :=
    inducedAffineInverseLimitMap_continuous E K project hprojectMaps f hcomm hf
  let Φ : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} → Set (∀ i, E i) :=
    fun x => {(F x : ∀ i, E i)}
  have hgraph : IsClosedGraph Φ := by
    change IsClosed {p : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} ×
      (∀ i, E i) | p.2 = (F p.1 : ∀ i, E i)}
    exact isClosed_eq continuous_snd
      (continuous_subtype_val.comp (hfixedContinuous.comp continuous_fst))
  have hvalues : ∀ x, Φ x ⊆ affineInverseLimitSet E K project ∧
      Convex ℝ (Φ x) ∧ (Φ x).Nonempty := by
    intro x
    refine ⟨?_, convex_singleton _, ⟨F x, Set.mem_singleton _⟩⟩
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using (F x).property
  obtain ⟨x, hx⟩ := fanGlicksbergFixedPoint
    (affineInverseLimitSet E K project) hcompact hconvex hne Φ hgraph hvalues
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp hx).symm

/-- 逆極限のコンパクト・凸性が定理16の層条件から得られた後は、層別写像への分解を
要求せず、逆極限全体上の任意の連続自己写像について固定点が存在する。原文のFが層別
連続写像から誘導されるとは限らない場合の定理16→25用入口。 -/
theorem theorem16_fixedPoint_exists_of_continuous_inverseLimitMap
    {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (hKconvex : ∀ i, Convex ℝ (K i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (hprojectRefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (hprojectContinuousOn : ∀ (j : ProjectionConstraintIndex I),
      ContinuousOn (project j.2) (K j.1.2))
    (hnoMax : ∀ i : I, ∃ j, i < j)
    (F : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} →
      {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project})
    (hF : Continuous F) :
    ∃ x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project}, F x = x := by
  obtain ⟨hne, hcompact, hconvex⟩ := theorem16_inverseLimit_of_originalLayerConditions
    E K hKcompact hKnonempty hKconvex project hprojectAffineOnK hprojectRefl
    hprojectComp hprojectMaps hprojectContinuousOn hnoMax
  let L := affineInverseLimitSet E K project
  let Φ : {x : ∀ i, E i // x ∈ L} → Set (∀ i, E i) :=
    fun x => {(F x : ∀ i, E i)}
  have hgraph : IsClosedGraph Φ := by
    change IsClosed {p : {x : ∀ i, E i // x ∈ L} × (∀ i, E i) |
      p.2 = (F p.1 : ∀ i, E i)}
    exact isClosed_eq continuous_snd
      (continuous_subtype_val.comp (hF.comp continuous_fst))
  have hvalues : ∀ x, Φ x ⊆ L ∧ Convex ℝ (Φ x) ∧ (Φ x).Nonempty := by
    intro x
    refine ⟨?_, convex_singleton _, ⟨F x, Set.mem_singleton _⟩⟩
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using (F x).property
  obtain ⟨x, hx⟩ := fanGlicksbergFixedPoint L hcompact hconvex hne Φ hgraph hvalues
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp hx).symm

/-- EconlibのFan–Glicksberg APIと同じ意味で、集合値写像のグラフ閉性を表す。 -/
def HasClosedGraph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Φ : X → Set Y) : Prop :=
  IsClosed {p : X × Y | p.2 ∈ Φ p.1}

/-- 局所凸Hausdorff空間の非空コンパクト凸集合上の連続自己写像は固定点を持つ。
EconlibのKakutani–Fan–Glicksberg定理を一元対応 `{f x}` に適用した、定理16の存在節に
対応する一般結果である。縮小性は仮定しない。 -/
theorem exists_fixedPoint_of_fanGlicksberg
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    (K : Set E) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty)
    (f : {x : E // x ∈ K} → {x : E // x ∈ K}) (hf : Continuous f) :
    ∃ x, f x = x := by
  let Φ : {x : E // x ∈ K} → Set E := fun x => {(f x : E)}
  have hgraph : IsClosedGraph Φ := by
    change IsClosed {p : {x : E // x ∈ K} × E | p.2 = (f p.1 : E)}
    exact isClosed_eq continuous_snd
      (continuous_subtype_val.comp (hf.comp continuous_fst))
  have hvalues : ∀ x, Φ x ⊆ K ∧ Convex ℝ (Φ x) ∧ (Φ x).Nonempty := by
    intro x
    refine ⟨?_, convex_singleton _, ⟨f x, Set.mem_singleton _⟩⟩
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using (f x).property
  obtain ⟨x, hx⟩ := fanGlicksbergFixedPoint
    K hKcompact hKconvex hKnonempty Φ hgraph hvalues
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp hx).symm

/-- Fan–Glicksbergの存在とBanach縮小条件を同じ一般設定で合成する。
コンパクト部分集合はambient距離が誘導する距離で完備なので、連続性から存在を得て、
縮小性からその固定点の一意性を得る。原文定理16の縮小節を、toyモデルによらず記述する。 -/
theorem existsUnique_fixedPoint_of_fanGlicksberg_and_contraction
    {E : Type u} [AddCommGroup E] [Module ℝ E] [MetricSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    (K : Set E) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty)
    (f : {x : E // x ∈ K} → {x : E // x ∈ K}) (hf : Continuous f)
    {q : NNReal} (hcontract : ContractingWith q f) :
    ∃! x, f x = x := by
  letI : CompleteSpace {x : E // x ∈ K} := hKcompact.isComplete.completeSpace_coe
  letI : Nonempty {x : E // x ∈ K} :=
    ⟨⟨Classical.choose hKnonempty, Classical.choose_spec hKnonempty⟩⟩
  obtain ⟨x, hx⟩ := exists_fixedPoint_of_fanGlicksberg K hKcompact hKconvex
    hKnonempty f hf
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (hcontract.fixedPoint_unique' hx hy).symm

/-- 原文定理16の存在節と縮小条件節を、定量的反復評価まで含めて合成する。
`q<1` のもと、任意の初期点からBanach固定点へ収束し、誤差は初期残差に比例して
`q^n/(1-q)` 以下となる。 -/
theorem existsUnique_fixedPoint_and_geometricIterates_of_fanGlicksberg_and_contraction
    {E : Type u} [AddCommGroup E] [Module ℝ E] [MetricSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    (K : Set E) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty)
    (f : {x : E // x ∈ K} → {x : E // x ∈ K}) (hf : Continuous f)
    {q : NNReal} (hcontract : ContractingWith q f)
    (x₀ : {x : E // x ∈ K}) :
    ∃! x, f x = x ∧
      Filter.Tendsto (fun n : Nat => f^[n] x₀) Filter.atTop (nhds x) ∧
      ∀ n : Nat, dist (f^[n] x₀) x ≤
        dist x₀ (f x₀) * (q : ℝ) ^ n / (1 - (q : ℝ)) := by
  letI : CompleteSpace {x : E // x ∈ K} := hKcompact.isComplete.completeSpace_coe
  letI : Nonempty {x : E // x ∈ K} := ⟨x₀⟩
  obtain ⟨x, hx⟩ := exists_fixedPoint_of_fanGlicksberg K hKcompact hKconvex
    hKnonempty f hf
  have hxbanach : x = ContractingWith.fixedPoint f hcontract :=
    hcontract.fixedPoint_unique' (x := x)
      (y := ContractingWith.fixedPoint f hcontract) hx hcontract.fixedPoint_isFixedPt
  refine ⟨x, ⟨hx, ?_, ?_⟩, ?_⟩
  · simpa [hxbanach] using hcontract.tendsto_iterate_fixedPoint x₀
  · intro n
    simpa [hxbanach] using hcontract.apriori_dist_iterate_fixedPoint_le x₀ n
  · intro y hy
    exact hcontract.fixedPoint_unique' (x := y) (y := x) hy.1 hx

/-- 連続自己写像を一元集合値対応にしたとき、そのグラフはHausdorff ambientで閉じる。
これにより連続性からFan–Glicksbergの閉グラフ仮定への移行を明示する。 -/
theorem singletonCorrespondence_hasClosedGraph
    {E : Type u} [TopologicalSpace E] [T2Space E]
    {K : Set E} (f : {x : E // x ∈ K} → {x : E // x ∈ K})
    (hf : Continuous f) :
    HasClosedGraph (fun x : {x : E // x ∈ K} => ({(f x : E)} : Set E)) := by
  change IsClosed {p : {x : E // x ∈ K} × E | p.2 = (f p.1 : E)}
  exact isClosed_eq continuous_snd
    (continuous_subtype_val.comp (hf.comp continuous_fst))

/-- 一元集合値対応の値は、もとの自己写像が自己写像である限り、非空・凸でKに含まれる。 -/
theorem singletonCorrespondence_values
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (f : {x : E // x ∈ K} → {x : E // x ∈ K}) :
    ∀ x, ({(f x : E)} : Set E) ⊆ K ∧
      Convex ℝ ({(f x : E)} : Set E) ∧ ({(f x : E)} : Set E).Nonempty := by
  intro x
  refine ⟨?_, convex_singleton _, ⟨f x, Set.mem_singleton _⟩⟩
  intro y hy
  simpa only [Set.mem_singleton_iff.mp hy] using (f x).2

/-- 各層フィードバックを恒等写像に選ぶと、誘導逆極限作用素も恒等写像になる。
したがって、層間可換性や逆系条件だけでは縮小性は得られない。 -/
theorem inducedMap_of_identityLayerFeedback_is_identity
    {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β)) :
    inducedAffineInverseLimitMap E K project hprojectMaps
      (fun i => id)
      (by
        intro β α hβα x
        rfl) = id := by
  funext x
  apply Subtype.ext
  funext i
  rfl

/-- 各層の状態集合と射影からなる逆系。射影の恒等律・合成律を明示する。 -/
structure LayeredState (I : Type u) [Preorder I] where
  State : I → Type u
  project : ∀ {β α : I}, β ≤ α → State α → State β
  project_refl : ∀ (α : I) (x : State α), project (le_rfl) x = x
  project_comp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
    (x : State α),
      project hγβ (project hβα x) = project (hγβ.trans hβα) x

/-- 逆系の射影と整合する層別状態族。 -/
abbrev CompatibleFamily {I : Type u} [Preorder I]
    (sys : LayeredState I) : Type u :=
  {x : ∀ α, sys.State α //
    ∀ ⦃β α : I⦄ (hβα : β ≤ α), sys.project hβα (x α) = x β}

/-- 履歴 h に相対する逆極限（互換な全層状態）の表現。 -/
abbrev SelfState {I : Type u} [Preorder I] (sys : LayeredState I) :=
  CompatibleFamily sys

/-- 積空間上で「α層をβ層へ射影するとβ成分に一致する」という閉条件候補。 -/
def projectionConstraint {I : Type u} [Preorder I] (sys : LayeredState I)
    (j : ProjectionConstraintIndex I) : Set (∀ α, sys.State α) :=
  {x | sys.project j.2 (x j.1.2) = x j.1.1}

/-- 射影写像が連続で各層がHausdorffなら、逆極限の整合方程式は閉条件である。
ここでは射影の連続性を積空間へ合成した形で与える。 -/
theorem projectionConstraint_isClosed
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, T2Space (sys.State α)]
    (hcontinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ α, sys.State α => sys.project j.2 (x j.1.2)))
    (j : ProjectionConstraintIndex I) :
    IsClosed (projectionConstraint sys j) := by
  exact isClosed_eq (hcontinuous j) (continuous_apply j.1.1)

/-- 射影条件をすべて満たす積空間内の逆極限部分集合。 -/
def inverseLimitSet {I : Type u} [Preorder I] (sys : LayeredState I) :
    Set (∀ α, sys.State α) :=
  ⋂ j, projectionConstraint sys j

/-- 射影整合方程式が閉なら逆極限は積空間の閉部分集合である。
各層がコンパクトならTychonoffにより積もコンパクトなので、逆極限もコンパクトとなる。 -/
theorem inverseLimit_isCompact_of_closed_constraints
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, CompactSpace (sys.State α)]
    (hclosed : ∀ j, IsClosed (projectionConstraint sys j)) :
    IsCompact (inverseLimitSet sys) := by
  have hclosedLimit : IsClosed (inverseLimitSet sys) := by
    exact isClosed_iInter hclosed
  exact hclosedLimit.isCompact

/-- Tychonoffと閉部分集合定理による逆極限のコンパクト性。 -/
theorem inverseLimit_isCompact_of_continuous_projections
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, CompactSpace (sys.State α)]
    [∀ α, T2Space (sys.State α)]
    (hcontinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ α, sys.State α => sys.project j.2 (x j.1.2))) :
    IsCompact (inverseLimitSet sys) := by
  exact inverseLimit_isCompact_of_closed_constraints sys
    (projectionConstraint_isClosed sys hcontinuous)

/-- 原文の「任意の有限層族に整合点がある」条件を、射影方程式族の有限交叉性へ
移す。未指定層は非空性から任意に埋めるので、有限制約の端点だけが整合すればよい。 -/
theorem finite_layer_compatibility_implies_constraint_fip
    {I : Type u} [Preorder I] (sys : LayeredState I)
    (hnonempty : ∀ α, Nonempty (sys.State α))
    (hfinite : ∀ t : Finset I,
      ∃ z : ∀ α, α ∈ t → sys.State α,
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          sys.project hβα (z α hα) = z β hβ) :
    ∀ s : Finset (ProjectionConstraintIndex I),
      (⋂ j ∈ s, projectionConstraint sys j).Nonempty := by
  classical
  intro s
  let layers : Finset I := s.biUnion (fun j => {j.1.1, j.1.2})
  obtain ⟨z, hz⟩ := hfinite layers
  let x : ∀ α, sys.State α := fun α =>
    if hα : α ∈ layers then z α hα else Classical.choice (hnonempty α)
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter]
  intro j hj
  have hβ : j.1.1 ∈ layers := by
    simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨j, hj, Or.inl rfl⟩
  have hα : j.1.2 ∈ layers := by
    simp only [layers, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨j, hj, Or.inr rfl⟩
  change sys.project j.2 (x j.1.2) = x j.1.1
  simp only [x, dite_eq_left hα, dite_eq_left hβ]
  exact hz j.2 hβ hα

/-- 各層がコンパクトで、射影整合方程式が閉じ、任意の有限個の方程式が同時に
満たせるなら逆極限は非空である。有限層族の整合性から方程式族の有限整合性を導く
仕上げは、層別モデルの具体的射影に即した別補題として扱う。 -/
theorem inverseLimit_nonempty_of_closed_finite_compatibility
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, CompactSpace (sys.State α)]
    (hclosed : ∀ j, IsClosed (projectionConstraint sys j))
    (hfip : ∀ s : Finset (ProjectionConstraintIndex I),
      (⋂ j ∈ s, projectionConstraint sys j).Nonempty) :
    Nonempty (CompatibleFamily sys) := by
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfip
  have hx' : ∀ j, x ∈ projectionConstraint sys j := by
    simpa only [Set.mem_iInter] using hx
  refine ⟨⟨x, ?_⟩⟩
  intro β α hβα
  have hcoord := hx' (⟨(β, α), hβα⟩ : ProjectionConstraintIndex I)
  change sys.project hβα (x α) = x β at hcoord
  exact hcoord

/-- 原文のコンパクトHausdorff層・連続射影の設定では、整合条件の閉性は自動である。
有限層整合性から有限方程式族の同時解を得る部分は `hfip` に明示される。 -/
theorem inverseLimit_nonempty_of_continuous_finite_compatibility
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, CompactSpace (sys.State α)]
    [∀ α, T2Space (sys.State α)]
    (hnonempty : ∀ α, Nonempty (sys.State α))
    (hcontinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ α, sys.State α => sys.project j.2 (x j.1.2)))
    (hfinite : ∀ t : Finset I,
      ∃ z : ∀ α, α ∈ t → sys.State α,
        ∀ ⦃β α : I⦄ (hβα : β ≤ α) (hβ : β ∈ t) (hα : α ∈ t),
          sys.project hβα (z α hα) = z β hβ) :
    Nonempty (CompatibleFamily sys) := by
  have hfip := finite_layer_compatibility_implies_constraint_fip sys hnonempty hfinite
  apply inverseLimit_nonempty_of_closed_finite_compatibility sys
    (projectionConstraint_isClosed sys hcontinuous) hfip

/-- 定理16の層別写像が互換性を保つとき誘導される逆極限上の自己写像。
この定義は固定点の存在を主張せず、写像の構成に必要な可換性だけを入力にする。 -/
def inducedMap {I : Type u} [Preorder I] (sys : LayeredState I)
    (f : ∀ α, sys.State α → sys.State α)
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : sys.State α),
      sys.project hβα (f α x) = f β (sys.project hβα x))
    (x : CompatibleFamily sys) : CompatibleFamily sys := by
  refine ⟨fun α => f α (x.1 α), ?_⟩
  intro β α hβα
  rw [hcomm hβα (x.1 α), x.2 hβα]

/-- 連続な層別フィードバックが互換性を保つなら、誘導される逆極限写像も連続である。
これはSchauder–Tychonoffを逆極限に適用するために必要な接続である。 -/
theorem inducedMap_continuous {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)]
    (f : ∀ α, sys.State α → sys.State α)
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : sys.State α),
      sys.project hβα (f α x) = f β (sys.project hβα x))
    (hf : ∀ α, Continuous (f α)) :
    Continuous (inducedMap sys f hcomm) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun α =>
    (hf α).comp ((continuous_apply α).comp continuous_subtype_val)

/-- 射影条件と各層固定点条件の有限部分系が常に同時可解なら、逆極限上に固定点がある。
これは連続性・コンパクト性から自動的には出ず、有限段階の固定点整合性を追加条件とする。 -/
theorem inverseLimit_fixedPoint_of_finite_constraint_consistency
    {I : Type u} [Preorder I] (sys : LayeredState I)
    [∀ α, TopologicalSpace (sys.State α)] [∀ α, CompactSpace (sys.State α)]
    [∀ α, T2Space (sys.State α)]
    (f : ∀ α, sys.State α → sys.State α)
    (hcomm : ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : sys.State α),
      sys.project hβα (f α x) = f β (sys.project hβα x))
    (hprojContinuous : ∀ (j : ProjectionConstraintIndex I), Continuous
      (fun x : ∀ α, sys.State α => sys.project j.2 (x j.1.2)))
    (hfcontinuous : ∀ α, Continuous (f α))
    (hfinite : ∀ s : Finset (ProjectionConstraintIndex I ⊕ I),
      ∃ x : ∀ α, sys.State α,
        ∀ j ∈ s, match j with
          | Sum.inl p => x ∈ projectionConstraint sys p
          | Sum.inr α => f α (x α) = x α) :
    ∃ x : CompatibleFamily sys, inducedMap sys f hcomm x = x := by
  classical
  let constraint : ProjectionConstraintIndex I ⊕ I → Set (∀ α, sys.State α) :=
    fun j => match j with
      | Sum.inl p => projectionConstraint sys p
      | Sum.inr α => {x | f α (x α) = x α}
  have hclosed : ∀ j, IsClosed (constraint j) := by
    intro j
    cases j with
    | inl p => exact projectionConstraint_isClosed sys hprojContinuous p
    | inr α =>
        exact isClosed_eq ((hfcontinuous α).comp (continuous_apply α))
          (continuous_apply α)
  have hfip : ∀ s : Finset (ProjectionConstraintIndex I ⊕ I),
      (Set.univ ∩ ⋂ j ∈ s, constraint j).Nonempty := by
    intro s
    obtain ⟨x, hx⟩ := hfinite s
    refine ⟨x, ?_⟩
    constructor
    · simp
    simp only [Set.mem_iInter]
    intro j hj
    cases j with
    | inl p => simpa only [constraint] using hx (Sum.inl p) hj
    | inr α => simpa only [constraint, Set.mem_ofPred_eq] using hx (Sum.inr α) hj
  obtain ⟨x, hx⟩ := IsCompact.inter_iInter_nonempty
    (isCompact_univ : IsCompact (Set.univ : Set (∀ α, sys.State α)))
    constraint hclosed hfip
  have hconstraint : ∀ j, x ∈ constraint j := by
    have hx' := hx.2
    simpa only [Set.mem_iInter] using hx'
  have hcompatible : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      sys.project hβα (x α) = x β := by
    intro β α hβα
    have h := hconstraint (Sum.inl ⟨(β, α), hβα⟩)
    change sys.project hβα (x α) = x β at h
    exact h
  have hfixed : ∀ α, f α (x α) = x α := by
    intro α
    exact hconstraint (Sum.inr α)
  refine ⟨⟨x, hcompatible⟩, ?_⟩
  apply Subtype.ext
  funext α
  exact hfixed α

/-- 固定した履歴に対する固定点の存在を表す命題。固定点一意性を含めない。 -/
def HasFixedPoint {S : Type*} (F : S → S) : Prop :=
  ∃ x, F x = x

/-- 定理16の自己表象データ。コンパクトHausdorffな表象空間、閉じた表象関係、
連続な表象写像を保持する。Injective（単射性）は原文でも必須条件ではない。 -/
structure SelfRepresentation (S Rep : Type*) [TopologicalSpace S]
    [TopologicalSpace Rep] [CompactSpace Rep] [T2Space Rep] where
  relation : Set (Rep × S)
  relation_closed : IsClosed relation
  represent : S → Rep
  represent_continuous : Continuous represent
  represents : ∀ s, (represent s, s) ∈ relation

/-- 固定点が一意であること。 -/
def HasUniqueFixedPoint {S : Type*} (F : S → S) : Prop :=
  ∃ x, F x = x ∧ ∀ y, F y = y → y = x

/-- 原文25-A(2)の法則等式部分を、固定主体 i の全自己過程 `Rᵢ` と将来出力
`Yᵢ⁺` の同時確率法則として25-Dモデルから独立に表す。ここでは入力履歴からの
候補独立性を別フィールドに保持し、層別Γとの同一視は仮定しない。 -/
structure Theorem25SelfProcessLawModel
    (Subject History : Type*) (Representation Output : Subject → Type*)
    (Candidate : Subject → Type*)
    [∀ i : Subject, MeasurableSpace (Representation i)]
    [∀ i : Subject, MeasurableSpace (Output i)] where
  baselineJointLaw : ∀ i : Subject, History →
    MeasureTheory.ProbabilityMeasure (Representation i × Output i)
  intervenedJointLaw : ∀ i : Subject, History → Candidate i →
    MeasureTheory.ProbabilityMeasure (Representation i × Output i)
  candidateIndependentOfInputHistory : ∀ i : Subject, Prop

/-- 原文25-A(2)に対応する型付き条件。候補独立性はこのモデルが渡す抽象命題で、
`IndepFun` による確率的独立性の証明ではない。全履歴・全候補介入で
`(Rᵢ,Yᵢ⁺)` の同時法則が不変となる等式を記す。25-Dとは別条件。 -/
def Theorem25SelfProcessLawModel.Condition25A2
    {Subject History : Type*} {Representation Output : Subject → Type*}
    {Candidate : Subject → Type*}
    [∀ i : Subject, MeasurableSpace (Representation i)]
    [∀ i : Subject, MeasurableSpace (Output i)]
    (M : Theorem25SelfProcessLawModel Subject History Representation Output Candidate)
    (i : Subject) : Prop :=
  M.candidateIndependentOfInputHistory i ∧
    ∀ h s, M.intervenedJointLaw i h s = M.baselineJointLaw i h

/-- 原文25-A(2)の実確率版。外生確率空間上に履歴・候補変数を置き、
自己過程全体と将来出力の同時観測を構造式で与える。候補と履歴の独立性、
および介入前後の可測性は明示的なモデル条件として保持する。 -/
structure Theorem25SelfProcessSCM
    (History : Type*) (U : Type*) (Representation Output Candidate : Type*)
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate] where
  exogenousLaw : MeasureTheory.ProbabilityMeasure U
  inputHistory : U → History
  candidateVariable : U → Candidate
  inputHistoryAEMeasurable : AEMeasurable inputHistory
    (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  candidateAEMeasurable : AEMeasurable candidateVariable
    (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  baselineEquation : History → U → Representation × Output
  intervenedEquation : History → Candidate → U → Representation × Output
  baselineAEMeasurable : ∀ h, AEMeasurable (baselineEquation h)
    (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  intervenedAEMeasurable : ∀ h s, AEMeasurable (intervenedEquation h s)
    (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)

/-- SCMの構造式を外生法則で押し出して、原文25-A(2)の同時法則を生成する。 -/
noncomputable def Theorem25SelfProcessSCM.toLawModel
    {History U Representation Output Candidate : Type*}
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate]
    (M : Theorem25SelfProcessSCM History U Representation Output Candidate) :
    Theorem25SelfProcessLawModel Unit History
      (fun _ => Representation) (fun _ => Output) (fun _ => Candidate) :=
  { baselineJointLaw := fun _ h =>
      M.exogenousLaw.map (M.baselineEquation h)
    intervenedJointLaw := fun _ h s =>
      M.exogenousLaw.map (M.intervenedEquation h s)
    candidateIndependentOfInputHistory := fun _ =>
      ProbabilityTheory.IndepFun M.inputHistory M.candidateVariable
        (MeasureTheory.ProbabilityMeasure.toMeasure M.exogenousLaw) }

/-- 実際の確率変数の独立性と生成された同時法則の不変性から、25-A(2)を得る。 -/
theorem Theorem25SelfProcessSCM.condition25A2
    {History U Representation Output Candidate : Type*}
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate]
    (M : Theorem25SelfProcessSCM History U Representation Output Candidate)
    (hindependent : ProbabilityTheory.IndepFun M.inputHistory M.candidateVariable
      (MeasureTheory.ProbabilityMeasure.toMeasure M.exogenousLaw))
    (hlaw : ∀ h s,
      M.exogenousLaw.map (M.intervenedEquation h s) =
        M.exogenousLaw.map (M.baselineEquation h)) :
    M.toLawModel.Condition25A2 () := by
  constructor
  · exact hindependent
  · exact hlaw

/-- 定理16の自己意識固定点が存在すれば、同変な自己表象も固定点を表す。
この移送は固定点存在（Schauder節）とは独立に、同変性だけから従う。 -/
theorem represented_fixedPoint_of_equivariance
    {S Rep : Type*} [TopologicalSpace S] [TopologicalSpace Rep]
    [CompactSpace Rep] [T2Space Rep]
    (R : SelfRepresentation S Rep)
    (F : S → S) (FRep : Rep → Rep)
    (_hFRepContinuous : Continuous FRep)
    (hequiv : ∀ s, R.represent (F s) = FRep (R.represent s))
    (hexists : HasFixedPoint F) :
    ∃ s, F s = s ∧ FRep (R.represent s) = R.represent s ∧
      (R.represent s, s) ∈ R.relation := by
  obtain ⟨s, hs⟩ := hexists
  refine ⟨s, hs, ?_, R.represents s⟩
  rw [← hequiv s, hs]

/-- コンパクト空間上の任意の閉制約族について、有限整合性から全体の整合点を得る一般補題。
上の逆極限定理は、これを層別射影条件に適用している。 -/
theorem compatible_point_of_closed_finite_constraints
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {ι : Type v} (constraint : ι → Set X)
    (hclosed : ∀ i, IsClosed (constraint i))
    (hfip : ∀ s : Finset ι, (⋂ i ∈ s, constraint i).Nonempty) :
    (⋂ i, constraint i).Nonempty := by
  exact CompactSpace.iInter_nonempty hclosed hfip

/-- Knaster–Tarskiによる固定点存在。これは定理16の局所凸コンパクト条件とは別の
順序論的十分条件（完備束上の単調写像）であり、定理16の仮定から自動的には従わない。 -/
theorem hasFixedPoint_of_completeLattice_monotone
    {α : Type u} [CompleteLattice α] (f : α →o α) : HasFixedPoint f := by
  exact ⟨f.lfp, f.isFixedPt_lfp⟩

/-- MathlibのBanach固定点定理を使う追加条件付きルート。
完備距離空間上で縮小性を仮定すると固定点が存在し、しかも一意となる。
これは原文定理16に明記された縮小条件節の形式化である。
ただし縮小性を定理16のコンパクト凸な逆極限条件から導いてはいない。 -/
theorem hasUniqueFixedPoint_of_contraction
    {α : Type u} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f) :
    HasUniqueFixedPoint f := by
  let x : α := Classical.choice (inferInstance : Nonempty α)
  have hfinite : edist x (f x) ≠ ⊤ := edist_ne_top x (f x)
  obtain ⟨y, hy, _, _⟩ := hf.exists_fixedPoint x hfinite
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact ((hf.eq_or_edist_eq_top_of_fixedPoints hy hz).resolve_right
    (edist_ne_top y z)).symm

/-- 定理16の縮小条件を加えた統合結論。同じ作用素のBanach固定点が一意であり、
その固定点の自己表象も同変作用素の固定点となり、表象関係に属する。 -/
theorem theorem16_uniqueRepresentedFixedPoint_of_contraction
    {S Rep : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
    [TopologicalSpace S] [TopologicalSpace Rep] [CompactSpace Rep] [T2Space Rep]
    (R : SelfRepresentation S Rep)
    (F : S → S) (FRep : Rep → Rep) (K : NNReal)
    (_hFRepContinuous : Continuous FRep)
    (hequiv : ∀ s, R.represent (F s) = FRep (R.represent s))
    (hcontract : ContractingWith K F) :
    ∃! s, F s = s ∧ FRep (R.represent s) = R.represent s ∧
      (R.represent s, s) ∈ R.relation := by
  obtain ⟨s, hs, huniq⟩ := hasUniqueFixedPoint_of_contraction hcontract
  have hrepresented :
      FRep (R.represent s) = R.represent s ∧ (R.represent s, s) ∈ R.relation := by
    refine ⟨?_, R.represents s⟩
    rw [← hequiv s, hs]
  refine ⟨s, ⟨hs, hrepresented⟩, ?_⟩
  intro t ht
  exact huniq t ht.1

/-- 定理16のFan–Glicksberg存在点とBanach点の同一性。
同じ逆極限型SC上の同じ誘導写像Fについて、原文条件から得た任意の固定点は、
SCに追加した完備距離とContractingWith条件のもとでBanach固定点に一致する。
この橋渡しはSC上のMetricSpace・CompleteSpaceと縮小性を追加仮定として要求する。 -/
theorem theorem16_banach_point_agrees_with_existing_fixedPoint
    {SC : Type u} [MetricSpace SC] [CompleteSpace SC] [Nonempty SC]
    {F : SC → SC} {K : NNReal} (hF : ContractingWith K F)
    (s : SC) (hs : F s = s) :
    s = ContractingWith.fixedPoint F hF := by
  obtain ⟨b, _, huniq⟩ := hasUniqueFixedPoint_of_contraction hF
  have hsb : s = b := huniq s hs
  have hbanach : ContractingWith.fixedPoint F hF = b :=
    huniq (ContractingWith.fixedPoint F hF) hF.fixedPoint_isFixedPt
  exact hsb.trans hbanach.symm

/-- 定理16の存在定理の結論を縮小条件で精密化する。
Fan–Glicksbergからすでに得た固定点はBanach固定点と等しく、したがって唯一である。 -/
theorem theorem16_existing_fixedPoint_is_unique_under_contraction
    {SC : Type u} [MetricSpace SC] [CompleteSpace SC] [Nonempty SC]
    {F : SC → SC} {K : NNReal} (hF : ContractingWith K F)
    (hexists : ∃ s : SC, F s = s) :
    ∃! s : SC, F s = s := by
  obtain ⟨s, hs⟩ := hexists
  refine ⟨s, hs, ?_⟩
  intro t ht
  calc
    t = ContractingWith.fixedPoint F hF :=
      theorem16_banach_point_agrees_with_existing_fixedPoint hF t ht
    _ = s := (theorem16_banach_point_agrees_with_existing_fixedPoint hF s hs).symm

/-- 縮小写像ルートの定量的反復収束。Mathlibの固定点 API が与える事前誤差評価と
極限に加え、Lipschitz評価を各反復へ適用して `K^n` の誤差境界を得る。
係数 `K < 1` と完備距離性は、定理16の無条件存在節に対する追加仮定ではなく、
原文が明記する一意性・反復収束の条件節に属する。 -/
theorem contraction_iterates_tendsto_and_rate
    {α : Type u} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f) (x : α) :
    Filter.Tendsto (fun n : ℕ => f^[n] x) Filter.atTop
      (nhds (ContractingWith.fixedPoint f hf)) ∧
      ∀ n : ℕ,
        dist (f^[n] x) (ContractingWith.fixedPoint f hf) ≤
          (K : ℝ) ^ n * dist x (ContractingWith.fixedPoint f hf) := by
  exact ⟨hf.tendsto_iterate_fixedPoint x,
    fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [iterate_succ']
          calc
            dist (f (f^[n] x)) (ContractingWith.fixedPoint f hf) =
                dist (f (f^[n] x)) (f (ContractingWith.fixedPoint f hf)) := by
                  rw [hf.fixedPoint_isFixedPt]
            _ ≤ (K : ℝ) * dist (f^[n] x) (ContractingWith.fixedPoint f hf) :=
              hf.toLipschitzWith.dist_le_mul _ _
            _ ≤ (K : ℝ) * ((K : ℝ) ^ n *
                dist x (ContractingWith.fixedPoint f hf)) :=
              mul_le_mul_of_nonneg_left ih (by exact_mod_cast K.property)
            _ = (K : ℝ) ^ (n + 1) *
                dist x (ContractingWith.fixedPoint f hf) := by
              rw [pow_succ]
              ring⟩

/-- 定理16の固定点存在節と縮小条件節に、自己表象の忠実性・同変性を
まとめた一般結論。存在はFan–Glicksberg等から与え、縮小条件で一意性と
任意初期値からの定量的反復収束を得る。表象作用素の連続性は原文条件として保持する。 -/
theorem theorem16_fullRepresentedFixedPoint_of_exists_and_contraction
    {S Rep : Type*} [TopologicalSpace S] [MetricSpace S] [CompleteSpace S] [Nonempty S]
    [TopologicalSpace Rep] [CompactSpace Rep] [T2Space Rep]
    (R : SelfRepresentation S Rep)
    (F : S → S) (FRep : Rep → Rep) (K : NNReal)
    (_hFRepContinuous : Continuous FRep)
    (hequiv : ∀ s, R.represent (F s) = FRep (R.represent s))
    (hexists : HasFixedPoint F)
    (hcontract : ContractingWith K F) :
    ∃! s, F s = s ∧ FRep (R.represent s) = R.represent s ∧
      (R.represent s, s) ∈ R.relation ∧
      ∀ (x : S) (n : ℕ), dist (F^[n] x) s ≤ (K : ℝ) ^ n * dist x s := by
  obtain ⟨s, hs⟩ := hexists
  have hunique : ∀ t, F t = t → t = s := by
    intro t ht
    calc
      t = ContractingWith.fixedPoint F hcontract :=
        theorem16_banach_point_agrees_with_existing_fixedPoint hcontract t ht
      _ = s :=
        (theorem16_banach_point_agrees_with_existing_fixedPoint hcontract s hs).symm
  have hsame : s = ContractingWith.fixedPoint F hcontract :=
    theorem16_banach_point_agrees_with_existing_fixedPoint hcontract s hs
  have hrepresented :
      FRep (R.represent s) = R.represent s ∧ (R.represent s, s) ∈ R.relation := by
    refine ⟨?_, R.represents s⟩
    rw [← hequiv s, hs]
  refine ⟨s, ?_, ?_⟩
  · refine ⟨hs, hrepresented.1, hrepresented.2, ?_⟩
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [iterate_succ']
        calc
          dist (F (F^[n] x)) s = dist (F (F^[n] x)) (F s) := by rw [hs]
          _ ≤ (K : ℝ) * dist (F^[n] x) s := hcontract.toLipschitzWith.dist_le_mul _ _
          _ ≤ (K : ℝ) * ((K : ℝ) ^ n * dist x s) :=
            mul_le_mul_of_nonneg_left ih (by exact_mod_cast K.property)
          _ = (K : ℝ) ^ (n + 1) * dist x s := by
            rw [pow_succ]
            ring
  · intro t ht
    exact hunique t ht.1

/-- 固定点存在だけから一意性は導けない。恒等写像は二つ以上の元があれば
その全てを固定するため、縮小性などの一意性条件が別途必要である。 -/
theorem identity_has_two_fixedPoints
    {α : Type u} (x y : α) (hxy : x ≠ y) :
    (fun z : α => z) x = x ∧ (fun z : α => z) y = y ∧ x ≠ y :=
  ⟨rfl, rfl, hxy⟩

/-- 非自明な距離空間では恒等写像は縮小写像にならない。
したがって、連続自己写像という定理16の一般条件から縮小性は導けない。 -/
theorem identity_not_contracting_of_distinct
    {α : Type u} [MetricSpace α] (K : NNReal) (x y : α) (hxy : x ≠ y) :
    ¬ ContractingWith K (id : α → α) := by
  rintro ⟨hK, hLip⟩
  have hdist : dist x y ≤ (K : ℝ) * dist x y := by
    simpa using hLip.dist_le_mul x y
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hK' : (K : ℝ) < 1 := by exact_mod_cast hK
  nlinarith

/-- 単位区間の恒等写像は定理16の非空コンパクト凸連続自己写像の条件を満たすが、
その自然な距離では縮小写像にならない。コンパクト凸・連続性から縮小性が出ない例。 -/
theorem identity_on_unitInterval_not_contracting :
    ¬ ∃ K : NNReal, ContractingWith K
      (id : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1) := by
  rintro ⟨K, hK⟩
  exact (identity_not_contracting_of_distinct K
    (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1)
    ⟨1, by norm_num⟩ (by norm_num)) hK

/-- コンパクト凸性と連続性だけでは固定点の一意性は出ない。
単位区間上の恒等写像は全点を固定する、追加条件の必要性を示す例。 -/
theorem identity_on_unitInterval_nonunique :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧
      Convex ℝ (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun x : ℝ => x) (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo (fun x : ℝ => x) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
      ∃ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧
        x ≠ y ∧ (fun z : ℝ => z) x = x ∧ (fun z : ℝ => z) y = y := by
  refine ⟨isCompact_Icc, convex_Icc 0 1, continuousOn_id, ?_, ?_⟩
  · intro x hx
    exact hx
  · refine ⟨0, 1, ?_, ?_, ?_, rfl, rfl⟩
    · norm_num
    · norm_num
    · norm_num

/-- 定理25第1結論に使う履歴別固定点族。
各履歴に固定点があり、その固定点が一意であることだけを保持する。 -/
structure HistoryFixedPoints (History Self : Type*) where
  carrier : History → Self → Prop
  feedback : ∀ h, {s : Self // carrier h s} → {s : Self // carrier h s}
  fixedPoint : ∀ h, {s : Self // carrier h s}
  isFixed : ∀ h, feedback h (fixedPoint h) = fixedPoint h
  unique : ∀ h y, feedback h y = y → y = fixedPoint h

/-- 履歴ごとの連続写像について固定点存在を得て、別途与えた一意性から
`HistoryFixedPoints` を組み立てる。存在はFan–Glicksberg等から、一意性は原文の縮小条件
などから供給できるため、両者を一つの根拠へ混同しない。 -/
noncomputable def historyFixedPointsOfExistenceAndUniqueness
    {History Self : Type*}
    (carrier : History → Self → Prop)
    (feedback : ∀ h, {s : Self // carrier h s} → {s : Self // carrier h s})
    (hexists : ∀ h, ∃ x, feedback h x = x)
    (hunique : ∀ h x y, feedback h x = x → feedback h y = y → x = y) :
    HistoryFixedPoints History Self := by
  classical
  let fixed (h : History) : {s : Self // carrier h s} := Classical.choose (hexists h)
  have hfixed (h : History) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (hexists h)
  exact {
    carrier := carrier
    feedback := feedback
    fixedPoint := fixed
    isFixed := hfixed
    unique := by
      intro h y hy
      exact hunique h y (fixed h) hy (hfixed h)
  }

/-- 履歴ごとの原文型逆極限条件と、その逆極限上に直接定義された連続写像から、
履歴別固定点族を構成する。固定点存在は各履歴に定理16のFan–Glicksberg適用を行い、
一意性は独立条件として受け取るので、原文が縮小条件を置く場合の依存も明示される。 -/
noncomputable def historyFixedPointsOfContinuousInverseLimitMaps
    {History : Type*} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ (h : History) (i : I), Set (E i))
    (hKcompact : ∀ (h : History) (i : I), IsCompact (K h i))
    (hKnonempty : ∀ (h : History) (i : I), (K h i).Nonempty)
    (hKconvex : ∀ (h : History) (i : I), Convex ℝ (K h i))
    (project : ∀ (h : History) {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ (h : History) ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K h α → y ∈ K h α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project h hβα (a • x + b • y) =
          a • project h hβα x + b • project h hβα y)
    (hprojectRefl : ∀ (h : History) (i : I) (x : {x : E i // x ∈ K h i}),
      project h (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ (h : History) {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K h α}),
      project h hγβ (project h hβα x.1) = project h (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ (h : History) ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project h hβα) (K h α) (K h β))
    (hprojectContinuousOn : ∀ (h : History) (j : ProjectionConstraintIndex I),
      ContinuousOn (project h j.2) (K h j.1.2))
    (hnoMax : ∀ i : I, ∃ j, i < j)
    (F : ∀ (h : History), {x : ∀ i, E i //
      x ∈ affineInverseLimitSet E (K h) (fun {β α} hβα => project h hβα)} →
      {x : ∀ i, E i // x ∈ affineInverseLimitSet E (K h)
        (fun {β α} hβα => project h hβα)})
    (hF : ∀ (h : History), Continuous (F h))
    (hunique : ∀ (h : History) x y, F h x = x → F h y = y → x = y) :
    HistoryFixedPoints History (∀ i, E i) := by
  let carrier : History → (∀ i, E i) → Prop := fun h x =>
    x ∈ affineInverseLimitSet E (K h) (fun {β α} hβα => project h hβα)
  let feedback : ∀ h, {x : (∀ i, E i) // carrier h x} →
      {x : (∀ i, E i) // carrier h x} := fun h => F h
  have hexists : ∀ h, ∃ x, feedback h x = x := by
    intro h
    exact theorem16_fixedPoint_exists_of_continuous_inverseLimitMap
      E (K h) (hKcompact h) (hKnonempty h) (hKconvex h)
      (fun {β α} hβα => project h hβα)
      (hprojectAffineOnK h) (hprojectRefl h) (hprojectComp h) (hprojectMaps h)
      (hprojectContinuousOn h) hnoMax (F h) (hF h)
  exact historyFixedPointsOfExistenceAndUniqueness carrier feedback hexists hunique

/-- 各履歴carrier固有の完備距離と縮小性から固定点族を直接構成する。
周囲Self全体の距離空間構造を仮定しない。 -/
noncomputable def historyFixedPointsOfCarrierContractions
    {History Self : Type*}
    (carrier : History → Self → Prop)
    [∀ h, MetricSpace {s : Self // carrier h s}]
    [∀ h, CompleteSpace {s : Self // carrier h s}]
    (feedback : ∀ h, {s : Self // carrier h s} → {s : Self // carrier h s})
    (q : History → NNReal)
    (hnonempty : ∀ h, Nonempty {s : Self // carrier h s})
    (hcontract : ∀ h, ContractingWith (q h) (feedback h)) :
    HistoryFixedPoints History Self := by
  classical
  let fixed (h : History) : {s : Self // carrier h s} := by
    letI : Nonempty {s : Self // carrier h s} := hnonempty h
    exact ContractingWith.fixedPoint (feedback h) (hcontract h)
  have hfixed (h : History) : feedback h (fixed h) = fixed h :=
    (hcontract h).fixedPoint_isFixedPt
  exact {
    carrier := carrier
    feedback := feedback
    fixedPoint := fixed
    isFixed := hfixed
    unique := by
      intro h y hy
      exact (hcontract h).fixedPoint_unique' hy (hfixed h)
  }

/-- 履歴別の状態集合上で各フィードバックが縮小写像なら、Banachの定理から
`HistoryFixedPoints` を構成する。フィードバックはTCZ部分型上で直接与え、
周囲空間全体への延長を要求しない。 -/
noncomputable def historyFixedPointsOfContractions
    {History Self : Type*} [MetricSpace Self]
    (carrier : History → Set Self)
    (feedback : ∀ h, {s : Self // s ∈ carrier h} → {s : Self // s ∈ carrier h})
    (K : History → NNReal)
    (hnonempty : ∀ h, (carrier h).Nonempty)
    (hcomplete : ∀ h, IsComplete (carrier h))
    (hcontract : ∀ h, ContractingWith (K h) (feedback h)) :
    HistoryFixedPoints History Self := by
  classical
  have hfixed : ∀ h, ∃ y : {x : Self // x ∈ carrier h},
      IsFixedPt (feedback h) y := by
    intro h
    letI : CompleteSpace {x : Self // x ∈ carrier h} := (hcomplete h).completeSpace_coe
    let x : {x : Self // x ∈ carrier h} :=
      ⟨Classical.choose (hnonempty h), Classical.choose_spec (hnonempty h)⟩
    have hdist : edist x (feedback h x) ≠ ⊤ := edist_ne_top x (feedback h x)
    obtain ⟨y, hfix, _, _⟩ := (hcontract h).exists_fixedPoint x hdist
    exact ⟨y, hfix⟩
  let fixed (h : History) : {x : Self // x ∈ carrier h} := Classical.choose (hfixed h)
  have hfixed_spec (h : History) : IsFixedPt (feedback h) (fixed h) :=
    Classical.choose_spec (hfixed h)
  exact {
    carrier := carrier
    feedback := feedback
    fixedPoint := fixed
    isFixed := hfixed_spec
    unique := by
      intro h y hfix
      exact (hcontract h).fixedPoint_unique' hfix (hfixed_spec h)
  }

/-- 完備束上の単調写像から、履歴ごとの固定点族を構成する代替ルート。
Knaster–Tarskiが存在を与え、一意性は別仮定 `hunique` として切り分ける。
距離・縮小性は要らないが、定理16のコンパクト凸・連続性条件とは別の十分条件である。 -/
noncomputable def historyFixedPointsOfUniqueMonotoneLattice
    {History α : Type*} [CompleteLattice α]
    (feedback : History → α →o α)
    (hunique : ∀ h x y, feedback h x = x → feedback h y = y → x = y) :
    HistoryFixedPoints History α := by
  classical
  let fixed (h : History) : {x : α // True} := ⟨(feedback h).lfp, trivial⟩
  exact {
    carrier := fun _ _ => True
    feedback := fun h x => ⟨feedback h x.1, trivial⟩
    fixedPoint := fixed
    isFixed := by
      intro h
      apply Subtype.ext
      exact (feedback h).map_lfp
    unique := by
      intro h y hfix
      apply Subtype.ext
      apply hunique h y.1 (feedback h).lfp
      · exact congrArg Subtype.val hfix
      · exact (feedback h).map_lfp
  }

/-- 定理25第1結論（履歴別一意固定点と条件25-A(1)のもとで、共通固定点はない）。 -/
theorem no_common_fixed_point_of_history_separation
    {History Self : Type*} (F : HistoryFixedPoints History Self)
    {h₁ h₂ : History}
    (hsep : (F.fixedPoint h₁).1 ≠ (F.fixedPoint h₂).1) :
    ¬ ∃ s : Self, ∃ hs₁ : F.carrier h₁ s, ∃ hs₂ : F.carrier h₂ s,
      F.feedback h₁ ⟨s, hs₁⟩ = ⟨s, hs₁⟩ ∧
      F.feedback h₂ ⟨s, hs₂⟩ = ⟨s, hs₂⟩ := by
  rintro ⟨s, hs₁mem, hs₂mem, hs₁, hs₂⟩
  have hs₁' : (⟨s, hs₁mem⟩ : {x : Self // F.carrier h₁ x}) = F.fixedPoint h₁ :=
    F.unique h₁ ⟨s, hs₁mem⟩ hs₁
  have hs₂' : (⟨s, hs₂mem⟩ : {x : Self // F.carrier h₂ x}) = F.fixedPoint h₂ :=
    F.unique h₂ ⟨s, hs₂mem⟩ hs₂
  exact hsep (congrArg Subtype.val hs₁' |>.symm.trans (congrArg Subtype.val hs₂'))

/-- Knaster–Tarski存在と仮定した一意性を履歴ごとに使い、定理25第1結論へ接続する。
25-A(1)に対応する履歴固定点分離があれば共通固定点はない。 -/
theorem theorem25_firstConclusion_of_uniqueMonotoneLattice
    {History α : Type*} [CompleteLattice α]
    (feedback : History → α →o α)
    (hunique : ∀ h x y, feedback h x = x → feedback h y = y → x = y)
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfUniqueMonotoneLattice feedback hunique).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfUniqueMonotoneLattice feedback hunique).fixedPoint h₂).1) :
    ¬ ∃ s : α, feedback h₁ s = s ∧ feedback h₂ s = s := by
  rintro ⟨s, hs₁, hs₂⟩
  have hs₁' : s = (feedback h₁).lfp := hunique h₁ s (feedback h₁).lfp hs₁
    (feedback h₁).map_lfp
  have hs₂' : s = (feedback h₂).lfp := hunique h₂ s (feedback h₂).lfp hs₂
    (feedback h₂).map_lfp
  exact hsep (hs₁'.symm.trans hs₂')

/-- 各履歴の縮小写像条件からBanach固定点を取り、条件25-A(1)の履歴分離を使って
定理25第1結論を得る接続定理。縮小性は定理16の条件節・定理25の前提に明記される。
完備距離構造は定理16の位相的な存在条件とは別に要る。 -/
theorem theorem25_firstConclusion_of_historyContractions
    {History Self : Type*} [MetricSpace Self]
    (carrier : History → Set Self)
    (feedback : ∀ h, {s : Self // s ∈ carrier h} → {s : Self // s ∈ carrier h})
    (K : History → NNReal)
    (hnonempty : ∀ h, (carrier h).Nonempty)
    (hcomplete : ∀ h, IsComplete (carrier h))
    (hcontract : ∀ h, ContractingWith (K h) (feedback h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfContractions carrier feedback K hnonempty
      hcomplete hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfContractions carrier feedback K hnonempty
        hcomplete hcontract).fixedPoint h₂).1) :
    ¬ ∃ s : Self, ∃ _hs₁ : carrier h₁ s, ∃ _hs₂ : carrier h₂ s,
      feedback h₁ ⟨s, _hs₁⟩ = ⟨s, _hs₁⟩ ∧
      feedback h₂ ⟨s, _hs₂⟩ = ⟨s, _hs₂⟩ := by
  exact no_common_fixed_point_of_history_separation
    (historyFixedPointsOfContractions carrier feedback K hnonempty
      hcomplete hcontract) hsep

/-- 定理16のコンパクト凸固定点存在を先に使い、縮小性は一意性だけに使う。
Banach存在定理を再度使う方法と異なり、履歴別キャリアの完備性は要求しない。 -/
noncomputable def historyFixedPointsOfExistingPointsAndContractions
    {History Self : Type*} [MetricSpace Self]
    (carrier : History → Set Self)
    (feedback : ∀ h, {s : Self // s ∈ carrier h} → {s : Self // s ∈ carrier h})
    (K : History → NNReal)
    (hexists : ∀ h, ∃ x : {s : Self // s ∈ carrier h}, feedback h x = x)
    (hcontract : ∀ h, ContractingWith (K h) (feedback h)) :
    HistoryFixedPoints History Self := by
  classical
  let fixed (h : History) : {s : Self // s ∈ carrier h} := Classical.choose (hexists h)
  have hfixed (h : History) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (hexists h)
  exact {
    carrier := fun h s => s ∈ carrier h
    feedback := feedback
    fixedPoint := fixed
    isFixed := hfixed
    unique := by
      intro h y hy
      have hsep := (hcontract h).eq_or_edist_eq_top_of_fixedPoints (hfixed h) hy
      have hfinite : edist (fixed h) y ≠ ⊤ := edist_ne_top _ _
      exact (hsep.resolve_right hfinite).symm
  }

/-- 定理16の各履歴固定点存在（例：Fan–Glicksberg）と縮小一意性を合わせて25.1へ進む。
25-A(1)に相当する履歴間の固定点分離を加えれば共通固定点はない。
逆極限キャリアの完備距離性は要求せず、縮小性から存在も導かず、定理16の存在点を使う。 -/
theorem theorem25_firstConclusion_of_theorem16ExistenceAndContraction
    {History Self : Type*} [MetricSpace Self]
    (carrier : History → Set Self)
    (feedback : ∀ h, {s : Self // s ∈ carrier h} → {s : Self // s ∈ carrier h})
    (K : History → NNReal)
    (hexists : ∀ h, ∃ x : {s : Self // s ∈ carrier h}, feedback h x = x)
    (hcontract : ∀ h, ContractingWith (K h) (feedback h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfExistingPointsAndContractions
      carrier feedback K hexists hcontract).fixedPoint h₁).1 ≠
        ((historyFixedPointsOfExistingPointsAndContractions
          carrier feedback K hexists hcontract).fixedPoint h₂).1) :
    ¬ ∃ s : Self, ∃ hs₁ : s ∈ carrier h₁, ∃ hs₂ : s ∈ carrier h₂,
      feedback h₁ ⟨s, hs₁⟩ = ⟨s, hs₁⟩ ∧ feedback h₂ ⟨s, hs₂⟩ = ⟨s, hs₂⟩ := by
  exact no_common_fixed_point_of_history_separation
    (historyFixedPointsOfExistingPointsAndContractions
      carrier feedback K hexists hcontract) hsep

/-- 履歴ごとに異なる層TCZから作る逆極限部分集合。 -/
def historyAffineInverseLimitSet {History : Type v} {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : History → ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β) (h : History) :
    Set (∀ i, E i) := affineInverseLimitSet E (K h) project

/-- 射影と可換する履歴別の層フィードバックが逆極限上に誘導する写像。 -/
def historyInducedAffineInverseLimitMap {History : Type v} {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (K : History → ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K h α) (K h β))
    (f : ∀ h : History, ∀ i, {x : E i // x ∈ K h i} → {x : E i // x ∈ K h i})
    (hcomm : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K h α}),
      affineLayerProjection E (K h) project (hprojectMaps h) hβα (f h α x) =
        f h β (affineLayerProjection E (K h) project (hprojectMaps h) hβα x))
    (h : History) :
    {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E K project h} →
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E K project h} :=
  by
    simpa [historyAffineInverseLimitSet] using
      (inducedAffineInverseLimitMap E (K h) project (hprojectMaps h) (f h) (hcomm h))

/-- 定理16の層ごとの原文条件を履歴族として束ねる。
同一の層 ambient と射影系を使い、TCZ・フィードバックだけが履歴に依存する設定。 -/
structure Theorem16HistoryLayerSystem
    (History : Type v) (I : Type u) [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] where
  carrier : History → ∀ i, Set (E i)
  compact : ∀ h i, IsCompact (carrier h i)
  nonempty : ∀ h i, (carrier h i).Nonempty
  convex : ∀ h i, Convex ℝ (carrier h i)
  project : ∀ {β α : I}, β ≤ α → E α → E β
  projectAffineOnCarrier : ∀ h ⦃β α : I⦄ (hβα : β ≤ α)
    (x y : E α) (a b : ℝ), x ∈ carrier h α → y ∈ carrier h α →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      project hβα (a • x + b • y) = a • project hβα x + b • project hβα y
  projectRefl : ∀ h i (x : {x : E i // x ∈ carrier h i}),
    project (le_rfl : i ≤ i) x.1 = x.1
  projectComp : ∀ h {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
    (x : {x : E α // x ∈ carrier h α}),
    project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1
  projectMaps : ∀ h ⦃β α : I⦄ (hβα : β ≤ α),
    Set.MapsTo (project hβα) (carrier h α) (carrier h β)
  projectContinuousOn : ∀ h (j : ProjectionConstraintIndex I),
    ContinuousOn (project j.2) (carrier h j.1.2)
  noMax : ∀ i : I, ∃ j, i < j
  feedback : ∀ h i,
    {x : E i // x ∈ carrier h i} → {x : E i // x ∈ carrier h i}
  feedbackCommutes : ∀ h ⦃β α : I⦄ (hβα : β ≤ α)
    (x : {x : E α // x ∈ carrier h α}),
    affineLayerProjection E (carrier h) project (projectMaps h) hβα (feedback h α x) =
      feedback h β (affineLayerProjection E (carrier h) project (projectMaps h) hβα x)
  feedbackContinuous : ∀ h i, Continuous (feedback h i)

/-- 履歴ごとに原文§7の逆極限固定点存在定理を適用する。 -/
theorem Theorem16HistoryLayerSystem.fixedPointExists
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E) (h : History) :
    ∃ x : {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h},
      historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h x = x := by
  exact theorem16_fixedPoint_exists_of_originalLayerConditions
    E (M.carrier h) (M.compact h) (M.nonempty h) (M.convex h) M.project
    (M.projectAffineOnCarrier h) (M.projectRefl h) (M.projectComp h)
    (M.projectMaps h) (M.projectContinuousOn h) M.noMax
    (M.feedback h) (M.feedbackCommutes h) (M.feedbackContinuous h)

/-- 履歴別の原文§7層データから得た固定点存在を、表象・縮小・幾何誤差評価まで
つなぐ定理16の完全な固定点結論。距離・縮小性・表象データは原文の追加条件節として入力する。 -/
theorem Theorem16HistoryLayerSystem.fullRepresentedFixedPointConclusion
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    (Rep : History → Type*) [∀ h, TopologicalSpace (Rep h)]
    [∀ h, CompactSpace (Rep h)] [∀ h, T2Space (Rep h)]
    (R : ∀ h, SelfRepresentation
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h} (Rep h))
    (FRep : ∀ h, Rep h → Rep h)
    (hFRepContinuous : ∀ h, Continuous (FRep h))
    (hequiv : ∀ h x, (R h).represent
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h x) = FRep h ((R h).represent x)) :
    ∀ h, ∃! x : {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h},
      historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h x = x ∧
      FRep h ((R h).represent x) = (R h).represent x ∧
      ((R h).represent x, x) ∈ (R h).relation ∧
      ∀ (x₀ : {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
        (n : ℕ),
        dist ((historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h)^[n] x₀) x ≤
          (q h : ℝ) ^ n * dist x₀ x := by
  intro h
  letI := metric h
  letI : CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h} :=
    hcomplete h
  letI : Nonempty
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h} :=
    ⟨Classical.choose (M.fixedPointExists h)⟩
  exact theorem16_fullRepresentedFixedPoint_of_exists_and_contraction
    (S := {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (Rep := Rep h)
    (R h)
    (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
      M.feedback M.feedbackCommutes h)
    (FRep h) (q h) (hFRepContinuous h) (hequiv h)
    (M.fixedPointExists h) (hcontract h)

/-- 定理16の原文条件から履歴ごとの固定点を得て、縮小性は一意性だけに使う履歴族。
Banachの存在定理を使わないため、逆極限の完備距離性は要求しない。
この実装の `ContractingWith` は共通Pi ambientの距離を逆極限部分型へ制限して使う。
原文の「SC上だけの完備距離」より強いambient距離の拡張可能性を含むため、モデル接続条件として扱う。 -/
noncomputable def historyFixedPointsOfTheorem16LayerSystem
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [MetricSpace (∀ i, E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (q : History → NNReal)
    (hcontract : ∀ h, ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h)) : HistoryFixedPoints History (∀ i, E i) := by
  apply historyFixedPointsOfExistingPointsAndContractions
    (historyAffineInverseLimitSet E M.carrier M.project)
    (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
      M.feedback M.feedbackCommutes)
    q
  · intro h
    exact M.fixedPointExists h
  · exact hcontract

/-- 履歴別TCZ・連続整合フィードバックから定理16の固定点を得た後、縮小性による
一意性と25-A(1)の固定点分離を用いて、25.1の共通固定状態不存在へ接続する。
さらに、縮小計量がPi ambient全体へ延長できることを要求する実装版である。 -/
theorem theorem25_firstConclusion_of_originalTheorem16HistorySystem
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [MetricSpace (∀ i, E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (q : History → NNReal)
    (hcontract : ∀ h, ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfTheorem16LayerSystem M q hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfTheorem16LayerSystem M q hcontract).fixedPoint h₂).1) :
    ¬ ∃ x : ∀ i, E i,
      (∃ hx₁ : x ∈ historyAffineInverseLimitSet E M.carrier M.project h₁,
        historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h₁ ⟨x, hx₁⟩ = ⟨x, hx₁⟩) ∧
      (∃ hx₂ : x ∈ historyAffineInverseLimitSet E M.carrier M.project h₂,
        historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h₂ ⟨x, hx₂⟩ = ⟨x, hx₂⟩) := by
  intro hcommon
  rcases hcommon with ⟨x, ⟨hx₁, hfix₁⟩, ⟨hx₂, hfix₂⟩⟩
  exact (no_common_fixed_point_of_history_separation
    (historyFixedPointsOfTheorem16LayerSystem M q hcontract) hsep)
    ⟨x, hx₁, hx₂, hfix₁, hfix₂⟩

/-- 原文どおり各履歴の逆極限SC自体に距離を置く固定点族。
Pi ambient全体への距離拡張を要求せず、SC上の完備距離と縮小性から一意性を使う。
存在は定理16の局所凸位相固定点定理から得るため、ここではBanach存在を重ねて使わない。 -/
noncomputable def historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h)) : HistoryFixedPoints History (∀ i, E i) := by
  classical
  let carrier : History → (∀ i, E i) → Prop :=
    fun h x => x ∈ historyAffineInverseLimitSet E M.carrier M.project h
  let feedback : ∀ h, {x : (∀ i, E i) // carrier h x} →
      {x : (∀ i, E i) // carrier h x} :=
    fun h => historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
      M.feedback M.feedbackCommutes h
  let fixed (h : History) : {x : (∀ i, E i) // carrier h x} :=
    Classical.choose (M.fixedPointExists h)
  have hfixed (h : History) : feedback h (fixed h) = fixed h :=
    Classical.choose_spec (M.fixedPointExists h)
  exact {
    carrier := carrier
    feedback := feedback
    fixedPoint := fun h => fixed h
    isFixed := hfixed
    unique := by
      intro h y hy
      letI := metric h
      have huniq := (hcontract h).fixedPoint_unique' (hfixed h) hy
      exact huniq.symm
  }

/-- 履歴ごとのSCに直接与えた完備距離・縮小性と25-A(1)分離を用いて25.1を導く。
これがPi ambientの距離拡張を避ける原文条件に沿った接続である。 -/
theorem theorem25_firstConclusion_of_originalTheorem16HistorySystemWithSCMetric
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
      M metric hcomplete q hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h₂).1) :
    ¬ ∃ x : ∀ i, E i,
      (∃ hx₁ : x ∈ historyAffineInverseLimitSet E M.carrier M.project h₁,
        historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h₁ ⟨x, hx₁⟩ = ⟨x, hx₁⟩) ∧
      (∃ hx₂ : x ∈ historyAffineInverseLimitSet E M.carrier M.project h₂,
        historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h₂ ⟨x, hx₂⟩ = ⟨x, hx₂⟩) := by
  let F := historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    M metric hcomplete q hcontract
  intro hcommon
  rcases hcommon with ⟨x, ⟨hx₁, hfix₁⟩, ⟨hx₂, hfix₂⟩⟩
  exact (no_common_fixed_point_of_history_separation F hsep)
    ⟨x, hx₁, hx₂, hfix₁, hfix₂⟩

/-- 定理16の履歴別逆極限存在とSC上の完備距離縮小条件を使い、25-A(1)の
「ある二履歴で固定点が異なる」から、25.1の全履歴共通固定点不存在を導く。
25-A(2)の確率法則条件はこの結論の依存に含めない。 -/
theorem theorem25_fullFirstConclusion_of_originalTheorem16HistorySystemWithSCMetric
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    (hhistorySensitive : ∃ h₁ h₂,
      ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h₂).1) :
    ¬ ∃ x : ∀ i, E i,
      ∃ hx : ∀ h, x ∈ historyAffineInverseLimitSet E M.carrier M.project h,
        ∀ h, historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h ⟨x, hx h⟩ = ⟨x, hx h⟩ := by
  let F := historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    M metric hcomplete q hcontract
  obtain ⟨h₁, h₂, hsep⟩ := hhistorySensitive
  intro hcommon
  rcases hcommon with ⟨x, hmem, hfix⟩
  exact (no_common_fixed_point_of_history_separation F hsep)
    ⟨x, hmem h₁, hmem h₂, hfix h₁, hfix h₂⟩

/-- 定理16の逆極限フィードバックを履歴別Banach固定点族へ直接渡し、定理25 (25.1) を得る。
各逆極限の完備性・縮小性と25-A(1)の固定点分離は明示仮定であり、定理16の
局所凸コンパクト固定点存在条件から自動的には導かない。 -/
theorem theorem25_firstConclusion_of_inverseLimitContractions
    {History : Type v} {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [MetricSpace (∀ i, E i)]
    (K : History → ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K h α) (K h β))
    (f : ∀ h : History, ∀ i, {x : E i // x ∈ K h i} → {x : E i // x ∈ K h i})
    (hcomm : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K h α}),
      affineLayerProjection E (K h) project (hprojectMaps h) hβα (f h α x) =
        f h β (affineLayerProjection E (K h) project (hprojectMaps h) hβα x))
    (q : History → NNReal)
    (hnonempty : ∀ h, (historyAffineInverseLimitSet E K project h).Nonempty)
    (hcomplete : ∀ h, IsComplete (historyAffineInverseLimitSet E K project h))
    (hcontract : ∀ h, ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfContractions
      (historyAffineInverseLimitSet E K project)
      (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm)
      q hnonempty hcomplete hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfContractions
        (historyAffineInverseLimitSet E K project)
        (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm)
        q hnonempty hcomplete hcontract).fixedPoint h₂).1) :
    ¬ ∃ x : ∀ i, E i,
      (∃ hx₁ : x ∈ historyAffineInverseLimitSet E K project h₁,
        historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h₁
          ⟨x, hx₁⟩ = ⟨x, hx₁⟩) ∧
      (∃ hx₂ : x ∈ historyAffineInverseLimitSet E K project h₂,
        historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h₂
          ⟨x, hx₂⟩ = ⟨x, hx₂⟩) := by
  let feedback : ∀ h,
      {x : (∀ i, E i) // x ∈ historyAffineInverseLimitSet E K project h} →
      {x : (∀ i, E i) // x ∈ historyAffineInverseLimitSet E K project h} :=
    historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm
  let F := historyFixedPointsOfContractions
    (historyAffineInverseLimitSet E K project) feedback q hnonempty hcomplete hcontract
  intro hcommon
  rcases hcommon with ⟨x, ⟨hx₁, hfix₁⟩, ⟨hx₂, hfix₂⟩⟩
  exact (no_common_fixed_point_of_history_separation F hsep)
    ⟨x, hx₁, hx₂, hfix₁, hfix₂⟩

/-- 履歴別逆極限が採用距離の位相でコンパクトなら、その完備性は別仮定にせず導ける。
定理16のコンパクト逆極限を距離化して定理25へ接続するときに使う補正版。
距離位相が定理16で用いた積位相と一致することは、モデル側の接続条件として必要。 -/
theorem theorem25_firstConclusion_of_compactInverseLimitContractions
    {History : Type v} {I : Type u} [Preorder I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [MetricSpace (∀ i, E i)]
    (K : History → ∀ i, Set (E i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectMaps : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K h α) (K h β))
    (f : ∀ h : History, ∀ i, {x : E i // x ∈ K h i} → {x : E i // x ∈ K h i})
    (hcomm : ∀ h : History, ∀ ⦃β α : I⦄ (hβα : β ≤ α) (x : {x : E α // x ∈ K h α}),
      affineLayerProjection E (K h) project (hprojectMaps h) hβα (f h α x) =
        f h β (affineLayerProjection E (K h) project (hprojectMaps h) hβα x))
    (q : History → NNReal)
    (hnonempty : ∀ h, (historyAffineInverseLimitSet E K project h).Nonempty)
    (hcompact : ∀ h, IsCompact (historyAffineInverseLimitSet E K project h))
    (hcontract : ∀ h, ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h))
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfContractions
      (historyAffineInverseLimitSet E K project)
      (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm)
      q hnonempty (fun h => (hcompact h).isComplete) hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfContractions
        (historyAffineInverseLimitSet E K project)
        (historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm)
        q hnonempty (fun h => (hcompact h).isComplete) hcontract).fixedPoint h₂).1) :
    ¬ ∃ x : ∀ i, E i,
      (∃ hx₁ : x ∈ historyAffineInverseLimitSet E K project h₁,
        historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h₁
          ⟨x, hx₁⟩ = ⟨x, hx₁⟩) ∧
      (∃ hx₂ : x ∈ historyAffineInverseLimitSet E K project h₂,
        historyInducedAffineInverseLimitMap E K project hprojectMaps f hcomm h₂
          ⟨x, hx₂⟩ = ⟨x, hx₂⟩) := by
  exact theorem25_firstConclusion_of_inverseLimitContractions
    E K project hprojectMaps f hcomm q hnonempty
    (fun h => (hcompact h).isComplete) hcontract hsep

/-- 定理21型の強凸ポテンシャルから履歴ごとにEuler勾配更新を作り、
勾配Lipschitz条件とステップ幅条件で縮小性を得て定理25第1結論へ接続する。
Euler離散化・共通完備距離・履歴別強凸性は明示的なモデル条件であり、
定理16の原文だけから得られる結果ではない。 -/
theorem theorem25_firstConclusion_of_historyGradientEulerSteps
    {History E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (carrier : History → Set E)
    (potential : History → E → ℝ) (gradient : History → E → E)
    (η c L : History → ℝ) (K : History → NNReal)
    (hnonempty : ∀ h, (carrier h).Nonempty)
    (hcomplete : ∀ h, IsComplete (carrier h))
    (hconvex : ∀ h, Tomabechi.Theorem21.StronglyConvexOn (carrier h)
      (potential h) (gradient h) (c h))
    (hη : ∀ h, 0 < η h) (hL : ∀ h, 0 ≤ L h)
    (hK : ∀ h, K h < 1)
    (hstep : ∀ h, 1 - 2 * η h * c h + (η h) ^ 2 * (L h) ^ 2 ≤ (K h : ℝ) ^ 2)
    (hgradLip : ∀ h (x : E), x ∈ carrier h → ∀ y, y ∈ carrier h →
      ‖gradient h y - gradient h x‖ ≤ L h * ‖y - x‖)
    (hmaps : ∀ h (x : E), x ∈ carrier h → x - η h • gradient h x ∈ carrier h)
    {h₁ h₂ : History}
    (hsep : ((historyFixedPointsOfContractions carrier
      (fun h x => ⟨x.1 - η h • gradient h x.1, hmaps h x.1 x.2⟩)
      K hnonempty hcomplete (by
        intro h
        exact gradientEulerStep_contracting (carrier h) (potential h)
          (gradient h) (η h) (c h) (L h) (K h) (hconvex h) (hη h)
          (hL h) (hK h) (hstep h) (hgradLip h) (hmaps h))).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfContractions carrier
        (fun h x => ⟨x.1 - η h • gradient h x.1, hmaps h x.1 x.2⟩)
        K hnonempty hcomplete (by
          intro h
          exact gradientEulerStep_contracting (carrier h) (potential h)
            (gradient h) (η h) (c h) (L h) (K h) (hconvex h) (hη h)
            (hL h) (hK h) (hstep h) (hgradLip h) (hmaps h))).fixedPoint h₂).1) :
    ¬ ∃ s : E, ∃ hs₁ : carrier h₁ s, ∃ hs₂ : carrier h₂ s,
      (⟨s - η h₁ • gradient h₁ s, hmaps h₁ s hs₁⟩ :
        {x : E // x ∈ carrier h₁}) = ⟨s, hs₁⟩ ∧
      (⟨s - η h₂ • gradient h₂ s, hmaps h₂ s hs₂⟩ :
        {x : E // x ∈ carrier h₂}) = ⟨s, hs₂⟩ := by
  apply theorem25_firstConclusion_of_historyContractions carrier
    (fun h x => ⟨x.1 - η h • gradient h x.1, hmaps h x.1 x.2⟩)
    K hnonempty hcomplete ?_ hsep
  intro h
  exact gradientEulerStep_contracting (carrier h) (potential h)
    (gradient h) (η h) (c h) (L h) (K h) (hconvex h) (hη h)
    (hL h) (hK h) (hstep h) (hgradLip h) (hmaps h)

/-- 定理25-Dを因果モデルの抽象的な「同時法則」として表すデータ。
`intervenedLaw` は do(Σ=s) 後の (Γ_{d,α}, Y⁺_{d,α}) の同時法則、`baselineLaw` は
候補自性を介入しない基準法則を表す。実際の確率モデルでは、これらを対応する積空間上の
確率測度として具体化する。 -/
structure Theorem25CausalModel
    (D Layer History : Type*) (Candidate Law : D → Layer → Type*) where
  baselineLaw : ∀ d a, History → Law d a
  intervenedLaw : ∀ d a, History → Candidate d a → Law d a
  independentFixedIndividualization : ∀ d a, Candidate d a → Prop

/-- ある介入で関係状態と将来出力の同時法則が基準法則から変化することを、
本形式化における「非冗長な因果効果」とする。 -/
def Theorem25CausalModel.hasNonRedundantCausalEffect
    {D Layer History : Type*} {Candidate Law : D → Layer → Type*}
    (M : Theorem25CausalModel D Layer History Candidate Law)
    (d : D) (a : Layer) (s : Candidate d a) : Prop :=
  ∃ h, M.intervenedLaw d a h s ≠ M.baselineLaw d a h

/-- 操作的な Atman(d,α): 独立・固定的な個体化と、関係状態を超える
非冗長な因果効果を同時にもつ候補自性が存在すること。 -/
def Theorem25CausalModel.hasAtman
    {D Layer History : Type*} {Candidate Law : D → Layer → Type*}
    (M : Theorem25CausalModel D Layer History Candidate Law)
    (d : D) (a : Layer) : Prop :=
  ∃ s, M.independentFixedIndividualization d a s ∧
    M.hasNonRedundantCausalEffect d a s

/-- 条件25-Dの操作的形式。任意の存在・層・履歴・候補介入で同時法則が不変。 -/
def Theorem25CausalModel.FunctionallyComplete
    {D Layer History : Type*} {Candidate Law : D → Layer → Type*}
    (M : Theorem25CausalModel D Layer History Candidate Law) : Prop :=
  ∀ d a h s, M.intervenedLaw d a h s = M.baselineLaw d a h

/-- 定理25第2結論の因果コア: 条件25-Dの法則不変性のもとでは、どの存在・層にも
関係状態を超える因果効果をもつ固定的自性はない。

25-B（全層プロファイル）と25-C（関係網）はモデルの意味づけ・存在構造を与えるが、
この含意には使われない。原文§14.5も25-Dを決定条件と明記する。これは25-B/Cから
25-Dを導いた結果ではなく、25-Dを明示仮定とした結論である。 -/
theorem theorem25_secondConclusion_of_functionalCompleteness
    {D Layer History : Type*} {Candidate Law : D → Layer → Type*}
    (M : Theorem25CausalModel D Layer History Candidate Law)
    (hcomplete : M.FunctionallyComplete) :
    ∀ d a, ¬ M.hasAtman d a := by
  intro d a ⟨s, _hindependent, hcausal⟩
  obtain ⟨h, hchange⟩ := hcausal
  exact hchange (hcomplete d a h s)

/-- (Γ_{d,α},Y⁺_{d,α}) の同時分布を実際の確率測度で与える定理25因果モデル。
基準法則と do(Σ=s) 介入後法則を、それぞれ積可測空間上の一般の確率測度として保持する。
分布族の生成（構造方程式・介入意味論）が条件25-Dを満たすかは別のモデル検証である。 -/
structure Theorem25ProbabilityCausalModel
    (D Layer History : Type*) (Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)] where
  baselineJointLaw : ∀ (d : D) (a : Layer), History →
    MeasureTheory.ProbabilityMeasure (Gamma a × Output a)
  intervenedJointLaw : ∀ (d : D) (a : Layer), History → Candidate a →
    MeasureTheory.ProbabilityMeasure (Gamma a × Output a)
  independentFixedIndividualization : ∀ (d : D) (a : Layer), Candidate a → Prop

/-- 構造因果モデルの簡約表現。外生法則は履歴 h に依存せず、do(H=h) は構造方程式の
入力 h を固定する。`stateEquation` は関係状態 Γ、`outputEquation` は将来出力を与える。
基準過程は `defaultCandidate` を用い、do(Σ=s) では出力方程式へ s を代入する。
ここではH・Σへの介入意味論をこの置換規則で定義し、グラフ手術型の一般SCMまでは主張しない。 -/
structure Theorem25StructuralCausalModel
    (D Layer History U : Type*) [MeasurableSpace U]
    (Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)] where
  defaultCandidate : ∀ a, Candidate a
  exogenousLaw : ∀ (d : D) (a : Layer), MeasureTheory.ProbabilityMeasure U
  stateEquation : ∀ (d : D) (a : Layer), History → U → Candidate a → Gamma a
  outputEquation : ∀ (d : D) (a : Layer), History → U → Candidate a → Output a
  baselineJointAEMeasurable : ∀ d a h,
    AEMeasurable
      (fun u => (stateEquation d a h u (defaultCandidate a),
        outputEquation d a h u (defaultCandidate a)))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  intervenedJointAEMeasurable : ∀ d a h s,
    AEMeasurable
      (fun u => (stateEquation d a h u s, outputEquation d a h u s))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  independentFixedIndividualization : ∀ (d : D) (a : Layer), Candidate a → Prop

/-- 構造方程式と外生変数法則のpushforwardで、基準・介入後の同時分布を生成する。 -/
noncomputable def Theorem25StructuralCausalModel.toProbabilityCausalModel
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate) :
  Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate :=
  { baselineJointLaw := fun d a h => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u (M.defaultCandidate a),
          M.outputEquation d a h u (M.defaultCandidate a)))
    intervenedJointLaw := fun d a h s => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u s, M.outputEquation d a h u s))
    independentFixedIndividualization := M.independentFixedIndividualization }

theorem Theorem25StructuralCausalModel.baselineJointLaw_apply
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (A : Set (Gamma a × Output a))
    (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.baselineJointLaw d a h) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u (M.defaultCandidate a),
          M.outputEquation d a h u (M.defaultCandidate a))) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u (M.defaultCandidate a),
        M.outputEquation d a h u (M.defaultCandidate a))) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.baselineJointAEMeasurable d a h) hA

theorem Theorem25StructuralCausalModel.intervenedJointLaw_apply
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (s : Candidate a)
    (A : Set (Gamma a × Output a)) (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.intervenedJointLaw d a h s) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u s,
          M.outputEquation d a h u s)) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u s, M.outputEquation d a h u s)) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.intervenedJointAEMeasurable d a h s) hA

/-- 確率測度モデルを、法則の型に依存しない因果コアへ忘却する。 -/
def Theorem25ProbabilityCausalModel.toCausalModel
    {D Layer History : Type*} {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate) :
    Theorem25CausalModel D Layer History (fun _ a => Candidate a)
      (fun d a => MeasureTheory.ProbabilityMeasure (Gamma a × Output a)) :=
  { baselineLaw := M.baselineJointLaw
    intervenedLaw := M.intervenedJointLaw
    independentFixedIndividualization := M.independentFixedIndividualization }

/-- 25-Dの同時法則不変性は、関係状態Γから可測に読み出せる表現Rへ射影しても保たれる。
これはRをΓの関数として表せる場合に限り、25-Dから25-A(2)型の法則不変性へ縮約する橋である。
原文は一般にその符号化写像を与えていないため、`encode` とその可測性はモデル接続条件として明示する。 -/
theorem theorem25_functionalCompleteness_projects_to_representation
    {D Layer History : Type*} {Gamma Output Candidate Representation : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Representation a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate)
    (encode : ∀ a, Gamma a → Representation a)
    (_hencode : ∀ a, Measurable (encode a))
    (hcomplete : ∀ d a h s,
      M.intervenedJointLaw d a h s = M.baselineJointLaw d a h) :
    ∀ d a h s,
      (M.intervenedJointLaw d a h s).map
        (fun z => (encode a z.1, z.2)) =
      (M.baselineJointLaw d a h).map
        (fun z => (encode a z.1, z.2)) := by
  intro d a h s
  exact congrArg (fun μ : MeasureTheory.ProbabilityMeasure (Gamma a × Output a) =>
    μ.map (fun z => (encode a z.1, z.2))) (hcomplete d a h s)

/-- 25-D法則モデルの一つの存在・層で、Γを表現空間へ写した後の介入法則不変性。
これは原文25-A(2)そのものではない。原文のR_i=(Self_i,Ego_i,TCZ_i)全体が
一つのΓ_{d,a}から復元されるときに限る、単一層の射影モデルである。 -/
def Theorem25ProbabilityCausalModel.RepresentationSliceLawInvariant
    {D Layer History : Type*} {Gamma Output Candidate Representation : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Representation a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate)
    (i : D) (a : Layer) (encode : Gamma a → Representation a) : Prop :=
  ∀ h s,
    (M.intervenedJointLaw i a h s).map (fun z => (encode z.1, z.2)) =
      (M.baselineJointLaw i a h).map (fun z => (encode z.1, z.2))

/-- 全索引25-Dは、各層Γから表現変数への符号化が与えられれば、
その一層射影の介入法則不変性を含意する。原文25-A(2)との同定には
自己過程全体を復元する追加の符号化条件が要る。 -/
theorem theorem25_representationSliceLawInvariant_of_functionalCompleteness
    {D Layer History : Type*} {Gamma Output Candidate Representation : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Representation a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate)
    (i : D) (a : Layer) (encode : Gamma a → Representation a)
    (_hencode : Measurable (fun z : Gamma a × Output a => (encode z.1, z.2)))
    (hcomplete : ∀ d a h s,
      M.intervenedJointLaw d a h s = M.baselineJointLaw d a h) :
    M.RepresentationSliceLawInvariant i a encode := by
  intro h s
  exact congrArg (fun μ : MeasureTheory.ProbabilityMeasure (Gamma a × Output a) =>
    μ.map (fun z => (encode z.1, z.2))) (hcomplete i a h s)

/-- 可測な符号化に可測な左逆があれば、その符号化後の確率法則等式から元の法則等式を
復元できる。従って `Γ ↔ R` が可測同型で、同じ全添字・介入で不変性が成立する場合、
`(R,Y⁺)` の法則条件と `(Γ,Y⁺)` の法則条件は同値になる。 -/
theorem probabilityMeasure_eq_of_measurable_leftInverse_pushforward
    {Ω Representation : Type*} [MeasurableSpace Ω] [MeasurableSpace Representation]
    (μ ν : MeasureTheory.ProbabilityMeasure Ω)
    (encode : Ω → Representation) (decode : Representation → Ω)
    (hencode : Measurable encode) (hdecode : Measurable decode)
    (hleft : ∀ x, decode (encode x) = x)
    (hpush : μ.map encode = ν.map encode) : μ = ν := by
  have hpush' := congrArg (fun ρ : MeasureTheory.ProbabilityMeasure Representation =>
    ρ.map decode) hpush
  have hmeasure := congrArg MeasureTheory.ProbabilityMeasure.toMeasure hpush'
  have hmap :
      ((MeasureTheory.ProbabilityMeasure.toMeasure μ).map encode).map decode =
        ((MeasureTheory.ProbabilityMeasure.toMeasure ν).map encode).map decode := by
    simpa only [MeasureTheory.ProbabilityMeasure.toMeasure_map] using hmeasure
  have hcomp : decode ∘ encode = id := by
    funext x
    exact hleft x
  rw [MeasureTheory.Measure.map_map hdecode hencode,
    MeasureTheory.Measure.map_map hdecode hencode, hcomp,
    MeasureTheory.Measure.map_id] at hmap
  apply Subtype.ext
  simpa using hmap

/-- RがΓを可測に完全復元し、`(R,Y⁺)`法則不変性が全存在・全層にわたるなら、
関係的な25-Dが従う。これは25-A(2)をそのまま使う定理ではなく、原文にない全索引への
拡張条件を明示した逆向きブリッジである。 -/
theorem theorem25_globalCompleteness_of_allEncodedRepresentationLaws
    {D Layer History : Type*} {Gamma Output Candidate Representation : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Representation a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate)
    (encode : ∀ a, Gamma a → Representation a)
    (decode : ∀ a, Representation a → Gamma a)
    (hencode : ∀ a, Measurable (fun z : Gamma a × Output a =>
      (encode a z.1, z.2)))
    (hdecode : ∀ a, Measurable (fun z : Representation a × Output a =>
      (decode a z.1, z.2)))
    (hleft : ∀ a γ, decode a (encode a γ) = γ)
    (hrepresentation : ∀ d a h s,
      (M.intervenedJointLaw d a h s).map (fun z => (encode a z.1, z.2)) =
        (M.baselineJointLaw d a h).map (fun z => (encode a z.1, z.2))) :
    ∀ d a h s,
      M.intervenedJointLaw d a h s = M.baselineJointLaw d a h := by
  intro d a h s
  exact probabilityMeasure_eq_of_measurable_leftInverse_pushforward
    (M.intervenedJointLaw d a h s) (M.baselineJointLaw d a h)
    (fun z => (encode a z.1, z.2)) (fun z => (decode a z.1, z.2))
    (hencode a) (hdecode a) (by
      intro z
      cases z with
      | mk γ y => simp [hleft a γ])
    (hrepresentation d a h s)

/-- 候補Σを実際の外生確率変数として持つSCM。独立性は各 `do(H=h)` スライスで
Σと関係状態Γの間に `IndepFun` として課し、候補値 s の個体化は s が正の確率で
現れることとして表す。H自体の確率分布・大域的なΣ⊥Hは別途モデル化が必要。 -/
structure Theorem25RandomizedStructuralCausalModel
    (D Layer History U : Type*) [MeasurableSpace U]
    (Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)] where
  exogenousLaw : ∀ (d : D) (a : Layer), MeasureTheory.ProbabilityMeasure U
  candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a
  candidateVariableAEMeasurable : ∀ d a,
    AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  stateEquation : ∀ (d : D) (a : Layer), History → U → Gamma a
  outputEquation : ∀ (d : D) (a : Layer), History → U → Candidate a → Output a
  baselineJointAEMeasurable : ∀ d a h,
    AEMeasurable
      (fun u => (stateEquation d a h u,
        outputEquation d a h u (candidateVariable d a u)))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  intervenedJointAEMeasurable : ∀ d a h s,
    AEMeasurable
      (fun u => (stateEquation d a h u, outputEquation d a h u s))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  candidateIndependentOfState : ∀ (d : D) (a : Layer) (h : History),
    ProbabilityTheory.IndepFun (candidateVariable d a) (stateEquation d a h)
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))

def Theorem25RandomizedStructuralCausalModel.candidateHasPositiveMass
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U
      Gamma Output Candidate)
    (d : D) (a : Layer) (s : Candidate a) : Prop :=
    ∃ _hmeas : MeasurableSet {u | M.candidateVariable d a u = s},
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        {u | M.candidateVariable d a u = s} > 0

def Theorem25RandomizedStructuralCausalModel.independentAcrossHistories
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U
      Gamma Output Candidate)
    (d : D) (a : Layer) : Prop :=
  ∀ h : History,
    ProbabilityTheory.IndepFun (M.candidateVariable d a) (M.stateEquation d a h)
      (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a))

/-- 大域履歴 `H` を外生空間上の確率変数として保持するSCM。
候補Σの `Σ ⟂ (H, Γ[H])` を明示する一方、外生法則は存在・層別に与える。
全存在・層で単一法則を使う原文寄りの型は `Theorem25SharedGlobalHistorySCM`。 -/
structure Theorem25GlobalHistorySCM
    (D Layer U History : Type*) [MeasurableSpace U] [MeasurableSpace History]
    (Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)] where
  exogenousLaw : ∀ (d : D) (a : Layer), MeasureTheory.ProbabilityMeasure U
  globalHistory : U → History
  globalHistoryAEMeasurable : ∀ d a,
    AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a
  candidateVariableAEMeasurable : ∀ d a,
    AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  stateEquation : ∀ (d : D) (a : Layer), History → U → Gamma a
  outputEquation : ∀ (d : D) (a : Layer), History → U → Candidate a → Output a
  baselineJointAEMeasurable : ∀ d a h,
    AEMeasurable
      (fun u => (stateEquation d a h u,
        outputEquation d a h u (candidateVariable d a u)))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  intervenedJointAEMeasurable : ∀ d a h s,
    AEMeasurable
      (fun u => (stateEquation d a h u, outputEquation d a h u s))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  candidateIndependentOfGlobalContext : ∀ (d : D) (a : Layer),
    ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        stateEquation d a (globalHistory u) u))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))
  globalContextAEMeasurable : ∀ d a,
    AEMeasurable (fun u => (globalHistory u,
      stateEquation d a (globalHistory u) u))
      (MeasureTheory.ProbabilityMeasure.toMeasure (exogenousLaw d a))

/-- 一つの確率空間・一つの外生法則のもとで、全存在・層が共有する大域履歴SCM。
`Theorem25GlobalHistorySCM` の索引別法則より原文のモデル全体のHに忠実である。 -/
structure Theorem25SharedGlobalHistorySCM
    (D Layer U History : Type*) [MeasurableSpace U] [MeasurableSpace History]
    (Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)] where
  exogenousLaw : MeasureTheory.ProbabilityMeasure U
  globalHistory : U → History
  globalHistoryAEMeasurable : AEMeasurable globalHistory
    (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a
  candidateVariableAEMeasurable : ∀ d a,
    AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  stateEquation : ∀ (d : D) (a : Layer), History → U → Gamma a
  outputEquation : ∀ (d : D) (a : Layer), History → U → Candidate a → Output a
  baselineJointAEMeasurable : ∀ d a h,
    AEMeasurable
      (fun u => (stateEquation d a h u,
        outputEquation d a h u (candidateVariable d a u)))
      (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  intervenedJointAEMeasurable : ∀ d a h s,
    AEMeasurable
      (fun u => (stateEquation d a h u, outputEquation d a h u s))
      (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  candidateIndependentOfGlobalContext : ∀ (d : D) (a : Layer),
    ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        stateEquation d a (globalHistory u) u))
      (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)
  globalContextAEMeasurable : ∀ d a,
    AEMeasurable (fun u => (globalHistory u,
      stateEquation d a (globalHistory u) u))
      (MeasureTheory.ProbabilityMeasure.toMeasure exogenousLaw)

/-- 共通法則SCMを、法則を索引ごとに複製する既存の一般APIへ埋め込む。 -/
noncomputable def Theorem25SharedGlobalHistorySCM.toIndexed
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate) :
    Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate :=
  { exogenousLaw := fun _ _ => M.exogenousLaw
    globalHistory := M.globalHistory
    globalHistoryAEMeasurable := fun _ _ => M.globalHistoryAEMeasurable
    candidateVariable := M.candidateVariable
    candidateVariableAEMeasurable := fun _ _ => M.candidateVariableAEMeasurable _ _
    stateEquation := M.stateEquation
    outputEquation := M.outputEquation
    baselineJointAEMeasurable := M.baselineJointAEMeasurable
    intervenedJointAEMeasurable := M.intervenedJointAEMeasurable
    candidateIndependentOfGlobalContext := M.candidateIndependentOfGlobalContext
    globalContextAEMeasurable := M.globalContextAEMeasurable }

/-- 定理16の履歴別固定点族を自己過程状態・将来出力の生成元とする共有法則SCM。
`stateCode` は固定点から関係状態Γを、`outputCode` はその固定点から現行過程の出力を読む。
したがって do(Σ=s) は候補変数だけを置換し、固定点由来の状態・出力は変えない。
候補独立性と可測性は明示入力であり、定理16の固定点条件から導いたとはしない。 -/
noncomputable def Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints
    {D Layer U History Self : Type*} [MeasurableSpace U]
    [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (F : HistoryFixedPoints History Self)
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (stateCode : ∀ (d : D) (a : Layer), Self → Gamma a)
    (outputCode : ∀ (d : D) (a : Layer), Self → Output a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        stateCode d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        stateCode d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law)) :
    Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate := by
  refine ⟨law, globalHistory, hHistory, candidateVariable, hCandidate,
    (fun d a h _ => stateCode d a (F.fixedPoint h).1),
    (fun d a h _ _ => outputCode d a (F.fixedPoint h).1), ?_, ?_,
    hIndependent, hContext⟩
  · intro d a h
    exact measurable_const.aemeasurable
  · intro d a h s
    exact measurable_const.aemeasurable

/-- 原文条件を満たす定理16の層データから固定点族を生成し、その固定点を状態・出力へ
符号化する25の共有法則SCMへ渡す。SC上の距離・完備性・縮小性と、確率的候補独立性は
明示入力である。出力符号化が候補値を参照しない条件では25-Dが成立するが、これは
定理16だけから出る性質ではない。 -/
noncomputable def Theorem25SharedGlobalHistorySCM.ofTheorem16LayerSystem
    {D Layer U History : Type*} {I : Type u} {E : I → Type u}
    [MeasurableSpace U] [MeasurableSpace History]
    [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (stateCode : ∀ (d : D) (a : Layer), (∀ i, E i) → Gamma a)
    (outputCode : ∀ (d : D) (a : Layer), (∀ i, E i) → Output a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        stateCode d a ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
          M metric hcomplete q hcontract).fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        stateCode d a ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
          M metric hcomplete q hcontract).fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law)) :
    Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate := by
  exact Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints
    (historyFixedPointsOfTheorem16LayerSystemWithSCMetric M metric hcomplete q hcontract)
    law globalHistory candidateVariable stateCode outputCode hHistory hCandidate
    hIndependent hContext

/-- 旧APIの外生法則がすべて等しい場合、その共通値を取り出して共有法則SCMへ移す。 -/
noncomputable def Theorem25GlobalHistorySCM.toShared
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (μ : MeasureTheory.ProbabilityMeasure U)
    (hcommon : ∀ d a, M.exogenousLaw d a = μ)
    (hHistory : AEMeasurable M.globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure μ))
    (hCandidate : ∀ d a, AEMeasurable (M.candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure μ)) :
    Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate :=
  { exogenousLaw := μ
    globalHistory := M.globalHistory
    globalHistoryAEMeasurable := hHistory
    candidateVariable := M.candidateVariable
    candidateVariableAEMeasurable := by
      intro d a
      exact hCandidate d a
    stateEquation := M.stateEquation
    outputEquation := M.outputEquation
    baselineJointAEMeasurable := by
      intro d a h
      simpa [hcommon d a] using M.baselineJointAEMeasurable d a h
    intervenedJointAEMeasurable := by
      intro d a h s
      simpa [hcommon d a] using M.intervenedJointAEMeasurable d a h s
    candidateIndependentOfGlobalContext := by
      intro d a
      rw [← hcommon d a]
      exact M.candidateIndependentOfGlobalContext d a
    globalContextAEMeasurable := by
      intro d a
      simpa [hcommon d a] using M.globalContextAEMeasurable d a }

def Theorem25GlobalHistorySCM.candidateHasPositiveMass
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (d : D) (a : Layer) (s : Candidate a) : Prop :=
    ∃ _hmeas : MeasurableSet {u | M.candidateVariable d a u = s},
    MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
      {u | M.candidateVariable d a u = s} > 0

/-- 大域履歴変数と履歴別構造方程式をもつSCMから、`do(H=h)` と `do(Σ=s)` の
意味論を区別した同時法則を生成する。基準法則ではΣを自然変数のまま残す。 -/
noncomputable def Theorem25GlobalHistorySCM.toProbabilityCausalModel
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate) :
    Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate :=
  { baselineJointLaw := fun d a h => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u,
          M.outputEquation d a h u (M.candidateVariable d a u)))
    intervenedJointLaw := fun d a h s => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u, M.outputEquation d a h u s))
    independentFixedIndividualization := fun d a s =>
      (show Prop from
        M.candidateHasPositiveMass d a s ∧
          ProbabilityTheory.IndepFun (M.candidateVariable d a)
            (fun u => (M.globalHistory u,
              M.stateEquation d a (M.globalHistory u) u))
      (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a))) }

/-- AEMeasurable条件のもとで、生成法則が外生法則の通常のpushforward適用則を満たす。 -/
theorem Theorem25GlobalHistorySCM.baselineJointLaw_apply
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (A : Set (Gamma a × Output a))
    (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.baselineJointLaw d a h) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u,
          M.outputEquation d a h u (M.candidateVariable d a u))) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u,
        M.outputEquation d a h u (M.candidateVariable d a u))) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.baselineJointAEMeasurable d a h) hA

theorem Theorem25GlobalHistorySCM.intervenedJointLaw_apply
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (s : Candidate a)
    (A : Set (Gamma a × Output a)) (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.intervenedJointLaw d a h s) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u,
          M.outputEquation d a h u s)) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.intervenedJointAEMeasurable d a h s) hA

/-- 大域履歴を含むSCMでも、候補値を自然値から置換して出力方程式が変わらなければ
25-Dが成立し、定理25第2結論に至る。履歴・関係状態との確率的独立性はAtman述語へ渡す。 -/
theorem theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (houtput : ∀ d a h u s,
      M.outputEquation d a h u (M.candidateVariable d a u) =
        M.outputEquation d a h u s) :
    ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h := by
  intro d a h s
  apply Subtype.ext
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) =
    (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u,
        M.outputEquation d a h u (M.candidateVariable d a u)))
  rw [MeasureTheory.Measure.map_congr]
  exact Filter.Eventually.of_forall fun u =>
    congrArg (fun y => (M.stateEquation d a h u, y))
      (houtput d a h u s).symm

/-- 候補値による出力方程式の変化が外生法則の零集合上だけなら、生成される
`(Γ,Y⁺)` の介入法則は基準法則と一致する。点ごとの不変性を a.e. 条件へ弱めた版。 -/
theorem theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (houtput : ∀ d a h s,
      ∀ᵐ u ∂ MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a),
        M.outputEquation d a h u (M.candidateVariable d a u) =
          M.outputEquation d a h u s) :
    ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h := by
  intro d a h s
  apply Subtype.ext
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) =
    (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u,
        M.outputEquation d a h u (M.candidateVariable d a u)))
  rw [MeasureTheory.Measure.map_congr]
  filter_upwards [houtput d a h s] with u hu
  exact congrArg (fun y => (M.stateEquation d a h u, y)) hu.symm

/-- 大域履歴SCMの候補介入が、外生法則を保つ再パラメータ化で基準過程へ移るなら、
同時pushforward法則として25-Dが成立する。出力の点ごとの候補非干渉を仮定しない対称性版。 -/
theorem theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (hsym : ∀ d a h s,
      ∃ τ : U → U,
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a))
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (M.stateEquation d a h u,
            M.outputEquation d a h u (M.candidateVariable d a u))) ∧
        Measurable (fun u =>
          (M.stateEquation d a h u, M.outputEquation d a h u s)) ∧
        (∀ u, (M.stateEquation d a h (τ u),
          M.outputEquation d a h (τ u) s) =
            (M.stateEquation d a h u,
              M.outputEquation d a h u (M.candidateVariable d a u)))) :
    ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h := by
  intro d a h s
  rcases hsym d a h s with ⟨τ, hpres, hτmeas, hbaseMeas, hinterMeas, hpair⟩
  apply Subtype.ext
  let μ := MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
  let baseline := fun u : U =>
    (M.stateEquation d a h u,
      M.outputEquation d a h u (M.candidateVariable d a u))
  let intervened := fun u : U =>
    (M.stateEquation d a h u, M.outputEquation d a h u s)
  change μ.map intervened = μ.map baseline
  have hfun : intervened ∘ τ = baseline := by
    funext u
    exact hpair u
  calc
    μ.map intervened = (μ.map τ).map intervened := by rw [hpres.map_eq]
    _ = μ.map (intervened ∘ τ) := by
      rw [MeasureTheory.Measure.map_map hinterMeas hτmeas]
    _ = μ.map baseline := by rw [hfun]

theorem theorem25_secondConclusion_of_globalHistorySCM_candidateIrrelevance
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (houtput : ∀ d a h u s,
      M.outputEquation d a h u (M.candidateVariable d a u) =
        M.outputEquation d a h u s) :
    ∀ d a,
      ¬ ((M.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_functionalCompleteness
  intro d a h s
  exact theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance
    M houtput d a h s

/-- a.e. の構造方程式不変性から25-Dを得て、定理25第2結論へ接続する。 -/
theorem theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25GlobalHistorySCM D Layer U History Gamma Output Candidate)
    (houtput : ∀ d a h s,
      ∀ᵐ u ∂ MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a),
        M.outputEquation d a h u (M.candidateVariable d a u) =
          M.outputEquation d a h u s) :
    ∀ d a,
      ¬ ((M.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_functionalCompleteness
  intro d a h s
  exact theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance
    M houtput d a h s

/-- 単一の大域外生法則をもつSCMで、候補出力が外生法則下a.e.不変なら25.2が成立する。 -/
theorem theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance
    {D Layer U History : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate)
    (houtput : ∀ d a h s,
      ∀ᵐ u ∂ MeasureTheory.ProbabilityMeasure.toMeasure M.exogenousLaw,
        M.outputEquation d a h u (M.candidateVariable d a u) =
          M.outputEquation d a h u s) :
    ∀ d a,
      ¬ ((M.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance
    M.toIndexed
  intro d a h s
  simpa [Theorem25SharedGlobalHistorySCM.toIndexed] using houtput d a h s

/-- 固定点から状態と出力を生成するSCMでは25-Dが成立し、条件25-A(2)と
大域履歴・固定点由来状態からの候補独立性のもとでAtman候補は存在しない。 -/
theorem theorem25_secondConclusion_of_historyFixedPointGeneratedSCM
    {D Layer U History Self : Type*} [MeasurableSpace U]
    [MeasurableSpace History]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (F : HistoryFixedPoints History Self)
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (stateCode : ∀ (d : D) (a : Layer), Self → Gamma a)
    (outputCode : ∀ (d : D) (a : Layer), Self → Output a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        stateCode d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        stateCode d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law)) :
    ∀ d a, ¬ ((Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints
      F law globalHistory candidateVariable stateCode outputCode hHistory hCandidate
      hIndependent hContext).toIndexed.toProbabilityCausalModel.toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance
    (Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints
      F law globalHistory candidateVariable stateCode outputCode hHistory hCandidate
      hIndependent hContext)
  intro d a h s
  filter_upwards with u
  rfl

/-- ランダムΣを残した基準方程式と、`do(Σ=s)`でΣだけを定数置換した方程式から
同時法則をpushforwardで生成する。Atman候補の独立性・正確率条件も因果モデルへ渡す。 -/
noncomputable def Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U
      Gamma Output Candidate) :
    Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate :=
  { baselineJointLaw := fun d a h => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u,
          M.outputEquation d a h u (M.candidateVariable d a u)))
    intervenedJointLaw := fun d a h s => by
      exact (M.exogenousLaw d a).map (fun u =>
        (M.stateEquation d a h u, M.outputEquation d a h u s))
    independentFixedIndividualization := fun d a s =>
      M.candidateHasPositiveMass d a s ∧ M.independentAcrossHistories d a }

theorem Theorem25RandomizedStructuralCausalModel.baselineJointLaw_apply
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (A : Set (Gamma a × Output a))
    (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.baselineJointLaw d a h) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u,
          M.outputEquation d a h u (M.candidateVariable d a u))) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u,
        M.outputEquation d a h u (M.candidateVariable d a u))) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.baselineJointAEMeasurable d a h) hA

theorem Theorem25RandomizedStructuralCausalModel.intervenedJointLaw_apply
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U Gamma Output Candidate)
    (d : D) (a : Layer) (h : History) (s : Candidate a)
    (A : Set (Gamma a × Output a)) (hA : MeasurableSet A) :
    MeasureTheory.ProbabilityMeasure.toMeasure
        (M.toProbabilityCausalModel.intervenedJointLaw d a h s) A =
      MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
        ((fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) ⁻¹' A) := by
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) A = _
  exact MeasureTheory.Measure.map_apply_of_aemeasurable
    (M.intervenedJointAEMeasurable d a h s) hA

/-- ランダム候補Σが出力方程式から因果的に無関係なら、構造方程式から25-Dの
同時法則不変性が従う。候補独立性だけでなく、この出力不変条件が必要な追加モデル条件である。 -/
theorem theorem25_randomizedStructuralFunctionalCompleteness_of_candidateIrrelevance
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U
      Gamma Output Candidate)
    (houtput : ∀ d a h u s,
      M.outputEquation d a h u (M.candidateVariable d a u) =
        M.outputEquation d a h u s) :
    ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h := by
  intro d a h s
  apply Subtype.ext
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u, M.outputEquation d a h u s)) =
    (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u,
        M.outputEquation d a h u (M.candidateVariable d a u)))
  rw [MeasureTheory.Measure.map_congr]
  exact Filter.Eventually.of_forall fun u =>
    congrArg (fun y => (M.stateEquation d a h u, y))
      (houtput d a h u s).symm

/-- ランダム候補の構造方程式が25-Dを満たす場合の (25.2) 接続。 -/
theorem theorem25_secondConclusion_of_randomizedStructuralCandidateIrrelevance
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25RandomizedStructuralCausalModel D Layer History U
      Gamma Output Candidate)
    (houtput : ∀ d a h u s,
      M.outputEquation d a h u (M.candidateVariable d a u) =
        M.outputEquation d a h u s) :
    ∀ d a, ¬ ((M.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_functionalCompleteness
  intro d a h s
  exact theorem25_randomizedStructuralFunctionalCompleteness_of_candidateIrrelevance
    M houtput d a h s

/-- 積空間上の確率測度で表した条件25-Dから、定理25 (25.2) を得る。 -/
theorem theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    {D Layer History : Type*} {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.intervenedJointLaw d a h s = M.baselineJointLaw d a h) :
    ∀ d a, ¬ (M.toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_functionalCompleteness
  exact hcomplete

/-- 構造方程式で生成した基準・介入法則が25-Dを満たすなら、統計モデルへの忘却を
介して定理25 (25.2) を得る。25-Dそのものは構造方程式から自動では出ず、ここでは
生成されたpushforward法則について明示的に仮定する。 -/
theorem theorem25_secondConclusion_of_structuralFunctionalCompleteness
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h) :
    ∀ d a, ¬ ((M.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    M.toProbabilityCausalModel hcomplete

/-- 各候補介入を基準過程へ移す外生変数の測度保存対称性があれば、構造方程式の
同時pushforward法則から25-Dを導く。候補値ごとの出力一致は要求せず、外生座標の
測度保存な再パラメータ化を認める。 -/
theorem theorem25_structuralFunctionalCompleteness_of_measurePreservingSymmetry
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate)
    (hsym : ∀ d a h s,
      ∃ τ : U → U,
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a))
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (M.stateEquation d a h u (M.defaultCandidate a),
            M.outputEquation d a h u (M.defaultCandidate a))) ∧
        Measurable (fun u =>
          (M.stateEquation d a h u s, M.outputEquation d a h u s)) ∧
        (∀ u, (M.stateEquation d a h (τ u) s,
          M.outputEquation d a h (τ u) s) =
            (M.stateEquation d a h u (M.defaultCandidate a),
              M.outputEquation d a h u (M.defaultCandidate a)))) :
    ∀ d a h s,
      (M.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.toProbabilityCausalModel).baselineJointLaw d a h := by
  intro d a h s
  rcases hsym d a h s with ⟨τ, hpres, hτmeas, hbaseMeas, hinterMeas, hpair⟩
  apply Subtype.ext
  change (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u s, M.outputEquation d a h u s)) =
    (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)).map
      (fun u => (M.stateEquation d a h u (M.defaultCandidate a),
        M.outputEquation d a h u (M.defaultCandidate a)))
  let μ := MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)
  let baseline := fun u : U =>
    (M.stateEquation d a h u (M.defaultCandidate a),
      M.outputEquation d a h u (M.defaultCandidate a))
  let intervened := fun u : U =>
    (M.stateEquation d a h u s, M.outputEquation d a h u s)
  have hfun : intervened ∘ τ = baseline := by
    funext u
    exact hpair u
  change μ.map intervened = μ.map baseline
  calc
    μ.map intervened = (μ.map τ).map intervened := by rw [hpres.map_eq]
    _ = μ.map (intervened ∘ τ) := by
      rw [MeasureTheory.Measure.map_map hinterMeas hτmeas]
    _ = μ.map baseline := by rw [hfun]

/-- 外生変数の測度保存対称性から25-Dを得て、定理25第2結論へ接続する。 -/
theorem theorem25_secondConclusion_of_structuralMeasurePreservingSymmetry
    {D Layer History U : Type*} [MeasurableSpace U]
    {Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25StructuralCausalModel D Layer History U Gamma Output Candidate)
    (hsym : ∀ d a h s,
      ∃ τ : U → U,
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a))
          (MeasureTheory.ProbabilityMeasure.toMeasure (M.exogenousLaw d a)) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (M.stateEquation d a h u (M.defaultCandidate a),
            M.outputEquation d a h u (M.defaultCandidate a))) ∧
        Measurable (fun u =>
          (M.stateEquation d a h u s, M.outputEquation d a h u s)) ∧
        (∀ u, (M.stateEquation d a h (τ u) s,
          M.outputEquation d a h (τ u) s) =
            (M.stateEquation d a h u (M.defaultCandidate a),
              M.outputEquation d a h u (M.defaultCandidate a)))) :
    ∀ d a, ¬ ((M.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  apply theorem25_secondConclusion_of_structuralFunctionalCompleteness M
  exact theorem25_structuralFunctionalCompleteness_of_measurePreservingSymmetry M hsym

/-- 条件25-B/Cのデータ。`profile` は存在ごとの層別表現（`none` は不在記号）を表す。
上位層は全存在・履歴に共通する一元表現 `topMarker` をもつ。`relationEdge` は逆役割ラベル
を含む層間の有向記述で、射影した存在グラフは連結かつ各存在が他者と関係する。 -/
structure Theorem25PresenceRelationModel
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (Gamma : Layer → Type*) where
  profile : D → History → (a : Layer) → Option (Gamma a)
  topMarker : Gamma ⊤
  topRepresentationIsSubsingleton : ∀ x y : Gamma ⊤, x = y
  supportNonempty : ∀ d h, ∃ a, profile d h a ≠ none
  supportUpwardClosed : ∀ d h a b, profile d h a ≠ none → a ≤ b →
    profile d h b ≠ none
  topLayerHasCommonMarker : ∀ d h, profile d h ⊤ = some topMarker
  roleInverse : Role → Role
  roleInverseInvolutive : ∀ r, roleInverse (roleInverse r) = r
  relationEdge : History → D → Layer → Role → D → Layer → Prop
  relationEdgeReverses : ∀ h d a r e b,
    relationEdge h d a r e b ↔ relationEdge h e b (roleInverse r) d a
  everyExistenceIsRelated : ∀ h d, ∃ e a b r,
    e ≠ d ∧ relationEdge h d a r e b
  relationGraphConnected : ∀ h d e,
    Relation.ReflTransGen
      (fun x y => x ≠ y ∧ ∃ a b r, relationEdge h x a r y b) d e

/-- 原文25-C2の、関係辺を存在索引へ射影した基礎無向グラフの一歩。 -/
def Theorem25PresenceRelationModel.horizontalRelationAdjacent
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Gamma : Layer → Type*}
    (M : Theorem25PresenceRelationModel D History Layer Role Gamma)
    (h : History) (x y : D) : Prop :=
  x ≠ y ∧ ∃ a b r,
    M.relationEdge h x a r y b ∨ M.relationEdge h y b r x a

/-- 25-C1の逆役割対により、無向射影グラフの辺は両向きの有向関係辺と同値。 -/
theorem Theorem25PresenceRelationModel.directedStep_iff_horizontalAdjacency
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Gamma : Layer → Type*}
    (M : Theorem25PresenceRelationModel D History Layer Role Gamma)
    (h : History) (x y : D) :
    (x ≠ y ∧ ∃ a b r, M.relationEdge h x a r y b) ↔
      M.horizontalRelationAdjacent h x y := by
  constructor
  · rintro ⟨hne, a, b, r, hedge⟩
    exact ⟨hne, ⟨a, b, r, Or.inl hedge⟩⟩
  · rintro ⟨hne, a, b, r, hedge | hedge⟩
    · exact ⟨hne, ⟨a, b, r, hedge⟩⟩
    · exact ⟨hne, ⟨a, b, M.roleInverse r,
        (M.relationEdgeReverses h y b r x a).mp hedge⟩⟩

/-- 現在の有向 `ReflTransGen` 表現と、原文25-C2の基礎無向グラフ連結性は、
25-C1の逆役割条件のもとで同値である。よって構造体の連結性フィールドは原文より
強い別仮定を密かに置いてはいない。 -/
theorem Theorem25PresenceRelationModel.relationGraphConnected_iff_horizontalConnected
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Gamma : Layer → Type*}
    (M : Theorem25PresenceRelationModel D History Layer Role Gamma)
    (h : History) (x y : D) :
    Relation.ReflTransGen
        (M.horizontalRelationAdjacent h) x y ↔
      Relation.ReflTransGen
        (fun u v => u ≠ v ∧ ∃ a b r, M.relationEdge h u a r v b) x y := by
  constructor
  · apply Relation.ReflTransGen.mono
    intro u v huv
    exact (M.directedStep_iff_horizontalAdjacency h u v).mpr huv
  · apply Relation.ReflTransGen.mono
    intro u v huv
    exact (M.directedStep_iff_horizontalAdjacency h u v).mp huv

/-- 確率的因果法則・25-B存在プロファイル・25-C関係網を、同じ存在・層・履歴添字と
同じ層状態型 `Gamma` で束ねる。これにより各分野が同一モデルの添字を共有する。 -/
structure Theorem25IntegratedModel
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (Representation Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)] where
  probability : Theorem25ProbabilityCausalModel D Layer History Gamma Output Candidate
  presenceAndRelations : Theorem25PresenceRelationModel D History Layer Role Representation
  profileObservation : ∀ a, Gamma a → Option (Representation a)
  relationObservation : ∀ a, Gamma a → D → Layer → Role → D → Layer → Prop
  baselineProfileCoherent : ∀ d a h,
    MeasureTheory.ProbabilityMeasure.toMeasure (probability.baselineJointLaw d a h)
      {ω | profileObservation a ω.1 = presenceAndRelations.profile d h a} = 1
  baselineRelationsCoherent : ∀ d a h e b r,
    MeasureTheory.ProbabilityMeasure.toMeasure (probability.baselineJointLaw d a h)
      {ω | relationObservation a ω.1 d a r e b ↔
        presenceAndRelations.relationEdge h d a r e b} = 1

/-- 25-B/Cの基準観測一致を確率事象として読むために必要な、全一致イベントの可測性。
構造体の旧来の `...Coherent` フィールドは測度値1だけを課すため、一般インスタンスでは
この追加命題なしに「確率1」と解釈しない。 -/
def Theorem25IntegratedModel.ObservationEventsMeasurable
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25IntegratedModel D History Layer Role
      Representation Gamma Output Candidate) : Prop :=
  (∀ d a h, MeasurableSet
    {ω : Gamma a × Output a |
      M.profileObservation a ω.1 = M.presenceAndRelations.profile d h a}) ∧
  (∀ d a h e b r, MeasurableSet
    {ω : Gamma a × Output a |
      M.relationObservation a ω.1 d a r e b ↔
        M.presenceAndRelations.relationEdge h d a r e b})

/-- 原文25-C3の関係的状態 Γ=(全層プロファイル, 縦包摂近傍, 当該層の入出関係辺)。 -/
structure Theorem25RelationalState
    (D Layer Role : Type*) (Representation : Layer → Type*) where
  profile : ∀ a, Option (Representation a)
  verticalNeighborhood : Set Layer
  incidentRelation : D → Layer → Role → D → Layer → Prop

/-- 25-B/C構造から、存在 d・履歴 h・注目層 a のΓを組み立てる。縦近傍は現前し、aと
順序比較可能な層、入出辺はaを端点にもつ関係辺として定義する。 -/
def Theorem25PresenceRelationModel.relationalState
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation : Layer → Type*}
    (M : Theorem25PresenceRelationModel D History Layer Role Representation)
    (d : D) (h : History) (a : Layer) :
    Theorem25RelationalState D Layer Role Representation :=
  { profile := M.profile d h
    verticalNeighborhood := {b | M.profile d h b ≠ none ∧ (a ≤ b ∨ b ≤ a)}
    incidentRelation := fun e b r f c =>
      (e = d ∧ b = a ∧ M.relationEdge h d a r f c) ∨
      (f = d ∧ c = a ∧ M.relationEdge h e b r d a) }

/-- Γの incidentRelation は、その基準存在・層から出る関係辺を正確に復元する。 -/
theorem Theorem25PresenceRelationModel.relationalState_incidentRelation_iff
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation : Layer → Type*}
    (M : Theorem25PresenceRelationModel D History Layer Role Representation)
    (d e : D) (h : History) (a b : Layer) (r : Role) :
    (M.relationalState d h a).incidentRelation d a r e b ↔
      M.relationEdge h d a r e b := by
  constructor
  · intro hinc
    change (d = d ∧ a = a ∧ M.relationEdge h d a r e b) ∨
      (e = d ∧ b = a ∧ M.relationEdge h d a r d a) at hinc
    rcases hinc with ⟨_, _, hedge⟩ | ⟨heq, hbeq, hedge⟩
    · exact hedge
    · subst e
      subst b
      exact hedge
  · intro hedge
    left
    exact ⟨rfl, rfl, hedge⟩

/-- 統合モデルを強め、確率変数Γそのものが原文25-C3の全層プロファイル・縦近傍・
入出関係辺を確率1で符号化することを要求する。 -/
structure Theorem25C3IntegratedModel
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (Representation Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)] where
  integrated : Theorem25IntegratedModel D History Layer Role
    Representation Gamma Output Candidate
  relationalStateObservation : ∀ d a h, Gamma a →
    Theorem25RelationalState D Layer Role Representation
  encodeRelationalState : ∀ d a h,
    Theorem25RelationalState D Layer Role Representation → Gamma a
  relationalStateObservation_encode : ∀ d a h state,
    relationalStateObservation d a h (encodeRelationalState d a h state) = state
  baselineRelationalStateCoherent : ∀ d a h,
    MeasureTheory.ProbabilityMeasure.toMeasure
      (integrated.probability.baselineJointLaw d a h)
      {ω | relationalStateObservation d a h ω.1 =
      integrated.presenceAndRelations.relationalState d h a} = 1

/-- 完全なΓ観測の確率1整合を確率事象として読む追加可測性条件。 -/
def Theorem25C3IntegratedModel.ObservationEventsMeasurable
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25C3IntegratedModel D History Layer Role
      Representation Gamma Output Candidate) : Prop :=
  M.integrated.ObservationEventsMeasurable ∧
    ∀ d a h, MeasurableSet
      {ω : Gamma a × Output a |
        M.relationalStateObservation d a h ω.1 =
          M.integrated.presenceAndRelations.relationalState d h a}

/-- 単一の外生法則を共有する履歴SCMに、25-B/C3の構造と確率1観測整合を
同じ生成法則上で束ねる。Indexed SCM版と異なり、全存在・層の法則共有が型に残る。 -/
structure Theorem25SharedGlobalHistoryC3Model
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (U : Type*) [MeasurableSpace U] [MeasurableSpace History]
    (Representation Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)] where
  scm : Theorem25SharedGlobalHistorySCM D Layer U History Gamma Output Candidate
  presenceAndRelations : Theorem25PresenceRelationModel D History Layer Role Representation
  profileObservation : ∀ a, Gamma a → Option (Representation a)
  relationObservation : ∀ a, Gamma a → D → Layer → Role → D → Layer → Prop
  relationalStateObservation : ∀ d a h, Gamma a →
    Theorem25RelationalState D Layer Role Representation
  encodeRelationalState : ∀ d a h,
    Theorem25RelationalState D Layer Role Representation → Gamma a
  relationalStateObservation_encode : ∀ d a h state,
    relationalStateObservation d a h (encodeRelationalState d a h state) = state
  baselineProfileCoherent : ∀ d a h,
    MeasureTheory.ProbabilityMeasure.toMeasure
      ((scm.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
      {ω | profileObservation a ω.1 = presenceAndRelations.profile d h a} = 1
  baselineRelationsCoherent : ∀ d a h e b r,
    MeasureTheory.ProbabilityMeasure.toMeasure
      ((scm.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
      {ω | relationObservation a ω.1 d a r e b ↔
        presenceAndRelations.relationEdge h d a r e b} = 1
  baselineRelationalStateCoherent : ∀ d a h,
    MeasureTheory.ProbabilityMeasure.toMeasure
      ((scm.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h)
      {ω | relationalStateObservation d a h ω.1 =
        presenceAndRelations.relationalState d h a} = 1

/-- 共有法則C3モデルの全基準観測イベントの可測性。 -/
def Theorem25SharedGlobalHistoryC3Model.ObservationEventsMeasurable
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25SharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate) : Prop :=
  (∀ d a h, MeasurableSet
    {ω : Gamma a × Output a |
      M.profileObservation a ω.1 = M.presenceAndRelations.profile d h a}) ∧
  (∀ d a h e b r, MeasurableSet
    {ω : Gamma a × Output a |
      M.relationObservation a ω.1 d a r e b ↔
        M.presenceAndRelations.relationEdge h d a r e b}) ∧
  (∀ d a h, MeasurableSet
    {ω : Gamma a × Output a |
      M.relationalStateObservation d a h ω.1 =
      M.presenceAndRelations.relationalState d h a})

/-- B/C3の観測一致を本当に確率1条件として使う、イベント可測性付き統合モデル。 -/
structure Theorem25MeasuredC3IntegratedModel
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (Representation Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)] where
  model : Theorem25C3IntegratedModel D History Layer Role
    Representation Gamma Output Candidate
  observationEventsMeasurable : model.ObservationEventsMeasurable

/-- 共有大域履歴SCMのB/C3観測整合を確率論的に使うための可測版ラッパー。 -/
structure Theorem25MeasuredSharedGlobalHistoryC3Model
    (D History Layer Role : Type*) [CompleteLattice Layer]
    (U : Type*) [MeasurableSpace U] [MeasurableSpace History]
    (Representation Gamma Output Candidate : Layer → Type*)
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)] where
  model : Theorem25SharedGlobalHistoryC3Model D History Layer Role U
    Representation Gamma Output Candidate
  observationEventsMeasurable : model.ObservationEventsMeasurable

/-- 実際の履歴別固定点が25-C3関係状態を符号化する場合、固定点から生成するSCMを
共有大域履歴C3モデルへ持ち上げる。固定点と関係網の一致はモデル対応仮定として受け取る。
候補独立性・可測性も入力し、これらを定理16の位相条件から導いたとはしない。 -/
noncomputable def Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    {D History Layer Role U Self : Type*} [CompleteLattice Layer]
    [MeasurableSpace U] [MeasurableSpace History]
    {Representation : Layer → Type*}
    {Output Candidate : Layer → Type*}
    [MeasurableSpace (Theorem25RelationalState D Layer Role Representation)]
    [∀ a, MeasurableSpace (Output a)] [∀ a, MeasurableSpace (Candidate a)]
    (F : HistoryFixedPoints History Self)
    (presence : Theorem25PresenceRelationModel D History Layer Role Representation)
    (code : ∀ (d : D) (a : Layer), Self →
      Theorem25RelationalState D Layer Role Representation)
    (hCode : ∀ d a h,
      code d a (F.fixedPoint h).1 = presence.relationalState d h a)
    (outputCode : ∀ (d : D) (a : Layer), Self → Output a)
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        code d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        code d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hProfileEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1.profile a = presence.profile d h a})
    (hRelationEvent : ∀ d a h e b r, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        (ω.1.incidentRelation d a r e b) ↔ presence.relationEdge h d a r e b})
    (hRelationalStateEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1 = presence.relationalState d h a}) :
    Theorem25MeasuredSharedGlobalHistoryC3Model D History Layer Role U Representation
      (fun _ : Layer => Theorem25RelationalState D Layer Role Representation)
      Output Candidate := by
  let stateCode : ∀ (d : D) (a : Layer), Self →
      Theorem25RelationalState D Layer Role Representation := code
  let scm := Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints F law globalHistory
    candidateVariable stateCode outputCode hHistory hCandidate hIndependent hContext
  refine ⟨?_, ?_⟩
  · refine ⟨scm, presence, (fun a γ => γ.profile a),
      (fun _ γ d a r e b => γ.incidentRelation d a r e b),
      (fun _ _ _ γ => γ), (fun _ _ _ γ => γ), ?_, ?_, ?_, ?_⟩
    · intro d a h state
      rfl
    · intro d a h
      let A : Set (Theorem25RelationalState D Layer Role Representation × Output a) :=
        {ω | ω.1.profile a = presence.profile d h a}
      rw [Theorem25GlobalHistorySCM.baselineJointLaw_apply scm.toIndexed d a h A
        (hProfileEvent d a h)]
      have hpre : (fun u =>
          (scm.toIndexed.stateEquation d a h u,
            scm.toIndexed.outputEquation d a h u (scm.toIndexed.candidateVariable d a u)))
          ⁻¹' A = Set.univ := by
        ext u
        change ((scm.toIndexed.stateEquation d a h u).profile a =
          presence.profile d h a) ↔ True
        have hstate : scm.toIndexed.stateEquation d a h u =
            presence.relationalState d h a := by
          change code d a (F.fixedPoint h).1 = _
          exact hCode d a h
        rw [hstate]
        simp [Theorem25PresenceRelationModel.relationalState]
      rw [hpre]
      simp
    · intro d a h e b r
      let A : Set (Theorem25RelationalState D Layer Role Representation × Output a) :=
        {ω | (ω.1.incidentRelation d a r e b) ↔ presence.relationEdge h d a r e b}
      rw [Theorem25GlobalHistorySCM.baselineJointLaw_apply scm.toIndexed d a h A
        (hRelationEvent d a h e b r)]
      have hpre : (fun u =>
          (scm.toIndexed.stateEquation d a h u,
            scm.toIndexed.outputEquation d a h u (scm.toIndexed.candidateVariable d a u)))
          ⁻¹' A = Set.univ := by
        ext u
        change (((scm.toIndexed.stateEquation d a h u).incidentRelation d a r e b) ↔
          presence.relationEdge h d a r e b) ↔ True
        have hstate : scm.toIndexed.stateEquation d a h u =
            presence.relationalState d h a := by
          change code d a (F.fixedPoint h).1 = _
          exact hCode d a h
        rw [hstate]
        exact ⟨fun _ => trivial,
          fun _ => presence.relationalState_incidentRelation_iff d e h a b r⟩
      rw [hpre]
      simp
    · intro d a h
      let A : Set (Theorem25RelationalState D Layer Role Representation × Output a) :=
        {ω | ω.1 = presence.relationalState d h a}
      rw [Theorem25GlobalHistorySCM.baselineJointLaw_apply scm.toIndexed d a h A
        (hRelationalStateEvent d a h)]
      have hpre : (fun u =>
          (scm.toIndexed.stateEquation d a h u,
            scm.toIndexed.outputEquation d a h u (scm.toIndexed.candidateVariable d a u)))
          ⁻¹' A = Set.univ := by
        ext u
        change scm.toIndexed.stateEquation d a h u =
          presence.relationalState d h a ↔ True
        have hstate : scm.toIndexed.stateEquation d a h u =
            presence.relationalState d h a := by
          change code d a (F.fixedPoint h).1 = _
          exact hCode d a h
        rw [hstate]
        simp
      rw [hpre]
      simp
  · refine ⟨?_, ?_, ?_⟩
    · intro d a h
      exact hProfileEvent d a h
    · intro d a h e b r
      exact hRelationEvent d a h e b r
    · intro d a h
      exact hRelationalStateEvent d a h

/-- 共通法則を保つ25-B/C3統合型でも、25-Dなら定理25第2結論が従う。 -/
theorem theorem25_secondConclusion_of_sharedGlobalHistoryC3Model
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25SharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      (M.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.scm.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h) :
    ∀ d a, ¬ ((M.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    (M.scm.toIndexed.toProbabilityCausalModel) hcomplete

/-- 可測なB/C3統合モデルでも、25-Dから定理25第2結論が従う。可測イベントの仮定により、
入力モデルの確率1観測整合を任意集合上の測度値と取り違えない。 -/
theorem theorem25_secondConclusion_of_measurableC3IntegratedModel
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25MeasuredC3IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.model.integrated.probability.intervenedJointLaw d a h s =
        M.model.integrated.probability.baselineJointLaw d a h) :
    ∀ d a, ¬ (M.model.integrated.probability.toCausalModel).hasAtman d a :=
  theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    M.model.integrated.probability hcomplete

/-- 可測な共有法則B/C3モデル上で、25-Dから定理25第2結論を得る。 -/
theorem theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25MeasuredSharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      (M.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw d a h s =
        (M.model.scm.toIndexed.toProbabilityCausalModel).baselineJointLaw d a h) :
    ∀ d a, ¬
      ((M.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a :=
  theorem25_secondConclusion_of_sharedGlobalHistoryC3Model M.model hcomplete

/-- 可測な共有法則C3モデルで、候補介入が将来出力をa.e.変えず、関係状態も構造方程式で
固定されているなら、25-Dをpushforward法則から導いて定理25第2結論へ接続する。 -/
theorem theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25MeasuredSharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate)
    (houtput : ∀ d a h s,
      ∀ᵐ u ∂ MeasureTheory.ProbabilityMeasure.toMeasure M.model.scm.exogenousLaw,
        M.model.scm.outputEquation d a h u (M.model.scm.candidateVariable d a u) =
          M.model.scm.outputEquation d a h u s) :
    ∀ d a,
      ¬ ((M.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance
    M.model.scm houtput

/-- 25-B/C3観測整合を備えた共有履歴SCMで、候補介入ごとの外生測度保存対称性から
25-Dを導き、25.2の全存在・全層結論まで接続する。C3の確率1整合条件を保ったまま、
点ごとの候補非干渉より一般的なノイズ再配置を許す。 -/
theorem theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_measurePreservingSymmetry
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25MeasuredSharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate)
    (hsym : ∀ d a h s,
      ∃ τ : U → U,
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure M.model.scm.exogenousLaw)
          (MeasureTheory.ProbabilityMeasure.toMeasure M.model.scm.exogenousLaw) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (M.model.scm.stateEquation d a h u,
            M.model.scm.outputEquation d a h u
              (M.model.scm.candidateVariable d a u))) ∧
        Measurable (fun u =>
          (M.model.scm.stateEquation d a h u,
            M.model.scm.outputEquation d a h u s)) ∧
        (∀ u, (M.model.scm.stateEquation d a h (τ u),
          M.model.scm.outputEquation d a h (τ u) s) =
            (M.model.scm.stateEquation d a h u,
              M.model.scm.outputEquation d a h u
                (M.model.scm.candidateVariable d a u)))) :
    ∀ d a,
      ¬ ((M.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_sharedGlobalHistoryC3Model M.model
    (theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry
      M.model.scm.toIndexed hsym)

/-- 測度保存対称性からの25-Dは25.2だけでなく、基準モデルで確率1だった25-B/C3観測の
全てを候補介入後も保存する。法則不変性と、プロファイル・関係辺・完全Γ状態の観測整合を
同じ共有履歴C3モデル上でまとめて返す。 -/
theorem theorem25_measurePreservingSymmetry_preservesSharedC3Observations
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {U : Type*} [MeasurableSpace U] [MeasurableSpace History]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem25MeasuredSharedGlobalHistoryC3Model D History Layer Role U
      Representation Gamma Output Candidate)
    (hsym : ∀ d a h s,
      ∃ τ : U → U,
        MeasureTheory.MeasurePreserving τ
          (MeasureTheory.ProbabilityMeasure.toMeasure M.model.scm.exogenousLaw)
          (MeasureTheory.ProbabilityMeasure.toMeasure M.model.scm.exogenousLaw) ∧
        Measurable τ ∧
        Measurable (fun u =>
          (M.model.scm.stateEquation d a h u,
            M.model.scm.outputEquation d a h u
              (M.model.scm.candidateVariable d a u))) ∧
        Measurable (fun u =>
          (M.model.scm.stateEquation d a h u,
            M.model.scm.outputEquation d a h u s)) ∧
        (∀ u, (M.model.scm.stateEquation d a h (τ u),
          M.model.scm.outputEquation d a h (τ u) s) =
            (M.model.scm.stateEquation d a h u,
              M.model.scm.outputEquation d a h u
                (M.model.scm.candidateVariable d a u)))) :
    (∀ d a, ¬
      ((M.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a) ∧
    (∀ d a h s,
      MeasureTheory.ProbabilityMeasure.toMeasure
        ((M.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw d a h s)
        {ω | M.model.profileObservation a ω.1 =
          M.model.presenceAndRelations.profile d h a} = 1 ∧
      (∀ e b r, MeasureTheory.ProbabilityMeasure.toMeasure
        ((M.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw d a h s)
        {ω | M.model.relationObservation a ω.1 d a r e b ↔
          M.model.presenceAndRelations.relationEdge h d a r e b} = 1) ∧
      MeasureTheory.ProbabilityMeasure.toMeasure
        ((M.model.scm.toIndexed.toProbabilityCausalModel).intervenedJointLaw d a h s)
        {ω | M.model.relationalStateObservation d a h ω.1 =
          M.model.presenceAndRelations.relationalState d h a} = 1) := by
  have hcomplete := theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry
    M.model.scm.toIndexed hsym
  refine ⟨theorem25_secondConclusion_of_sharedGlobalHistoryC3Model M.model hcomplete, ?_⟩
  intro d a h s
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomplete d a h s]
    exact M.model.baselineProfileCoherent d a h
  · intro e b r
    rw [hcomplete d a h s]
    exact M.model.baselineRelationsCoherent d a h e b r
  · rw [hcomplete d a h s]
    exact M.model.baselineRelationalStateCoherent d a h

/-- 履歴別固定点をC3関係状態へ符号化して生成した可測SCMでは、候補介入が出力を変えない
構成上の性質から25-Dが成立し、定理25第2結論へ至る。 -/
theorem theorem25_secondConclusion_of_historyFixedPointGeneratedMeasuredC3Model
    {D History Layer Role U Self : Type*} [CompleteLattice Layer]
    [MeasurableSpace U] [MeasurableSpace History]
    {Representation : Layer → Type*}
    {Output Candidate : Layer → Type*}
    [MeasurableSpace (Theorem25RelationalState D Layer Role Representation)]
    [∀ a, MeasurableSpace (Output a)] [∀ a, MeasurableSpace (Candidate a)]
    (F : HistoryFixedPoints History Self)
    (presence : Theorem25PresenceRelationModel D History Layer Role Representation)
    (code : ∀ (d : D) (a : Layer), Self →
      Theorem25RelationalState D Layer Role Representation)
    (hCode : ∀ d a h,
      code d a (F.fixedPoint h).1 = presence.relationalState d h a)
    (outputCode : ∀ (d : D) (a : Layer), Self → Output a)
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        code d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        code d a (F.fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hProfileEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1.profile a = presence.profile d h a})
    (hRelationEvent : ∀ d a h e b r, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        (ω.1.incidentRelation d a r e b) ↔ presence.relationEdge h d a r e b})
    (hRelationalStateEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1 = presence.relationalState d h a}) :
    let M := Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
      F presence code hCode outputCode law globalHistory candidateVariable hHistory
      hCandidate hIndependent hContext hProfileEvent hRelationEvent hRelationalStateEvent
    ∀ d a, ¬ ((M.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  let M := Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    F presence code hCode outputCode law globalHistory candidateVariable hHistory
    hCandidate hIndependent hContext hProfileEvent hRelationEvent hRelationalStateEvent
  apply theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference M
  intro d a h s
  filter_upwards with u
  rfl

/-- §7の層系から固定点族を生成し、SC上の縮小一意性を経て、測度付きC3モデルと
候補非干渉条件から25.2まで接続する合成定理。コード一致・独立性・可測性・候補非干渉は
位相的な定理16条件から導かず、モデル対応条件として明示する。 -/
theorem theorem25_secondConclusion_of_Theorem16LayerSystemGeneratedMeasuredC3Model
    {D History Layer Role U : Type*} {I : Type u} {E : I → Type u}
    [CompleteLattice Layer] [MeasurableSpace U] [MeasurableSpace History]
    [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {Representation : Layer → Type*} {Output Candidate : Layer → Type*}
    [MeasurableSpace (Theorem25RelationalState D Layer Role Representation)]
    [∀ a, MeasurableSpace (Output a)] [∀ a, MeasurableSpace (Candidate a)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    (presence : Theorem25PresenceRelationModel D History Layer Role Representation)
    (code : ∀ (d : D) (a : Layer), (∀ i, E i) →
      Theorem25RelationalState D Layer Role Representation)
    (hCode : ∀ d a h,
      code d a ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h).1 =
          presence.relationalState d h a)
    (outputCode : ∀ (d : D) (a : Layer), (∀ i, E i) → Output a)
    (law : MeasureTheory.ProbabilityMeasure U)
    (globalHistory : U → History)
    (candidateVariable : ∀ (d : D) (a : Layer), U → Candidate a)
    (hHistory : AEMeasurable globalHistory
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hCandidate : ∀ d a, AEMeasurable (candidateVariable d a)
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hIndependent : ∀ d a, ProbabilityTheory.IndepFun (candidateVariable d a)
      (fun u => (globalHistory u,
        code d a ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
          M metric hcomplete q hcontract).fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hContext : ∀ d a, AEMeasurable
      (fun u => (globalHistory u,
        code d a ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
          M metric hcomplete q hcontract).fixedPoint (globalHistory u)).1))
      (MeasureTheory.ProbabilityMeasure.toMeasure law))
    (hProfileEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1.profile a = presence.profile d h a})
    (hRelationEvent : ∀ d a h e b r, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        (ω.1.incidentRelation d a r e b) ↔ presence.relationEdge h d a r e b})
    (hRelationalStateEvent : ∀ d a h, MeasurableSet
      {ω : Theorem25RelationalState D Layer Role Representation × Output a |
        ω.1 = presence.relationalState d h a}) :
    let F := historyFixedPointsOfTheorem16LayerSystemWithSCMetric
      M metric hcomplete q hcontract
    let C := Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
      F presence code hCode outputCode law globalHistory candidateVariable hHistory
      hCandidate hIndependent hContext hProfileEvent hRelationEvent hRelationalStateEvent
    ∀ d a, ¬ ((C.model.scm.toIndexed.toProbabilityCausalModel).toCausalModel).hasAtman d a := by
  let F := historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    M metric hcomplete q hcontract
  let C := Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints
    F presence code hCode outputCode law globalHistory candidateVariable hHistory
    hCandidate hIndependent hContext hProfileEvent hRelationEvent hRelationalStateEvent
  exact theorem25_secondConclusion_of_historyFixedPointGeneratedMeasuredC3Model
    F presence code hCode outputCode law globalHistory candidateVariable hHistory
    hCandidate hIndependent hContext hProfileEvent hRelationEvent hRelationalStateEvent

/-- 完全なΓの符号化を含むモデルでも、25-Dから定理25 (25.2) が従う。 -/
theorem theorem25_secondConclusion_of_c3IntegratedModel
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25C3IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.integrated.probability.intervenedJointLaw d a h s =
        M.integrated.probability.baselineJointLaw d a h) :
    ∀ d a, ¬ (M.integrated.probability.toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    M.integrated.probability hcomplete

/-- 定理16・25の最終論理核を一つの入口に束ねる。

`fixedPoints` は定理16層系から得た履歴別固定点族（存在は定理16、唯一性は縮小条件）、
`hhistorySensitive` は25-A(1)、`hA2` は実確率SCM上の25-A(2)、`h25D` は
全存在・全層の25-Dである。結論は25.1とC3統合モデル上の25.2。
25-A(2)は原文条件として入力するが、この二結論の論理証明には使用しない。
`SelfProcessSCM` と `C3IntegratedModel` の間の無条件な同一視も仮定しない。 -/
theorem theorem16_25_conditionalProofCore
    {History Self : Type*} {U : Type*}
    {Representation Output Candidate : Type*}
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate]
    {D Layer Role : Type*} [CompleteLattice Layer]
    {Gamma C3Representation : Layer → Type*}
    {C3Output C3Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (C3Output a)]
    (fixedPoints : HistoryFixedPoints History Self)
    (hhistorySensitive : ∃ h₁ h₂,
      (fixedPoints.fixedPoint h₁).1 ≠ (fixedPoints.fixedPoint h₂).1)
    (selfProcess : Theorem25SelfProcessSCM History U Representation Output Candidate)
    (hA2 : selfProcess.toLawModel.Condition25A2 ())
    (c3Model : Theorem25C3IntegratedModel D History Layer Role
      C3Representation Gamma C3Output C3Candidate)
    (h25D : ∀ d a h s,
      c3Model.integrated.probability.intervenedJointLaw d a h s =
        c3Model.integrated.probability.baselineJointLaw d a h) :
    (¬ ∃ s : Self, ∀ h,
      ∃ hs : fixedPoints.carrier h s,
        fixedPoints.feedback h ⟨s, hs⟩ = ⟨s, hs⟩) ∧
      (∀ d a, ¬ (c3Model.integrated.probability.toCausalModel).hasAtman d a) := by
  constructor
  · obtain ⟨h₁, h₂, hsep⟩ := hhistorySensitive
    intro hcommon
    apply (no_common_fixed_point_of_history_separation fixedPoints hsep)
    rcases hcommon with ⟨s, hfixed⟩
    obtain ⟨hs₁, hf₁⟩ := hfixed h₁
    obtain ⟨hs₂, hf₂⟩ := hfixed h₂
    exact ⟨s, hs₁, hs₂, hf₁, hf₂⟩
  · exact theorem25_secondConclusion_of_c3IntegratedModel c3Model h25D

/-- 25-B、25-Cの層別・関係構造を備えた統合モデルで、条件25-Dを仮定すれば
原文定理25 (25.2) を得る。証明の因果部分が実際に使う前提は25-Dである。 -/
theorem theorem25_secondConclusion_of_integratedModel
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.probability.intervenedJointLaw d a h s = M.probability.baselineJointLaw d a h) :
    ∀ d a, ¬ (M.probability.toCausalModel).hasAtman d a := by
  exact theorem25_secondConclusion_of_probabilityFunctionalCompleteness
    M.probability hcomplete

/-- 条件25-Dの全同時法則不変性により、基準分布で確率1だった層別プロファイルの
観測的一致は、任意の候補自性介入後にも確率1で保たれる。 -/
theorem theorem25_profileCoherent_afterIntervention
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.probability.intervenedJointLaw d a h s = M.probability.baselineJointLaw d a h)
    (d : D) (a : Layer) (h : History) (s : Candidate a) :
    MeasureTheory.ProbabilityMeasure.toMeasure
      (M.probability.intervenedJointLaw d a h s)
      {ω | M.profileObservation a ω.1 = M.presenceAndRelations.profile d h a} = 1 := by
  rw [hcomplete d a h s]
  exact M.baselineProfileCoherent d a h

/-- 同じく、基準分布で一致している各層の関係辺観測も、25-Dのもとで
候補自性介入後に確率1で保存される。 -/
theorem theorem25_relationsCoherent_afterIntervention
    {D History Layer Role : Type*} [CompleteLattice Layer]
    {Representation Gamma Output Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)]
    [∀ a, MeasurableSpace (Output a)]
    (M : Theorem25IntegratedModel D History Layer Role
      Representation Gamma Output Candidate)
    (hcomplete : ∀ d a h s,
      M.probability.intervenedJointLaw d a h s = M.probability.baselineJointLaw d a h)
    (d : D) (a : Layer) (h : History) (s : Candidate a)
    (e : D) (b : Layer) (r : Role) :
    MeasureTheory.ProbabilityMeasure.toMeasure
      (M.probability.intervenedJointLaw d a h s)
      {ω | M.relationObservation a ω.1 d a r e b ↔
        M.presenceAndRelations.relationEdge h d a r e b} = 1 := by
  rw [hcomplete d a h s]
  exact M.baselineRelationsCoherent d a h e b r

/-- 固定履歴ごとの唯一固定点が少なくとも一組の履歴間で異なるなら、
全履歴に共通し、全履歴の作用素で固定される状態は存在しない。
定理25 (25.1) の量化をそのまま履歴族上で表す。 -/
theorem theorem25_no_common_fixedPoint_of_historyFamily
    {History Self : Type*} (F : HistoryFixedPoints History Self)
    {h₁ h₂ : History}
    (hsep : (F.fixedPoint h₁).1 ≠ (F.fixedPoint h₂).1) :
    ¬ ∃ s : Self, ∃ hmem : ∀ h, F.carrier h s,
      ∀ h, F.feedback h ⟨s, hmem h⟩ = ⟨s, hmem h⟩ := by
  rintro ⟨s, hmem, hfix⟩
  have h₁eq : (⟨s, hmem h₁⟩ : {x : Self // F.carrier h₁ x}) = F.fixedPoint h₁ :=
    F.unique h₁ ⟨s, hmem h₁⟩ (hfix h₁)
  have h₂eq : (⟨s, hmem h₂⟩ : {x : Self // F.carrier h₂ x}) = F.fixedPoint h₂ :=
    F.unique h₂ ⟨s, hmem h₂⟩ (hfix h₂)
  exact hsep (congrArg Subtype.val h₁eq |>.symm.trans (congrArg Subtype.val h₂eq))

/-- 原文の逆極限条件と一般連続Fから、忠実同変自己表象まで一度に接続する。
層別feedbackの連続性・自己表象の単射性は要求しない。 -/
theorem theorem16_represented_fixedPoint_of_continuous_inverseLimitMap
    {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKcompact : ∀ i, IsCompact (K i))
    (hKnonempty : ∀ i, (K i).Nonempty)
    (hKconvex : ∀ i, Convex ℝ (K i))
    (project : ∀ {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K α → y ∈ K α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project hβα (a • x + b • y) = a • project hβα x + b • project hβα y)
    (hprojectRefl : ∀ i (x : {x : E i // x ∈ K i}),
      project (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K α}),
      project hγβ (project hβα x.1) = project (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project hβα) (K α) (K β))
    (hprojectContinuousOn : ∀ (j : ProjectionConstraintIndex I),
      ContinuousOn (project j.2) (K j.1.2))
    (hnoMax : ∀ i : I, ∃ j, i < j)
    (F : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} →
      {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project})
    (hF : Continuous F)
    {Rep : Type*} [TopologicalSpace Rep] [CompactSpace Rep] [T2Space Rep]
    (R : SelfRepresentation
      {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project} Rep)
    (FRep : Rep → Rep) (hFRep : Continuous FRep)
    (hequiv : ∀ x, R.represent (F x) = FRep (R.represent x)) :
    ∃ x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K project},
      F x = x ∧ FRep (R.represent x) = R.represent x ∧
        (R.represent x, x) ∈ R.relation := by
  apply represented_fixedPoint_of_equivariance R F FRep hFRep hequiv
  exact theorem16_fixedPoint_exists_of_continuous_inverseLimitMap
    E K hKcompact hKnonempty hKconvex project hprojectAffineOnK hprojectRefl
    hprojectComp hprojectMaps hprojectContinuousOn hnoMax F hF

/-- 履歴別固定点族の各固定点を、履歴別の忠実同変表象へ移す。
履歴間で状態carrier・表象空間が異なることを保持する。 -/
theorem history_represented_fixedPoints_of_equivariance
    {History Self : Type*} [TopologicalSpace Self]
    (fixedPoints : HistoryFixedPoints History Self)
    (Rep : History → Type*) [∀ h, TopologicalSpace (Rep h)]
    [∀ h, CompactSpace (Rep h)] [∀ h, T2Space (Rep h)]
    (R : ∀ h, SelfRepresentation {s : Self // fixedPoints.carrier h s} (Rep h))
    (FRep : ∀ h, Rep h → Rep h)
    (hFRep : ∀ h, Continuous (FRep h))
    (hequiv : ∀ h s, (R h).represent (fixedPoints.feedback h s) =
      FRep h ((R h).represent s)) :
    ∀ h, ∃ s : {s : Self // fixedPoints.carrier h s},
      fixedPoints.feedback h s = s ∧
      FRep h ((R h).represent s) = (R h).represent s ∧
      ((R h).represent s, s) ∈ (R h).relation := by
  intro h
  apply represented_fixedPoint_of_equivariance (R h) (fixedPoints.feedback h)
    (FRep h) (hFRep h) (hequiv h)
  exact ⟨fixedPoints.fixedPoint h, fixedPoints.isFixed h⟩

/-- 原文定理16の幾何率：初期残差ではなく固定点までの初期距離で評価する。
任意の距離空間上の縮小写像で成立し、完備性はこの評価自体には不要。 -/
theorem contraction_iterates_dist_le_initial_fixedPoint
    {S : Type*} [MetricSpace S] {q : NNReal} {F : S → S}
    (hcontract : ContractingWith q F) (s : S) (hs : F s = s) (x : S) :
    ∀ n : ℕ, dist (F^[n] x) s ≤ (q : ℝ)^n * dist x s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      dist (F (F^[n] x)) s = dist (F (F^[n] x)) (F s) := by rw [hs]
      _ ≤ (q : ℝ) * dist (F^[n] x) s := hcontract.dist_le_mul _ _
      _ ≤ (q : ℝ) * ((q : ℝ)^n * dist x s) :=
        mul_le_mul_of_nonneg_left ih q.coe_nonneg
      _ = (q : ℝ)^(n+1) * dist x s := by rw [pow_succ]; ring

/-- 原文の完備距離・縮小条件節を忠実同変自己表象と合成する。
一意性・初期固定点距離による幾何率・極限・表象固定点を同じFについて返す。 -/
theorem represented_unique_fixedPoint_and_geometricIterates_of_contraction
    {S Rep : Type*} [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace Rep] [CompactSpace Rep] [T2Space Rep]
    (R : SelfRepresentation S Rep) (F : S → S) (FRep : Rep → Rep)
    (hequiv : ∀ s, R.represent (F s) = FRep (R.represent s))
    {q : NNReal} (hcontract : ContractingWith q F) (x₀ : S) :
    ∃ s, F s = s ∧ (∀ y, F y = y → y = s) ∧
      (∀ n : ℕ, dist (F^[n] x₀) s ≤ (q : ℝ)^n * dist x₀ s) ∧
      Filter.Tendsto (fun n : ℕ => F^[n] x₀) Filter.atTop (nhds s) ∧
      FRep (R.represent s) = R.represent s ∧ (R.represent s, s) ∈ R.relation := by
  letI : Nonempty S := ⟨x₀⟩
  let s := ContractingWith.fixedPoint F hcontract
  have hs : F s = s := hcontract.fixedPoint_isFixedPt
  refine ⟨s, hs, ?_, contraction_iterates_dist_le_initial_fixedPoint hcontract s hs x₀,
    hcontract.tendsto_iterate_fixedPoint x₀, ?_, R.represents s⟩
  · intro y hy
    exact hcontract.fixedPoint_unique' (x := y) (y := s) hy hs
  · rw [← hequiv s, hs]

/-- 履歴族が既に選んだ固定点について原文幾何率・極限・同変自己表象を返す。
距離・完備性は各履歴carrierにだけ要求し、共通周囲空間の距離化は要求しない。
Banach側で別の固定点を選び直して結論の点を取り替えない。 -/
theorem history_fixedPoints_geometric_and_represented
    {History Self : Type*}
    (fixedPoints : HistoryFixedPoints History Self)
    [∀ h, MetricSpace {s : Self // fixedPoints.carrier h s}]
    [∀ h, CompleteSpace {s : Self // fixedPoints.carrier h s}]
    (q : History → NNReal)
    (hcontract : ∀ h, ContractingWith (q h) (fixedPoints.feedback h))
    (Rep : History → Type*) [∀ h, TopologicalSpace (Rep h)]
    [∀ h, CompactSpace (Rep h)] [∀ h, T2Space (Rep h)]
    (R : ∀ h, SelfRepresentation {s : Self // fixedPoints.carrier h s} (Rep h))
    (FRep : ∀ h, Rep h → Rep h)
    (hequiv : ∀ h s, (R h).represent (fixedPoints.feedback h s) =
      FRep h ((R h).represent s)) :
    ∀ h, (∀ x₀ : {s : Self // fixedPoints.carrier h s},
      (∀ n : ℕ, dist ((fixedPoints.feedback h)^[n] x₀) (fixedPoints.fixedPoint h) ≤
        (q h : ℝ)^n * dist x₀ (fixedPoints.fixedPoint h)) ∧
      Filter.Tendsto (fun n : ℕ => (fixedPoints.feedback h)^[n] x₀)
        Filter.atTop (nhds (fixedPoints.fixedPoint h))) ∧
      FRep h ((R h).represent (fixedPoints.fixedPoint h)) =
        (R h).represent (fixedPoints.fixedPoint h) ∧
      ((R h).represent (fixedPoints.fixedPoint h), fixedPoints.fixedPoint h) ∈
        (R h).relation := by
  intro h
  refine ⟨?_, ?_, (R h).represents _⟩
  · intro x₀
    letI : Nonempty {s : Self // fixedPoints.carrier h s} := ⟨x₀⟩
    have heq : ContractingWith.fixedPoint (fixedPoints.feedback h) (hcontract h) =
        fixedPoints.fixedPoint h :=
      (hcontract h).fixedPoint_unique' (hcontract h).fixedPoint_isFixedPt
        (fixedPoints.isFixed h)
    refine ⟨contraction_iterates_dist_le_initial_fixedPoint
      (hcontract h) _ (fixedPoints.isFixed h) x₀, ?_⟩
    simpa only [heq] using (hcontract h).tendsto_iterate_fixedPoint x₀
  · rw [← hequiv h, fixedPoints.isFixed h]

/-- 同一履歴固定点族の原文幾何収束・自己表象と25.1/25.2を合成する。
履歴分離と25-Dは原文の独立条件として保持し、モデルからの導出を要求しない。 -/
theorem theorem16_25_geometricRepresentation_conditionalProofCore
    {History Self : Type*} {U : Type*}
    {Representation Output Candidate : Type*}
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate]
    {D Layer Role : Type*} [CompleteLattice Layer]
    {Gamma C3Representation : Layer → Type*}
    {C3Output C3Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (C3Output a)]
    (fixedPoints : HistoryFixedPoints History Self)
    [∀ h, MetricSpace {s : Self // fixedPoints.carrier h s}]
    [∀ h, CompleteSpace {s : Self // fixedPoints.carrier h s}]
    (q : History → NNReal)
    (hcontract : ∀ h, ContractingWith (q h) (fixedPoints.feedback h))
    (Rep : History → Type*) [∀ h, TopologicalSpace (Rep h)]
    [∀ h, CompactSpace (Rep h)] [∀ h, T2Space (Rep h)]
    (R : ∀ h, SelfRepresentation {s : Self // fixedPoints.carrier h s} (Rep h))
    (FRep : ∀ h, Rep h → Rep h)
    (hequiv : ∀ h s, (R h).represent (fixedPoints.feedback h s) =
      FRep h ((R h).represent s))
    (hhistorySensitive : ∃ h₁ h₂,
      (fixedPoints.fixedPoint h₁).1 ≠ (fixedPoints.fixedPoint h₂).1)
    (selfProcess : Theorem25SelfProcessSCM History U Representation Output Candidate)
    (hA2 : selfProcess.toLawModel.Condition25A2 ())
    (c3Model : Theorem25C3IntegratedModel D History Layer Role
      C3Representation Gamma C3Output C3Candidate)
    (h25D : ∀ d a h s,
      c3Model.integrated.probability.intervenedJointLaw d a h s =
        c3Model.integrated.probability.baselineJointLaw d a h) :
    (∀ h, (∀ x₀ : {s : Self // fixedPoints.carrier h s},
      (∀ n : ℕ, dist ((fixedPoints.feedback h)^[n] x₀) (fixedPoints.fixedPoint h) ≤
        (q h : ℝ)^n * dist x₀ (fixedPoints.fixedPoint h)) ∧
      Filter.Tendsto (fun n : ℕ => (fixedPoints.feedback h)^[n] x₀)
        Filter.atTop (nhds (fixedPoints.fixedPoint h))) ∧
      FRep h ((R h).represent (fixedPoints.fixedPoint h)) =
        (R h).represent (fixedPoints.fixedPoint h) ∧
      ((R h).represent (fixedPoints.fixedPoint h), fixedPoints.fixedPoint h) ∈
        (R h).relation) ∧
    (¬ ∃ s : Self, ∀ h,
      ∃ hs : fixedPoints.carrier h s,
        fixedPoints.feedback h ⟨s, hs⟩ = ⟨s, hs⟩) ∧
      (∀ d a, ¬ (c3Model.integrated.probability.toCausalModel).hasAtman d a) := by
  exact ⟨history_fixedPoints_geometric_and_represented fixedPoints q hcontract Rep R FRep hequiv,
    theorem16_25_conditionalProofCore fixedPoints hhistorySensitive selfProcess hA2 c3Model h25D⟩

/-- 定理16の履歴別層条件から固定点を構成し、同じ逆極限carrier・誘導feedback・
SC上の距離で幾何収束と自己表象を得たうえで、25.1/25.2へ一括接続する。
縮小率、25-A(1)の履歴分離、25-A(2)、25-Dはそれぞれ独立の原文条件として残す。
縮小性は定理16の連続固定点存在とは別に、各履歴のSC距離上で入力される。 -/
theorem theorem16HistoryLayerSystem_to_theorem25_fullConnection
    {History : Type v} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {E : I → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (M : Theorem16HistoryLayerSystem History I E)
    (metric : ∀ h, MetricSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (hcomplete : ∀ h, letI := metric h; CompleteSpace
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h})
    (q : History → NNReal)
    (hcontract : ∀ h, letI := metric h; ContractingWith (q h)
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h))
    (Rep : History → Type*) [∀ h, TopologicalSpace (Rep h)]
    [∀ h, CompactSpace (Rep h)] [∀ h, T2Space (Rep h)]
    (R : ∀ h, SelfRepresentation
      {x : ∀ i, E i // x ∈ historyAffineInverseLimitSet E M.carrier M.project h} (Rep h))
    (FRep : ∀ h, Rep h → Rep h)
    (hFRepContinuous : ∀ h, Continuous (FRep h))
    (hequiv : ∀ h x, (R h).represent
      (historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h x) = FRep h ((R h).represent x))
    (hhistorySensitive : ∃ h₁ h₂,
      ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h₁).1 ≠
      ((historyFixedPointsOfTheorem16LayerSystemWithSCMetric
        M metric hcomplete q hcontract).fixedPoint h₂).1)
    {U : Type*} {Representation Output Candidate : Type*}
    [MeasurableSpace U] [MeasurableSpace History]
    [MeasurableSpace Representation] [MeasurableSpace Output]
    [MeasurableSpace Candidate]
    {D Layer Role : Type*} [CompleteLattice Layer]
    {Gamma C3Representation : Layer → Type*}
    {C3Output C3Candidate : Layer → Type*}
    [∀ a, MeasurableSpace (Gamma a)] [∀ a, MeasurableSpace (C3Output a)]
    (selfProcess : Theorem25SelfProcessSCM History U Representation Output Candidate)
    (hA2 : selfProcess.toLawModel.Condition25A2 ())
    (c3Model : Theorem25C3IntegratedModel D History Layer Role
      C3Representation Gamma C3Output C3Candidate)
    (h25D : ∀ d a h s,
      c3Model.integrated.probability.intervenedJointLaw d a h s =
        c3Model.integrated.probability.baselineJointLaw d a h) :
    (∀ h, ∃! x : {x : ∀ i, E i //
      x ∈ historyAffineInverseLimitSet E M.carrier M.project h},
      historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
        M.feedback M.feedbackCommutes h x = x ∧
      FRep h ((R h).represent x) = (R h).represent x ∧
      ((R h).represent x, x) ∈ (R h).relation ∧
      ∀ (x₀ : {x : ∀ i, E i //
        x ∈ historyAffineInverseLimitSet E M.carrier M.project h}) (n : ℕ),
        dist ((historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h)^[n] x₀) x ≤
          (q h : ℝ) ^ n * dist x₀ x) ∧
    (¬ ∃ x : ∀ i, E i,
      ∀ h, ∃ hx : x ∈ historyAffineInverseLimitSet E M.carrier M.project h,
        historyInducedAffineInverseLimitMap E M.carrier M.project M.projectMaps
          M.feedback M.feedbackCommutes h ⟨x, hx⟩ = ⟨x, hx⟩) ∧
    (∀ d a, ¬ (c3Model.integrated.probability.toCausalModel).hasAtman d a) := by
  let points := historyFixedPointsOfTheorem16LayerSystemWithSCMetric
    M metric hcomplete q hcontract
  refine ⟨M.fullRepresentedFixedPointConclusion metric hcomplete q hcontract
      Rep R FRep hFRepContinuous hequiv, ?_⟩
  exact theorem16_25_conditionalProofCore points hhistorySensitive selfProcess hA2 c3Model h25D

/-- 一般連続逆極限から構成した履歴固定点族は、元の逆極限carrierとFを保持する。
縮小条件・自己表象・定理25への接続で別のcarrier/作用素に置き換わらないことを確認。 -/
theorem historyContinuousInverseLimit_fixedPoints_data
    {History : Type*} {I : Type u} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    (E : I → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    (K : ∀ (h : History) (i : I), Set (E i))
    (hKcompact : ∀ (h : History) (i : I), IsCompact (K h i))
    (hKnonempty : ∀ (h : History) (i : I), (K h i).Nonempty)
    (hKconvex : ∀ (h : History) (i : I), Convex ℝ (K h i))
    (project : ∀ (h : History) {β α : I}, β ≤ α → E α → E β)
    (hprojectAffineOnK : ∀ (h : History) ⦃β α : I⦄ (hβα : β ≤ α)
      (x y : E α) (a b : ℝ), x ∈ K h α → y ∈ K h α →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        project h hβα (a • x + b • y) =
          a • project h hβα x + b • project h hβα y)
    (hprojectRefl : ∀ (h : History) (i : I) (x : {x : E i // x ∈ K h i}),
      project h (le_rfl : i ≤ i) x.1 = x.1)
    (hprojectComp : ∀ (h : History) {γ β α : I} (hγβ : γ ≤ β) (hβα : β ≤ α)
      (x : {x : E α // x ∈ K h α}),
      project h hγβ (project h hβα x.1) = project h (hγβ.trans hβα) x.1)
    (hprojectMaps : ∀ (h : History) ⦃β α : I⦄ (hβα : β ≤ α),
      Set.MapsTo (project h hβα) (K h α) (K h β))
    (hprojectContinuousOn : ∀ (h : History) (j : ProjectionConstraintIndex I),
      ContinuousOn (project h j.2) (K h j.1.2))
    (hnoMax : ∀ i : I, ∃ j, i < j)
    (F : ∀ (h : History), {x : ∀ i, E i //
      x ∈ affineInverseLimitSet E (K h) (fun {β α} hβα => project h hβα)} →
      {x : ∀ i, E i // x ∈ affineInverseLimitSet E (K h)
        (fun {β α} hβα => project h hβα)})
    (hF : ∀ (h : History), Continuous (F h))
    (hunique : ∀ (h : History) x y, F h x = x → F h y = y → x = y) :
    let points := historyFixedPointsOfContinuousInverseLimitMaps
      E K hKcompact hKnonempty hKconvex project hprojectAffineOnK hprojectRefl
      hprojectComp hprojectMaps hprojectContinuousOn hnoMax F hF hunique
    (points.carrier = fun h x => x ∈ affineInverseLimitSet E (K h)
      (fun {β α} hβα => project h hβα)) ∧
    (∀ h x, points.feedback h x = F h x) := by
  exact ⟨rfl, fun _ _ => rfl⟩

end Tomabechi.Theorem16_25

#print axioms Tomabechi.Theorem16_25.theorem16_represented_fixedPoint_of_continuous_inverseLimitMap

#print axioms Tomabechi.Theorem16_25.history_represented_fixedPoints_of_equivariance

#print axioms Tomabechi.Theorem16_25.contraction_iterates_dist_le_initial_fixedPoint
#print axioms Tomabechi.Theorem16_25.represented_unique_fixedPoint_and_geometricIterates_of_contraction

#print axioms Tomabechi.Theorem16_25.history_fixedPoints_geometric_and_represented

#print axioms Tomabechi.Theorem16_25.theorem16_25_geometricRepresentation_conditionalProofCore

#print axioms Tomabechi.Theorem16_25.historyContinuousInverseLimit_fixedPoints_data

#print axioms Tomabechi.Theorem16_25.historyFixedPointsOfCarrierContractions

#print axioms Tomabechi.Theorem16_25.theorem16HistoryLayerSystem_to_theorem25_fullConnection
