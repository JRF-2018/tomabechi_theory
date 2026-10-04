import Theorem1

/-!
# 定理2：共有TCZ収束の有限主体コア

有限主体・有限結合辺について、非負の個人残差と辺不整合を正の重みで
足した共有残差が指数減衰するとき、各個人残差と各辺不整合も明示的な
指数上界を持つことを示す。共有零集合への距離収束には別途、原文どおり
非空性・下降条件・誤差境界が必要であり、ここではそれらを導いたとはしない。
-/

namespace Tomabechi.Theorem2

open Finset
open MeasureTheory

/-- 個人の閾値超過残差と、有限個の結合辺の不整合を集約した共有残差。
辺の両端の順序は入力データで固定される。対称性は各辺の不整合関数側の条件で扱う。 -/
def sharedResidual {I : Type*} {E : Type*}
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (individual : I → ℝ → ℝ) (edgeMismatch : E → ℝ → ℝ)
    (w : I → ℝ) (γ : E → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w i * individual i t) + ∑ e, γ e * edgeMismatch e t

/-- 非負の個人項は個人残差の有限総和以下である。 -/
theorem weightedIndividual_le_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℝ) (individual : I → ℝ → ℝ) (t : ℝ) (i : I)
    (hnonneg : ∀ j, 0 ≤ w j * individual j t) :
    w i * individual i t ≤ ∑ j, w j * individual j t := by
  exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)

/-- 定義した共有残差は、各個人の重み付き残差を上回る。
他の個人項と辺項が非負であることを仮定する。 -/
theorem weightedIndividual_le_sharedResidual
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (individual : I → ℝ → ℝ) (edgeMismatch : E → ℝ → ℝ)
    (w : I → ℝ) (γ : E → ℝ) (t : ℝ) (i : I)
    (hindividual : ∀ j, 0 ≤ w j * individual j t)
    (hedge : ∀ e, 0 ≤ γ e * edgeMismatch e t) :
    w i * individual i t ≤ sharedResidual individual edgeMismatch w γ t := by
  have hi := weightedIndividual_le_sum w individual t i hindividual
  have he : 0 ≤ ∑ e, γ e * edgeMismatch e t :=
    Finset.sum_nonneg fun e _ => hedge e
  simp only [sharedResidual]
  linarith

/-- 定義した共有残差は、各結合辺の重み付き不整合を上回る。 -/
theorem weightedEdge_le_sharedResidual
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (individual : I → ℝ → ℝ) (edgeMismatch : E → ℝ → ℝ)
    (w : I → ℝ) (γ : E → ℝ) (t : ℝ) (e : E)
    (hindividual : ∀ i, 0 ≤ w i * individual i t)
    (hedge : ∀ f, 0 ≤ γ f * edgeMismatch f t) :
    γ e * edgeMismatch e t ≤ sharedResidual individual edgeMismatch w γ t := by
  have hi : 0 ≤ ∑ i, w i * individual i t :=
    Finset.sum_nonneg fun i _ => hindividual i
  have he := Finset.single_le_sum (fun f _ => hedge f) (Finset.mem_univ e)
  simp only [sharedResidual]
  linarith

/-- 無向辺として解釈した有限グラフの隣接関係。 -/
def adjacent {I : Type*} (edges : Finset (I × I)) (i j : I) : Prop :=
  (i, j) ∈ edges ∨ (j, i) ∈ edges

/-- 連結なグラフでは、全辺の表象一致から全主体間の表象一致が従う。
`connected` は隣接関係の反射推移閉包として与え、零点同値性を `hEdgeEq` に明示する。 -/
theorem representation_agreement_of_connected
    {I E : Type*} [Fintype E] [DecidableEq E]
    (edges : Finset (I × I)) (h : I → E)
    (connected : ∀ i j, Relation.ReflTransGen (adjacent edges) i j)
    (hEdgeEq : ∀ i j, adjacent edges i j → h i = h j) :
    ∀ i j, h i = h j := by
  intro i j
  have hwalk := connected i j
  induction hwalk with
  | refl => rfl
  | tail hab hbc ih =>
      exact ih.trans (hEdgeEq _ _ hbc)

/-- 集約残差から個人・辺ごとの誤差を取り出す定量補題。
重みの正値、全項の非負性、および個別項が共有残差以下であることを明示入力にする。 -/
theorem component_exponential_bound
    (r aggregate : ℝ → ℝ) (c t₀ t a initialBound : ℝ)
    (ha : 0 < a)
    (hdecay : aggregate t ≤ aggregate t₀ * Real.exp (-c * (t - t₀)))
    (hcomponent_le : a * r t ≤ aggregate t)
    (hinitial_le : aggregate t₀ ≤ initialBound) :
    r t ≤ (initialBound / a) * Real.exp (-c * (t - t₀)) := by
  have hexp_nonneg : 0 ≤ Real.exp (-c * (t - t₀)) := Real.exp_nonneg _
  have hdiv : r t ≤ aggregate t / a :=
    (le_div_iff₀ ha).2 (by nlinarith [hcomponent_le])
  have hbound : r t ≤ (aggregate t₀ / a) * Real.exp (-c * (t - t₀)) := by
    calc
      r t ≤ aggregate t / a := hdiv
      _ ≤ (aggregate t₀ * Real.exp (-c * (t - t₀))) / a := by
        exact div_le_div_of_nonneg_right hdecay (le_of_lt ha)
      _ = (aggregate t₀ / a) * Real.exp (-c * (t - t₀)) := by ring
  calc
    r t ≤ (aggregate t₀ / a) * Real.exp (-c * (t - t₀)) := hbound
    _ ≤ (initialBound / a) * Real.exp (-c * (t - t₀)) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hinitial_le (le_of_lt ha)) hexp_nonneg

/-- 正の指数率を持つ非負関数が指数包絡で抑えられるなら、その関数は零へ収束する。 -/
theorem exponential_envelope_tendsto_zero
    (f : ℝ → ℝ) (amplitude rate start : ℝ) (hrate : 0 < rate)
    (hnonneg : ∀ᶠ t in Filter.atTop, 0 ≤ f t)
    (hbound : ∀ᶠ t in Filter.atTop,
      f t ≤ amplitude * Real.exp (-rate * (t - start))) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun t : ℝ => t - start) Filter.atTop Filter.atTop := by
    change Filter.map (fun t : ℝ => t - start) Filter.atTop ≤ Filter.atTop
    rw [Filter.map_sub_atTop_eq]
  have hlinear : Filter.Tendsto (fun t : ℝ => -rate * (t - start))
      Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hrate)).2 hshift
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-rate * (t - start)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_comp_nhds_zero.mpr hlinear
  have hboundTendsto : Filter.Tendsto
      (fun t : ℝ => amplitude * Real.exp (-rate * (t - start)))
      Filter.atTop (nhds 0) := by
    simpa [mul_comm] using hexp.const_mul amplitude
  exact squeeze_zero' hnonneg hbound hboundTendsto

/-- `exp(-2ct)` 包絡に対する同じ比較補題。 -/
theorem exponential_envelope_tendsto_zero_rate_two
    (f : ℝ → ℝ) (amplitude c start : ℝ) (hc : 0 < c)
    (hnonneg : ∀ᶠ t in Filter.atTop, 0 ≤ f t)
    (hbound : ∀ᶠ t in Filter.atTop,
      f t ≤ amplitude * Real.exp (-2 * c * (t - start))) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun t : ℝ => t - start) Filter.atTop Filter.atTop := by
    change Filter.map (fun t : ℝ => t - start) Filter.atTop ≤ Filter.atTop
    rw [Filter.map_sub_atTop_eq]
  have hlinear : Filter.Tendsto (fun t : ℝ => -2 * c * (t - start))
      Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (by nlinarith)).2 hshift
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-2 * c * (t - start)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_comp_nhds_zero.mpr hlinear
  have hboundTendsto : Filter.Tendsto
      (fun t : ℝ => amplitude * Real.exp (-2 * c * (t - start)))
      Filter.atTop (nhds 0) := by
    simpa [mul_comm] using hexp.const_mul amplitude
  exact squeeze_zero' hnonneg hbound hboundTendsto

/-- 共有残差の指数評価を個人残差へ適用した定量帰結。
有限和の各項が非負であるため、共有残差が個人の重み付き残差を支配する。 -/
theorem individual_residual_exponential_bound
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (individual : I → ℝ → ℝ) (edgeMismatch : E → ℝ → ℝ)
    (w : I → ℝ) (γ : E → ℝ) (i : I) (c t₀ t initialBound : ℝ)
    (_hc : 0 < c) (hw : 0 < w i) (_hInitial : 0 < initialBound)
    (_ht : t₀ ≤ t)
    (hdecay : sharedResidual individual edgeMismatch w γ t ≤
      sharedResidual individual edgeMismatch w γ t₀ * Real.exp (-c * (t - t₀)))
    (hterms : ∀ j, 0 ≤ w j * individual j t)
    (hedges : ∀ e, 0 ≤ γ e * edgeMismatch e t)
    (hinitial : sharedResidual individual edgeMismatch w γ t₀ ≤ initialBound) :
    individual i t ≤ (initialBound / w i) * Real.exp (-c * (t - t₀)) := by
  apply component_exponential_bound (fun s => individual i s)
    (sharedResidual individual edgeMismatch w γ) c t₀ t (w i) initialBound
    hw hdecay
    (weightedIndividual_le_sharedResidual individual edgeMismatch w γ t i
      hterms hedges)
    hinitial

/-- 共有残差の指数評価を辺不整合へ適用した定量帰結。 -/
theorem edge_mismatch_exponential_bound
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (individual : I → ℝ → ℝ) (edgeMismatch : E → ℝ → ℝ)
    (w : I → ℝ) (γ : E → ℝ) (e : E) (c t₀ t initialBound : ℝ)
    (_hc : 0 < c) (hγ : 0 < γ e) (_hInitial : 0 < initialBound)
    (_ht : t₀ ≤ t)
    (hdecay : sharedResidual individual edgeMismatch w γ t ≤
      sharedResidual individual edgeMismatch w γ t₀ * Real.exp (-c * (t - t₀)))
    (hterms : ∀ i, 0 ≤ w i * individual i t)
    (hedges : ∀ f, 0 ≤ γ f * edgeMismatch f t)
    (hinitial : sharedResidual individual edgeMismatch w γ t₀ ≤ initialBound) :
    edgeMismatch e t ≤ (initialBound / γ e) * Real.exp (-c * (t - t₀)) := by
  apply component_exponential_bound (fun s => edgeMismatch e s)
    (sharedResidual individual edgeMismatch w γ) c t₀ t (γ e) initialBound
    hγ hdecay
    (weightedEdge_le_sharedResidual individual edgeMismatch w γ t e
      hterms hedges)
    hinitial

/-- 共有残差の指数散逸と距離誤差境界から共有TCZへの定量収束を得る。
`sharedPotential` の微分条件と距離境界は入力条件であり、結合や最適方策だけから
それらが導かれるとは主張しない。原文の共有零集合族に対する条件付き結論である。 -/
theorem shared_tcz_distance_exponential_decay
    {X : Type*} [PseudoMetricSpace X]
    (trajectory : ℝ → X) (sharedTCZ : ℝ → Set X)
    (sharedPotential : ℝ → ℝ) (c C t₀ t : ℝ)
    (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (hsharedTCZ_nonempty : ∀ s ∈ Set.Icc t₀ t, (sharedTCZ s).Nonempty)
    (hpotential_ac : AbsolutelyContinuousOnInterval sharedPotential t₀ t)
    (hpotential_nonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ sharedPotential s)
    (hshared_dissipation : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv sharedPotential s ≤ -2 * c * sharedPotential s)
    (hshared_error : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (sharedTCZ s)) ^ 2 ≤ C * sharedPotential s) :
    Metric.infDist (trajectory t) (sharedTCZ t) ≤
      Real.sqrt (C * sharedPotential t₀) * Real.exp (-c * (t - t₀)) := by
  exact Tomabechi.Theorem1.individual_tcz_distance_decay_of_ac_ae_derivative
    trajectory sharedTCZ sharedPotential c C t₀ t hc hC ht hsharedTCZ_nonempty
    hpotential_ac hpotential_nonneg hshared_dissipation hshared_error

/-- 定理2の共有残差を、主体別状態・個人残差・辺不整合から組み立てるデータ。
各辺コストの零点同値性は原文の `Sᵢⱼ=0 ↔ hᵢ(xᵢ)=hⱼ(xⱼ)` に対応する。 -/
structure SharedResidualSystem (I E : Type*)
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] where
  State : I → Type
  Representation : Type
  endpoint : E → I × I
  repr : ∀ i, State i → Representation
  basePotential : ∀ i, State i → ℝ → ℝ
  threshold : I → ℝ
  individual : ∀ i, State i → ℝ → ℝ
  mismatch : E → Representation → Representation → ℝ → ℝ
  individualWeight : I → ℝ
  edgeWeight : E → ℝ
  mismatch_symmetric : ∀ e u v t, mismatch e u v t = mismatch e v u t
  individualWeight_pos : ∀ i, 0 < individualWeight i
  edgeWeight_pos : ∀ e, 0 < edgeWeight e
  individual_eq_positivePart : ∀ i x t,
    individual i x t = max (basePotential i x t - threshold i) 0
  individual_nonneg : ∀ i x t, 0 ≤ individualWeight i * individual i x t
  mismatch_nonneg : ∀ e u v t, 0 ≤ mismatch e u v t
  mismatch_zero_iff : ∀ e u v t,
    mismatch e u v t = 0 ↔ u = v

namespace SharedResidualSystem

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  (D : SharedResidualSystem I E)

/-- 辺 `e` が評価する対称不整合 `Sᵢⱼ(xᵢ,xⱼ)`。 -/
def edgeResidual (x : ∀ i, D.State i) (e : E) (t : ℝ) : ℝ :=
  D.mismatch e (D.repr (D.endpoint e).1 (x (D.endpoint e).1))
    (D.repr (D.endpoint e).2 (x (D.endpoint e).2)) t

/-- 主体別の非負残差と結合辺の非負不整合を正重みで足した `Φ₂`。 -/
def potential (x : ∀ i, D.State i) (t : ℝ) : ℝ :=
  (∑ i, D.individualWeight i * D.individual i (x i) t) +
    ∑ e, D.edgeWeight e * D.edgeResidual x e t

/-- `Φ₂=0` は個人残差・辺不整合の同時消失と同値。
正重みと全項の非負性を使う、定理2の共有零集合の基本的な構造補題。 -/
theorem potential_eq_zero_iff_components_eq_zero
    (x : ∀ i, D.State i) (t : ℝ) :
    D.potential x t = 0 ↔
      (∀ i, D.individual i (x i) t = 0) ∧
      (∀ e, D.edgeResidual x e t = 0) := by
  constructor
  · intro hpotential
    have hindSum : 0 ≤ ∑ i, D.individualWeight i * D.individual i (x i) t :=
      Finset.sum_nonneg fun i _ => D.individual_nonneg i (x i) t
    have hedgeSum : 0 ≤ ∑ e, D.edgeWeight e * D.edgeResidual x e t :=
      Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
        (D.mismatch_nonneg e
        (D.repr (D.endpoint e).1 (x (D.endpoint e).1))
        (D.repr (D.endpoint e).2 (x (D.endpoint e).2)) t)
    have hindZero : ∑ i, D.individualWeight i * D.individual i (x i) t = 0 := by
      dsimp [potential] at hpotential
      linarith
    have hedgeZero : ∑ e, D.edgeWeight e * D.edgeResidual x e t = 0 := by
      dsimp [potential] at hpotential
      linarith
    constructor
    · intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => D.individual_nonneg j (x j) t)).mp hindZero i (Finset.mem_univ i)
      rcases mul_eq_zero.mp hterm with hweight | hvalue
      · exact False.elim ((ne_of_gt (D.individualWeight_pos i)) hweight)
      · exact hvalue
    · intro e
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun f _ => mul_nonneg (le_of_lt (D.edgeWeight_pos f)) (D.mismatch_nonneg f
          (D.repr (D.endpoint f).1 (x (D.endpoint f).1))
          (D.repr (D.endpoint f).2 (x (D.endpoint f).2)) t))).mp
          hedgeZero e (Finset.mem_univ e)
      rcases mul_eq_zero.mp hterm with hweight | hvalue
      · exact False.elim ((ne_of_gt (D.edgeWeight_pos e)) hweight)
      · exact hvalue
  · rintro ⟨hind, hedge⟩
    have hindZero : ∑ i, D.individualWeight i * D.individual i (x i) t = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hind i, mul_zero]
    have hedgeZero : ∑ e, D.edgeWeight e * D.edgeResidual x e t = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [hedge e, mul_zero]
    simp [potential, hindZero, hedgeZero]

/-- 共有残差が零なら、各結合辺上で全主体の表象が一致する。 -/
theorem representations_agree_on_edges_of_potential_eq_zero
    (x : ∀ i, D.State i) (t : ℝ) (hzero : D.potential x t = 0)
    (e : E) :
    D.repr (D.endpoint e).1 (x (D.endpoint e).1) =
      D.repr (D.endpoint e).2 (x (D.endpoint e).2) := by
  have hcomponents := (D.potential_eq_zero_iff_components_eq_zero x t).mp hzero
  exact (D.mismatch_zero_iff e
    (D.repr (D.endpoint e).1 (x (D.endpoint e).1))
    (D.repr (D.endpoint e).2 (x (D.endpoint e).2)) t).mp (hcomponents.2 e)

/-- 構造データ `endpoint` が定める無向隣接関係。 -/
def systemAdjacent (D : SharedResidualSystem I E) (i j : I) : Prop :=
  ∃ e, ((D.endpoint e).1 = i ∧ (D.endpoint e).2 = j) ∨
    ((D.endpoint e).1 = j ∧ (D.endpoint e).2 = i)

/-- 共有残差が零で、辺グラフが連結なら全主体の表象が一致する。 -/
theorem representations_agree_of_connected
    (x : ∀ i, D.State i) (t : ℝ) (hzero : D.potential x t = 0)
    (connected : ∀ i j, Relation.ReflTransGen (systemAdjacent D) i j) :
    ∀ i j, D.repr i (x i) = D.repr j (x j) := by
  have hedgeEq : ∀ i j, systemAdjacent D i j → D.repr i (x i) = D.repr j (x j) := by
    intro i j hadj
    rcases hadj with ⟨e, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · have heq := D.representations_agree_on_edges_of_potential_eq_zero x t hzero e
      rw [← h₁, ← h₂]
      exact heq
    · have heq := D.representations_agree_on_edges_of_potential_eq_zero x t hzero e
      rw [← h₂, ← h₁]
      exact heq.symm
  intro i j
  have hwalk := connected i j
  induction hwalk with
  | refl => rfl
  | tail hpath hstep ih => exact ih.trans (hedgeEq _ _ hstep)

/-- 共有残差が零となる閉到達可能領域内の時刻別TCZスライス。 -/
def sharedTCZ (D : SharedResidualSystem I E)
    (K : Set (∀ i, D.State i)) (t : ℝ) : Set (∀ i, D.State i) :=
  {x | x ∈ K ∧ D.potential x t = 0}

/-- 定理2の条件付き結論を一括して返す。
共通Lyapunov残差のAC・a.e.指数散逸、共有TCZの非空性、距離誤差境界を仮定し、
共有TCZまでの距離と個人残差・辺不整合の定量減衰を得る。さらに連結性から、
共有TCZ上では全主体の表象が一致する。 -/
theorem theorem2_conditional_conclusion
    (D : SharedResidualSystem I E)
    [∀ i, PseudoMetricSpace (D.State i)]
    (K : Set (∀ i, D.State i)) (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen (D.systemAdjacent) i j)
    (c C t₀ t : ℝ) (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (htrajectory_K : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ K)
    (hshared_nonempty : ∀ s ∈ Set.Icc t₀ t, (D.sharedTCZ K s).Nonempty)
    (hphi_ac : AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ t)
    (hphi_decay : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (D.sharedTCZ K s)) ^ 2 ≤
        C * D.potential (trajectory s) s) :
    (trajectory t ∈ K ∧ Metric.infDist (trajectory t) (D.sharedTCZ K t) ≤
        Real.sqrt (C * D.potential (trajectory t₀) t₀) *
          Real.exp (-c * (t - t₀))) ∧
    (∀ i, D.individual i (trajectory t i) t ≤
      (D.potential (trajectory t₀) t₀ / D.individualWeight i) *
        Real.exp (-2 * c * (t - t₀))) ∧
    (∀ e, D.edgeResidual (trajectory t) e t ≤
      (D.potential (trajectory t₀) t₀ / D.edgeWeight e) *
        Real.exp (-2 * c * (t - t₀))) ∧
    (∀ s ∈ Set.Icc t₀ t, ∀ x ∈ D.sharedTCZ K s, ∀ i j,
      D.repr i (x i) = D.repr j (x j)) := by
  let phi : ℝ → ℝ := fun s => D.potential (trajectory s) s
  have hphi_nonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ phi s := by
    intro s hs
    dsimp [phi, SharedResidualSystem.potential]
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => D.individual_nonneg i (trajectory s i) s
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
        (D.mismatch_nonneg e
        (D.repr (D.endpoint e).1 (trajectory s (D.endpoint e).1))
        (D.repr (D.endpoint e).2 (trajectory s (D.endpoint e).2)) s)
  have hphi_exp := Tomabechi.Theorem1.lyapunov_exponential_decay_of_ac_ae_derivative
    phi c t₀ t hc ht hphi_ac hphi_decay
  have hindividual (i : I) : D.individual i (trajectory t i) t ≤
      (phi t₀ / D.individualWeight i) * Real.exp (-2 * c * (t - t₀)) := by
    have hcomponent : D.individualWeight i * D.individual i (trajectory t i) t ≤ phi t := by
      dsimp [phi, SharedResidualSystem.potential]
      have hsum := Finset.single_le_sum
        (fun j _ => D.individual_nonneg j (trajectory t j) t) (Finset.mem_univ i)
      have hedgeSum : 0 ≤ ∑ e, D.edgeWeight e * D.edgeResidual (trajectory t) e t :=
        Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
          (D.mismatch_nonneg e
          (D.repr (D.endpoint e).1 (trajectory t (D.endpoint e).1))
          (D.repr (D.endpoint e).2 (trajectory t (D.endpoint e).2)) t)
      linarith
    have hbound := component_exponential_bound
      (fun s => D.individual i (trajectory s i) s) phi (2 * c) t₀ t
      (D.individualWeight i) (phi t₀) (D.individualWeight_pos i)
      (by simpa [phi] using hphi_exp)
      hcomponent
      le_rfl
    simpa [mul_assoc] using hbound
  have hedge (e : E) : D.edgeResidual (trajectory t) e t ≤
      (phi t₀ / D.edgeWeight e) * Real.exp (-2 * c * (t - t₀)) := by
    have hcomponent : D.edgeWeight e * D.edgeResidual (trajectory t) e t ≤ phi t := by
      dsimp [phi, SharedResidualSystem.potential, SharedResidualSystem.edgeResidual]
      have hsum := Finset.single_le_sum
        (fun f _ => mul_nonneg (le_of_lt (D.edgeWeight_pos f)) (D.mismatch_nonneg f
          (D.repr (D.endpoint f).1 (trajectory t (D.endpoint f).1))
          (D.repr (D.endpoint f).2 (trajectory t (D.endpoint f).2)) t))
        (Finset.mem_univ e)
      have hindSum : 0 ≤ ∑ i, D.individualWeight i * D.individual i (trajectory t i) t :=
        Finset.sum_nonneg fun i _ => D.individual_nonneg i (trajectory t i) t
      linarith
    have hbound := component_exponential_bound
      (fun s => D.edgeResidual (trajectory s) e s) phi (2 * c) t₀ t
      (D.edgeWeight e) (phi t₀) (D.edgeWeight_pos e)
      (by simpa [phi] using hphi_exp)
      hcomponent
      le_rfl
    simpa [mul_assoc] using hbound
  have hdistance := shared_tcz_distance_exponential_decay
    trajectory (D.sharedTCZ K) phi c C t₀ t hc hC ht hshared_nonempty
    (by simpa [phi] using hphi_ac) hphi_nonneg hphi_decay hdistance_error
  refine ⟨⟨htrajectory_K t ⟨ht, le_rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · simpa [phi] using hdistance
  · intro i
    simpa [phi] using hindividual i
  · intro e
    simpa [phi] using hedge e
  · intro s hs x hx i j
    have hz : D.potential x s = 0 := hx.2
    exact D.representations_agree_of_connected x s hz connected i j

/-- 任意の終端時刻で上の条件付き評価が使えるときの定性的収束API。
各結論は指数包絡から導く。共有残差・軌道・距離境界に関する大域条件は入力仮定である。 -/
theorem theorem2_tendsto_zero
    (D : SharedResidualSystem I E)
    [∀ i, PseudoMetricSpace (D.State i)]
    (K : Set (∀ i, D.State i)) (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen (D.systemAdjacent) i j)
    (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C)
    (htrajectory_K : ∀ s ≥ t₀, trajectory s ∈ K)
    (hshared_nonempty : ∀ s ≥ t₀, (D.sharedTCZ K s).Nonempty)
    (hphi_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ T)
    (hphi_decay : ∀ T ≥ t₀, ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (trajectory s) (D.sharedTCZ K s)) ^ 2 ≤
        C * D.potential (trajectory s) s) :
    Filter.Tendsto (fun s => Metric.infDist (trajectory s) (D.sharedTCZ K s))
        Filter.atTop (nhds 0) ∧
    (∀ i, Filter.Tendsto (fun s => D.individual i (trajectory s i) s)
      Filter.atTop (nhds 0)) ∧
    (∀ e, Filter.Tendsto (fun s => D.edgeResidual (trajectory s) e s)
      Filter.atTop (nhds 0)) := by
  let distAlong : ℝ → ℝ := fun s => Metric.infDist (trajectory s) (D.sharedTCZ K s)
  let phi₀ := D.potential (trajectory t₀) t₀
  have hdistNonneg : ∀ᶠ s in Filter.atTop, 0 ≤ distAlong s :=
    Filter.Eventually.of_forall fun _ => Metric.infDist_nonneg
  have hdistBound : ∀ᶠ s in Filter.atTop,
      distAlong s ≤ Real.sqrt (C * phi₀) * Real.exp (-c * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    have hpoint := D.theorem2_conditional_conclusion K trajectory connected c C t₀ s
      hc hC hs
      (fun r hr => htrajectory_K r hr.1)
      (fun r hr => hshared_nonempty r hr.1)
      (hphi_ac s hs) (hphi_decay s hs)
      (fun r hr => hdistance_error r hr.1)
    simpa [distAlong, phi₀] using hpoint.1.2
  have hdistTendsto := exponential_envelope_tendsto_zero distAlong
    (Real.sqrt (C * phi₀)) c t₀ hc hdistNonneg hdistBound
  have hindividualTendsto (i : I) : Filter.Tendsto
      (fun s => D.individual i (trajectory s i) s) Filter.atTop (nhds 0) := by
    have hnonneg : ∀ᶠ s in Filter.atTop, 0 ≤ D.individual i (trajectory s i) s :=
      Filter.Eventually.of_forall fun s => by
        rw [D.individual_eq_positivePart]
        exact le_max_right _ _
    have hbound : ∀ᶠ s in Filter.atTop,
        D.individual i (trajectory s i) s ≤
          (phi₀ / D.individualWeight i) * Real.exp (-2 * c * (s - t₀)) := by
      filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
      have hpoint := D.theorem2_conditional_conclusion K trajectory connected c C t₀ s
        hc hC hs
        (fun r hr => htrajectory_K r hr.1)
        (fun r hr => hshared_nonempty r hr.1)
        (hphi_ac s hs) (hphi_decay s hs)
        (fun r hr => hdistance_error r hr.1)
      simpa [phi₀] using hpoint.2.1 i
    exact exponential_envelope_tendsto_zero_rate_two _
      (phi₀ / D.individualWeight i) c t₀ hc hnonneg hbound
  have hedgeTendsto (e : E) : Filter.Tendsto
      (fun s => D.edgeResidual (trajectory s) e s) Filter.atTop (nhds 0) := by
    have hnonneg : ∀ᶠ s in Filter.atTop, 0 ≤ D.edgeResidual (trajectory s) e s :=
      Filter.Eventually.of_forall fun s =>
        D.mismatch_nonneg e
          (D.repr (D.endpoint e).1 (trajectory s (D.endpoint e).1))
          (D.repr (D.endpoint e).2 (trajectory s (D.endpoint e).2)) s
    have hbound : ∀ᶠ s in Filter.atTop,
        D.edgeResidual (trajectory s) e s ≤
          (phi₀ / D.edgeWeight e) * Real.exp (-2 * c * (s - t₀)) := by
      filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
      have hpoint := D.theorem2_conditional_conclusion K trajectory connected c C t₀ s
        hc hC hs
        (fun r hr => htrajectory_K r hr.1)
        (fun r hr => hshared_nonempty r hr.1)
        (hphi_ac s hs) (hphi_decay s hs)
        (fun r hr => hdistance_error r hr.1)
      simpa [phi₀] using hpoint.2.2.1 e
    exact exponential_envelope_tendsto_zero_rate_two _
      (phi₀ / D.edgeWeight e) c t₀ hc hnonneg hbound
  exact ⟨hdistTendsto, hindividualTendsto, hedgeTendsto⟩

end SharedResidualSystem

/-! ## 状態対に直接作用する辺不整合

旧 `SharedResidualSystem` は `Sᵢⱼ` を表象値から計算する特殊形だった。
以下では主体の依存型状態を直接受け取る辺コストを定義する。零点条件だけが
表象一致を指定し、正の重み付き有限和から各成分評価・連結整合を得る。
-/

/-- 表象写像を経由せず、辺両端の状態に直接作用する不整合コスト。 -/
structure StatePairResidualSystem (I E : Type*)
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] where
  State : I → Type
  Representation : Type
  endpoint : E → I × I
  reverseEdge : E → E
  reverseEdge_involutive : ∀ e, reverseEdge (reverseEdge e) = e
  reverse_endpoint_left : ∀ e,
    (endpoint (reverseEdge e)).1 = (endpoint e).2
  reverse_endpoint_right : ∀ e,
    (endpoint (reverseEdge e)).2 = (endpoint e).1
  repr : ∀ i, State i → Representation
  basePotential : ∀ i, State i → ℝ → ℝ
  threshold : I → ℝ
  individual : ∀ i, State i → ℝ → ℝ
  individualWeight : I → ℝ
  edgeWeight : E → ℝ
  edgeWeight_reverse : ∀ e, edgeWeight (reverseEdge e) = edgeWeight e
  mismatch : ∀ e, State (endpoint e).1 → State (endpoint e).2 → ℝ → ℝ
  reverseLeft : ∀ e, State (endpoint e).1 →
    State (endpoint (reverseEdge e)).2
  reverseRight : ∀ e, State (endpoint e).2 →
    State (endpoint (reverseEdge e)).1
  reverseLeft_repr : ∀ e x,
    repr (endpoint (reverseEdge e)).2 (reverseLeft e x) = repr (endpoint e).1 x
  reverseRight_repr : ∀ e y,
    repr (endpoint (reverseEdge e)).1 (reverseRight e y) = repr (endpoint e).2 y
  mismatch_symmetric : ∀ e x y t,
    mismatch e x y t = mismatch (reverseEdge e) (reverseRight e y) (reverseLeft e x) t
  mismatch_nonneg : ∀ e x y t, 0 ≤ mismatch e x y t
  mismatch_zero_iff : ∀ e x y t, mismatch e x y t = 0 ↔ repr (endpoint e).1 x = repr (endpoint e).2 y
  individualWeight_pos : ∀ i, 0 < individualWeight i
  edgeWeight_pos : ∀ e, 0 < edgeWeight e
  individual_nonneg : ∀ i x t, 0 ≤ individualWeight i * individual i x t
  individual_eq_positivePart : ∀ i x t,
    individual i x t = max (basePotential i x t - threshold i) 0

namespace StatePairResidualSystem

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  (D : StatePairResidualSystem I E)

/-- 依存型状態上の `Φ₂`。辺項は表象ではなく状態対を直接評価する。 -/
def potential (x : ∀ i, D.State i) (t : ℝ) : ℝ :=
  (∑ i, D.individualWeight i * D.individual i (x i) t) +
    ∑ e, D.edgeWeight e * D.mismatch e (x (D.endpoint e).1) (x (D.endpoint e).2) t

/-- `Φ₂=0` は個人残差と全状態辺不整合の同時消失と同値。 -/
theorem potential_eq_zero_iff_components_eq_zero (x : ∀ i, D.State i) (t : ℝ) :
    D.potential x t = 0 ↔
      (∀ i, D.individual i (x i) t = 0) ∧
      (∀ e, D.mismatch e (x (D.endpoint e).1) (x (D.endpoint e).2) t = 0) := by
  constructor
  · intro hz
    have hi : 0 ≤ ∑ i, D.individualWeight i * D.individual i (x i) t :=
      Finset.sum_nonneg fun i _ => D.individual_nonneg i (x i) t
    have he : 0 ≤ ∑ e, D.edgeWeight e * D.mismatch e (x (D.endpoint e).1)
        (x (D.endpoint e).2) t :=
      Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
        (D.mismatch_nonneg e _ _ t)
    have hi0 : ∑ i, D.individualWeight i * D.individual i (x i) t = 0 := by
      dsimp [potential] at hz
      linarith
    have he0 : ∑ e, D.edgeWeight e * D.mismatch e (x (D.endpoint e).1)
        (x (D.endpoint e).2) t = 0 := by
      dsimp [potential] at hz
      linarith
    constructor
    · intro i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => D.individual_nonneg j (x j) t)).mp hi0 i (Finset.mem_univ i)
      rcases mul_eq_zero.mp hterm with hw | hv
      · exact False.elim ((ne_of_gt (D.individualWeight_pos i)) hw)
      · exact hv
    · intro e
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun f _ => mul_nonneg (le_of_lt (D.edgeWeight_pos f))
          (D.mismatch_nonneg f _ _ t))).mp he0 e (Finset.mem_univ e)
      rcases mul_eq_zero.mp hterm with hw | hv
      · exact False.elim ((ne_of_gt (D.edgeWeight_pos e)) hw)
      · exact hv
  · rintro ⟨hi, he⟩
    have hi0 : ∑ i, D.individualWeight i * D.individual i (x i) t = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hi i, mul_zero]
    have he0 : ∑ e, D.edgeWeight e * D.mismatch e (x (D.endpoint e).1)
        (x (D.endpoint e).2) t = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [he e, mul_zero]
    simp [potential, hi0, he0]

/-- 零になった状態辺コストは、その端点の表象を一致させる。 -/
theorem repr_eq_of_mismatch_eq_zero (x : ∀ i, D.State i) (t : ℝ) (e : E)
    (hz : D.mismatch e (x (D.endpoint e).1) (x (D.endpoint e).2) t = 0) :
    D.repr (D.endpoint e).1 (x (D.endpoint e).1) =
      D.repr (D.endpoint e).2 (x (D.endpoint e).2) :=
  (D.mismatch_zero_iff e _ _ t).mp hz

/-- A zero shared residual gives complete representation agreement on every
connected graph, using only the component zero-equivalences. -/
theorem representations_agree_of_potential_eq_zero
    (x : ∀ i, D.State i) (t : ℝ) (hzero : D.potential x t = 0)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j) :
    ∀ i j, D.repr i (x i) = D.repr j (x j) := by
  have hparts := (D.potential_eq_zero_iff_components_eq_zero x t).mp hzero
  have hedgeEq : ∀ a b, (∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
      ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) →
      D.repr a (x a) = D.repr b (x b) := by
    intro a b hadj
    rcases hadj with ⟨e, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · have hrepr := D.repr_eq_of_mismatch_eq_zero x t e (hparts.2 e)
      rw [← h₁, ← h₂]
      exact hrepr
    · have hrepr := D.repr_eq_of_mismatch_eq_zero x t e (hparts.2 e)
      rw [← h₂, ← h₁]
      exact hrepr.symm
  intro i j
  have hpath := connected i j
  induction hpath with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hedgeEq _ _ hstep)

/-- 閉到達可能領域に制限した共有TCZ。 -/
def sharedTCZ (K : Set (∀ i, D.State i)) (t : ℝ) : Set (∀ i, D.State i) :=
  {x | x ∈ K ∧ D.potential x t = 0}

/-- 状態対不整合版の定理2。原文の正準個人残差・共有残差のAC/散逸・距離誤差境界を
入口にし、共有TCZへの距離指数評価、個人残差と状態対不整合の指数評価、連結した
グラフ上の表象一致、個人残差の極限を一つの結論として返す。
不整合は端点の状態に直接作用し、表象写像を通じた因子化を仮定しない。 -/
theorem theorem2_state_pair_conditional_conclusion
    [∀ i, PseudoMetricSpace (D.State i)]
    (K : Set (∀ i, D.State i)) (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ t : ℝ) (hc : 0 < c) (hC : 0 < C) (ht : t₀ ≤ t)
    (htrajectory_K : ∀ s ∈ Set.Icc t₀ t, trajectory s ∈ K)
    (hshared_nonempty : ∀ s ∈ Set.Icc t₀ t, (D.sharedTCZ K s).Nonempty)
    (hphi_ac : AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ t)
    (hphi_decay : ∀ᵐ s ∂volume.restrict (Set.Icc t₀ t),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ∈ Set.Icc t₀ t,
      (Metric.infDist (trajectory s) (D.sharedTCZ K s)) ^ 2 ≤
        C * D.potential (trajectory s) s) :
    (trajectory t ∈ K ∧ Metric.infDist (trajectory t) (D.sharedTCZ K t) ≤
        Real.sqrt (C * D.potential (trajectory t₀) t₀) *
          Real.exp (-c * (t - t₀))) ∧
    (∀ i, D.individual i (trajectory t i) t ≤
      (D.potential (trajectory t₀) t₀ / D.individualWeight i) *
        Real.exp (-2 * c * (t - t₀))) ∧
    (∀ e, D.mismatch e (trajectory t (D.endpoint e).1)
      (trajectory t (D.endpoint e).2) t ≤
      (D.potential (trajectory t₀) t₀ / D.edgeWeight e) *
        Real.exp (-2 * c * (t - t₀))) ∧
    (∀ s ∈ Set.Icc t₀ t, ∀ x ∈ D.sharedTCZ K s, ∀ i j,
      D.repr i (x i) = D.repr j (x j)) := by
  let phi : ℝ → ℝ := fun s => D.potential (trajectory s) s
  have hnonneg : ∀ s ∈ Set.Icc t₀ t, 0 ≤ phi s := by
    intro s _
    dsimp [phi, potential]
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => D.individual_nonneg i (trajectory s i) s
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
        (D.mismatch_nonneg e _ _ s)
  have hexp := Tomabechi.Theorem1.lyapunov_exponential_decay_of_ac_ae_derivative
    phi c t₀ t hc ht hphi_ac hphi_decay
  have hdistance := Tomabechi.Theorem1.individual_tcz_distance_decay_of_ac_ae_derivative
    trajectory (D.sharedTCZ K) phi c C t₀ t hc hC ht hshared_nonempty
    (by simpa [phi] using hphi_ac) hnonneg hphi_decay hdistance_error
  have hindividual (i : I) : D.individual i (trajectory t i) t ≤
      (phi t₀ / D.individualWeight i) * Real.exp (-2 * c * (t - t₀)) := by
    have hcomponent : D.individualWeight i * D.individual i (trajectory t i) t ≤ phi t := by
      dsimp [phi, potential]
      have hsum := Finset.single_le_sum
        (fun j _ => D.individual_nonneg j (trajectory t j) t) (Finset.mem_univ i)
      have hedge : 0 ≤ ∑ e, D.edgeWeight e *
          D.mismatch e (trajectory t (D.endpoint e).1) (trajectory t (D.endpoint e).2) t :=
        Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (D.edgeWeight_pos e))
          (D.mismatch_nonneg e _ _ t)
      linarith
    have hb := Tomabechi.Theorem2.component_exponential_bound
      (fun s => D.individual i (trajectory s i) s) phi (2 * c) t₀ t
      (D.individualWeight i) (phi t₀) (D.individualWeight_pos i)
      (by simpa [phi] using hexp) hcomponent le_rfl
    simpa [phi, mul_assoc] using hb
  have hedge (e : E) : D.mismatch e (trajectory t (D.endpoint e).1)
      (trajectory t (D.endpoint e).2) t ≤
      (phi t₀ / D.edgeWeight e) * Real.exp (-2 * c * (t - t₀)) := by
    have hcomponent : D.edgeWeight e *
        D.mismatch e (trajectory t (D.endpoint e).1) (trajectory t (D.endpoint e).2) t ≤
        phi t := by
      dsimp [phi, potential]
      have hsum := Finset.single_le_sum
        (fun f _ => mul_nonneg (le_of_lt (D.edgeWeight_pos f))
          (D.mismatch_nonneg f (trajectory t (D.endpoint f).1)
            (trajectory t (D.endpoint f).2) t)) (Finset.mem_univ e)
      have hind : 0 ≤ ∑ i, D.individualWeight i * D.individual i (trajectory t i) t :=
        Finset.sum_nonneg fun i _ => D.individual_nonneg i (trajectory t i) t
      linarith
    have hb := Tomabechi.Theorem2.component_exponential_bound
      (fun s => D.mismatch e (trajectory s (D.endpoint e).1)
        (trajectory s (D.endpoint e).2) s) phi (2 * c) t₀ t
      (D.edgeWeight e) (phi t₀) (D.edgeWeight_pos e)
      (by simpa [phi] using hexp) hcomponent le_rfl
    simpa [phi, mul_assoc] using hb
  refine ⟨⟨htrajectory_K t ⟨ht, le_rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · simpa [phi] using hdistance
  · intro i
    simpa [phi] using hindividual i
  · intro e
    simpa [phi] using hedge e
  · intro s hs x hx i j
    have hzero : D.potential x s = 0 := hx.2
    have hparts := (D.potential_eq_zero_iff_components_eq_zero x s).mp hzero
    have hedgeEq : ∀ a b, (∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) → D.repr a (x a) = D.repr b (x b) := by
      intro a b hadj
      rcases hadj with ⟨e, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · have hrepr := D.repr_eq_of_mismatch_eq_zero x s e (hparts.2 e)
        rw [← h₁, ← h₂]
        exact hrepr
      · have hrepr := D.repr_eq_of_mismatch_eq_zero x s e (hparts.2 e)
        rw [← h₂, ← h₁]
        exact hrepr.symm
    have hpath := connected i j
    induction hpath with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (hedgeEq _ _ hstep)

/-- 状態対不整合版の大域収束。すべての終端時刻で原文の区間条件が成り立つとき、
有限時刻版から距離・個人残差・各状態対不整合の指数包絡を取り出し、各々の極限を得る。 -/
theorem theorem2_state_pair_tendsto_zero
    [∀ i, PseudoMetricSpace (D.State i)]
    (K : Set (∀ i, D.State i)) (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C)
    (htrajectory_K : ∀ s ≥ t₀, trajectory s ∈ K)
    (hshared_nonempty : ∀ s ≥ t₀, (D.sharedTCZ K s).Nonempty)
    (hphi_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ T)
    (hphi_decay : ∀ T ≥ t₀, ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (trajectory s) (D.sharedTCZ K s)) ^ 2 ≤
        C * D.potential (trajectory s) s) :
    Filter.Tendsto (fun s => Metric.infDist (trajectory s) (D.sharedTCZ K s))
        Filter.atTop (nhds 0) ∧
    (∀ i, Filter.Tendsto (fun s => D.individual i (trajectory s i) s)
      Filter.atTop (nhds 0)) ∧
    (∀ e, Filter.Tendsto
      (fun s => D.mismatch e (trajectory s (D.endpoint e).1)
        (trajectory s (D.endpoint e).2) s) Filter.atTop (nhds 0)) := by
  let phi₀ := D.potential (trajectory t₀) t₀
  let distAlong : ℝ → ℝ := fun s =>
    Metric.infDist (trajectory s) (D.sharedTCZ K s)
  have hdistNonneg : ∀ᶠ s in Filter.atTop, 0 ≤ distAlong s :=
    Filter.Eventually.of_forall fun _ => Metric.infDist_nonneg
  have hdistBound : ∀ᶠ s in Filter.atTop,
      distAlong s ≤ Real.sqrt (C * phi₀) * Real.exp (-c * (s - t₀)) := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
    have hpoint := D.theorem2_state_pair_conditional_conclusion K trajectory connected
      c C t₀ s hc hC hs (fun r hr => htrajectory_K r hr.1)
      (fun r hr => hshared_nonempty r hr.1) (hphi_ac s hs) (hphi_decay s hs)
      (fun r hr => hdistance_error r hr.1)
    simpa [distAlong, phi₀] using hpoint.1.2
  have hdist := Tomabechi.Theorem2.exponential_envelope_tendsto_zero
    distAlong (Real.sqrt (C * phi₀)) c t₀ hc hdistNonneg hdistBound
  have hindividual (i : I) : Filter.Tendsto
      (fun s => D.individual i (trajectory s i) s) Filter.atTop (nhds 0) := by
    have hnonneg : ∀ᶠ s in Filter.atTop, 0 ≤ D.individual i (trajectory s i) s :=
      Filter.Eventually.of_forall fun s => by
        rw [D.individual_eq_positivePart]
        exact le_max_right _ _
    have hbound : ∀ᶠ s in Filter.atTop,
        D.individual i (trajectory s i) s ≤
          (phi₀ / D.individualWeight i) * Real.exp (-2 * c * (s - t₀)) := by
      filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
      have hpoint := D.theorem2_state_pair_conditional_conclusion K trajectory connected
        c C t₀ s hc hC hs (fun r hr => htrajectory_K r hr.1)
        (fun r hr => hshared_nonempty r hr.1) (hphi_ac s hs) (hphi_decay s hs)
        (fun r hr => hdistance_error r hr.1)
      simpa [phi₀] using hpoint.2.1 i
    exact Tomabechi.Theorem2.exponential_envelope_tendsto_zero_rate_two _
      (phi₀ / D.individualWeight i) c t₀ hc hnonneg hbound
  have hedge (e : E) : Filter.Tendsto
      (fun s => D.mismatch e (trajectory s (D.endpoint e).1)
        (trajectory s (D.endpoint e).2) s) Filter.atTop (nhds 0) := by
    have hnonneg : ∀ᶠ s in Filter.atTop,
        0 ≤ D.mismatch e (trajectory s (D.endpoint e).1)
          (trajectory s (D.endpoint e).2) s :=
      Filter.Eventually.of_forall fun s => D.mismatch_nonneg e
        (trajectory s (D.endpoint e).1) (trajectory s (D.endpoint e).2) s
    have hbound : ∀ᶠ s in Filter.atTop,
        D.mismatch e (trajectory s (D.endpoint e).1)
          (trajectory s (D.endpoint e).2) s ≤
          (phi₀ / D.edgeWeight e) * Real.exp (-2 * c * (s - t₀)) := by
      filter_upwards [Filter.eventually_ge_atTop t₀] with s hs
      have hpoint := D.theorem2_state_pair_conditional_conclusion K trajectory connected
        c C t₀ s hc hC hs (fun r hr => htrajectory_K r hr.1)
        (fun r hr => hshared_nonempty r hr.1) (hphi_ac s hs) (hphi_decay s hs)
        (fun r hr => hdistance_error r hr.1)
      simpa [phi₀] using hpoint.2.2.1 e
    exact Tomabechi.Theorem2.exponential_envelope_tendsto_zero_rate_two _
      (phi₀ / D.edgeWeight e) c t₀ hc hnonneg hbound
  exact ⟨hdist, hindividual, hedge⟩

/-- 定理2の共有TCZを、選択済み共同方策の時刻別到達集合から作った閉包へ
接続する。軌道所属・共有零スライスの非空性・散逸・誤差境界は同じ方策の
到達データに対する入力として保ち、共有距離・個人残差・辺不整合の極限を返す。 -/
theorem theorem2_reachable_state_pair_tendsto_zero
    [∀ i, PseudoMetricSpace (D.State i)]
    (reachableAt : ℝ → Set (∀ i, D.State i))
    (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (htrajectory_reachable : ∀ s ≥ t₀, trajectory s ∈ reachableAt s)
    (hshared_nonempty : ∀ s ≥ t₀,
      (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s).Nonempty)
    (hphi_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ T)
    (hphi_decay : ∀ T ≥ t₀, ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ≥ t₀,
      (Metric.infDist (trajectory s)
        (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s)) ^ 2 ≤
          C * D.potential (trajectory s) s) :
    (∀ s ≥ t₀, trajectory s ∈
      Tomabechi.Theorem1.closedLoopReachableSet reachableAt) ∧
    (Filter.Tendsto (fun s => Metric.infDist (trajectory s)
        (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s))
        Filter.atTop (nhds 0) ∧
      (∀ i, Filter.Tendsto
        (fun s => D.individual i (trajectory s i) s) Filter.atTop (nhds 0)) ∧
      (∀ e, Filter.Tendsto
        (fun s => D.mismatch e (trajectory s (D.endpoint e).1)
          (trajectory s (D.endpoint e).2) s) Filter.atTop (nhds 0))) := by
  constructor
  · intro s hs
    exact Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt
      reachableAt (le_trans ht₀ hs) (htrajectory_reachable s hs)
  · exact D.theorem2_state_pair_tendsto_zero
      (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) trajectory connected
      c C t₀ hc hC
      (fun s hs => Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt
        reachableAt (le_trans ht₀ hs) (htrajectory_reachable s hs))
      hshared_nonempty hphi_ac hphi_decay hdistance_error

/-! A structured result keeps the quantitative Theorem 2 outputs readable and
available separately to downstream proofs. -/
structure ReachableStatePairConclusion
    (D : StatePairResidualSystem I E)
    [∀ i, PseudoMetricSpace (D.State i)]
    (reachableAt : ℝ → Set (∀ i, D.State i))
    (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ : ℝ) : Prop where
  trajectory_in_closed_reachable : ∀ s ≥ t₀,
    trajectory s ∈ Tomabechi.Theorem1.closedLoopReachableSet reachableAt
  quantitative_bounds : ∀ t, t₀ ≤ t →
    Metric.infDist (trajectory t)
      (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) t) ≤
        Real.sqrt (C * D.potential (trajectory t₀) t₀) *
          Real.exp (-c * (t - t₀)) ∧
    (∀ i, D.individual i (trajectory t i) t ≤
      (D.potential (trajectory t₀) t₀ / D.individualWeight i) *
        Real.exp (-2 * c * (t - t₀))) ∧
    (∀ e, D.mismatch e (trajectory t (D.endpoint e).1)
      (trajectory t (D.endpoint e).2) t ≤
      (D.potential (trajectory t₀) t₀ / D.edgeWeight e) *
        Real.exp (-2 * c * (t - t₀)))
  representation_agreement_on_shared_tcz : ∀ s ≥ t₀, ∀ y ∈
    D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s,
    ∀ i j, D.repr i (y i) = D.repr j (y j)
  shared_distance_tendsto_zero : Filter.Tendsto
    (fun s => Metric.infDist (trajectory s)
      (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s))
    Filter.atTop (nhds 0)
  individual_residual_tendsto_zero : ∀ i, Filter.Tendsto
    (fun s => D.individual i (trajectory s i) s) Filter.atTop (nhds 0)
  edge_mismatch_tendsto_zero : ∀ e, Filter.Tendsto
    (fun s => D.mismatch e (trajectory s (D.endpoint e).1)
      (trajectory s (D.endpoint e).2) s) Filter.atTop (nhds 0)

/-- 同じ閉到達可能TCZ入口から、定理2の距離・個人残差・辺不整合の指数率と
それぞれの極限をまとめて返す。有限時間部分は条件付き定量核を各終端時刻へ適用する。 -/
theorem theorem2_reachable_state_pair_quantitative_conclusion
    [∀ i, PseudoMetricSpace (D.State i)]
    (reachableAt : ℝ → Set (∀ i, D.State i))
    (trajectory : ℝ → ∀ i, D.State i)
    (connected : ∀ i j, Relation.ReflTransGen
      (fun a b => ∃ e, ((D.endpoint e).1 = a ∧ (D.endpoint e).2 = b) ∨
        ((D.endpoint e).1 = b ∧ (D.endpoint e).2 = a)) i j)
    (c C t₀ : ℝ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 ≤ t₀)
    (htrajectory_reachable : ∀ s ≥ t₀, trajectory s ∈ reachableAt s)
    (hshared_nonempty : ∀ s ≥ t₀,
      (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s).Nonempty)
    (hphi_ac : ∀ T ≥ t₀, AbsolutelyContinuousOnInterval
      (fun s => D.potential (trajectory s) s) t₀ T)
    (hphi_decay : ∀ T ≥ t₀, ∀ᵐ s ∂volume.restrict (Set.Icc t₀ T),
      deriv (fun s => D.potential (trajectory s) s) s ≤
        -2 * c * D.potential (trajectory s) s)
    (hdistance_error : ∀ s ≥ t₀,
    (Metric.infDist (trajectory s)
        (D.sharedTCZ (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) s)) ^ 2 ≤
          C * D.potential (trajectory s) s) :
    ReachableStatePairConclusion D reachableAt trajectory connected c C t₀ := by
  have hK : ∀ s ≥ t₀,
      trajectory s ∈ Tomabechi.Theorem1.closedLoopReachableSet reachableAt := by
    intro s hs
    exact Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt
      reachableAt (le_trans ht₀ hs) (htrajectory_reachable s hs)
  have hlimits := D.theorem2_state_pair_tendsto_zero
    (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) trajectory connected
    c C t₀ hc hC hK hshared_nonempty hphi_ac hphi_decay hdistance_error
  refine ⟨hK, ?_, ?_, hlimits.1, hlimits.2.1, hlimits.2.2⟩
  intro t ht
  have hpoint := D.theorem2_state_pair_conditional_conclusion
    (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) trajectory connected
    c C t₀ t hc hC ht
    (fun s hs => hK s hs.1)
    (fun s hs => hshared_nonempty s hs.1)
    (hphi_ac t ht) (hphi_decay t ht)
    (fun s hs => hdistance_error s hs.1)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hpoint.1.2
  · intro i
    simpa using hpoint.2.1 i
  · intro e
    simpa using hpoint.2.2.1 e
  · intro s hs y hy i j
    have hpoint := D.theorem2_state_pair_conditional_conclusion
      (Tomabechi.Theorem1.closedLoopReachableSet reachableAt) trajectory connected
      c C t₀ s hc hC hs
      (fun r hr => hK r hr.1)
      (fun r hr => hshared_nonempty r hr.1)
      (hphi_ac s hs) (hphi_decay s hs)
      (fun r hr => hdistance_error r hr.1)
    exact hpoint.2.2.2 s ⟨hs, le_rfl⟩ y hy i j

end StatePairResidualSystem

namespace SharedResidualSystem

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  (D : SharedResidualSystem I E)

/-- 表象値不整合APIを、各無向辺の二つの向きを持つ状態対APIへ埋め込む。
辺重みを半分にするため、二方向を合計した共有残差は元の `Φ₂` と一致する。 -/
noncomputable def toStatePairResidualSystem : StatePairResidualSystem I (E × Bool) where
  State := D.State
  Representation := D.Representation
  endpoint := fun
    | (e, false) => D.endpoint e
    | (e, true) => (D.endpoint e).swap
  reverseEdge eb := (eb.1, !eb.2)
  reverseEdge_involutive := by
    rintro ⟨e, b⟩
    cases b <;> rfl
  reverse_endpoint_left := by
    rintro ⟨e, b⟩
    cases b <;> rfl
  reverse_endpoint_right := by
    rintro ⟨e, b⟩
    cases b <;> rfl
  repr := D.repr
  basePotential := D.basePotential
  threshold := D.threshold
  individual := D.individual
  individualWeight := D.individualWeight
  edgeWeight eb := D.edgeWeight eb.1 / 2
  edgeWeight_reverse := by
    rintro ⟨e, b⟩
    cases b <;> rfl
  mismatch := by
    intro eb x y t
    rcases eb with ⟨e, b⟩
    cases b
    · exact D.mismatch e (D.repr (D.endpoint e).1 x)
        (D.repr (D.endpoint e).2 y) t
    · exact D.mismatch e (D.repr (D.endpoint e).2 x)
        (D.repr (D.endpoint e).1 y) t
  reverseLeft := by
    intro eb x
    rcases eb with ⟨e, b⟩
    cases b <;> exact x
  reverseRight := by
    intro eb y
    rcases eb with ⟨e, b⟩
    cases b <;> exact y
  reverseLeft_repr := by
    intro eb x
    rcases eb with ⟨e, b⟩
    cases b <;> rfl
  reverseRight_repr := by
    intro eb y
    rcases eb with ⟨e, b⟩
    cases b <;> rfl
  mismatch_symmetric := by
    intro eb x y t
    rcases eb with ⟨e, b⟩
    cases b
    · exact D.mismatch_symmetric e
        (D.repr (D.endpoint e).1 x) (D.repr (D.endpoint e).2 y) t
    · exact D.mismatch_symmetric e
        (D.repr (D.endpoint e).2 x) (D.repr (D.endpoint e).1 y) t
  mismatch_nonneg := by
    intro eb x y t
    rcases eb with ⟨e, b⟩
    cases b <;> exact D.mismatch_nonneg e _ _ t
  mismatch_zero_iff := by
    intro eb x y t
    rcases eb with ⟨e, b⟩
    cases b
    · exact D.mismatch_zero_iff e
        (D.repr (D.endpoint e).1 x) (D.repr (D.endpoint e).2 y) t
    · exact D.mismatch_zero_iff e
        (D.repr (D.endpoint e).2 x) (D.repr (D.endpoint e).1 y) t
  individualWeight_pos := D.individualWeight_pos
  edgeWeight_pos := by
    intro eb
    exact div_pos (D.edgeWeight_pos eb.1) (by norm_num)
  individual_nonneg := D.individual_nonneg
  individual_eq_positivePart := D.individual_eq_positivePart

/-- 二方向・半重みの状態対残差は、元の表象値残差と一致する。 -/
theorem potential_toStatePairResidualSystem_eq
    (x : ∀ i, D.State i) (t : ℝ) :
    StatePairResidualSystem.potential D.toStatePairResidualSystem x t =
      D.potential x t := by
  classical
  simp [StatePairResidualSystem.potential, toStatePairResidualSystem,
    SharedResidualSystem.potential, SharedResidualSystem.edgeResidual,
    Fintype.sum_prod_type, D.mismatch_symmetric]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- 無向辺の状態対持ち上げでも、時刻別共有TCZは元の集合と一致する。 -/
theorem sharedTCZ_toStatePairResidualSystem_eq
    (K : Set (∀ i, D.State i)) (t : ℝ) :
    StatePairResidualSystem.sharedTCZ D.toStatePairResidualSystem K t =
      D.sharedTCZ K t := by
  ext x
  change (x ∈ K ∧ StatePairResidualSystem.potential
      D.toStatePairResidualSystem x t = 0) ↔
    (x ∈ K ∧ D.potential x t = 0)
  have hpot := D.potential_toStatePairResidualSystem_eq x t
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, hpot ▸ hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, hpot.symm ▸ hz⟩

/-- 持ち上げた辺 `(e,false)` の直接状態不整合は、元の辺残差そのもの。 -/
theorem edge_mismatch_toStatePairResidualSystem_eq
    (x : ∀ i, D.State i) (e : E) (t : ℝ) :
    StatePairResidualSystem.mismatch D.toStatePairResidualSystem (e, false)
      (x (D.endpoint e).1) (x (D.endpoint e).2) t = D.edgeResidual x e t := by
  rfl

end SharedResidualSystem

end Tomabechi.Theorem2

#print axioms Tomabechi.Theorem2.StatePairResidualSystem.theorem2_state_pair_conditional_conclusion
#print axioms Tomabechi.Theorem2.StatePairResidualSystem.theorem2_state_pair_tendsto_zero
#print axioms Tomabechi.Theorem2.StatePairResidualSystem.theorem2_reachable_state_pair_tendsto_zero
#print axioms Tomabechi.Theorem2.StatePairResidualSystem.theorem2_reachable_state_pair_quantitative_conclusion
#print axioms Tomabechi.Theorem2.SharedResidualSystem.potential_toStatePairResidualSystem_eq
