import Theorem2

/-!
# 定理2の Python 例 (`examples/theorem02_shared_tcz.py`) の共有TCZ根拠

2主体 `i∈Fin 2`、状態 `x_i∈ℝ`、`h_i(x)=x`、基礎評価 `V0_i=(x-c_i)²`、閾値 `θ=1/10`、
不整合 `S=(x_0-x_1)²`（有向辺2本、各重み `γ/2`、`γ=2`）。共有残差
`Φ2=Σ_i[(x_i-c_i)²-θ]₊+γ(x_0-x_1)²`（`StatePairResidualSystem.potential`）。

* **ケースA（谷が一致 `c=(0,0)`）:** 共有零集合 `Ω2={(z,z):|z|≤√θ}` は非空。
  このファイルでは共同方策 `ẋ_i=-x_i` の定理2適用を示す。Pythonの劣勾配流に対応する
  解析軌道と定理2への接続は `Theorem2_SubgradientFlow.lean` で別途証明する。
* **ケースB（谷が遠い `c=(0,3)`）:** すべての `x` で `Φ2≥3`。共有零集合は空で、補題0の下降条件と誤差境界は
  満たされえず、不整合または個人残差が正のまま残る（原文§4「必要な追加条件」）。

注意: `trajA` は追加の合意方策であり、Python のEuler更新を表す軌道ではない。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem2

open Tomabechi.Theorem2

def θ : ℝ := 1 / 10
def γ : ℝ := 2

/-- 有向辺 `e0=(0,1)`, `e1=(1,0)`。 -/
def endpointF : Fin 2 → Fin 2 × Fin 2 := ![(0, 1), (1, 0)]

abbrev Dsys (c : Fin 2 → ℝ) : StatePairResidualSystem (Fin 2) (Fin 2) where
  State := fun _ => ℝ
  Representation := ℝ
  endpoint := endpointF
  reverseEdge := Fin.rev
  reverseEdge_involutive := Fin.rev_rev
  reverse_endpoint_left := by intro e; fin_cases e <;> rfl
  reverse_endpoint_right := by intro e; fin_cases e <;> rfl
  repr := fun _ x => x
  basePotential := fun i x _ => (x - c i) ^ 2
  threshold := fun _ => θ
  individual := fun i x _ => max ((x - c i) ^ 2 - θ) 0
  individualWeight := fun _ => 1
  edgeWeight := fun _ => γ / 2
  edgeWeight_reverse := fun _ => rfl
  mismatch := fun _ x y _ => (x - y) ^ 2
  reverseLeft := fun _ x => x
  reverseRight := fun _ y => y
  reverseLeft_repr := fun _ _ => rfl
  reverseRight_repr := fun _ _ => rfl
  mismatch_symmetric := by intro e x y t; show (x - y) ^ 2 = (y - x) ^ 2; ring
  mismatch_nonneg := fun _ _ _ _ => sq_nonneg _
  mismatch_zero_iff := by
    intro e x y t
    show (x - y) ^ 2 = 0 ↔ x = y
    rw [sq_eq_zero_iff, sub_eq_zero]
  individualWeight_pos := fun _ => one_pos
  edgeWeight_pos := fun _ => by unfold γ; norm_num
  individual_nonneg := fun _ _ _ => by simp
  individual_eq_positivePart := fun _ _ _ => rfl

abbrev DA : StatePairResidualSystem (Fin 2) (Fin 2) := Dsys ![0, 0]
abbrev DB : StatePairResidualSystem (Fin 2) (Fin 2) := Dsys ![0, 3]

/-- 共有残差の具体形（`Φ2=Σ_i[(x_i-c_i)²-θ]₊+γ(x_0-x_1)²`）。 -/
theorem potential_eq (c : Fin 2 → ℝ) (x : ∀ i, (Dsys c).State i) (t : ℝ) :
    (Dsys c).potential x t =
      max ((x 0 - c 0) ^ 2 - θ) 0 + max ((x 1 - c 1) ^ 2 - θ) 0 + γ * (x 0 - x 1) ^ 2 := by
  have : (Dsys c).potential x t = _ := rfl
  rw [this]
  simp [Fin.sum_univ_two, endpointF, StatePairResidualSystem.potential, γ]
  ring

/-! ## ケースB（反例）: すべての `x` で `Φ2 ≥ 3` -/

theorem caseB_potential_ge (x : ∀ i, (DB).State i) (t : ℝ) : 3 ≤ DB.potential x t := by
  have hp : DB.potential x t = max ((x 0 - (![0, 3] : Fin 2 → ℝ) 0) ^ 2 - θ) 0 +
      max ((x 1 - (![0, 3] : Fin 2 → ℝ) 1) ^ 2 - θ) 0 + γ * (x 0 - x 1) ^ 2 := potential_eq ![0, 3] x t
  rw [hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, θ, γ]
  have h1 := le_max_left ((x 0 - 0) ^ 2 - 1 / 10) 0
  have h2 := le_max_left ((x 1 - 3) ^ 2 - 1 / 10) 0
  nlinarith [sq_nonneg (x 0 - 6 / 5), sq_nonneg (x 1 - 9 / 5), sq_nonneg (x 0 - x 1 + 3 / 5)]

/-- 共有零集合は空: どの点でも `Φ2≠0`、したがって下降条件・誤差境界の前提が満たされえない。 -/
theorem caseB_sharedTCZ_empty (K : Set (∀ i, (DB).State i)) (t : ℝ) : DB.sharedTCZ K t = ∅ := by
  ext x
  simp only [StatePairResidualSystem.sharedTCZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, h⟩
  have := caseB_potential_ge x t
  linarith

/-! ## ケースA: 誤差境界 -/

theorem sqrtθ_sq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt (by unfold θ; norm_num)
theorem sqrtθ_pos : 0 < Real.sqrt θ := Real.sqrt_pos.2 (by unfold θ; norm_num)

/-- 平均 `s` の合意点への射影 `z*=clamp(s,-√θ,√θ)`。 -/
def zstar (s : ℝ) : ℝ := max (-Real.sqrt θ) (min (Real.sqrt θ) s)

theorem zstar_sq_le (s : ℝ) : zstar s ^ 2 ≤ θ := by
  have h0 := sqrtθ_sq
  have hp := sqrtθ_pos
  unfold zstar
  have h1 : -Real.sqrt θ ≤ max (-Real.sqrt θ) (min (Real.sqrt θ) s) := le_max_left _ _
  have h2 : max (-Real.sqrt θ) (min (Real.sqrt θ) s) ≤ Real.sqrt θ :=
    max_le (by linarith) (min_le_left _ _)
  nlinarith

/-- 目標外の平均 `s`: `(s-z*)² ≤` 個人残差の和。 -/
theorem clamp_sq_le_hinge (a b : ℝ) :
    (((a + b) / 2) - zstar ((a + b) / 2)) ^ 2 ≤ max (a ^ 2 - θ) 0 + max (b ^ 2 - θ) 0 := by
  have h0 := sqrtθ_sq
  have hp := sqrtθ_pos
  have ha := le_max_left (a ^ 2 - θ) 0
  have hb := le_max_left (b ^ 2 - θ) 0
  have ha' := le_max_right (a ^ 2 - θ) 0
  have hb' := le_max_right (b ^ 2 - θ) 0
  set s := (a + b) / 2 with hs
  by_cases hup : Real.sqrt θ ≤ s
  · have hz : zstar s = Real.sqrt θ := by
      unfold zstar; rw [min_eq_left hup, max_eq_right (by linarith)]
    rw [hz]
    by_cases hab : s ≤ a
    · have : (s - Real.sqrt θ) ^ 2 ≤ a ^ 2 - θ := by nlinarith
      linarith
    · have hbs : s ≤ b := by linarith
      have : (s - Real.sqrt θ) ^ 2 ≤ b ^ 2 - θ := by nlinarith
      linarith
  · by_cases hlo : s ≤ -Real.sqrt θ
    · have hz : zstar s = -Real.sqrt θ := by
        unfold zstar; rw [min_eq_right (by linarith), max_eq_left hlo]
      rw [hz]
      by_cases hab : a ≤ s
      · have : (s + Real.sqrt θ) ^ 2 ≤ a ^ 2 - θ := by nlinarith
        linarith
      · have hbs : b ≤ s := by linarith
        have : (s + Real.sqrt θ) ^ 2 ≤ b ^ 2 - θ := by nlinarith
        linarith
    · have hz : zstar s = s := by
        unfold zstar
        rw [min_eq_right (not_le.1 hup).le, max_eq_right (not_le.1 hlo).le]
      rw [hz]; simp; linarith

/-- 誤差境界 `dist(x,Ω2)² ≤ 2Φ2`（全ての `x` で。`Ω2=sharedTCZ univ`）。 -/
theorem caseA_error_bound (x : ∀ i, (DA).State i) (t : ℝ) :
    Metric.infDist x (DA.sharedTCZ Set.univ t) ^ 2 ≤ 2 * DA.potential x t := by
  set a := x 0 with ha
  set b := x 1 with hb
  set s := (a + b) / 2 with hs
  set q : ∀ i, (DA).State i := fun _ => zstar s with hq
  have hqmem : q ∈ DA.sharedTCZ Set.univ t := by
    refine ⟨trivial, ?_⟩
    have hp : DA.potential q t = max ((q 0 - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - θ) 0 +
        max ((q 1 - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - θ) 0 + γ * (q 0 - q 1) ^ 2 := potential_eq ![0, 0] q t
    rw [hp]
    simp only [hq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hz : max ((zstar s - 0) ^ 2 - θ) 0 = 0 :=
      max_eq_right (by have := zstar_sq_le s; nlinarith)
    simp [hz]
    exact zstar_sq_le s
  have hpot : DA.potential x t = max (a ^ 2 - θ) 0 + max (b ^ 2 - θ) 0 + γ * (a - b) ^ 2 := by
    have hp : DA.potential x t = max ((x 0 - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - θ) 0 +
        max ((x 1 - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - θ) 0 + γ * (x 0 - x 1) ^ 2 := potential_eq ![0, 0] x t
    rw [hp]
    simp [hb, ha]
  have hdist : dist x q ≤ |s - zstar s| + |a - b| / 2 := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    fin_cases i
    · show dist a (zstar s) ≤ _
      rw [Real.dist_eq]
      have : a - zstar s = (s - zstar s) + (a - b) / 2 := by rw [hs]; ring
      rw [this]; exact (abs_add_le _ _).trans (by rw [abs_div]; norm_num)
    · show dist b (zstar s) ≤ _
      rw [Real.dist_eq]
      have : b - zstar s = (s - zstar s) - (a - b) / 2 := by rw [hs]; ring
      rw [this]; exact (abs_sub _ _).trans (by rw [abs_div]; norm_num)
  have hinf : Metric.infDist x (DA.sharedTCZ Set.univ t) ≤ |s - zstar s| + |a - b| / 2 :=
    (Metric.infDist_le_dist_of_mem hqmem).trans hdist
  have hnn : 0 ≤ Metric.infDist x (DA.sharedTCZ Set.univ t) := Metric.infDist_nonneg
  have hcl := clamp_sq_le_hinge a b
  rw [← hs] at hcl
  rw [hpot]
  have hsq : (|s - zstar s| + |a - b| / 2) ^ 2 ≤ 2 * (s - zstar s) ^ 2 + (a - b) ^ 2 / 2 := by
    have h1 := sq_abs (s - zstar s)
    have h2 := sq_abs (a - b)
    nlinarith [sq_nonneg (|s - zstar s| - |a - b| / 2)]
  calc Metric.infDist x (DA.sharedTCZ Set.univ t) ^ 2
      ≤ (|s - zstar s| + |a - b| / 2) ^ 2 := by gcongr
    _ ≤ 2 * (s - zstar s) ^ 2 + (a - b) ^ 2 / 2 := hsq
    _ ≤ 2 * (max (a ^ 2 - θ) 0 + max (b ^ 2 - θ) 0 + γ * (a - b) ^ 2) := by
        unfold γ; nlinarith [sq_nonneg (a - b)]

/-! ## ケースA: 合意方策 `ẋ_i=-x_i` の軌道 -/

open MeasureTheory

/-- 初期点 `(2,-2)`。 -/
def x0 : Fin 2 → ℝ := ![2, -2]

/-- 共同方策（Ω2 内の点 `0` への合意）`ẋ_i=-x_i` の解。 -/
def trajA (t : ℝ) : ∀ i, (DA).State i := fun i => x0 i * Real.exp (-t)

/-- 軌道上の `Φ2`: `2[4e^{-2t}-θ]₊+16γe^{-2t}`。 -/
def PhiA (t : ℝ) : ℝ := 2 * max (4 * Real.exp (-t) ^ 2 - θ) 0 + 16 * γ * Real.exp (-t) ^ 2

theorem potential_trajA (t : ℝ) : DA.potential (trajA t) t = PhiA t := by
  have hp : DA.potential (trajA t) t = max (((trajA t) 0 - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - θ) 0 +
      max (((trajA t) 1 - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - θ) 0 + γ * ((trajA t) 0 - (trajA t) 1) ^ 2 :=
    potential_eq ![0, 0] (trajA t) t
  rw [hp]
  simp only [trajA, x0, PhiA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring_nf

theorem hasDerivAt_rsq (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t) ^ 2) (-2 * Real.exp (-t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t :=
    ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring)
  have := h1.pow 2
  exact this.congr_deriv (by simp; ring)

theorem contDiff_rsq : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t) ^ 2) := by fun_prop

theorem PhiA_ac (T : ℝ) : AbsolutelyContinuousOnInterval PhiA 0 T := by
  have hg : AbsolutelyContinuousOnInterval (fun t : ℝ => 4 * Real.exp (-t) ^ 2 - θ) 0 T :=
    (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => 4 * Real.exp (-t) ^ 2 - θ)).contDiffOn.absolutelyContinuousOnInterval
  have hm : LipschitzWith 1 (fun r : ℝ => max r 0) := by simpa using LipschitzWith.id.max_const (0 : ℝ)
  have h1 := (hm.comp_absolutelyContinuousOnInterval hg).const_mul 2
  have h2 := (contDiff_rsq.contDiffOn (s := Set.uIcc 0 T)).absolutelyContinuousOnInterval.const_mul (16 * γ)
  exact h1.add h2

theorem zero_set_subsingleton : {t : ℝ | 4 * Real.exp (-t) ^ 2 - θ = 0}.Subsingleton := by
  intro a ha b hb
  by_contra hne
  have hanti : ∀ u v : ℝ, u < v → Real.exp (-v) ^ 2 < Real.exp (-u) ^ 2 := by
    intro u v huv
    have := Real.exp_lt_exp.2 (show -v < -u by linarith)
    exact pow_lt_pow_left₀ this (Real.exp_pos _).le (by norm_num)
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti a b h; simp only [Set.mem_setOf_eq] at ha hb; linarith
  · have := hanti b a h; simp only [Set.mem_setOf_eq] at ha hb; linarith

/-- a.e. 下降 `Φ' ≤ -2Φ`（`c=1`）。 -/
theorem PhiA_decay (T : ℝ) :
    ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), deriv PhiA s ≤ -2 * 1 * PhiA s := by
  have hnull : volume {t : ℝ | 4 * Real.exp (-t) ^ 2 - θ = 0} = 0 :=
    zero_set_subsingleton.measure_zero _
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull] with s hs _
  have hne : 4 * Real.exp (-s) ^ 2 - θ ≠ 0 := hs
  have hcont : Continuous (fun t : ℝ => 4 * Real.exp (-t) ^ 2 - θ) := by fun_prop
  have hr := hasDerivAt_rsq s
  have hθ : 0 ≤ θ := by unfold θ; norm_num
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hev : ∀ᶠ t in nhds s, 4 * Real.exp (-t) ^ 2 - θ < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds hneg)
    have hEq : PhiA =ᶠ[nhds s] fun t => 16 * γ * Real.exp (-t) ^ 2 := by
      filter_upwards [hev] with t ht
      simp [PhiA, max_eq_right ht.le]
    rw [hEq.deriv_eq, (hr.const_mul (16 * γ)).deriv]
    simp [PhiA, max_eq_right hneg.le]
    nlinarith
  · have hev : ∀ᶠ t in nhds s, 0 < 4 * Real.exp (-t) ^ 2 - θ :=
      hcont.continuousAt.eventually (lt_mem_nhds hpos)
    have hEq : PhiA =ᶠ[nhds s] fun t => 2 * (4 * Real.exp (-t) ^ 2 - θ) + 16 * γ * Real.exp (-t) ^ 2 := by
      filter_upwards [hev] with t ht
      simp [PhiA, max_eq_left ht.le]
    rw [hEq.deriv_eq]
    have hd : HasDerivAt (fun t : ℝ => 2 * (4 * Real.exp (-t) ^ 2 - θ) + 16 * γ * Real.exp (-t) ^ 2)
        (2 * (4 * (-2 * Real.exp (-s) ^ 2)) + 16 * γ * (-2 * Real.exp (-s) ^ 2)) s := by
      have := (((hr.const_mul 4).sub_const θ).const_mul 2).add (hr.const_mul (16 * γ))
      exact this
    rw [hd.deriv]
    simp [PhiA, max_eq_left hpos.le]
    nlinarith [sq_nonneg (Real.exp (-s))]

/-- 連結性。 -/
theorem connectedA : ∀ i j : Fin 2, Relation.ReflTransGen
    (fun a b => ∃ e, ((DA.endpoint e).1 = a ∧ (DA.endpoint e).2 = b) ∨
      ((DA.endpoint e).1 = b ∧ (DA.endpoint e).2 = a)) i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  · exact Relation.ReflTransGen.refl

/-- 共有零集合は非空（原点）。 -/
theorem sharedTCZ_nonempty (s : ℝ) : (DA.sharedTCZ Set.univ s).Nonempty := by
  refine ⟨fun _ => 0, trivial, ?_⟩
  have hp : DA.potential (fun _ : Fin 2 => (0 : ℝ)) s = max (((0 : ℝ) - (![0, 0] : Fin 2 → ℝ) 0) ^ 2 - θ) 0 +
      max (((0 : ℝ) - (![0, 0] : Fin 2 → ℝ) 1) ^ 2 - θ) 0 + γ * ((0 : ℝ) - 0) ^ 2 :=
    potential_eq ![0, 0] (fun _ => 0) s
  rw [hp]
  simp [θ]

/-- 定理2の一般結論（ケースA）。 -/
theorem caseA_conclusion (t : ℝ) (ht : 0 ≤ t) :
    (trajA t ∈ (Set.univ : Set (∀ i, (DA).State i)) ∧
      Metric.infDist (trajA t) (DA.sharedTCZ Set.univ t) ≤
        Real.sqrt (2 * DA.potential (trajA 0) 0) * Real.exp (-1 * (t - 0))) ∧
    (∀ i, DA.individual i (trajA t i) t ≤
      (DA.potential (trajA 0) 0 / DA.individualWeight i) * Real.exp (-2 * 1 * (t - 0))) ∧
    (∀ e, DA.mismatch e (trajA t (DA.endpoint e).1) (trajA t (DA.endpoint e).2) t ≤
      (DA.potential (trajA 0) 0 / DA.edgeWeight e) * Real.exp (-2 * 1 * (t - 0))) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) t, ∀ x ∈ DA.sharedTCZ Set.univ s, ∀ i j, DA.repr i (x i) = DA.repr j (x j)) := by
  refine DA.theorem2_state_pair_conditional_conclusion Set.univ trajA connectedA 1 2 0 t
    one_pos two_pos ht (fun s _ => trivial) (fun s _ => sharedTCZ_nonempty s) ?_ ?_
    (fun s _ => caseA_error_bound (trajA s) s)
  · have : (fun s => DA.potential (trajA s) s) = PhiA := funext potential_trajA
    rw [this]; exact PhiA_ac t
  · have : (fun s => DA.potential (trajA s) s) = PhiA := funext potential_trajA
    simp only [this, potential_trajA]
    exact PhiA_decay t

end Tomabechi.Examples.Theorem2

end
