import Theorem3

/-!
# 定理3の Python 例 (`examples/theorem03_lub_consensus.py`) の Lean 根拠

3主体 `i∈Fin 3`、各主体の状態 `x_i∈ℝ³`、概念束 `𝕃=Fin 3 → [0,1]`（ファジー集合、各点順序）、
順序埋め込み `ι=座標の実数値`、`φ_i(x)=clamp(x)`、世界 `W_i=e_i`（i番目の概念だけ1）。
`L*=⨆W_i=⊤=(1,1,1)`（平均 `(1/3,1/3,1/3)` ではない）。`Φ3=γΣ_{i<j}S_ij+ηΣA_i`、
`A_i=‖ι(φ_i(x_i))-ι(L*)‖²`、`S_ij=‖x_i-x_j‖²`。勾配流 `ẋ_i=-2∇_{x_i}Φ3`（Python の
`x ← x-dt·2·g`）、初期値 `x_i(0)=e_i`。

* 厳密解 `x_ik(t)=1+y_ik(t)`、`y_ik=-(2/3)a(t)+(δ_ik-1/3)b(t)`、`a=e^{-4ηt}`、`b=e^{-4(η+3γ)t}`
  を求め、勾配流であること、`[0,1]` に留まることを証明する。
* `Φ3(t)=4η a²+2(η+3γ) b²`（閉形式）、したがって `Φ3'≤-8ηΦ3`（`c=4η`）。
* 一般定理 `AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent` の全前提を満たし、
  共有零集合への距離と `‖ι(φ_i(x_i))-ι(L*)‖` が 0 に収束する。誤差境界は `C=1/η`。

注意: 束の型 `Fin 3 → [0,1]` はファジー集合（Python の連続状態に合わせた）で、2値集合束
`Finset (Fin 3)` ではない。`ι(φ_i(x))` は `[0,1]` への射影（clamp）を介する。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem3

open Tomabechi.Theorem3

abbrev Concept : Type := Fin 3 → unitInterval

def iota : Concept ↪o CoordinateSpace 3 :=
  OrderEmbedding.ofMapLEIff (fun f i => (f i : ℝ)) (by
    intro f g; simp only [Pi.le_def]; exact forall_congr' fun i => Subtype.coe_le_coe)

/-- 世界 `W_i=e_i`。 -/
def world (i : Fin 3) : Concept := fun k => if k = i then 1 else 0

abbrev Dsys : AbstractSharedSystem (Fin 3) Concept 3 where
  State := fun _ => Fin 3 → ℝ
  abstraction := fun _ x k => Set.projIcc (0 : ℝ) 1 zero_le_one (x k)
  worlds := world
  ι := iota

theorem iota_apply (f : Concept) (k : Fin 3) : iota f k = (f k : ℝ) := rfl

theorem Dsys_abstraction (i : Fin 3) (x : Fin 3 → ℝ) (k : Fin 3) :
    Dsys.abstraction i x k = Set.projIcc (0 : ℝ) 1 zero_le_one (x k) := rfl

/-- `L*=⨆ W_i=⊤=(1,1,1)`（平均ではない）。 -/
theorem lub_apply (k : Fin 3) : Dsys.lub k = 1 := by
  have h1 : (1 : unitInterval) ≤ Dsys.lub k := by
    have h : world k ≤ Dsys.lub := le_iSup (fun i => Dsys.worlds i) k
    simpa [world] using h k
  exact le_antisymm (le_top.trans_eq rfl) h1

theorem iota_lub (k : Fin 3) : (iota Dsys.lub) k = 1 := by
  rw [iota_apply, lub_apply]; simp

/-- `A_i(x)=Σ_k (clamp(x_k)-1)²`。 -/
theorem abstractResidual_eq (i : Fin 3) (x : Fin 3 → ℝ) :
    Dsys.abstractResidual i x = ∑ k, ((Set.projIcc (0 : ℝ) 1 zero_le_one (x k) : ℝ) - 1) ^ 2 := by
  unfold AbstractSharedSystem.abstractResidual euclideanCoordinateNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((iota (Dsys.abstraction i x) - iota Dsys.lub) k) ^ 2 = _
  rw [Pi.sub_apply, iota_apply, iota_lub, Dsys_abstraction]

/-! ## 厳密解と勾配流 -/

section Solution
variable (η γ : ℝ)

def aF (t : ℝ) : ℝ := Real.exp (-4 * η * t)
def bF (t : ℝ) : ℝ := Real.exp (-4 * (η + 3 * γ) * t)
/-- `δ_ik-1/3`。 -/
def coef (i k : Fin 3) : ℝ := if i = k then 2 / 3 else -1 / 3

/-- 厳密解 `x_ik(t)=1-(2/3)a+(δ_ik-1/3)b`（初期値 `x_i(0)=e_i`）。 -/
def xt (t : ℝ) (i k : Fin 3) : ℝ := 1 + (-(2 / 3) * aF η t + coef i k * bF η γ t)

theorem xt_zero (i k : Fin 3) : xt η γ 0 i k = if k = i then 1 else 0 := by
  fin_cases i <;> fin_cases k <;> simp [xt, coef, aF, bF] <;> norm_num

theorem coef_sum (k : Fin 3) : ∑ j, coef j k = 0 := by
  fin_cases k <;> simp [coef, Fin.sum_univ_three] <;> norm_num

theorem hasDerivAt_aF (t : ℝ) : HasDerivAt (aF η) (-4 * η * aF η t) t := by
  unfold aF
  have := (Real.hasDerivAt_exp (-4 * η * t)).comp t ((hasDerivAt_id t).const_mul (-4 * η))
  exact this.congr_deriv (by simp [mul_comm])

theorem hasDerivAt_bF (t : ℝ) : HasDerivAt (bF η γ) (-4 * (η + 3 * γ) * bF η γ t) t := by
  unfold bF
  have := (Real.hasDerivAt_exp (-4 * (η + 3 * γ) * t)).comp t
    ((hasDerivAt_id t).const_mul (-4 * (η + 3 * γ)))
  exact this.congr_deriv (by simp [mul_comm])

/-- 勾配流: `ẋ_ik = -2(2η(x_ik-1)+2γΣ_j(x_ik-x_jk))`（Python の `x←x-dt·2·g`）。 -/
theorem xt_gradient_flow (t : ℝ) (i k : Fin 3) :
    HasDerivAt (fun t => xt η γ t i k)
      (-2 * (2 * η * (xt η γ t i k - 1) + 2 * γ * ∑ j, (xt η γ t i k - xt η γ t j k))) t := by
  have h := (((hasDerivAt_aF η t).const_mul (-(2 / 3))).add
    ((hasDerivAt_bF η γ t).const_mul (coef i k))).const_add 1
  refine h.congr_deriv ?_
  have hs : ∑ j, (xt η γ t i k - xt η γ t j k) = 3 * coef i k * bF η γ t := by
    simp only [xt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    have := coef_sum k
    simp only [Fin.sum_univ_three] at this ⊢
    have hb : (coef 0 k + coef 1 k + coef 2 k) * bF η γ t = 0 := by rw [this, zero_mul]
    linarith [hb]
  rw [hs]
  simp only [xt]
  ring

/-- `t≥0` で `x_ik∈[0,1]`（`η,γ>0`）。 -/
theorem xt_mem (hη : 0 < η) (hγ : 0 < γ) (t : ℝ) (ht : 0 ≤ t) (i k : Fin 3) :
    0 ≤ xt η γ t i k ∧ xt η γ t i k ≤ 1 := by
  have ha1 : aF η t ≤ 1 := by unfold aF; rw [Real.exp_le_one_iff]; nlinarith
  have hb1 : bF η γ t ≤ aF η t := by
    unfold bF aF; apply Real.exp_le_exp.2; nlinarith
  have hapos : 0 < aF η t := Real.exp_pos _
  have hbpos : 0 < bF η γ t := Real.exp_pos _
  unfold xt coef
  split_ifs <;> constructor <;> nlinarith

/-! ## 総残差 `Φ3` の閉形式 -/

/-- 共有残差 `Φ2=γΣ_{i<j}S_ij=γ/2 Σ_{i,j}‖x_i-x_j‖²`（時間不変）。 -/
def sharedAtF (γ : ℝ) (x : ∀ i : Fin 3, Dsys.State i) (_ : ℝ) : ℝ :=
  γ / 2 * ∑ i, ∑ j, ∑ k, (x i k - x j k) ^ 2

/-- 軌道 `x_i(t)`。 -/
def traj (η γ : ℝ) : ∀ i : Fin 3, ℝ → Dsys.State i := fun i t k => xt η γ t i k

/-- 共有残差の軌道上の値。 -/
def sharedT (η γ : ℝ) (t : ℝ) : ℝ := sharedAtF γ (fun i k => xt η γ t i k) t

/-- 閉形式 `Φ3(t)=4η a²+2(η+3γ) b²`。 -/
def PhiF (η γ : ℝ) (t : ℝ) : ℝ := 4 * η * aF η t ^ 2 + 2 * (η + 3 * γ) * bF η γ t ^ 2

theorem potential_eq (hη : 0 < η) (hγ : 0 < γ) (t : ℝ) (ht : 0 ≤ t) :
    Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) t = PhiF η γ t := by
  have hA : ∀ i, Dsys.abstractResidual i (traj η γ i t) = ∑ k, (xt η γ t i k - 1) ^ 2 := by
    intro i
    refine (abstractResidual_eq i (fun k => xt η γ t i k)).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm := xt_mem η γ hη hγ t ht i k
    rw [Set.projIcc_of_mem _ ⟨hm.1, hm.2⟩]
  have hdef : Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) t =
      sharedT η γ t + ∑ i, η * Dsys.abstractResidual i (traj η γ i t) := rfl
  rw [hdef]
  simp only [hA, sharedT, sharedAtF, PhiF, xt, Fin.sum_univ_three, coef]
  norm_num
  ring

end Solution


/-! ## 一般定理 3 の前提 -/

section Main
variable (η γ : ℝ)

/-- 共有 TCZ（`Φ3=0` の零集合、時間不変）。 -/
def TCZ (η γ : ℝ) (s : ℝ) : Set (∀ i : Fin 3, Dsys.State i) :=
  {x | Dsys.statePotential (sharedAtF γ) (fun _ => η) x s = 0}

/-- LUB 配置 `x_ik≡1` は TCZ に属す（非空性）。 -/
theorem Lcfg_mem (s : ℝ) : (fun (_ : Fin 3) (_ : Fin 3) => (1 : ℝ)) ∈ TCZ η γ s := by
  have hA : ∀ i, Dsys.abstractResidual i (fun (_ : Fin 3) => (1 : ℝ)) = 0 := by
    intro i
    refine (abstractResidual_eq i (fun _ => (1 : ℝ))).trans ?_
    simp [Set.projIcc_of_mem (zero_le_one' ℝ) (Set.right_mem_Icc.2 (zero_le_one' ℝ))]
  show Dsys.statePotential (sharedAtF γ) (fun _ => η) (fun _ _ => (1 : ℝ)) s = 0
  have hdef : Dsys.statePotential (sharedAtF γ) (fun _ => η) (fun _ _ => (1 : ℝ)) s =
      sharedAtF γ (fun _ _ => (1 : ℝ)) s + ∑ i, η * Dsys.abstractResidual i (fun _ => (1 : ℝ)) := rfl
  rw [hdef]
  simp [hA, sharedAtF]

theorem sharedT_nonneg (hγ : 0 < γ) (t : ℝ) : 0 ≤ sharedT η γ t := by
  unfold sharedT sharedAtF
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg _)

theorem hasDerivAt_PhiF (t : ℝ) :
    HasDerivAt (PhiF η γ) (-32 * η ^ 2 * aF η t ^ 2 - 16 * (η + 3 * γ) ^ 2 * bF η γ t ^ 2) t := by
  have ha := hasDerivAt_aF η t
  have hb := hasDerivAt_bF η γ t
  have h := ((ha.pow 2).const_mul (4 * η)).add ((hb.pow 2).const_mul (2 * (η + 3 * γ)))
  unfold PhiF
  refine h.congr_deriv ?_
  simp
  ring

theorem contDiff_PhiF : ContDiff ℝ 1 (PhiF η γ) := by
  unfold PhiF aF bF; fun_prop

/-- `Φ3'≤-8ηΦ3`（`c=4η`）。 -/
theorem PhiF_decay (hη : 0 < η) (hγ : 0 < γ) (t : ℝ) :
    -32 * η ^ 2 * aF η t ^ 2 - 16 * (η + 3 * γ) ^ 2 * bF η γ t ^ 2 ≤ -2 * (4 * η) * PhiF η γ t := by
  unfold PhiF
  nlinarith [sq_nonneg (bF η γ t), mul_pos hη hγ, sq_nonneg (aF η t),
    mul_nonneg (mul_nonneg hη.le hγ.le) (sq_nonneg (bF η γ t))]

/-- 誤差境界 `dist(x(s),TCZ)² ≤ Φ3/η`（`C=1/η`）。 -/
theorem error_bound (hη : 0 < η) (hγ : 0 < γ) (s : ℝ) (hs : 0 ≤ s) :
    Metric.infDist (fun j => traj η γ j s) (TCZ η γ s) ^ 2 ≤
      (1 / η) * Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) s := by
  set D2 : ℝ := ∑ i, ∑ k, (xt η γ s i k - 1) ^ 2 with hD2
  have hpot : Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) s =
      sharedT η γ s + η * D2 := by
    have hA : ∀ i, Dsys.abstractResidual i (traj η γ i s) = ∑ k, (xt η γ s i k - 1) ^ 2 := by
      intro i
      refine (abstractResidual_eq i (fun k => xt η γ s i k)).trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      have hm := xt_mem η γ hη hγ s hs i k
      rw [Set.projIcc_of_mem _ ⟨hm.1, hm.2⟩]
    have hdef : Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) s =
        sharedT η γ s + ∑ i, η * Dsys.abstractResidual i (traj η γ i s) := rfl
    rw [hdef]
    simp only [hA, ← Finset.mul_sum, hD2]
  have hsh : 0 ≤ sharedT η γ s := sharedT_nonneg η γ hγ s
  have hD2nonneg : 0 ≤ D2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  -- dist ≤ √D2
  have hdist : dist (fun j => traj η γ j s) (fun (_ : Fin 3) (_ : Fin 3) => (1 : ℝ)) ≤ Real.sqrt D2 := by
    rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
    intro i
    rw [dist_pi_le_iff (Real.sqrt_nonneg _)]
    intro k
    rw [Real.dist_eq]
    show |xt η γ s i k - 1| ≤ Real.sqrt D2
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    calc (xt η γ s i k - 1) ^ 2 ≤ ∑ k', (xt η γ s i k' - 1) ^ 2 :=
          Finset.single_le_sum (f := fun k' => (xt η γ s i k' - 1) ^ 2)
            (fun k' _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ D2 := Finset.single_le_sum (f := fun i' => ∑ k', (xt η γ s i' k' - 1) ^ 2)
            (fun i' _ => Finset.sum_nonneg fun k' _ => sq_nonneg _) (Finset.mem_univ i)
  have hinf : Metric.infDist (fun j => traj η γ j s) (TCZ η γ s) ≤ Real.sqrt D2 :=
    (Metric.infDist_le_dist_of_mem (Lcfg_mem η γ s)).trans hdist
  have hinf0 : 0 ≤ Metric.infDist (fun j => traj η γ j s) (TCZ η γ s) := Metric.infDist_nonneg
  calc Metric.infDist (fun j => traj η γ j s) (TCZ η γ s) ^ 2 ≤ Real.sqrt D2 ^ 2 := by gcongr
    _ = D2 := Real.sq_sqrt hD2nonneg
    _ ≤ (1 / η) * (sharedT η γ s + η * D2) := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hη]
        nlinarith
    _ = (1 / η) * Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) s := by rw [hpot]

/-- 定理3の結論: 共有零集合への距離と、LUB 表象への距離が 0 に収束する。 -/
theorem python_instance (hη : 0 < η) (hγ : 0 < γ) (i : Fin 3) :
    Filter.Tendsto (fun s => Metric.infDist (fun j => traj η γ j s) (TCZ η γ s))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun s => euclideanCoordinateNorm
        (Dsys.ι (Dsys.abstraction i (traj η γ i s)) - Dsys.ι Dsys.lub))
        Filter.atTop (nhds 0) := by
  refine Dsys.theorem3_two_distances_tendsto_of_ac_ae_descent (traj η γ) (TCZ η γ) (sharedT η γ)
    (fun _ => η) i (4 * η) (1 / η) 0 hη (by positivity) (by positivity)
    (fun s _ => sharedT_nonneg η γ hγ s)
    (fun s _ j => by
      have : 0 ≤ Dsys.abstractResidual j (traj η γ j s) := AbstractSharedSystem.abstractResidual_nonneg _ _ _
      positivity)
    (fun s _ => ⟨_, Lcfg_mem η γ s⟩) ?_ ?_ (fun s hs => error_bound η γ hη hγ s hs)
  · intro T hT
    have hpot : Set.EqOn (PhiF η γ) (Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η))
        (Set.uIcc 0 T) := by
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      exact (potential_eq η γ hη hγ t ht.1).symm
    exact (contDiff_PhiF η γ).contDiffOn.absolutelyContinuousOnInterval.congr hpot
  · intro T hT
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem MeasureTheory.volume] with s hs0 hsI
    have hspos : 0 < s := lt_of_le_of_ne hsI.1 (fun h => hs0 (by simp [← h]))
    have hev : Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) =ᶠ[nhds s] PhiF η γ := by
      filter_upwards [Ioi_mem_nhds hspos] with t ht
      exact potential_eq η γ hη hγ t (le_of_lt ht)
    rw [hev.deriv_eq, (hasDerivAt_PhiF η γ s).deriv, potential_eq η γ hη hγ s hsI.1]
    exact PhiF_decay η γ hη hγ s

/-- 同じ実LUB・同じ抽象残差・同じflowについて、定理3入口の定量評価を得る。 -/
theorem python_instance_quantitative (hη : 0 < η) (hγ : 0 < γ)
    (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    Metric.infDist (fun j => traj η γ j t) (TCZ η γ t) ≤
        Real.sqrt ((1 / η) * Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) 0) *
          Real.exp (-(4 * η) * (t - 0)) ∧
      euclideanCoordinateNorm
        (Dsys.ι (Dsys.abstraction i (traj η γ i t)) - Dsys.ι Dsys.lub) ≤
        Real.sqrt (Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) 0 / η) *
          Real.exp (-(4 * η) * (t - 0)) := by
  refine Dsys.theorem3_two_distance_bounds_of_ac_ae_descent
    (traj η γ) (TCZ η γ) (sharedT η γ) (fun _ => η) i
    (4 * η) (1 / η) 0 t hη (by positivity) (by positivity) ht
    (fun s _ => sharedT_nonneg η γ hγ s)
    (fun s _ j => by
      have hr := AbstractSharedSystem.abstractResidual_nonneg Dsys j (traj η γ j s)
      positivity)
    (fun s _ => ⟨_, Lcfg_mem η γ s⟩) ?_ ?_
    (fun s hs => error_bound η γ hη hγ s hs.1)
  · have hpot : Set.EqOn (PhiF η γ)
        (Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η)) (Set.uIcc 0 t) := by
      intro u hu
      rw [Set.uIcc_of_le ht] at hu
      exact (potential_eq η γ hη hγ u hu.1).symm
    exact (contDiff_PhiF η γ).contDiffOn.absolutelyContinuousOnInterval.congr hpot
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem MeasureTheory.volume]
      with s hs0 hsI
    have hspos : 0 < s := lt_of_le_of_ne hsI.1 (fun h => hs0 (by simp [← h]))
    have hev : Dsys.potential (traj η γ) (sharedT η γ) (fun _ => η) =ᶠ[nhds s]
        PhiF η γ := by
      filter_upwards [Ioi_mem_nhds hspos] with u hu
      exact potential_eq η γ hη hγ u (le_of_lt hu)
    rw [hev.deriv_eq, (hasDerivAt_PhiF η γ s).deriv,
      potential_eq η γ hη hγ s hsI.1]
    exact PhiF_decay η γ hη hγ s

end Main

end Tomabechi.Examples.Theorem3

end
