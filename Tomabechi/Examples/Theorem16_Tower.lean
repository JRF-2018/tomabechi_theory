import Theorem16_25_Core
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# 定理16の Python 例 (`examples/theorem16_inverse_limit_fixed_point.py`) の Lean 根拠

塔 `K_n=[0,1]^{n+1}`（射影＝末尾座標を落とす）、下三角フィードバック
`F_k(x)=(1-L)c_k+L(x_k+x_{k-1})/2`（`x_{-1}:=0`、`L=7/10`、`c_k∈[0,1]` は任意の有界列）。

* **縮小と一意性・幾何収束（逆極限＝列空間）:** 逆極限 `lim←[0,1]^{n+1}` を、`[0,1]` に値をもつ有界列の
  空間 `SeqSpace`（sup 距離で完備）として扱い、`F` が `SeqSpace` を保存し縮小率 `7/10` の縮小写像であることを
  証明する。表象 `M(S)=S_0`（連続、`Rep=[0,1]` はコンパクトHausdorff）は同変
  `M∘F=F_Rep∘M`。一般定理 `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction` から、
  一意な固定点 `S*` が存在し、`F_Rep(M S*)=M S*`、`(M S*,S*)∈ℜ`、`d(F^n S0,S*)≤(7/10)^n d(S0,S*)`。
* **層整合性:** 各層 `n` の固定点方程式は先頭 `n+1` 本の方程式であり、解は一意（帰納法）。
  したがって層ごとの固定点は互いに射影で一致する（Python の `consistency`）。
* 位相論的な存在節（Tychonoff＋Schauder 型の逆極限定理）は縮小性があれば Banach で代替できるため、
  この例では縮小性側の主張を使う。原文の層条件（`theorem16_fixedPoint_exists_of_originalLayerConditions`）
  を塔で満たすことの証明は別ファイル（対応表の「部分」）。
-/

noncomputable section

namespace Tomabechi.Examples.Theorem16Tower

open Tomabechi.Theorem16_25 BoundedContinuousFunction

/-- 前座標 `x_{k-1}`（`k=0` では `0`）。 -/
def prev (x : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else x (k - 1)

/-- Python の `F`: `F_k(x)=(1-L)c_k+L(x_k+x_{k-1})/2`、`L=7/10`。 -/
noncomputable def Fseq (c : ℕ → ℝ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 - 7 / 10) * c k + 7 / 10 * (x k + prev x k) / 2

/-- `[0,1]` に値をもつ有界列の空間（逆極限）。 -/
abbrev SeqSpace : Type := {x : ℕ →ᵇ ℝ // ∀ k, x k ∈ Set.Icc (0 : ℝ) 1}

/-- 評価 `f ↦ f k` は連続（1-リプシッツ）。 -/
theorem evalContinuous (k : ℕ) : Continuous (fun f : ℕ →ᵇ ℝ => f k) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f g => by
    simpa using dist_coe_le_dist (f := f) (g := g) k).continuous

instance : CompleteSpace SeqSpace := by
  have hclosed : IsClosed {x : ℕ →ᵇ ℝ | ∀ k, x k ∈ Set.Icc (0 : ℝ) 1} := by
    have : {x : ℕ →ᵇ ℝ | ∀ k, x k ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ k, {x : ℕ →ᵇ ℝ | x k ∈ Set.Icc (0 : ℝ) 1} := by ext x; simp
    rw [this]
    exact isClosed_iInter fun k =>
      isClosed_Icc.preimage (evalContinuous k)
  exact hclosed.completeSpace_coe

instance : Nonempty SeqSpace := ⟨⟨0, fun k => by simp⟩⟩

/-- 表象 `M(S)=S_0`（`Rep=[0,1]`）。 -/
def M (x : SeqSpace) : Set.Icc (0 : ℝ) 1 := ⟨x.1 0, x.2 0⟩

theorem M_continuous : Continuous M :=
  Continuous.subtype_mk
    ((evalContinuous 0).comp continuous_subtype_val) _

/-- 自己表象データ（関係は `M` のグラフ）。 -/
def selfRep : SelfRepresentation SeqSpace (Set.Icc (0 : ℝ) 1) where
  relation := {p | p.1 = M p.2}
  relation_closed := isClosed_eq continuous_fst (M_continuous.comp continuous_snd)
  represent := M
  represent_continuous := M_continuous
  represents := fun _ => rfl

section
variable (c : ℕ →ᵇ ℝ) (hc : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1)
include hc

theorem Fseq_mem (x : SeqSpace) (k : ℕ) : Fseq c x.1 k ∈ Set.Icc (0 : ℝ) 1 := by
  have hx := x.2 k
  have hp : prev x.1 k ∈ Set.Icc (0 : ℝ) 1 := by
    unfold prev; split_ifs
    · simp
    · exact x.2 _
  have hck := hc k
  simp only [Fseq, Set.mem_Icc] at *
  constructor <;> nlinarith [hx.1, hx.2, hp.1, hp.2, hck.1, hck.2]

/-- `F` を `SeqSpace` 上の写像として実現（`mkOfDiscrete` で有界列にする）。 -/
noncomputable def F : SeqSpace → SeqSpace := fun x =>
  ⟨BoundedContinuousFunction.mkOfDiscrete (Fseq c x.1) 1 (fun k k' => by
      have h1 := Fseq_mem c hc x k
      have h2 := Fseq_mem c hc x k'
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]),
   fun k => Fseq_mem c hc x k⟩

theorem F_apply (x : SeqSpace) (k : ℕ) : (F c hc x).1 k = Fseq c x.1 k := rfl

theorem F_contracting : ContractingWith (7 / 10 : NNReal) (F c hc) := by
  refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq]
  have hd : 0 ≤ dist x.1 y.1 := dist_nonneg
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro k
  have hk := BoundedContinuousFunction.dist_coe_le_dist (f := x.1) (g := y.1) k
  have hp : dist (prev x.1 k) (prev y.1 k) ≤ dist x.1 y.1 := by
    unfold prev; split_ifs
    · simp
    · exact BoundedContinuousFunction.dist_coe_le_dist (f := x.1) (g := y.1) (k - 1)
  change dist (Fseq c x.1 k) (Fseq c y.1 k) ≤ ((7 / 10 : NNReal) : ℝ) * dist x.1 y.1
  simp only [Fseq, Real.dist_eq] at *
  have : (1 - 7 / 10) * c k + 7 / 10 * (x.1 k + prev x.1 k) / 2 -
      ((1 - 7 / 10) * c k + 7 / 10 * (y.1 k + prev y.1 k) / 2) =
      7 / 20 * ((x.1 k - y.1 k) + (prev x.1 k - prev y.1 k)) := by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 20)]
  have := abs_add_le (x.1 k - y.1 k) (prev x.1 k - prev y.1 k)
  push_cast
  nlinarith [abs_nonneg (x.1 k - y.1 k)]

/-- `F_Rep(r)=(1-L)c_0+L r/2`。 -/
noncomputable def FRep : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun r =>
  ⟨(1 - 7 / 10) * c 0 + 7 / 10 * r.1 / 2, by
    have := hc 0; have := r.2
    simp only [Set.mem_Icc] at *
    constructor <;> nlinarith⟩

theorem FRep_continuous : Continuous (FRep c hc) :=
  Continuous.subtype_mk (by fun_prop) _

theorem equivariant (x : SeqSpace) : M (F c hc x) = FRep c hc (M x) := by
  apply Subtype.ext
  simp [M, FRep, F_apply, Fseq, prev]

/-- 定理16（縮小条件節）: 一意な固定点 `S*`、同変表象の固定点、幾何収束。 -/
theorem theorem16_tower :
    ∃! s : SeqSpace, F c hc s = s ∧ FRep c hc (M s) = M s ∧ (M s, s) ∈ (selfRep).relation ∧
      ∀ (x : SeqSpace) (n : ℕ), dist ((F c hc)^[n] x) s ≤ ((7 / 10 : NNReal) : ℝ) ^ n * dist x s := by
  refine theorem16_fullRepresentedFixedPoint_of_exists_and_contraction (selfRep) (F c hc) (FRep c hc)
    (7 / 10 : NNReal) (FRep_continuous c hc) (fun s => by exact equivariant c hc s) ?_ (F_contracting c hc)
  exact ⟨ContractingWith.fixedPoint (F c hc) (F_contracting c hc),
    ContractingWith.fixedPoint_isFixedPt (F_contracting c hc)⟩

end

/-! ## 層整合性: 下三角方程式の解は一意 -/

/-- 層 `n` の固定点方程式（先頭 `n+1` 本）。 -/
def LayerEq (c : ℕ → ℝ) (n : ℕ) (y : ℕ → ℝ) : Prop := ∀ k ≤ n, y k = Fseq c y k

/-- 層 `n` の固定点は先頭 `n+1` 座標で一意。 -/
theorem layer_unique (c : ℕ → ℝ) (n : ℕ) (y z : ℕ → ℝ) (hy : LayerEq c n y) (hz : LayerEq c n z) :
    ∀ k ≤ n, y k = z k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hyk := hy k hk
    have hzk := hz k hk
    have hprev : prev y k = prev z k := by
      unfold prev; split_ifs with h0
      · rfl
      · exact ih (k - 1) (by omega) (by omega)
    simp only [Fseq] at hyk hzk
    rw [hprev] at hyk
    linarith

/-- 一般の `n≤m` で層 `m` の解を層 `n` へ制限すると層 `n` の解（射影整合性）。 -/
theorem layerEq_mono (c : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) (y : ℕ → ℝ) (hy : LayerEq c m y) :
    LayerEq c n y := fun k hk => hy k (hk.trans h)

/-- 固定点 `S*` は全層の方程式を満たし、各層の（一意な）固定点に一致する。 -/
theorem fixedPoint_satisfies_all_layers (c : ℕ →ᵇ ℝ) (hc : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1)
    (s : SeqSpace) (hs : F c hc s = s) (n : ℕ) : LayerEq c n s.1 := by
  intro k _
  have := congrArg (fun t : SeqSpace => t.1 k) hs
  simpa [F_apply] using this.symm

end Tomabechi.Examples.Theorem16Tower

end
