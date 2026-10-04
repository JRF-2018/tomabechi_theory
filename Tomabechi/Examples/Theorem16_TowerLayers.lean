import Theorem16_25_Core
import Tomabechi.Examples.Theorem16_Tower

/-!
# 定理16の Python 例の「原文の層条件」への適用 (`Theorem16_Tower.lean` の補完)

塔 `I=ℕ`、層空間 `E_n=ℝ^{n+1}`（Pi 型）、候補集合 `K_n=[0,1]^{n+1}`（非空コンパクト凸）、射影 `p_{βα}`
＝先頭 `β+1` 座標への制限（連続アフィン、`p_{αα}=id`、`p_{γβ}∘p_{βα}=p_{γα}`）、層別フィードバック
`f_n(x)_k=(1-L)c_k+L(x_k+x_{k-1})/2`（`L=7/10`、`c_k∈[0,1]` 任意、`x_{-1}:=0`、射影と可換・連続）。
一般定理 `theorem16_fixedPoint_exists_of_originalLayerConditions` の全前提（有限層整合性は上界層から導出）を満たし、
逆極限（積空間の部分集合）上に固定点が存在する（Tychonoff + Schauder 型の存在節）。
幾何収束は `Theorem16_Tower.lean`（縮小性）。このファイルの後半では、逆極限の要素の各層の最後の座標を
並べた列（`flatten`）で逆極限と `SeqSpace` を型として同一視し（位相同型ではない）、フィードバックと
固定点がこの対応で保たれること、逆極限側の固定点が一意で `SeqSpace` 側の唯一の固定点と座標列として
一致することを示す。
-/

namespace Tomabechi.Examples.Theorem16TowerLayers

open Tomabechi.Theorem16_25
open Tomabechi.Examples.Theorem16Tower
open BoundedContinuousFunction

abbrev E (n : ℕ) : Type := Fin (n + 1) → ℝ

/-- `K_n=[0,1]^{n+1}`。 -/
def K (n : ℕ) : Set (E n) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- 射影（先頭 `β+1` 座標）。 -/
def proj {β α : ℕ} (h : β ≤ α) (x : E α) : E β := fun i => x (Fin.castLE (Nat.succ_le_succ h) i)

theorem proj_refl (n : ℕ) (x : E n) : proj (le_refl n) x = x := by
  funext i; simp [proj]

theorem proj_comp {γ β α : ℕ} (h1 : γ ≤ β) (h2 : β ≤ α) (x : E α) :
    proj h1 (proj h2 x) = proj (h1.trans h2) x := by
  funext i; simp [proj]

theorem proj_maps {β α : ℕ} (h : β ≤ α) : Set.MapsTo (proj h) (K α) (K β) := by
  intro x hx i _
  exact hx _ (Set.mem_univ _)

/-- 前座標 `x_{k-1}`（`k=0` では 0）。 -/
def prevF {n : ℕ} (x : E n) (k : Fin (n + 1)) : ℝ :=
  if h : (k : ℕ) = 0 then 0 else x ⟨k - 1, by omega⟩

section
variable (c : ℕ → ℝ) (hc : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1)

/-- 同じ係数列を有界連続関数空間にも載せる。ℕは離散なので連続性は自動である。 -/
noncomputable def boundedC : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete c 1 (by
    intro i j
    have hi := hc i
    have hj := hc j
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2])

theorem boundedC_mem (k : ℕ) : (boundedC c hc) k ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [boundedC] using hc k

/-- 層 `n` のフィードバック。 -/
noncomputable def Fn (n : ℕ) (x : E n) : E n := fun k => (1 - 7 / 10) * c k + 7 / 10 * (x k + prevF x k) / 2

include hc in
theorem Fn_mem (n : ℕ) (x : E n) (hx : x ∈ K n) : Fn c n x ∈ K n := by
  intro k _
  have hxk := hx k (Set.mem_univ _)
  have hp : prevF x k ∈ Set.Icc (0 : ℝ) 1 := by
    unfold prevF
    split_ifs with h
    · simp
    · exact hx _ (Set.mem_univ _)
  have hck := hc k
  simp only [Fn, Set.mem_Icc] at *
  constructor <;> nlinarith [hxk.1, hxk.2, hp.1, hp.2, hck.1, hck.2]

noncomputable def f (hc : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : {x : E n // x ∈ K n} → {x : E n // x ∈ K n} :=
  fun x => ⟨Fn c n x.1, Fn_mem c hc n x.1 x.2⟩

theorem prevF_proj {β α : ℕ} (h : β ≤ α) (x : E α) (k : Fin (β + 1)) :
    prevF x (Fin.castLE (Nat.succ_le_succ h) k) = prevF (proj h x) k := by
  unfold prevF proj
  by_cases hk : (k : ℕ) = 0
  · simp [hk]
  · simp [hk]

theorem Fn_proj {β α : ℕ} (h : β ≤ α) (x : E α) :
    proj h (Fn c α x) = Fn c β (proj h x) := by
  funext k
  simp only [proj, Fn, Fin.val_castLE]
  rw [prevF_proj h x k]

theorem continuous_prevF (n : ℕ) (k : Fin (n + 1)) : Continuous fun x : E n => prevF x k := by
  unfold prevF
  by_cases hk : (k : ℕ) = 0
  · simp [hk]; exact continuous_const
  · simp only [hk, dite_false]
    exact continuous_apply _

theorem continuous_Fn (n : ℕ) : Continuous (Fn c n) := by
  refine continuous_pi fun k => ?_
  unfold Fn
  have h1 : Continuous fun x : E n => x k := continuous_apply k
  have h2 := continuous_prevF n k
  fun_prop

theorem continuous_f (n : ℕ) : Continuous (f c hc n) :=
  Continuous.subtype_mk ((continuous_Fn c n).comp continuous_subtype_val) _

/-- 原文の層条件を満たす塔上で、逆極限に固定点が存在する。 -/
theorem tower_fixedPoint_exists :
    ∃ x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj},
      inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x := by
  refine theorem16_fixedPoint_exists_of_originalLayerConditions (I := ℕ) E K
    (fun n => isCompact_univ_pi fun _ => isCompact_Icc)
    (fun n => ⟨fun _ => 0, fun _ _ => by simp⟩)
    (fun n => convex_pi fun _ _ => convex_Icc 0 1)
    (fun h => proj h)
    (fun β α h x y a b _ _ _ _ _ => by funext i; simp [proj])
    (fun i x => proj_refl i x.1)
    (fun h1 h2 x => proj_comp h1 h2 x.1)
    (fun _ _ h => proj_maps h)
    (fun j => (continuous_pi fun i => continuous_apply _).continuousOn)
    (fun i => ⟨i + 1, Nat.lt_succ_self i⟩)
    (f c hc) (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) (continuous_f c hc)

/-! ### 逆極限と有界列の座標同定

逆極限の層 `n` の最後の座標を列の第 `n` 項と読む。射影整合性により、
層 `n` の他の座標もこの列の対応する項に一致する。この同定は位相同型を
主張するものではなく、固定点の座標列を比較するための代数的な対応である。
-/

/-- 逆極限要素から、各層の最後の座標を読む列。 -/
def flatten (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) : ℕ → ℝ :=
  fun n => x.1 n (Fin.last n)

/-- 射影整合性により、層 `n` の各座標は flatten の同じ番号の項である。 -/
theorem layer_coord_eq_flatten
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj})
    (n : ℕ) (k : Fin (n + 1)) : x.1 n k = flatten x k := by
  have hproj := x.2.2 (show k.val ≤ n by omega)
  have h := congrFun hproj (Fin.last k.val)
  have hcast : Fin.castLE (Nat.succ_le_succ (show k.val ≤ n by omega))
      (Fin.last k.val) = k := by
    apply Fin.ext
    simp [Fin.val_last]
  change x.1 n k = x.1 k.val (Fin.last k.val)
  calc
    x.1 n k = x.1 n (Fin.castLE (Nat.succ_le_succ (show k.val ≤ n by omega)) (Fin.last k.val)) := by rw [hcast]
    _ = x.1 k.val (Fin.last k.val) := by
      change (proj (show k.val ≤ n by omega) (x.1 n) (Fin.last k.val)) = _
      exact h

/-- 逆極限要素のflattenは、すべての座標が単位区間に入る。 -/
theorem flatten_mem_Icc
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) (n : ℕ) :
    flatten x n ∈ Set.Icc (0 : ℝ) 1 := by
  exact x.2.1 n (Fin.last n) (Set.mem_univ _)

/-- 逆極限要素を、有界連続関数空間上の `[0,1]` 値列へ持ち上げる。 -/
noncomputable def toSeqSpace
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) : SeqSpace :=
  ⟨BoundedContinuousFunction.mkOfDiscrete (flatten x) 1 (by
      intro i j
      have hi := flatten_mem_Icc x i
      have hj := flatten_mem_Icc x j
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]),
    flatten_mem_Icc x⟩

/-- `toSeqSpace` は座標を変えずに保存する。 -/
theorem toSeqSpace_apply
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) (n : ℕ) :
    (toSeqSpace x).1 n = flatten x n := rfl

/-- 逆極限上の固定点はflatten後も同じ下三角固定点方程式を満たす。 -/
theorem flatten_fixedPoint
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj})
    (hx : inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x) :
    ∀ k, flatten x k = Fseq c (flatten x) k := by
  intro k
  let j : Fin (k + 1) := Fin.last k
  have hfix := congrArg (fun y : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj} => y.1 k j) hx
  change Fn c k (x.1 k) j = x.1 k j at hfix
  have hcur := layer_coord_eq_flatten x k j
  by_cases hk : k = 0
  · subst k
    have hzero : prevF (x.1 0) j = 0 := by simp [prevF, j]
    have hcur' : x.1 0 j = flatten x 0 := by simpa [j] using hcur
    calc
      flatten x 0 = x.1 0 j := hcur'.symm
      _ = Fn c 0 (x.1 0) j := hfix.symm
      _ = Fseq c (flatten x) 0 := by simp [Fn, Fseq, prev, flatten, j, prevF]
  · have hpred : (x.1 k) ⟨k - 1, by omega⟩ = flatten x (k - 1) :=
      layer_coord_eq_flatten x k ⟨k - 1, by omega⟩
    have hprev : prevF (x.1 k) j = flatten x (k - 1) := by
      simp [prevF, j, hk, hpred]
    have hcur' : x.1 k j = flatten x k := by simpa [j] using hcur
    calc
      flatten x k = x.1 k j := hcur'.symm
      _ = Fn c k (x.1 k) j := hfix.symm
      _ = Fseq c (flatten x) k := by simp [Fn, Fseq, prev, flatten, j, hk, hprev]

/-- 有界列から各層への有限制限を作る逆向きの写像。 -/
def fromSeqSpace (s : SeqSpace) :
    {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj} := by
  refine ⟨fun n i => s.1 i, ?_⟩
  constructor
  · intro n i _
    exact s.2 i
  · intro β α h
    funext i
    simp [proj]

/-- flatten と有限制限は座標ごとに互いに逆である。 -/
theorem flatten_fromSeqSpace (s : SeqSpace) (n : ℕ) :
    flatten (fromSeqSpace s) n = s.1 n := rfl

theorem layer_fromSeqSpace (s : SeqSpace) (n : ℕ) (i : Fin (n + 1)) :
    (fromSeqSpace s).1 n i = s.1 i := rfl

/-- 射影整合列の全ての層座標はflattenで復元されるので、逆写像も座標ごとに一致する。 -/
theorem fromSeqSpace_flatten
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) :
    fromSeqSpace (toSeqSpace x) = x := by
  apply Subtype.ext
  funext n
  funext i
  change (toSeqSpace x).1 i.val = x.1 n i
  rw [toSeqSpace_apply]
  exact (layer_coord_eq_flatten x n i).symm

/-- 列空間の固定点を各有限層へ制限すると、逆極限上の固定点になる。 -/
theorem fromSeqSpace_fixedPoint
    (s : SeqSpace) (hs : F (boundedC c hc) (boundedC_mem c hc) s = s) :
    inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) (fromSeqSpace s) = fromSeqSpace s := by
  apply Subtype.ext
  funext n
  funext i
  have hseq := congrArg (fun z : SeqSpace => z.1 i.val) hs
  change Fn c n ((fromSeqSpace s).1 n) i = (fromSeqSpace s).1 n i
  simpa [fromSeqSpace, Fn, prevF, F_apply, Fseq, prev, boundedC] using hseq

/-- 有界列へ写してから有限制限を取ると、元の列に戻る。 -/
theorem toSeqSpace_fromSeqSpace (s : SeqSpace) : toSeqSpace (fromSeqSpace s) = s := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro n
  rfl

/-- 逆極限上のフィードバックと列空間のフィードバックはflattenで可換する。 -/
theorem flatten_inducedMap
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) (k : ℕ) :
    flatten (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) k =
      Fseq c (flatten x) k := by
  let j : Fin (k + 1) := Fin.last k
  have hcur := layer_coord_eq_flatten x k j
  have hfixed : Fn c k (x.1 k) j =
      (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x).1 k j := rfl
  have hout : (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x).1 k j =
      flatten (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) k := by
    exact (layer_coord_eq_flatten _ k j).symm
  by_cases hk : k = 0
  · subst k
    have hcur' : x.1 0 j = flatten x 0 := by simpa [j] using hcur
    calc
      flatten (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) 0 =
          (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
            (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x).1 0 j := hout.symm
      _ = Fn c 0 (x.1 0) j := hfixed.symm
      _ = Fseq c (flatten x) 0 := by
        simpa [Fn, Fseq, prevF, prev, j, hcur']
  · have hcur' : x.1 k j = flatten x k := by simpa [j] using hcur
    have hpred : (x.1 k) ⟨k - 1, by omega⟩ = flatten x (k - 1) :=
      layer_coord_eq_flatten x k ⟨k - 1, by omega⟩
    calc
      flatten (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) k =
          (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
            (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x).1 k j := hout.symm
      _ = Fn c k (x.1 k) j := hfixed.symm
      _ = Fseq c (flatten x) k := by
        simp [Fn, Fseq, prevF, prev, j, hk, hcur', hpred]

/-- `toSeqSpace` はfeedbackを列空間の `F` へ移す。 -/
theorem toSeqSpace_feedback
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) :
    toSeqSpace (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) =
      F (boundedC c hc) hc (toSeqSpace x) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro k
  change flatten (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x) k =
    Fseq (boundedC c hc) (toSeqSpace x).1 k
  rw [flatten_inducedMap]
  rfl

/-- 列空間のfeedbackを有限制限すると、各層のfeedbackと一致する。 -/
theorem fromSeqSpace_feedback
    (s : SeqSpace) :
    inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) (fromSeqSpace s) =
    fromSeqSpace (F (boundedC c hc) (boundedC_mem c hc) s) := by
  apply Subtype.ext
  funext n
  funext i
  change Fn c n ((fromSeqSpace s).1 n) i =
    (F (boundedC c hc) (boundedC_mem c hc) s).1 i.val
  rw [F_apply]
  simp [fromSeqSpace, Fn, prevF, Fseq, prev, boundedC]

/-- 逆極限固定点を列へ写すと、sup距離空間側の縮小写像固定点になる。 -/
theorem toSeqSpace_fixedPoint
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj})
    (hx : inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x) :
    F (boundedC c hc) (boundedC_mem c hc) (toSeqSpace x) = toSeqSpace x := by
  have h := congrArg toSeqSpace hx
  rw [toSeqSpace_feedback] at h
  exact h

/-- 二つの固定点表現の間で、固定点であることが同値に保存される。 -/
theorem fixedPoint_iff
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj}) :
    (inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x) ↔
    F (boundedC c hc) (boundedC_mem c hc) (toSeqSpace x) = toSeqSpace x := by
  constructor
  · exact toSeqSpace_fixedPoint c hc x
  · intro hs
    rw [← fromSeqSpace_flatten x]
    rw [fromSeqSpace_feedback]
    simpa using congrArg fromSeqSpace hs

/-- 逆極限部分型とsup距離の列空間は、座標対応による型同値をなす。
これは位相同型を含意しない。 -/
noncomputable def inverseLimitSeqEquiv :
    {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj} ≃ SeqSpace where
  toFun := toSeqSpace
  invFun := fromSeqSpace
  left_inv := fromSeqSpace_flatten
  right_inv := toSeqSpace_fromSeqSpace

/-- 縮小条件のもとで、層空間上の固定点は一意である。
固定点の存在自体は `tower_fixedPoint_exists` で既に与えられている。 -/
theorem tower_fixedPoint_unique
    (x y : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj})
    (hx : inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x)
    (hy : inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) y = y) : x = y := by
  apply Subtype.ext
  funext n
  funext i
  have hxs := toSeqSpace_fixedPoint c hc x hx
  have hys := toSeqSpace_fixedPoint c hc y hy
  have hcontract := F_contracting (boundedC c hc) (boundedC_mem c hc)
  have hseq := hcontract.fixedPoint_unique' hxs hys
  have hcoord := congrArg (fun s : SeqSpace => s.1 i.val) hseq
  calc
    x.1 n i = flatten x i.val := layer_coord_eq_flatten x n i
    _ = flatten y i.val := by simpa [toSeqSpace_apply] using hcoord
    _ = y.1 n i := (layer_coord_eq_flatten y n i).symm

/-- 原文の層条件から得た存在定理と縮小条件を合わせ、逆極限固定点が一意となる。 -/
theorem tower_fixedPoint_exists_unique :
    ∃! x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj},
      inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
        (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x := by
  obtain ⟨x, hx⟩ := tower_fixedPoint_exists c hc
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact tower_fixedPoint_unique c hc y x hy hx

/-- 逆極限固定点をflattenしたものは、sup距離側で得た唯一の固定点そのもの。 -/
theorem tower_fixedPoint_has_same_coordinates
    (x : {x : ∀ i, E i // x ∈ affineInverseLimitSet E K proj})
    (hx : inducedAffineInverseLimitMap E K proj (fun _ _ h => proj_maps h) (f c hc)
      (fun _ _ h x => Subtype.ext (Fn_proj c h x.1)) x = x) :
    toSeqSpace x = ContractingWith.fixedPoint (F (boundedC c hc) (boundedC_mem c hc))
      (F_contracting (boundedC c hc) (boundedC_mem c hc)) := by
  apply (F_contracting (boundedC c hc) (boundedC_mem c hc)).fixedPoint_unique'
  · exact toSeqSpace_fixedPoint c hc x hx
  · exact (F_contracting (boundedC c hc) (boundedC_mem c hc)).fixedPoint_isFixedPt

end

end Tomabechi.Examples.Theorem16TowerLayers
