import Mathlib

/-!
# R1: 共通概念束の基本構成

有限個の座標を持つ単位区間の積を、概念・記号情報・層添字を接続する
共通束の候補として用いる。このファイルは束への保存付き埋込みの基礎を
与える。既存の定理群や統合モデルへの接続は別途必要である。
-/

namespace Tomabechi.Consistency.R1

open scoped BigOperators
open scoped Topology

/-- 二つの座標を持つ共通概念束。順序と束演算は座標ごとに定める。 -/
abbrev CommonConcept := Fin 2 → unitInterval

/-- Nat段を共通束の対角線上へ送るための有理数列 `n/(n+1)`。 -/
noncomputable def layerRatio (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + 1)

theorem layerRatio_nonneg (n : ℕ) : 0 ≤ layerRatio n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  exact div_nonneg hn hden.le

theorem layerRatio_lt_one (n : ℕ) : layerRatio n < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [layerRatio, div_lt_one hden]
  linarith

theorem layerRatio_strictMono : StrictMono layerRatio := by
  intro m n hmn
  have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hd₁ : 0 < (m : ℝ) + 1 := by positivity
  have hd₂ : 0 < (n : ℝ) + 1 := by positivity
  rw [layerRatio, layerRatio, div_lt_div_iff₀ hd₁ hd₂]
  nlinarith

/-- 各Nat層を共通束の対角上に配置する。すべての有限層は共通の頂より下にある。 -/
noncomputable def diagonalLayer (n : ℕ) : CommonConcept := fun _ =>
  ⟨layerRatio n, ⟨layerRatio_nonneg n, (layerRatio_lt_one n).le⟩⟩

theorem diagonalLayer_strictMono : StrictMono diagonalLayer := by
  intro m n hmn
  have hcoord (i : Fin 2) : diagonalLayer m i < diagonalLayer n i := by
    simp [diagonalLayer]
    exact_mod_cast layerRatio_strictMono hmn
  apply lt_iff_le_not_ge.mpr
  refine ⟨?_, ?_⟩
  · intro i
    exact le_of_lt (hcoord i)
  · intro hrev
    have hcoordRev : diagonalLayer n 0 ≤ diagonalLayer m 0 := hrev 0
    have hratioRev : layerRatio n ≤ layerRatio m := by exact_mod_cast hcoordRev
    exact (not_le_of_gt (layerRatio_strictMono hmn)) hratioRev

theorem diagonalLayer_le_iff (m n : ℕ) :
    diagonalLayer m ≤ diagonalLayer n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hmn
    have hlt : n < m := Nat.lt_of_not_ge hmn
    exact (not_lt_of_ge h) (diagonalLayer_strictMono hlt)
  · intro hmn
    exact diagonalLayer_strictMono.monotone hmn

/-- 対角層列はどの有限段よりも後の段を持つので、最大層を持たない。 -/
theorem exists_diagonalLayer_strictly_above (n : ℕ) :
    ∃ m, diagonalLayer n < diagonalLayer m :=
  ⟨n + 1, diagonalLayer_strictMono (Nat.lt_succ_self n)⟩

/-- 二つのNat層には、その両方以上となる対角層がある。 -/
theorem diagonalLayer_pair_has_upper (m n : ℕ) :
    ∃ k, diagonalLayer m ≤ diagonalLayer k ∧ diagonalLayer n ≤ diagonalLayer k := by
  refine ⟨max m n, ?_, ?_⟩
  · exact (diagonalLayer_strictMono.monotone (Nat.le_max_left m n))
  · exact (diagonalLayer_strictMono.monotone (Nat.le_max_right m n))

theorem diagonalLayer_lt_top (n : ℕ) : diagonalLayer n < ⊤ := by
  have hcoord (i : Fin 2) : diagonalLayer n i < ⊤ := by
    simp [diagonalLayer]
    exact_mod_cast layerRatio_lt_one n
  apply lt_iff_le_not_ge.mpr
  refine ⟨le_top, ?_⟩
  intro htop
  have hcoordTop : (⊤ : CommonConcept) 0 ≤ diagonalLayer n 0 := htop 0
  have hone : (1 : ℝ) ≤ layerRatio n := by exact_mod_cast hcoordTop
  exact (not_le_of_gt (layerRatio_lt_one n)) hone

/-- 対角Nat層は共通束の頂点へ近づき、その上限は頂点そのものになる。 -/
theorem diagonalLayer_range_isLUB_top :
    IsLUB (Set.range diagonalLayer) (⊤ : CommonConcept) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact le_top
  · intro b hb
    change ∀ i, (⊤ : unitInterval) ≤ b i
    intro i
    have hbound : ∀ n, layerRatio n ≤ (b i : ℝ) := by
      intro n
      have hpoint : diagonalLayer n ≤ b := hb (Set.mem_range_self n)
      have hi := hpoint i
      exact_mod_cast hi
    have hevent : ∀ᶠ n : ℕ in Filter.atTop, layerRatio n ∈ Set.Iic (b i : ℝ) :=
      Filter.Eventually.of_forall hbound
    have hlim : Filter.Tendsto layerRatio Filter.atTop (𝓝 (1 : ℝ)) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    have htop : (1 : ℝ) ∈ Set.Iic (b i : ℝ) :=
      isClosed_Iic.mem_of_tendsto hlim hevent
    exact_mod_cast htop

/-- 既存の有限Nat層と無限頂点を、同じ共通束の対角列と頂点へ移す写像。 -/
noncomputable def layerAddress (a : WithTop ℕ) : CommonConcept :=
  WithTop.recTopCoe ⊤ diagonalLayer a

@[simp]
theorem layerAddress_top : layerAddress (⊤ : WithTop ℕ) = ⊤ := by
  simp [layerAddress]

@[simp]
theorem layerAddress_nat (n : ℕ) : layerAddress (n : WithTop ℕ) = diagonalLayer n := by
  rfl

/-- 有限Nat段と無限頂を共通束の対角鎖と束頂へ移す順序埋込み。 -/
noncomputable def layerAddressEmbedding : WithTop ℕ ↪o CommonConcept :=
  OrderEmbedding.ofMapLEIff layerAddress (by
    intro a b
    cases a with
    | top =>
      cases b with
      | top => simp
      | coe n =>
        change (⊤ ≤ diagonalLayer n) ↔ (⊤ ≤ (n : WithTop ℕ))
        constructor
        · intro h
          exact (not_le_of_gt (diagonalLayer_lt_top n) h).elim
        · intro h
          exact (WithTop.not_top_le_coe n h).elim
    | coe m =>
      cases b with
      | top => simp [layerAddress]
      | coe n =>
        change diagonalLayer m ≤ diagonalLayer n ↔
          (m : WithTop ℕ) ≤ (n : WithTop ℕ)
        constructor
        · intro h
          exact_mod_cast (diagonalLayer_le_iff m n).mp h
        · intro h
          exact (diagonalLayer_le_iff m n).mpr (by exact_mod_cast h))

/-- 任意の共通束点を、その下にある最大の対角Nat層へ戻す単調な層番号。 -/
noncomputable def layerProjection (x : CommonConcept) : WithTop ℕ :=
  ⨆ n : {k : ℕ // diagonalLayer k ≤ x}, (n.1 : WithTop ℕ)

theorem layerProjection_monotone : Monotone layerProjection := by
  intro x y hxy
  apply iSup_le
  intro n
  exact le_iSup_of_le ⟨n.1, le_trans n.2 hxy⟩ (by rfl)

/-- 投影は各有限Nat層で元の層番号を正確に返す。 -/
theorem layerProjection_diagonal (n : ℕ) :
    layerProjection (diagonalLayer n) = n := by
  unfold layerProjection
  apply le_antisymm
  · apply iSup_le
    intro m
    have hmn : m.1 ≤ n := (diagonalLayer_le_iff m.1 n).mp m.2
    exact_mod_cast hmn
  · exact le_iSup_of_le ⟨n, le_rfl⟩ (by rfl)

@[simp] theorem layerProjection_layerAddress (a : WithTop ℕ) :
    layerProjection (layerAddress a) = a := by
  cases a with
  | top =>
    rw [layerAddress_top]
    unfold layerProjection
    have hnot : ¬BddAbove
        (Set.range fun n : {k : ℕ // diagonalLayer k ≤ ⊤} => n.1) := by
      rw [not_bddAbove_iff]
      intro b
      refine ⟨b + 1, ⟨⟨b + 1, le_top⟩, rfl⟩, ?_⟩
      omega
    exact (WithTop.iSup_coe_eq_top
      (f := fun n : {k : ℕ // diagonalLayer k ≤ ⊤} => n.1)).2 hnot
  | coe n =>
    change layerProjection (diagonalLayer n) = n
    exact layerProjection_diagonal n

/-- 下限層投影は、共通束の真部分点を頂添字へ誤って送らない。 -/
theorem layerProjection_lt_top_of_lt_top {x : CommonConcept} (hx : x < ⊤) :
    layerProjection x < ⊤ := by
  by_contra hlt
  have hle : ⊤ ≤ layerProjection x := not_lt.mp hlt
  have heq : layerProjection x = ⊤ := le_antisymm le_top hle
  unfold layerProjection at heq
  have hnotbdd : ¬BddAbove
      (Set.range fun n : {k : ℕ // diagonalLayer k ≤ x} => n.1) :=
    (WithTop.iSup_coe_eq_top (f := fun n : {k : ℕ // diagonalLayer k ≤ x} => n.1)).mp heq
  have hupper : ∀ y ∈ Set.range diagonalLayer, y ≤ x := by
    intro y hy
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨k, ⟨n, hn⟩, hmk⟩ := (not_bddAbove_iff.mp hnotbdd) m
    have hmn : m ≤ n.1 := Nat.le_of_lt (by simpa [hn] using hmk)
    exact (diagonalLayer_strictMono.monotone hmn).trans n.2
  have hxupper : x ∈ upperBounds (Set.range diagonalLayer) := hupper
  have htopx : (⊤ : CommonConcept) ≤ x := diagonalLayer_range_isLUB_top.2 hxupper
  exact (not_le_of_gt hx) htopx

/-- 既存のNat/頂添字データを、新しい共通束全体へ延長する関数。 -/
noncomputable def extendLayerData {α : Sort*} (f : WithTop ℕ → α) : CommonConcept → α :=
  fun x => f (layerProjection x)

/-- 延長データは埋込み像上で元の有限層/頂データを厳密に回収する。 -/
theorem extendLayerData_on_oldAddress {α : Sort*} (f : WithTop ℕ → α)
    (a : WithTop ℕ) :
    extendLayerData f (layerAddressEmbedding a) = f a := by
  change f (layerProjection (layerAddress a)) = f a
  rw [layerProjection_layerAddress]

theorem extendLayerData_top {α : Sort*} (f : WithTop ℕ → α) :
    extendLayerData f ⊤ = f ⊤ := by
  simpa [extendLayerData, layerAddressEmbedding, layerAddress_top] using
    extendLayerData_on_oldAddress f (⊤ : WithTop ℕ)

/-- 層順序に関して単調な既存データは、全共通束上への延長後も単調である。 -/
theorem extendLayerData_monotone {α : Type*} [Preorder α]
    (f : WithTop ℕ → α) (hf : Monotone f) :
    Monotone (extendLayerData f) := by
  intro x y hxy
  exact hf (layerProjection_monotone hxy)

/-- 各座標の単位区間を、他座標を底に固定して共通束へ埋め込む。 -/
def coordinateEmbedding (i : Fin 2) : unitInterval ↪o CommonConcept :=
  OrderEmbedding.ofMapLEIff
    (fun x j => if j = i then x else 0)
    (by
      intro x y
      constructor
      · intro h
        simpa using h i
      · intro h j
        by_cases hj : j = i
        · subst j
          simpa using h
        · simp [hj])

@[simp]
theorem coordinateEmbedding_apply_self (i : Fin 2) (x : unitInterval) :
    coordinateEmbedding i x i = x := by
  simp [coordinateEmbedding]

@[simp]
theorem coordinateEmbedding_apply_other (i j : Fin 2) (h : j ≠ i)
    (x : unitInterval) : coordinateEmbedding i x j = 0 := by
  simp [coordinateEmbedding, h]

/-- 有限記號集合を0/1指示関数へ移す。有限集合の包含は座標ごとの順序と同値。 -/
def finiteSymbolsEmbedding : Finset (Fin 2) ↪o CommonConcept :=
  OrderEmbedding.ofMapLEIff
    (fun s i => if i ∈ s then 1 else 0)
    (by
      intro s t
      constructor
      · intro h i hi
        have hcoord := h i
        simp only [hi, ↓reduceIte] at hcoord
        by_contra hit
        simp [hit] at hcoord
      · intro h i
        by_cases hi : i ∈ s
        · have hit : i ∈ t := h hi
          simp [hi, hit]
        · simp [hi]
      )

@[simp]
theorem finiteSymbolsEmbedding_apply (s : Finset (Fin 2)) (i : Fin 2) :
    finiteSymbolsEmbedding s i = if i ∈ s then 1 else 0 := by
  rfl

theorem finiteSymbolsEmbedding_le_iff (s t : Finset (Fin 2)) :
    finiteSymbolsEmbedding s ≤ finiteSymbolsEmbedding t ↔ s ⊆ t :=
  finiteSymbolsEmbedding.le_iff_le

/-- 有限記号の和集合は、共通束上のjoinへそのまま移る。 -/
theorem finiteSymbolsEmbedding_union (s t : Finset (Fin 2)) :
    finiteSymbolsEmbedding (s ∪ t) = finiteSymbolsEmbedding s ⊔
      finiteSymbolsEmbedding t := by
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [finiteSymbolsEmbedding, hs, ht]

/-- 有限記号の共通部分は、共通束上のmeetへそのまま移る。 -/
theorem finiteSymbolsEmbedding_inter (s t : Finset (Fin 2)) :
    finiteSymbolsEmbedding (s ∩ t) = finiteSymbolsEmbedding s ⊓
      finiteSymbolsEmbedding t := by
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [finiteSymbolsEmbedding, hs, ht]

@[simp]
theorem finiteSymbolsEmbedding_empty :
    finiteSymbolsEmbedding (∅ : Finset (Fin 2)) = ⊥ := by
  funext i
  change (if i ∈ (∅ : Finset (Fin 2)) then (1 : unitInterval) else 0) = 0
  simp

@[simp]
theorem finiteSymbolsEmbedding_univ :
    finiteSymbolsEmbedding Finset.univ = ⊤ := by
  funext i
  change (if i ∈ Finset.univ then (1 : unitInterval) else 0) = 1
  simp

end Tomabechi.Consistency.R1
