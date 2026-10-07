import Tomabechi.Consistency.ConsistencyR123_FinalV2
import Tomabechi.Examples.Theorem25_NoSelf

/-!
# 25-C4（父母子の逆役割）の非空実例

原文 §14 の (25.C4) は「簡約した生物学的系譜モデルでは…と表せる」というモデル例で、
定理25の結論の前提ではない。共有モデル N の主体は `Bool` の二つで、父・母・子の役割や
出生をもつ存在 𝔇born を持たないため、N では (25.C4) は 𝔇born=∅ により空虚に成立する。

ここでは (25.C4) の式を述語 `GenealogyC4` として書き下し、既存の六人の系譜例
（`Tomabechi.Examples.Theorem25`、子 3 に父 1・母 2）が 𝔇born が**非空**のまま満たすことを示す。

**範囲：** これは N とは別の小さな有限モデルである。N の SCM・自己過程などの
受入型を拡張して父・母・子を載せたものではない。(25.C5)（死後の上位履歴層の表象）は、
死亡時刻・`AliveRealization0`・境界値 `∂α` が Lean のモデルに存在せず、定義を新しく
選ぶ必要があるので、ここでは扱わない（対応表に「対象外」と記録）。
-/

namespace Tomabechi.Consistency.R123
open Tomabechi.Examples.Theorem25

/-- (25.C4)：履歴 h∈ℋgene で、`FatherOf`/`HasFather`・`MotherOf`/`HasMother` は同一関係の
逆向き記述で、𝔇born の各存在に父と母がいる。 -/
structure GenealogyC4 {D H : Type*} (Dborn : Set D) (Hgene : Set H)
    (FatherOf MotherOf HasFather HasMother : H → D → D → Prop) : Prop where
  father_inverse : ∀ h ∈ Hgene, ∀ f c : D, FatherOf h f c ↔ HasFather h c f
  mother_inverse : ∀ h ∈ Hgene, ∀ m c : D, MotherOf h m c ↔ HasMother h c m
  born_has_parents : ∀ h ∈ Hgene, ∀ c ∈ Dborn, ∃ f m : D, FatherOf h f c ∧ MotherOf h m c

/-- 六人の系譜例の `HasMother c m ⇔ MotherOf m c`（既存例は `HasFather` だけを定義している）。 -/
def HasMotherExample (c m : Person) : Prop := MotherOf m c

/-- 六人の系譜例（履歴は一つ）：𝔇born={子}（非空）で (25.C4) を満たす。 -/
theorem genealogyC4_example :
    GenealogyC4 ({3} : Set Person) (Set.univ : Set Unit)
      (fun _ f c => FatherOf f c) (fun _ m c => MotherOf m c)
      (fun _ c f => HasFather c f) (fun _ c m => HasMotherExample c m) where
  father_inverse := fun _ _ _ _ => Iff.rfl
  mother_inverse := fun _ _ _ _ => Iff.rfl
  born_has_parents := fun _ _ c hc => by
    rw [Set.mem_singleton_iff.mp hc]
    exact child_has_father_and_mother

theorem genealogyC4_example_born_nonempty : ({3} : Set Person).Nonempty := ⟨3, rfl⟩

#print axioms genealogyC4_example
end Tomabechi.Consistency.R123
