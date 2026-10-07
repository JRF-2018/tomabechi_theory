# Tomabechi/Consistency/ConsistencyC6_EntryAdapters.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_EntryAdapters.lean`](../Tomabechi/Consistency/ConsistencyC6_EntryAdapters.lean)（受け入れ済みの共有署名から、各定理の一般入口を呼ぶ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**受け入れ済みの共有署名 \(M\)** から、各定理の**一般の入口**を呼ぶファイルです。同じ \(M\) の、実際の段の列・時刻・完全軌道・D・E・自己過程を使います。原文の全対象を一つの軌道に押し込まず、箱の中の C1・凍結した段・全履歴の逆系・頂点の適用域を保ちます。中心の文脈の変更と、完全状態の更新も区別します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の、**定理ごとの呼び出し**の部分です。

| 定理 | 内容 |
| --- | --- |
| 1・2・4・20 | C1 の入口・距離の評価を、全有限層の実 D の選択軌道で読む |
| 15→23 | 完全軌道の非再訪（平均を含む完全状態でも） |
| 16 | 固定点の族は、C4 の逆系のもの |
| 19 | 情報の法則・容量（単調・底 0・頂で正） |
| 21 | 全段の四つの結論 |
| 22・23-B | 元の（緩和していない）H-stage の全前件から 23-B の一般入口 |
| 24→26→27 | 同じ \(M\) の D・E をそのまま渡す |
| 25 | 全主体・全共通層で自己（アートマン）が存在しない |

### 0.2 このファイルが証明していないこと

* 「受け入れ済み」の構造体（`OriginalPremises`・`AdditionalConditions`）は、別のファイル（`ConsistencyC6_Acceptance`）で定義・構成します。
* 頂点の許容方策は有界可測ゲインのものです。Borel 方策一般への主張ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 同じ M の実段列・時刻・完全軌道・D/E・自己過程を用いる。原文の全対象を一軌道へ押し込まず、箱内 C1、凍結段、全履歴逆系、頂点の適用域を保つ。中心 context の変更と完全状態の更新も区別する。

---

<a id="Tomabechi.Consistency.C6.ModelSignature.relaxedStages"></a>

## 定義 `ModelSignature.relaxedStages`

### 式

$$
\text{元の H-stage から不変領域版を派生}
$$

### Lean のコメント（日本語訳）

> 元H-stageを満たす同じMから、不変領域版を既存変換で派生させる。元の証人を緩和条件で置き換える構成ではない。

### 定義の説明

元の H-stage を満たす同じ \(M\) から、**不変領域版**（緩和した入力）を、既存の変換で派生させます。元の証人を、緩和した条件で**置き換える**構成ではありません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.meanStep"></a>

## 定義 `ModelSignature.meanStep`

### 式

$$
(m,z)\mapsto(m,\ \mathrm{step}(z))
$$

### Lean のコメント（日本語訳）

> 完全核の認知/物理状態に、C1で必要な保存平均を保持する。平均を射影時に外部から注入せず、入力状態の第一成分から読む。

### 定義の説明

完全状態の更新核に、C1 で必要な**保存された平均**を保持します。平均を、射影のときに外部から注入せず、入力の状態の第 1 成分から読みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.meanFiniteProjection"></a>

## 定義 `ModelSignature.meanFiniteProjection`

### 式

$$
(m,z)\mapsto\mathrm{finiteProjection}(m,c,z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

平均つきの完全状態から、C1 の二主体の状態への射影です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.mean_state_controls"></a>

## 補題 `AdditionalConditions.mean_state_controls`

### 式

$$
\text{自律的な全状態核が、全有限層の全制御軌道を保存する}
$$

### Lean のコメント（日本語訳）

> 同じ署名から定まる自律的な全状態核が、全有限層の全制御軌道を保存する。

### 補題の説明

同じ署名から決まる**自律的な全状態の更新核**が、すべての有限層の、すべての制御軌道を保存します（平均は変わらず、射影した状態が C1 の制御軌道になる）。

### 証明の概略

1. 追加条件の「全許容制御の回収」（`core_all_finite_controls`）と、平均の保存から。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.c1Entries"></a>

## 定義 `ModelSignature.c1Entries`

### 式

$$
\text{C1 の全入口・O13・O24 の証拠}
$$

### Lean のコメント（日本語訳）

> C1の全入口・O13・O24証拠はM自身のproof-bearingデータに含まれる。selectedFlowの実D軌道との等式はAdditionalConditions.c1_selected_flowで別途供給する。

### 定義の説明

C1 の全入口（定理1・2・4・20 など）・定理20の前提・原文 §2.4 の三つ組の証拠は、\(M\) 自身の証明つきデータ（`M.c1`）に含まれます。選択した流れと実際の D の軌道の等式は、追加条件（`c1_selected_flow`）で別に与えます。

### 証明の概略

1. `M.c1.allEntryConclusions` を適用する。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.finite_control_ac"></a>

## 補題 `OriginalPremises.finite_control_ac`

### 式

$$
\text{有限層の実軌道は絶対連続}
$$

### Lean のコメント（日本語訳）

> O01の有限層存在：半差のACと保存平均から全二主体状態のACを得る。

### 補題の説明

原文 §2.1 の「有限層の存在」：差の半分の絶対連続性と保存された平均から、**二主体の状態全体の絶対連続性**を得ます。

### 証明の概略

1. 軌道は \(\text{平均}+\text{半差}\cdot(1,-1)\)（`finite_control_solution`）。平均は定数、半差は絶対連続（`c1ControlledOrbit_absolutelyContinuousOnInterval`）。和・スカラー倍も絶対連続。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.finite_control_ode"></a>

## 補題 `OriginalPremises.finite_control_ode`

### 式

$$
\text{有限層の実軌道は、制御の場の ODE を a.e. 満たす}
$$

### Lean のコメント（日本語訳）

> 全有限層・全可測競合の実二主体ODE。平均の保存と半差のa.e.微分を使う。

### 補題の説明

すべての有限層・すべての可測な制御の、実際の二主体の軌道は、制御の場の**微分方程式をほとんど至る所で満たします**。平均の保存と、差の半分のほとんど至る所での微分を使います。

### 証明の概略

1. 半差の微分（`c1ControlledOrbit_ae_ode`）。平均は定数なので微分は 0。
2. 二主体の軌道の微分は、\(\dot d\cdot(1,-1)\) で、制御の場に一致する。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.finite_field_locallyLipschitz"></a>

## 補題 `ModelSignature.finite_field_locallyLipschitz`

### 式

$$
\text{有限層の場は局所リプシッツ}
$$

### Lean のコメント（日本語訳）

> 時刻と入力を固定した有限層場は全状態上で滑らかなので局所Lipschitz。

### 補題の説明

時刻と入力を固定した有限層の場は、全状態の上で滑らかなので、**局所リプシッツ**です。

### 証明の概略

1. 選んだ流れは率 3 の流れ。場の各成分が一次式（`fun_prop`）なので C¹。C¹ は局所リプシッツ（`ContDiff.locallyLipschitz`）。

----

<a id="Tomabechi.Consistency.C6.c6TopGainField_locallyLipschitz"></a>

## 補題 `c6TopGainField_locallyLipschitz`

### 式

$$
\text{頂点の任意ゲインの場は局所リプシッツ}
$$

### Lean のコメント（日本語訳）

> 頂点の任意ゲインでも状態場は全域で滑らか。Borel方策一般への主張ではない。

### 補題の説明

頂点の**任意のゲイン**についても、状態の場は全域で滑らかです（有界可測ゲインについての主張で、Borel 方策一般への主張ではありません）。

### 証明の概略

1. 場は状態の一次式（定義を展開して `fun_prop`）。C¹ から局所リプシッツ。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.top_control_ac"></a>

## 補題 `OriginalPremises.top_control_ac`

### 式

$$
\text{頂点の実軌道は絶対連続}
$$

### Lean のコメント（日本語訳）

> O01の頂点存在：全競合方策の実D軌道でACを保つ。

### 補題の説明

原文 §2.1 の「頂点の存在」：すべての競合する方策の、実際の D の軌道は絶対連続です。

### 証明の概略

1. 実軌道は選んだ有界可測ゲインの解（`top_control_solution`）。その絶対連続性は、ベクトル軌道の補題から。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.top_control_ode"></a>

## 補題 `OriginalPremises.top_control_ode`

### 式

$$
\text{頂点の実軌道は、同じ可測ゲイン場の a.e. 解}
$$

### Lean のコメント（日本語訳）

> O01の頂点存在：全競合方策の実D軌道は同じ可測ゲイン場のa.e.解である。

### 補題の説明

頂点のすべての競合する方策の、実際の D の軌道は、**同じ可測ゲインの場のほとんど至る所の解**です。

### 証明の概略

1. 実軌道は選んだゲインの解。ゲインのベクトル軌道がほとんど至る所で微分方程式を満たす（`measurableGainVectorOrbit_ae_ode`）。成分ごとに場の式と比べる。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.c1_distance"></a>

## 補題 `AdditionalConditions.c1_distance`

### 式

$$
\text{定理1の距離評価を、全有限層の実 D の選択軌道で読む}
$$

### Lean のコメント（日本語訳）

> 定理1の定量結論を、全有限層の実D選択軌道で読む。

### 補題の説明

定理1の定量的な結論（TCZ までの距離の評価）を、**すべての有限層の、実際の D の選択した軌道**で読みます。

### 証明の概略

1. C1 の証人の定理1の結論（`c1Witness_entry_results`）に、選択した流れと D の軌道の一致（`c1_selected_flow`）を使う。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.nonrecurrence"></a>

## 補題 `OriginalPremises.nonrecurrence`

### 式

$$
0\le a<b\Rightarrow\mathrm{path}(b)\ne\mathrm{path}(a)
$$

### Lean のコメント（日本語訳）

> 全非負時間域の15→23-Aを同じ完全pathへ適用する。

### 補題の説明

全非負の時間域で、定理15→23-A を、同じ完全軌道に適用します（軌道は同じ状態に戻らない）。

### 証明の概略

1. エントロピーの入力の非再訪（`EntropyBalanceInputs.nonrecurrence`）。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.mean_nonrecurrence"></a>

## 補題 `OriginalPremises.mean_nonrecurrence`

### 式

$$
(m,\mathrm{path}(b))\ne(m,\mathrm{path}(a))
$$

### Lean のコメント（日本語訳）

> 保存平均を含む完全状態でも、同じ15→23収支から非再訪が得られる。

### 補題の説明

保存された平均を含む完全状態でも、同じ 15→23 の収支から、非再訪が得られます。

### 証明の概略

1. 等しいとすると、第 2 成分が等しくなり、前の補題に矛盾。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.fixedPoints_eq_original"></a>

## 補題 `OriginalPremises.fixedPoints_eq_original`

### 式

$$
M.\mathrm{fixedPoints}=\text{C4 の固定点族}
$$

### Lean のコメント（日本語訳）

> 同じMの固定点族は、受入済み逆系の固定点族そのものである。

### 補題の説明

同じ \(M\) の固定点の族は、受け入れ済みの逆系（C4）の固定点の族そのものです。

### 証明の概略

1. 原文の前提の「逆極限」（`inverse_limit`）の証拠から、固定点族が C4 のものに等しいことを取り出す。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.information_laws"></a>

## 補題 `AdditionalConditions.information_laws`

### 式

$$
\text{物理層は零情報、上位層は正の情報、容量は単調で底 0・頂で正}
$$

### Lean のコメント（日本語訳）

> 固定した全層容量の問題族は、Mが採用する情報lawと同じjoint/referenceを使う。底層の零問題を全上層へ保存し、正情報問題を底層だけから除く。

### 補題の説明

固定した全層の容量の問題族は、\(M\) が採用する情報の法則と**同じ結合・参照の分布**を使います。底の層の零情報の問題を全上層へ保存し、正の情報の問題を底の層だけから除きます。結論は、底の層の結合は物理層のもの、上位の層の結合は上位層のもの、容量は単調で、底で 0、頂で正、です。

### 証明の概略

1. 追加条件の物理層・段の情報の等式（`physical_information`・`stage_information`）で書き換える。
2. 容量の単調性・端点は C3 の証明書（`c3_sharedWitness`）。

----

<a id="Tomabechi.Consistency.C6.c6Stage21Conclusion"></a>

## 定義 `c6Stage21Conclusion`

### 式

$$
\text{定理21の四つの結論}
$$

### Lean のコメント（日本語訳）

> 定理21の四結論。情報量はM自身の採用jointから計算する。谷の一意性・変位・凍結ODE/指数率・正情報/枝帰属をすべて保持する。

### 定義の説明

定理21の**四つの結論**です。情報量は \(M\) 自身が採用する結合法則から計算します。(1) 谷の一意な最小点、(2) 最小点の移動量の評価と停留条件、(3) 凍結した ODE と指数率、(4) 正の情報・枝への帰属、をすべて保持します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.theorem21"></a>

## 定理 `AdditionalConditions.theorem21`

### 式

$$
\text{全段の定理21の四結論}
$$

### Lean のコメント（日本語訳）

> 同じMの実jointとの等式を保持して、全段の21一般入口の四結論を取り出す。局所情報量の結論だけを別lawへ移したものではない。

### 補題の説明

同じ \(M\) の実際の結合法則との等式を保持したまま、**すべての段**で、定理21の一般入口の四つの結論を取り出します。局所の情報量の結論だけを別の法則へ移したものではありません。

### 証明の概略

1. 情報の法則が上位の結合法則（`stage_information`）。
2. 定理21の一般の入口を、\(M\) の段・採用した情報法則に適用する。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.theorem23B"></a>

## 定義 `AdditionalConditions.theorem23B`

### 式

$$
\text{元の H-stage の全前件から、23-B の一般入口を呼ぶ}
$$

### Lean のコメント（日本語訳）

> 元のH-stageの全前件から、Mの実段列と実切替時刻で23-B一般入口を呼ぶ。gap・線分・再始動・対数待ち条件を省かず、緩和版へ置き換えない。

### 定義の説明

元の H-stage の**全前件**から、\(M\) の実際の段の列と実際の切り替え時刻で、23-B の一般入口を呼びます。間隔・線分・再始動・対数的な待ち時間の条件を省かず、緩和版へ置き換えません。

### 証明の概略

1. 切り替えの核（`meanField_stage_specs_and_switches_give_condition23B_core`）に、C3 の層の列・表象・閾値・間隔・待ち時間と、\(M\) の段が C3 の元の H-stage であること（`original_stages`）を使って各前件を渡す。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.theorem24_26"></a>

## 定義 `ModelSignature.theorem24_26`

### 式

$$
\text{24→26 の入口に、同じ }M\text{ の D/E をそのまま渡す}
$$

### Lean のコメント（日本語訳）

> 同じMのD/Eを24→26入口へそのまま渡す。全alive初期状態と全非負開始時刻を保つ。

### 定義の説明

同じ \(M\) の D・E を、定理24→26 の入口へ、そのまま渡します。生きているすべての初期状態・すべての非負の開始時刻を保ちます。

### 証明の概略

1. 定理24→26 の一般の入口（`theorem24_to26_from_nonnegativeTimeData`）に `M.data`・`M.dynamics` を渡す。

----

<a id="Tomabechi.Consistency.C6.OriginalPremises.theorem27"></a>

## 定義 `OriginalPremises.theorem27`

### 式

$$
\text{27-A の受入入力から、同じ }M\text{ の D/E を運用入口へ渡す}
$$

### Lean のコメント（日本語訳）

> 27-A受入入力から同じMのD/Eを運用入口へ渡す。全初期状態を量化し、参照場・実入力・随伴評価も同じ入力recordから取る。

### 定義の説明

27-A の受け入れた入力から、同じ \(M\) の D・E を、定理27の運用入口へ渡します。全初期状態を量化し、基準の場・実際の入力・随伴の評価も、同じ入力の構造体から取ります。

### 証明の概略

1. 定理24・26 のデータから定理27への入口（`theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae`）に、`h.top_actuator`（頂点の全運用入力）のフィールド（やり直し・ODE・勾配・相殺・局所リプシッツ・微分・フィードバック入力・随伴の有界性）を対応させて渡す。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions.noAtman"></a>

## 補題 `AdditionalConditions.noAtman`

### 式

$$
\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)
$$

### Lean のコメント（日本語訳）

> 全主体/全共通層の25.2を、同じMのSCMから得る。

### 補題の説明

すべての主体・すべての共通層で、定理25の第二の結論（自己の不在）を、同じ \(M\) の SCM から得ます。

### 証明の概略

1. SCM の一般の入口を適用する（出力が候補に依らない）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
