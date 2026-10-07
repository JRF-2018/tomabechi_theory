# Tomabechi/Consistency/ConsistencyC6_TypedSelfProcess.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_TypedSelfProcess.lean`](../Tomabechi/Consistency/ConsistencyC6_TypedSelfProcess.lean)（共有 SCM の同じ観測から得る、型つきの自己過程（Self・Ego・TCZ））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文 §2.4 の**型の区別**（Self・Ego・TCZ を別の型で扱う）を、定理25の**共有 SCM**（構造的因果モデル）の**同じ観測**から得る、という接続です。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品です。

* 自己の三つの表現（Self・Ego・TCZ）を、C4 の実際のデータから取り、自然数のすべての層を保持する構造体 `C6TypedSelfRepresentation`。
* 元の SCM を、**同じ観測写像**（\(\Gamma\) を消さず、履歴から三表現を回収する）に通した**自己過程** `c6TypedSelfProcessSCM`。外生法則・入力履歴・候補の変数は元のまま。
* 介入した結合法則・ベースラインの結合法則は、元の SCM のものを同じ観測で押し出したものに**厳密に等しい**。元の \((\Gamma,Y^+)\) を完全に復元できる。
* 条件 25-A(2)（介入不変性）が、すべての主体・行為・履歴・候補で成り立つ。

### 0.2 このファイルが証明していないこと

* 三表現は、このモデルの具体的なデータ（区間 \([0,1]\) の勾配流）です。
* 原文の一般の自己過程の定義との同一視ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> Self 作用素・Ego 自己更新・TCZ 集合を異なる型で保持し、元 SCM の (Γ,Y⁺) から履歴を復元して同時に観測する。候補や行為を履歴の代用にしない。全主体・行為で同じ外生法則・入力履歴・候補変数を使う。

---

<a id="Tomabechi.Consistency.C6.C6TypedSelfRepresentation"></a>

## 構造体 `C6TypedSelfRepresentation`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ})
$$

### Lean のコメント（日本語訳）

> 実際のC4自己過程。Selfは集合選別作用素、Egoは自己更新写像、TCZは集合。Nat全層を保持し、固定点codeのBoolだけで三表現を代替しない。

### 定義の説明

実際の C4 の自己過程の**三つの表現**を、別々の型で持つ構造体です。**Self** は集合を選別する作用素（層 \(i\) ごとに、実数の集合から実数の集合へ）、**Ego** は自己更新の写像（\([0,1]\) の点から点へ）、**TCZ** は集合です。自然数のすべての層を保持し、固定点の符号（`Bool`）だけで三つの表現を代用することはしません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.instance@L25"></a>

## インスタンス `instance@L25`

### 式

$$
\text{可測空間の構造}=\text{最大}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

三つ組の型に、最大の可測空間の構造（すべての部分集合が可測）を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfRepresentation"></a>

## 定義 `c6TypedSelfRepresentation`

### 式

$$
h\mapsto(\mathrm{Self}^h,\mathrm{Ego}^h,\mathrm{TCZ}^h)
$$

### Lean のコメント（日本語訳）

> 元のC4型付きadapterの同じ履歴から三表現を取得する。

### 定義の説明

履歴 \(h\) に対し、もとの C4 の型つきの三つ組（Self・Ego・TCZ）から、同じ履歴の三つの表現を取り出します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfObservation"></a>

## 定義 `c6TypedSelfObservation`

### 式

$$
(\Gamma,h)\mapsto\bigl((\Gamma,\ R(h)),\ h\bigr)
$$

### Lean のコメント（日本語訳）

> 共有SCMのΓを消さず、将来出力に符号化された履歴から三表現を回収する。この観測をbaselineと介入の両方へ適用する。

### 定義の説明

共有の SCM の \(\Gamma\) を**消さずに**、将来の出力に符号化された履歴 \(h\) から、三つの表現 \(R(h)\) を回収する観測です。この観測を、ベースラインと介入の**両方**に同じように適用します（候補や行為を履歴の代用にしない）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfObservation_measurable"></a>

## 補題 `c6TypedSelfObservation_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測写像は可測です。

### 証明の概略

1. 各成分（第 1 成分は恒等、三つ組は有限の型からの写像なので可測、履歴は恒等）の可測性を合わせる。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM"></a>

## 定義 `c6TypedSelfProcessSCM`

### 式

$$
\text{元の SCM を、同じ観測写像に通した自己過程}
$$

### Lean のコメント（日本語訳）

> 全主体・行為で元のSCMを同じ観測写像に通した自己過程。原モデルの法則を別の独立法則で置き換えない。

### 定義の説明

すべての主体 \(d\)・行為 \(a\) で、**元の SCM**（構造的因果モデル）を**同じ観測写像**に通した自己過程です。外生法則・入力履歴・候補の変数は元の SCM のものをそのまま使い、ベースラインの式・介入した式は、元の状態の式・出力の式に観測写像を合成したものです。**原モデルの法則を、別の独立な法則で置き換えません**。

### 証明の概略

1. 外生法則・入力履歴・候補変数・それらの可測性は元の SCM から取る。
2. ベースライン・介入した式は、元の状態の式と出力の式を観測写像（`c6TypedSelfObservation`）に通したもの。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_representation"></a>

## 補題 `c6TypedSelfProcessSCM_representation`

### 式

$$
R_i=\mathrm{typedSelfRepresentation}(h)
$$

### Lean のコメント（日本語訳）

> R_iの三表現は、元SCMの同じ履歴hに対応する実C4データである。

### 補題の説明

自己過程が出す三つの表現 \(R_i\) は、元の SCM の同じ履歴 \(h\) に対応する、実際の C4 のデータです。

### 証明の概略

1. 介入した式の第 1 成分の第 2 成分が、出力の式（履歴を符号化）に表現の取得を適用したもの。定義を展開して一致を示す。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_satisfies25A2"></a>

## 補題 `c6TypedSelfProcessSCM_satisfies25A2`

### 式

$$
\text{条件 25-A(2)（介入不変性）}
$$

### Lean のコメント（日本語訳）

> 全主体・行為・履歴・候補に対する25-A2。候補と履歴は元の独立座標である。

### 補題の説明

すべての主体・行為・履歴・候補について、**条件 25-A(2)**（候補を介入しても出力の法則が変わらない）が成り立ちます。候補と履歴は、元の SCM の独立な座標です。

### 証明の概略

1. 候補と履歴の独立性：一様分布の積測度の二つの座標は独立（`indepFun_prod`）。
2. 条件 25-A(2) の一般の判定（`condition25A2`）に、独立性と、出力が候補に依らないことを渡す。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_intervenedLaw"></a>

## 補題 `c6TypedSelfProcessSCM_intervenedLaw`

### 式

$$
\text{自己過程の介入 joint}=\text{元の SCM の介入 joint を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

> 元SCMの介入jointを同じ観測写像で押し出した法則に厳密に等しい。

### 補題の説明

自己過程の介入した結合法則は、元の SCM の介入した結合法則を、同じ観測写像で押し出したものに**厳密に等しい**です。

### 証明の概略

1. 外生法則の像（`map`）の合成の計算。介入した式は、元の式と観測写像の合成。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_baselineLaw"></a>

## 補題 `c6TypedSelfProcessSCM_baselineLaw`

### 式

$$
\text{自己過程のベースライン joint}=\text{元の SCM のベースライン joint を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

> 元SCMのbaseline jointにも、介入と同じ観測写像を用いる。

### 補題の説明

ベースラインの結合法則にも、介入と同じ観測写像を使っています（同じ関係が成り立つ）。

### 証明の概略

1. 前の補題と同様に、像の合成の計算。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfObservationRecovery"></a>

## 定義 `c6TypedSelfObservationRecovery`

### 式

$$
((\Gamma,R),h)\mapsto(\Gamma,h)
$$

### Lean のコメント（日本語訳）

> 三表現を付加した観測から元の(Γ,Y⁺)を完全に復元する。

### 定義の説明

三つの表現を付加した観測から、元の \((\Gamma,Y^+)\)（状態と出力）を**完全に復元**する写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfObservationRecovery_leftInverse"></a>

## 補題 `c6TypedSelfObservationRecovery_leftInverse`

### 式

$$
\mathrm{Recovery}\circ\mathrm{Observation}=\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

復元写像は、観測写像の左逆です（観測で情報を失わない）。

### 証明の概略

1. 定義から（`rfl`）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_recoverIntervenedLaw"></a>

## 補題 `c6TypedSelfProcessSCM_recoverIntervenedLaw`

### 式

$$
\text{付加した介入 joint から、元の SCM の介入 joint を回収できる}
$$

### Lean のコメント（日本語訳）

> 三表現を付加した介入jointから、元SCMの同じ介入jointを厳密に回収する。R_iの付加でΓや出力の結合情報を失っていない。

### 補題の説明

三つの表現を付加した介入結合法則から、元の SCM の**同じ介入結合法則**を厳密に回収できます。表現 \(R_i\) を付加しても、\(\Gamma\) と出力の結合情報を失っていません。

### 証明の概略

1. 介入結合法則を復元写像で押し出す。復元写像は観測写像の左逆（前の補題）。
2. 像の合成（`map_map`）で、元の SCM の介入結合法則に一致する。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_fixedPointGamma"></a>

## 補題 `c6TypedSelfProcessSCM_fixedPointGamma`

### 式

$$
\Gamma_{\text{介入観測}}=\text{履歴別逆極限固定点の code}
$$

### Lean のコメント（日本語訳）

> 介入観測のΓは同じ履歴別逆極限固定点のcodeである。

### 補題の説明

介入観測の \(\Gamma\) は、同じ履歴ごとの逆極限の固定点を符号化したものです。

### 証明の概略

1. 元の SCM の状態の式が、固定点の符号化であること（定義）から。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfProcessSCM_relationalState"></a>

## 補題 `c6TypedSelfProcessSCM_relationalState`

### 式

$$
\Gamma=\text{relationalState}(d,h,a)
$$

### Lean のコメント（日本語訳）

> 固定点codeは元の全profile・関係近傍・入出辺を持つΓそのものに復元される。

### 補題の説明

固定点の符号は、元の**すべてのプロファイル・関係の近傍・入出の辺**を持つ \(\Gamma\)（関係的な状態）にそのまま復元されます。

### 証明の概略

1. 前の補題で \(\Gamma\) が固定点の符号。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfRepresentation_from_fixedPoint"></a>

## 補題 `c6TypedSelfRepresentation_from_fixedPoint`

### 式

$$
R(\text{固定点の第 0 座標から決めた符号})=R(h)
$$

### Lean のコメント（日本語訳）

> 同じ固定点の認知座標から、同じ履歴の三表現を復元する。

### 補題の説明

同じ固定点の認知座標（第 0 座標が 1 かどうか）から、同じ履歴の三つの表現が復元されます。

### 証明の概略

1. 履歴 \(h\) の二値で場合分けして、固定点の第 0 座標の値を計算する。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfRepresentation_self_tcz"></a>

## 補題 `c6TypedSelfRepresentation_self_tcz`

### 式

$$
\mathrm{Self}^h_i(\mathrm{reachable})=\mathrm{TCZ}^h_i
$$

### Lean のコメント（日本語訳）

> Selfを実到達集合に適用すると、このR_iが保持する同じTCZとなる。

### 補題の説明

Self を実際の到達集合に適用すると、この \(R_i\) が保持する同じ TCZ になります。

### 証明の概略

1. C4 の三つ組の関係の証拠（`self_is_tcz`）。

----

<a id="Tomabechi.Consistency.C6.c6TypedSelfRepresentation_ego_feedback"></a>

## 補題 `c6TypedSelfRepresentation_ego_feedback`

### 式

$$
\mathrm{Ego}^h_i(x)=\text{履歴流の時刻 1 の写像}(x)
$$

### Lean のコメント（日本語訳）

> Egoは同じ履歴流の時刻1自己更新である。

### 補題の説明

Ego は、同じ履歴の流れの、時刻 1 の自己更新です。

### 証明の概略

1. C4 の三つ組の関係の証拠（`ego_is_feedback`）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
