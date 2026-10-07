# Tomabechi/Consistency/ConsistencyR123_SubjectIdentity.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SubjectIdentity.lean`](../Tomabechi/Consistency/ConsistencyR123_SubjectIdentity.lean)（定理19の主体・履歴と定理16/25の主体・履歴の同一性（M8.1））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文 §8 は、定理 19 の自由意思容量を、**定理 16 と同じ主体 \(i\)・履歴 \(h\)** について述べます（M8.1）。従来は、主体を `Bool`、履歴を `Bool` で共通にしただけで、19 の実験の主体・履歴と、16/25 の自己過程の主体・履歴を等式で結ぶフィールドがありませんでした。ここでは次を述語にします。

1. **実験の自己過程＝25 の自己過程：** 19 の実験の自己過程成分の周辺は、`N.scm` の主体・層・履歴の自己過程のベースラインの結合法則そのもの。
2. **三表現＝16 の自己表象：** その自己過程の表象成分は、`N.legacy` に格納した定理 16 の自己表象（SCM の出力の履歴に対するもの）。
3. **出力は履歴：** SCM の出力は候補・介入によらず履歴そのもの。したがって三表現は、履歴 \(H\) の 16 の自己表象。
4. **\(\Gamma\) は 16 の固定点から：** 全主体・層の \(\Gamma\) は、履歴 \(h\) の定理 16 の固定点の符号から作られる。16 の系は全主体で同じ（主体ごとに別の系を持たない）。

### 0.2 このファイルが証明していないこと

* (3)(4) は `sharedModel` についての証明で、一般の \(N\) についての導出ではありません。
* 定理 16 の系が主体によらず一つであることを「同じ主体」と読みます。主体ごとに別の 16 の系を置く拡張は扱いません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §8 は、定理19の自由意思容量を定理16 と同じ主体 i・履歴 h について述べる。従来は、主体を Bool、履歴を Bool で共通にしただけで、19 の実験の主体・履歴と 16/25 の自己過程の主体・履歴を等式で結ぶ field がなかった。ここでは次を述語にする。（以下、上の四点。）範囲：(3)(4) は sharedModel についての証明で、一般の N についての導出ではない。定理16の系が主体に依らず一つであることを「同じ主体」と読む（主体ごとに別の16系を置く拡張は扱わない）。

---

<a id="Tomabechi.Consistency.R123.instance@L30"></a>

## インスタンス `instance@L30`

### 式

$$
\text{共通束の各点の状態型は可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の各点の状態の型に、可測空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedSubjectIdentity"></a>

## 構造体 `SharedSubjectIdentity`

### 式

$$
\text{19 の実験の主体・履歴}=\text{16/25 の主体・履歴}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 19 の主体・履歴と、定理 16/25 の主体・履歴の同一性を述べる受入の型です。フィールドは、(1) 19 の実験の自己過程成分の周辺が、`N.scm` の主体・層・履歴の自己過程のベースラインの結合法則そのもの、(2) その自己過程の表象成分が、`N.legacy.selfRepresentation`（SCM の出力の履歴に対するもの）、(3) SCM の出力は、候補・介入によらず履歴そのもの、(4) \(\Gamma\) は、履歴の定理 16 の固定点の符号から作られる（16 の系は全主体で同じ）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_subjectIdentity"></a>

## 定理 `sharedModel_subjectIdentity`

### 式

$$
\mathrm{SharedSubjectIdentity}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、主体・履歴の同一性を満たします。

### 証明の概略

1. (1)：全域の実験の自己過程の周辺（`fullExperiment_selfProcess`）。
2. (2)・(4)：定義から `rfl`。
3. (3)：SCM の出力が履歴であるという補題（`commonConceptSCM_output_eq_history`）。

----

<a id="Tomabechi.Consistency.R123.SharedSubjectIdentity.representation_eq_history"></a>

## 補題 `SharedSubjectIdentity.representation_eq_history`

### 式

$$
\text{三表現}=N.\mathrm{legacy}.\mathrm{selfRepresentation}(H)
$$

### Lean のコメント（日本語訳）

> 三表現は、履歴Hの定理16の自己表象（19の実験と25の自己過程が同じ16の系を読む）。

### 補題の説明

三つの表現は、履歴 \(H\) の定理 16 の自己表象です（19 の実験と 25 の自己過程が、同じ 16 の系を読みます）。

### 証明の概略

1. (2) の表象の等式と、(3) の出力が履歴であることを合わせる。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_subject_identity"></a>

## 定理 `final_consistency_v2_with_subject_identity`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedSubjectIdentity}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、主体・履歴の同一性を加えた版です。

### 証明の概略

1. 存在宣言です。前の版から \(N\) を取り、同一性を加える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
