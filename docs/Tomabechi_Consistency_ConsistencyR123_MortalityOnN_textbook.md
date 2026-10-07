# Tomabechi/Consistency/ConsistencyR123_MortalityOnN.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_MortalityOnN.lean`](../Tomabechi/Consistency/ConsistencyR123_MortalityOnN.lean)（25-C5 を N の主体に寄せる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**25-C5 を \(N\) の主体に寄せる**ファイルです。以前の 25-C5 の実例は、死ぬ人物（祖父・祖母）が \(N\) の主体に埋め込まれておらず、profile も定数でした。ここでは、**\(N\) の主体 `false` に死亡時刻 1 を与え**（`true` は死なない）、時刻に依存する profile `profileT` を拡張の側に持たせます。

* 物理層 \(\bot\) の profile は、死亡時刻以降は `none`（境界 \(\partial\)）、それ以前は \(N\) の profile と同じ。
* 上位層（\(\bot\) 以外）の profile は、全時刻で \(N\) の profile のまま（死後も表象が残る）。
* `AliveRealization0 d t ↔ 物理層の profile が ∂ でない`（\(t<\tau_d\)）。
* (25.C5)：\(t\ge\tau_d\Rightarrow\) `AliveRealization0 = 0` かつ物理層の profile \(=\partial\) かつ \(\exists\alpha_{\rm hist},\ 0\prec\alpha_{\rm hist}\prec\top\) で表象 \(\ne\partial\)。

\(N\) の SCM・自己過程・保存式は変更しません（\(N\) の profile は全時刻で一定で、拡張の側が、時刻に依存する読み替えを持ちます）。

### 0.2 このファイルが証明していないこと

* 死亡時刻は、構成したモデルの選択で、\(N\) の力学（軌道は \(\mathcal B_{\rm alive}\) に留まる）から導いたものではありません。
* \(N\) の現前の構造そのものを、時刻に依存するものにしたのではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前の 25-C5 の実例は、死ぬ人物（祖父・祖母）が N の主体に埋め込まれておらず、profile も定数だった。ここでは N の主体 false に死亡時刻 1 を与え（true は死なない）、時刻依存の profile profileT を拡張側に持たせる。…（以下、上の四点）。N の SCM・自己過程・保存式は変更しない（N の profile は全時刻で一定で、拡張側が時刻依存の読み替えを持つ）。範囲：死亡時刻は構成したモデルの選択で、N の力学（軌道は ℬ_alive に留まる）から導いたものではない。N の presence 構造そのものを時刻依存にしたのではない。

---

<a id="Tomabechi.Consistency.R123.deathTimeN"></a>

## 定義 `deathTimeN`

### 式

$$
\tau_{\rm false}=1,\ \tau_{\rm true}=\infty
$$

### Lean のコメント（日本語訳）

> Nの主体falseは時刻1に死亡、trueは死なない。

### 定義の説明

\(N\) の主体 `false` は時刻 1 に死亡し、`true` は死にません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.AliveRealization0N"></a>

## 定義 `AliveRealization0N`

### 式

$$
\mathrm{Alive}(d,t)\iff t<\tau_d
$$

### Lean のコメント（日本語訳）

> 物理層における生きた自己制御過程の直接実装の有無。

### 定義の説明

物理層における、生きた自己制御の過程の直接の実装の有無です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.profileT"></a>

## 定義 `profileT`

### 式

$$
\mathrm{profile}_T(d,t,\alpha)=\begin{cases}\mathrm{none}&\alpha=\bot,\ t\ge\tau_d\\ \mathrm{some}()&\text{それ以外}\end{cases}
$$

### Lean のコメント（日本語訳）

> 時刻依存のprofile：物理層⊥は死亡時刻以降none（境界∂）、他は常にsome ()。

### 定義の説明

**時刻に依存する profile** です。物理層 \(\bot\) は死亡時刻以降は `none`（境界 \(\partial\)）、他は常に `some ()` です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.MortalityOnN"></a>

## 構造体 `MortalityOnN`

### 式

$$
\mathrm{Alive}\iff\text{物理層の profile}\ne\partial\ \wedge\ \text{(25.C5)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

25-C5 を \(N\) の主体に寄せた述語です。フィールドは、(1) 生きた実装があることは、物理層の profile が境界でないことと同値、(2) 死亡前は、全層で \(N\) の profile と一致、(3) 上位層（\(\bot\) 以外）では、全時刻で \(N\) の profile と一致、(4) (25.C5)：死亡時刻以降は、物理層の実装は 0 で profile は境界、かつ \(0\prec\alpha_{\rm hist}\prec\top\) の層で表象が境界でない、(5) 死亡が実際に起きる主体と時刻がある（空虚でない）、(6) 死なない主体もある（死亡が全主体の自明な性質ではない）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_mortalityOnN"></a>

## 定理 `sharedModel_mortalityOnN`

### 式

$$
\mathrm{MortalityOnN}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、\(N\) の主体での死亡の述語を満たします。

### 証明の概略

1. (1)：主体で場合分けして、定義を展開する。
2. (2)(3)：profile の定義を展開。死亡前は条件が偽、上位層は \(\alpha\ne\bot\)。
3. (4)：死亡時刻以降の計算と、層 `diagonalLayer 1` が底と頂の間にあること。
4. (5)(6)：主体 `false`（時刻 1 に死亡）と `true`（死なない）。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v5_mortality"></a>

## 定理 `final_consistency_v5_mortality`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{MortalityOnN}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、\(N\) の主体での死亡の述語を加えた版です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
