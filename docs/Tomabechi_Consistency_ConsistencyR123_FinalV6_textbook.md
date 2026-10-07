# Tomabechi/Consistency/ConsistencyR123_FinalV6.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FinalV6.lean`](../Tomabechi/Consistency/ConsistencyR123_FinalV6.lean)（最終存在宣言 v6：一点版の受入型と 25-C5 の N 上の実例をまとめる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**最終の存在宣言の第 6 版**です。`final_consistency_v5`（一点版の受入の型を加えた版）と `final_consistency_v5_mortality`（25-C5 の \(N\) 上の実例を加えた版）は、別々のモジュールで、v4 に違う受入の型を足していました。ここで、両方を一つの `sharedModel` で同時に主張します。

あわせて、25-C5 の時刻に依存する profile `profileT` が、条件 25-B の現前の支持の条件（空でない・上向きに閉じている・\(\top\) を含む、最高層は非個体化のマーカー）を、全時刻で保つことを示します。死後に物理層の座標が \(\partial\) になっても、25-B は崩れません。

### 0.2 このファイルが証明していないこと

* 25-C5 の死亡の設定は、前のファイル（`ConsistencyR123_MortalityOnN`）のとおり、構成したモデルの選択です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> final_consistency_v5（ConsistencyR123_SelfProcessOnePoint）と final_consistency_v5_mortality（ConsistencyR123_MortalityOnN）は、別々のモジュールで v4 に違う受入型を足していた。ここで両方を一つの sharedModel で同時に主張する。あわせて、25-C5 の時刻依存の profile profileT が、条件25-B の現前支持の条件（非空・上向き閉・⊤ を含む、最高層は非個体化マーカー）を全時刻で保つことを示す。死後に物理層の座標が ∂ になっても、25-B は崩れない。

---

<a id="Tomabechi.Consistency.R123.supportT"></a>

## 定義 `supportT`

### 式

$$
\{\alpha\mid\mathrm{profile}_T(\alpha)\ne\mathrm{none}\}
$$

### Lean のコメント（日本語訳）

> 時刻依存のprofileの現前支持。

### 定義の説明

時刻に依存する profile の**現前の支持**（`none` でない層の集合）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.MortalityPresence25B"></a>

## 構造体 `MortalityPresence25B`

### 式

$$
\text{支持は非空・上向き閉・}\top\text{を含み、}\top\text{ の座標は非個体化マーカー}
$$

### Lean のコメント（日本語訳）

> 25-Bを時刻依存のprofileで：全時刻・全主体で、現前支持は非空・上向き閉・⊤を含み、⊤の座標は非個体化マーカーsome ()。

### 定義の説明

条件 25-B を、時刻に依存する profile で述べたものです。全時刻・全主体で、現前の支持は、空でなく、上向きに閉じていて、\(\top\) を含み、\(\top\) の座標は非個体化のマーカー `some ()` です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.bot_ne_top_commonConcept"></a>

## 補題 `bot_ne_top_commonConcept`

### 式

$$
\bot\ne\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の底と頂は異なります。

### 証明の概略

1. 等しいと仮定して、座標 0 での値を比べて矛盾を導く。

----

<a id="Tomabechi.Consistency.R123.mortalityPresence25B"></a>

## 補題 `mortalityPresence25B`

### 式

$$
\mathrm{MortalityPresence25B}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻に依存する profile でも、条件 25-B が全時刻で保たれます。

### 証明の概略

1. \(\top\) の座標は、\(\bot\ne\top\) なので、常に `some ()`。
2. 上向き閉：\(\beta=\bot\) の場合と、そうでない場合で場合分けする。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v6"></a>

## 定理 `final_consistency_v6`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{MortalityOnN}(N)\wedge\mathrm{MortalityPresence25B}
$$

### Lean のコメント（日本語訳）

> 一点版の受入型（一点版16担体をTCZにもつ25の自己過程、共通束上の21のV₀実例）と、25-C5のN上の実例・その25-Bを、一つのNで同時に主張する。

### 補題の説明

一点版の受入の型（一点版の 16 の担体を TCZ にもつ 25 の自己過程、共通束上の 21 の \(V_0\) の実例）と、25-C5 の \(N\) 上の実例・その 25-B を、**一つの \(N\) で同時に**主張する存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理（`mortalityPresence25B` を含む）です。

----


## コメント修正記録

表題と `final_consistency_v6` の docstring から、作業の段階を示す番号（「§17」）を削除し、「一点版の受入型」に書き換えました（コメントのみ）。
