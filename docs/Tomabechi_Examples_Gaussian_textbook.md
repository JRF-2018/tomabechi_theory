# Tomabechi/Examples/Gaussian.lean 解説

> 対象: [`Tomabechi/Examples/Gaussian.lean`](../Tomabechi/Examples/Gaussian.lean)（ガウス谷の微分補題（定理21・22の Python 例で共有））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**ガウス谷** \(\mathrm{well}(x)=-A\exp\!\bigl(-\tfrac{(x-c)^2}{2\sigma^2}\bigr)\) の 1 階・2 階の微分を与え、球 \(|x-c|\le r<\sigma\) の上で 2 階微分が正（**局所強凸**）であることを示す補題集です。定理21（局所谷）・定理22（谷の列）の Python 例で共有する、小さな共通部品です。

### 0.2 このファイルが証明していないこと

- 微分補題と局所強凸性だけで、谷の中の勾配流・不変性・収束は扱いません。それらは `Theorem21_GaussianValley.lean` などが、このファイルの補題を使って示します。
- Python の数値（格子上の値など）は証明対象外です。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # ガウス谷 `well A σ c x = -A exp(-(x-c)²/(2σ²))` の微分補題（定理21・22 の Python 例で共有）
>
> `dwell` は 1 階微分、`ddwell` は 2 階微分。\(|x-c|\le r<\sigma\) の球上で `ddwell>0`（局所強凸）。

名前空間は `Tomabechi.Examples.Gaussian`。

---

<a id="Tomabechi.Examples.Gaussian.well"></a>

## 定義 `well`

### 式

$$\mathrm{well}(x)=-A\,e^{-(x-c)^2/(2\sigma^2)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

深さ \(A\)、中心 \(c\)、幅 \(\sigma\) のガウス型の谷（ポテンシャル）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Gaussian.dwell"></a>

## 定義 `dwell`

### 式

$$\mathrm{well}'(x)=\frac{A(x-c)}{\sigma^2}\,e^{-(x-c)^2/(2\sigma^2)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

谷の 1 階微分（勾配）の公式です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Gaussian.ddwell"></a>

## 定義 `ddwell`

### 式

$$\mathrm{well}''(x)=\frac{A}{\sigma^2}\Bigl(1-\frac{(x-c)^2}{\sigma^2}\Bigr)e^{-(x-c)^2/(2\sigma^2)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

谷の 2 階微分の公式です。\(|x-c|<\sigma\) の内側で正、外側で負になります。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Gaussian.hasDerivAt_expArg"></a>

## 定理 `hasDerivAt_expArg`

### 式

$$\frac{d}{dx}\Bigl(-\frac{(x-c)^2}{2\sigma^2}\Bigr)=-\frac{x-c}{\sigma^2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

指数の中身の微分です（連鎖律の部品）。

### 証明の概略

1. \((x-c)^2\) の微分（`HasDerivAt.pow`）と定数倍の微分から計算。

----

<a id="Tomabechi.Examples.Gaussian.hasDerivAt_well"></a>

## 定理 `hasDerivAt_well`

### 式

$$\sigma\ne0\Rightarrow\mathrm{well}'=\mathrm{dwell}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`dwell` が実際に `well` の導関数であること。

### 証明の概略

1. `hasDerivAt_expArg` と `Real.hasDerivAt_exp` の合成、定数 \(-A\) の積。

----

<a id="Tomabechi.Examples.Gaussian.hasDerivAt_dwell"></a>

## 定理 `hasDerivAt_dwell`

### 式

$$\sigma\ne0\Rightarrow\mathrm{dwell}'=\mathrm{ddwell}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`ddwell` が実際に `dwell` の導関数であること。

### 証明の概略

1. 積の微分（\((x-c)\) と指数関数）と `hasDerivAt_expArg`。整理して `ddwell` の式に一致。

----

<a id="Tomabechi.Examples.Gaussian.ddwell_pos"></a>

## 定理 `ddwell_pos`

### 式

$$A>0,\ 0<\sigma,\ r<\sigma,\ |x-c|\le r\ \Rightarrow\ \mathrm{ddwell}(x)>0$$

### Lean のコメント（日本語訳）

> \(|x-c|\le r<\sigma\) の球上で \(\tilde V''>0\)（局所強凸）。

### 補題の説明

**局所強凸性**：谷の中心から幅 \(\sigma\) より近い範囲では、2 階微分が正です。

### 証明の概略

1. \((x-c)^2\le r^2<\sigma^2\) なので \(1-(x-c)^2/\sigma^2>0\)。
2. \(A/\sigma^2>0\)、指数関数 \(>0\) との積で正。

----


## コメント修正記録

（なし）
