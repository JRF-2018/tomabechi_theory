# Tomabechi/Consistency/ConsistencyR123_NoClockCoordinate.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_NoClockCoordinate.lean`](../Tomabechi/Consistency/ConsistencyR123_NoClockCoordinate.lean)（完全状態に時計座標を加えていないこと（M12.1））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文の §12（定理 23）は、完全状態 \(z=(x_0,(x_\alpha)_{\alpha>0},e)\) に、「\(\mathcal S\) を一価にするために必要な環境・記憶・履歴の変数は含めるが、**時計座標そのものを追加して、非再帰の結論を自明化しない**」と書き、総エントロピー \(\mathcal S(z)=\hat S_{\rm phys}(z)+\sum_\alpha w_\alpha\hat H_\alpha(z)\) を**時間に依存しない一価の状態汎関数**とします（M12.1）。

モデルの完全状態は `CompleteState = ℝ × ℝ`（認知座標 \(q\)・物理座標 \(p\)）です。物理座標は、エントロピーの収支 \(p'+q'^2=p+q^2+E\)（\(E\) は生成）で動き、時刻 \(A\) では動きません。このことを、次の形で証明します（`SharedNoClockCoordinate`）。

1. **時間に依存しない汎関数：** `totalEntropy N z` は完全状態だけの関数（時刻の引数を持たない）で、完全路 \(z(t)\) の上で \(\mathcal S(z(t))=1+3t\)（生成 \(\Pi=3\) による）。
2. **増分は生成で決まる：** 一歩の \(p+q^2\) の増分は、経過時間 \(A\) によらず、生成 \(E\) に等しい。\(E=0\) なら、どれだけ時間が経っても \(p+q^2\) は変わらない。
3. **状態は時刻で決まらない：** 同じ経過時間 \(A\) でも、生成 \(E=0\) と \(E=1\) では、異なる完全状態に着く。物理座標は時計ではない。

### 0.2 このファイルが証明していないこと

* 時計座標の不在を「状態が時刻の関数でない」ことで形式化しました。完全路の上では \(\mathcal S(z(t))=1+3t\) なので、\(\mathcal S\) を通せば時刻は読み出せます（これは定理 23 の結論そのもので、座標として時計を足したわけではありません）。
* 「\(\mathcal S\) を一価にする変数が足りている」ことは、\(\mathcal S\) が `CompleteState` 上の関数として定義されていること（型）で担保します。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §12（定理23）は、完全状態 z=(x₀,(x_α)_{α>0},e) に「𝒮 を一価にするため必要な環境・記憶・履歴変数は含めるが、時計座標そのものを追加して非再帰結論を自明化しない」と書き、総エントロピー 𝒮(z) = Ŝ_phys(z) + Σ_α w_α Ĥ_α(z) を時間非依存の一価状態汎関数とする。モデルの完全状態は CompleteState = ℝ × ℝ（認知座標 q・物理座標 p）。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.totalEntropy"></a>

## 定義 `SharedModelSignature.totalEntropy`

### 式

$$
\mathcal S(z)=\hat S_{\rm phys}(z)+\sum_\alpha w_\alpha\hat H_\alpha(z)
$$

### Lean のコメント（日本語訳）

> 総エントロピー汎関数：完全状態だけの関数。

### 定義の説明

**総エントロピーの汎関数**です。物理のエントロピーと、重みつきの各層のエントロピーの和で、**完全状態だけ**の関数です（時刻の引数を持ちません）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedNoClockCoordinate"></a>

## 構造体 `SharedNoClockCoordinate`

### 式

$$
\text{完全状態}=\mathbb R\times\mathbb R\ \wedge\ \mathcal S(z(t))=1+3t\ \wedge\ \text{増分}=\text{生成}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

完全状態に時計座標を加えていないことを述べる受入の型です。フィールドは、(1) 完全状態は認知座標と物理座標の二つ（時刻の座標を持たない）、(2) 完全路の上で \(\mathcal S(z(t))=1+3t\)、(3) \(p+q^2\) の増分は、経過時間 \(A\) によらず生成 \(E\) に等しい、(4) 生成 0 なら、時間が経っても \(p+q^2\) は変わらない、(5) 同じ経過時間でも、生成が違えば着く完全状態は異なる（状態は時刻の関数でない）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.noClockCoordinate"></a>

## 定理 `SharedDataPreservation.noClockCoordinate`

### 式

$$
\mathrm{SharedNoClockCoordinate}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式のもとで、署名は時計座標を持たないことを満たします。

### 証明の概略

1. (3)：エントロピー収支の核の補題（`core_entropy`）。
2. (4)：(3) で \(E=0\) とする。
3. (5)：生成が 0 と 1 の二つの一歩の物理座標が異なることを、具体的な計算で示す。
4. (2)：完全路の定義と、総エントロピーの定義。

----

<a id="Tomabechi.Consistency.R123.sharedModel_noClockCoordinate"></a>

## 定理 `sharedModel_noClockCoordinate`

### 式

$$
\mathrm{SharedNoClockCoordinate}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、時計座標を持たないことを満たします。

### 証明の概略

1. 前の定理を `sharedModel_preservation` に適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_no_clock"></a>

## 定理 `final_consistency_v2_with_no_clock`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedNoClockCoordinate}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、時計座標の不在を加えた版です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
