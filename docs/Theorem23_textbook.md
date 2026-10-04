# Theorem23.lean 解説

> 対象: [`Theorem23.lean`](../Theorem23.lean)（定理23の互換入口）。このファイルには宣言がなく、他のファイルを読み込むだけです。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（TCZ・段階切替・非再帰）の import 名を維持する**互換入口**です。実体は `Tomabechi/Dynamics/StageSwitching.lean`（解説書：[Tomabechi_Dynamics_StageSwitching_textbook.md](Tomabechi_Dynamics_StageSwitching_textbook.md)）にあります。エントロピー収支は `Tomabechi/Analysis/EntropyBalance.lean`（[解説](Tomabechi_Analysis_EntropyBalance_textbook.md)）です。

### ファイルのコメント（日本語訳）

> **互換入口**
>
> 定理23の TCZ・段階切替・非再帰の実体は `Tomabechi.Dynamics.StageSwitching` に配置した。従来の import 名を維持する。

（もとのコメントが日本語なのでそのまま写しています。）

### このファイルが証明していないこと

何も証明していません。内容は上で示したファイルにあります。

## コメント修正記録

（なし）
