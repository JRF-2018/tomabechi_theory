# Tomabechi/Examples/Theorem16_Identity.lean 解説

> 対象: [`Tomabechi/Examples/Theorem16_Identity.lean`](../Tomabechi/Examples/Theorem16_Identity.lean)（定理16の Python 例の反例部（恒等写像の固定点は一意でない））。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 一言でいうと

定理16の Python 例（`examples/theorem16_inverse_limit_fixed_point.py`）の**反例の部分**の Lean 根拠です。Python の反例は、「恒等写像 `ident` は連続な自己写像だが、固定点が一意でない（`fp_a=0` と `fp_b=1` がともに固定点）」というものです。

このファイルは、新しい定理を証明せず、`Theorem16_25_Core` の既存補題を、**別名（`alias`）**でこの例の名前空間 `Tomabechi.Examples.Theorem16` に置いているだけです。

| 別名 | 元の補題（`Tomabechi.Theorem16_25` 内） | 意味 |
| --- | --- | --- |
| `identity_fixedPoints_not_unique` | `identity_on_unitInterval_nonunique` | コンパクト凸な単位区間上の恒等写像は、固定点が複数ある（存在だけで、一意性は縮小性などの追加条件が必要） |
| `identity_not_contracting` | `identity_on_unitInterval_not_contracting` | 恒等写像は、自然な距離では縮小写像でない |

### 位置づけ

これは**原文の定理16の反例ではありません**。「縮小条件を外すと、一意性の節が成り立たない」ことの例です（定理16の存在節はそのまま成り立ち、一意性・幾何収束の節だけが縮小性という追加条件を必要とします）。


### ファイルのコメント（日本語訳）

> # 定理16の Python 例（`examples/theorem16_inverse_limit_fixed_point.py`）の反例部の Lean 根拠
>
> Python の反例は「恒等写像 `ident` は連続な自己写像だが、固定点が一意でない（`fp_a=0` と `fp_b=1` がともに固定点）」。Lean では、`Theorem16_25_Core` の既存補題が、コンパクト凸な単位区間上で、これを証明している。
> * 存在のみ（一意性は縮小性などの追加条件が必要）：`identity_on_unitInterval_nonunique`
> * 自然な距離では縮小写像でない：`identity_on_unitInterval_not_contracting`
>
> これは原文の定理16の反例ではなく、「縮小条件を外すと一意性の節が成り立たない」ことの例。

### このファイルが証明していないこと

このファイルには宣言（`theorem`/`def`）がなく、`alias` による別名だけです。元の補題の内容は `docs/Theorem16_25_Core_textbook.md` を参照してください。

## コメント修正記録

（なし）
