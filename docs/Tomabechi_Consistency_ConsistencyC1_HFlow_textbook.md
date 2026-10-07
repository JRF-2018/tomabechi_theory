# Tomabechi/Consistency/ConsistencyC1_HFlow.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_HFlow.lean`](../Tomabechi/Consistency/ConsistencyC1_HFlow.lean)（一次元モデルの H-flow（指数収縮する閉ループ流）と、定理1・20 の一次元結論）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

最も簡単な**一次元の制御モデル**を作り、定理1・定理20 の前提が成り立つことを、全実数の上で、きちんと確かめるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）のうち、「二主体合意系」の土台にあたります。

モデルは、状態 \(x\in\mathbb R\)、制御（ゲイン）\(u\in[0,3]\)、方程式 \(\dot x=-u\,(x-r)\) です。目標 \(r\) に向かって、ゲインの強さで引き寄せます。

| 内容 | 宣言の例 |
| --- | --- |
| 許容制御・累積量・明示軌道・やり直し則 | `C1GainSignal`、`c1ControlledOrbit` |
| 軌道が微分方程式を満たすこと、一意性 | `c1ControlledOrbit_ae_ode`、`c1ControlledState_unique_on_interval` |
| 有限地平の費用と、最大ゲインが最小であること（argmin） | `c1FiniteHorizonCost`、`c1_maximum_gain_attains_finite_horizon_argmin` |
| 反復ホライズン制御の選択（定数 3）と閉ループ流れの一致 | `c1SelectedHorizonControl`、`linearFlow` |
| 定理1の結論（指数収束） | `linearFlow_theorem1` |
| 定理20の結論（一次元モデル） | `linearFlow_theorem20` |

### 0.2 このファイルが証明していないこと

* ファイル冒頭のコメントのとおり、**原文の方策クラスとの厳密な同定、定理1–4・20 の全入力は別に必要**で、このファイルだけで C1 の完了を主張しません。
* 制御の集合は、可測で \([0,3]\) に入る関数に**具体化**したものです（原文は制御の関数空間を固定していません）。
* 状態は一次元です。二主体の二次元系は別のファイルで扱います。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> ここでは状態と制御を実数とし、正の率 `a` で目標 `r` に近づく流を構成する。流の式は開始時刻より前も含む全実数で定義する。したがって開始時刻での微分も通常の二側微分として扱える。有限ホライズンでは任意の許容可測ゲイン入力の ODE 解の一意性と最大ゲインの費用最小性まで示す。原文の方策クラスとの厳密な同定、定理1–4・20 の全入力は別途必要であり、C1 完了を主張しない。

---

<a id="Tomabechi.Consistency.ConsistencyC1.C1GainSignal"></a>

## 定義 `C1GainSignal`

### 式

$$
u:\mathbb R\to\mathbb R\ \text{可測},\quad 0\le u(t)\le 3\ (\forall t)
$$

### Lean のコメント（日本語訳）

> 有限ホライズンで許す制御。制御信号は可測で、全時刻で `[0,3]` に入る。

### 定義の説明

このモデルで「許される制御」の型です。時間の関数 \(u(t)\) で、可測（測れる）で、いつでも 0 以上 3 以下の値をとります。\(u\) は「ゲイン」で、状態を目標へ引き寄せる強さを表します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1AccumulatedGain"></a>

## 定義 `c1AccumulatedGain`

### 式

$$
\int_{t_0}^{t}u(s)\,ds
$$

### Lean のコメント（日本語訳）

> 制御 `u` の開始時刻 `t₀` からの累積量。

### 定義の説明

制御 \(u\) を時刻 \(t_0\) から \(t\) まで足し合わせた量（積分）です。後で状態が \(e^{-\text{累積量}}\) 倍に縮むことを表すのに使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1Gain_intervalIntegrable"></a>

## 補題 `c1Gain_intervalIntegrable`

### 式

$$
u\ \text{は任意の有限区間で可積分}
$$

### Lean のコメント（日本語訳）

> 可測かつ有界な制御は任意の有限区間で積分可能。

### 補題の説明

可測で 0〜3 に収まる関数は、有限区間で積分できます。累積量を定義するための基本の補題です。

### 証明の概略

1. 区間の長さが有限なので、その上の測度は有限測度。
2. 定数関数 3 は可積分。
3. \(\lvert u\rvert\le 3\) なので、可積分な定数で抑えられる可測関数として可積分（`Integrable.mono'`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1AccumulatedGain_add"></a>

## 補題 `c1AccumulatedGain_add`

### 式

$$
\int_{t_0}^{t}u=\int_{t_0}^{s}u+\int_{s}^{t}u
$$

### Lean のコメント（日本語訳）

> 累積ゲインは中間時刻で加法的に分割できる。

### 補題の説明

積分の区間を途中の時刻 \(s\) で二つに分けても、合計は変わりません。

### 証明の概略

1. 積分の区間加法性（`integral_add_adjacent_intervals`）を、可積分性の補題 `c1Gain_intervalIntegrable` と合わせて使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1AccumulatedGain_bounds"></a>

## 補題 `c1AccumulatedGain_bounds`

### 式

$$
t_0\le t\ \Rightarrow\ 0\le \int_{t_0}^{t}u\le 3(t-t_0)
$$

### Lean のコメント（日本語訳）

> 各時点までの累積ゲインは、0と最大制御の累積量の間にある。

### 補題の説明

\(0\le u\le 3\) を積分すると、累積量は 0 以上 \(3(t-t_0)\) 以下です。

### 証明の概略

1. 下からは \(u\ge0\)、上からは \(u\le3\) の点ごとの不等式を、積分の単調性（`integral_mono_on`）で積分する。
2. 定数の積分は `integral_const` で \((t-t_0)\cdot3\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit"></a>

## 定義 `c1ControlledOrbit`

### 式

$$
x\,\exp\Bigl(-\int_{t_0}^{t}u\Bigr)
$$

### Lean のコメント（日本語訳）

> 許容入力 `u` による明示軌道。最大ゲイン3の軌道も同じ式で得られる。

### 定義の説明

方程式 \(\dot x=-u(t)\,x\) の解を、式で書いたものです（初期値 \(x\)、開始時刻 \(t_0\)）。ゲインが大きいほど速く 0 に縮みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit_initial"></a>

## 補題 `c1ControlledOrbit_initial`

### 式

$$
\text{orbit}(t_0)=x
$$

### Lean のコメント（日本語訳）

> すべての制御信号について、積分軌道は開始状態を保つ。

### 補題の説明

開始時刻での値は初期値 \(x\) です（累積量が 0 だから）。

### 証明の概略

1. 累積量の定義を展開すると、区間の長さが 0 の積分で 0。\(\exp(0)=1\)（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit_restart"></a>

## 補題 `c1ControlledOrbit_restart`

### 式

$$
\text{orbit}_{x,t_0}(t)=\text{orbit}_{\text{orbit}_{x,t_0}(s),\,s}(t)
$$

### Lean のコメント（日本語訳）

> 積分軌道は任意の中間時刻から同じ制御信号で再始動する。

### 補題の説明

途中の時刻 \(s\) で止めて、その値から同じ制御で再び始めても、元の軌道と同じです（やり直し則）。

### 証明の概略

1. 累積量を \(s\) で分割（`c1AccumulatedGain_add`）。
2. \(\exp\) の和を積に直す（`Real.exp_add`）。
3. 式を整理する（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1MaxGain_orbit_sq_le"></a>

## 補題 `c1MaxGain_orbit_sq_le`

### 式

$$
\bigl(x\,e^{-3(t-t_0)}\bigr)^2\le \text{orbit}_u(t)^2
$$

### Lean のコメント（日本語訳）

> 最大ゲイン軌道は任意の許容可測制御より各時点で二乗状態が小さい。

### 補題の説明

ゲインを最大の 3 にすると、どんな許容制御よりも二乗の状態が小さくなります（一番速く縮む）。

### 証明の概略

1. 累積量の上界 \(\le3(t-t_0)\)（`c1AccumulatedGain_bounds`）から、指数の引数を比べる。
2. \(\exp\) の単調性と、二乗の単調性（`sq_le_sq₀`）で不等式を持ち上げ、\(x^2\) を掛ける。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit_ae_ode"></a>

## 補題 `c1ControlledOrbit_ae_ode`

### 式

$$
\dot{\text{orbit}}(t)=-u(t)\,\text{orbit}(t)\quad(\text{a.e. } t\in[t_0,t_0+T])
$$

### Lean のコメント（日本語訳）

> 任意の許容可測ゲイン信号が定める積分軌道は、有限地平上でa.e.にODEを満たす。

### 補題の説明

積分軌道は、ほとんど至る所の時刻で微分方程式 \(\dot x=-u\,x\) を満たします（\(u\) が不連続でもよい）。

### 証明の概略

1. 可積分関数の積分は、ほとんど至る所で微分できて、導関数は元の関数（`ae_hasDerivAt_integral`）。
2. \(-\)累積量、その \(\exp\)、\(x\) 倍と合成して微分する（連鎖律）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledOrbit_absolutelyContinuousOnInterval"></a>

## 補題 `c1ControlledOrbit_absolutelyContinuousOnInterval`

### 式

$$
\text{orbit}\ \text{は }[t_0,t_1]\text{ で絶対連続}
$$

### Lean のコメント（日本語訳）

> 許容可測入力の積分軌道は任意の有限前向き区間で絶対連続である。

### 補題の説明

積分軌道は絶対連続（折れ曲がりを許すが、導関数の積分で元に戻る程度の滑らかさ）です。微分方程式の解の一意性の議論に必要です。

### 証明の概略

1. 累積量は積分なので絶対連続。その符号反転も絶対連続。
2. \(\exp\) は \((-\infty,0]\) 上で 1-リプシッツ（導関数が 1 以下）。累積量の符号反転は 0 以下なので、この範囲に入る。
3. リプシッツ関数との合成は絶対連続（`comp_absolutelyContinuousOnInterval`）。\(x\) 倍も絶対連続。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState"></a>

## 定義 `c1ControlledState`

### 式

$$
r+\text{orbit}(x-r,\,t_0,\,u,\,t)
$$

### Lean のコメント（日本語訳）

> 目標 `r` のまわりに置いた任意制御の状態軌道。

### 定義の説明

目標 \(r\) を中心に動かした軌道です。偏差 \(x-r\) が \(e^{-\text{累積量}}\) 倍に縮みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_initial"></a>

## 補題 `c1ControlledState_initial`

### 式

$$
\text{state}(t_0)=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻での値は初期値です。

### 証明の概略

1. `c1ControlledOrbit_initial` と \(r+(x-r)=x\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_restart"></a>

## 補題 `c1ControlledState_restart`

### 式

$$
\text{state}_{x,t_0}(t)=\text{state}_{\text{state}_{x,t_0}(s),s}(t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心化した軌道でも、途中からのやり直し則が成り立ちます。

### 証明の概略

1. 中心化した偏差 \(\text{state}-r\) を取り出す（`hcenter`）。
2. `c1ControlledOrbit_restart` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_ae_ode"></a>

## 補題 `c1ControlledState_ae_ode`

### 式

$$
\dot{\text{state}}(t)=-u(t)\bigl(\text{state}(t)-r\bigr)\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 中心化した積分状態軌道は、元の制御ベクトル場を有限区間a.e.満たす。

### 補題の説明

中心化した軌道は、ほとんど至る所で \(\dot x=-u\,(x-r)\) を満たします。

### 証明の概略

1. `c1ControlledOrbit_ae_ode` に \(x-r\) を渡し、定数 \(r\) を足して微分する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_absolutelyContinuousOnInterval"></a>

## 補題 `c1ControlledState_absolutelyContinuousOnInterval`

### 式

$$
\text{state}\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心化した軌道も有限区間で絶対連続です。

### 証明の概略

1. 定数関数は滑らか（C¹）なので絶対連続。
2. 偏差の軌道の絶対連続性（前の補題）と足し合わせる（`.add`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_unique_on_interval"></a>

## 補題 `c1ControlledState_unique_on_interval`

### 式

$$
y\ \text{が AC・初期値 }x\text{・ODE を a.e. 満たす}\Rightarrow y(t_1)=\text{state}(t_1)
$$

### Lean のコメント（日本語訳）

> 任意のCarathéodory解は積分表示の候補軌道と一致する。差の二乗のa.e.導関数が非正で、初期値が0であることから一意性を得る。

### 補題の説明

微分方程式 \(\dot y=-u(y-r)\)、初期値 \(x\) の絶対連続な解は、構成した積分軌道と一致します（解の一意性）。

### 証明の概略

1. \(t_0=t_1\) なら初期値の等式。
2. \(t_0<t_1\) のとき、差 \(\delta=y-\text{候補}\) と \(q=\delta^2\) を置く。\(q\) は絶対連続。
3. a.e. で \(\dot\delta=-u\delta\)、よって \(\dot q=-2u\delta^2\le0\)（\(u\ge0\)）。
4. 微積分の基本定理で \(q(t_1)\le q(t_0)=0\)。\(q\ge0\) なので \(q(t_1)=0\)、よって \(\delta(t_1)=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ControlledState_unique_on_interval_all"></a>

## 補題 `c1ControlledState_unique_on_interval_all`

### 式

$$
\forall t\in[t_0,t_1],\ y(t)=\text{state}(t)
$$

### Lean のコメント（日本語訳）

> 区間内の各時刻で同じ解が一致する。終点一意性をその時刻までの部分区間へ適用する。

### 補題の説明

前の補題は終点だけでしたが、区間の**すべての時刻**で一致します。

### 証明の概略

1. 各時刻 \(s\) について、\([t_0,s]\) に制限した絶対連続性・ODE（a.e.）を作る。
2. 前の補題を \(t_1\) を \(s\) に替えて適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1FiniteHorizonCost"></a>

## 定義 `c1FiniteHorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}\bigl(1+\text{orbit}(t)^2\bigr)\,dt\in[0,\infty]
$$

### Lean のコメント（日本語訳）

> 正の基準値を加えた二次走行費用を有限時間区間上で積分した拡張実数値。

### 定義の説明

有限の時間幅 \(T\) のあいだの「費用」です。基準値 1 に、状態の二乗を足して時間で積分します。値は拡張実数（無限大も許す）で表します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1TrajectoryFiniteHorizonCost"></a>

## 定義 `c1TrajectoryFiniteHorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}\bigl(1+(y(t)-r)^2\bigr)\,dt
$$

### Lean のコメント（日本語訳）

> 同じ有限ホライズン上での、任意の状態軌道の費用。

### 定義の説明

任意の状態軌道 \(y\) について、同じ形の費用を定義したものです（中心を \(r\) にしてある）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1MaxGainSignal"></a>

## 定義 `c1MaxGainSignal`

### 式

$$
u(t)\equiv3
$$

### Lean のコメント（日本語訳）

> 有限ホライズンで選ぶ最大ゲイン信号。

### 定義の説明

ゲインを常に最大の 3 にした制御です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1ZeroGainSignal"></a>

## 定義 `c1ZeroGainSignal`

### 式

$$
u(t)\equiv0
$$

### Lean のコメント（日本語訳）

> 最大ゲインとは異なる許容信号。

### 定義の説明

ゲインを常に 0 にした制御です（許容制御ですが、何も動かしません）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_two_distinct_admissible_gains"></a>

## 補題 `c1_two_distinct_admissible_gains`

### 式

$$
u_0\ne u_{\max}
$$

### Lean のコメント（日本語訳）

> この最適化問題には少なくとも二つの異なる許容制御がある。

### 補題の説明

許容制御が一つしかないと、「最適な選択」が自明になってしまいます。そうでないことを示します。

### 証明の概略

1. 等しいと仮定すると、時刻 0 の値が \(0=3\) で矛盾（`norm_num`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1MaxGain_accumulation"></a>

## 補題 `c1MaxGain_accumulation`

### 式

$$
\int_{t_0}^{t}3\,ds=3(t-t_0)
$$

### Lean のコメント（日本語訳）

> 最大ゲイン信号の累積量は `3(t-t₀)` である。

### 補題の説明

（コメントなし）

### 証明の概略

1. 定数の積分（`integral_const`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1OptimalFeedback"></a>

## 定義 `c1OptimalFeedback`

### 式

$$
\pi(x,t)\equiv3
$$

### Lean のコメント（日本語訳）

> 選択する状態時刻feedbackは最大ゲインで、連続かつ右連続である。

### 定義の説明

最適として選ぶ状態フィードバックは、状態にも時刻にもよらず 3 という定数です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1OptimalFeedback_continuous"></a>

## 補題 `c1OptimalFeedback_continuous`

### 式

$$
(x,t)\mapsto\pi(x,t)\ \text{は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定数関数なので連続です。

### 証明の概略

1. `continuous_const`。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1OptimalFeedback_rightContinuous"></a>

## 補題 `c1OptimalFeedback_rightContinuous`

### 式

$$
t\mapsto\pi(x,t)\ \text{は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各状態で、時刻の関数として連続（したがって右連続）です。

### 証明の概略

1. `continuous_const`。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1OptimalFeedback_rightLimit"></a>

## 補題 `c1OptimalFeedback_rightLimit`

### 式

$$
\lim_{t\downarrow t_0}\pi(x,t)=3
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻の右側からの極限が 3 です。

### 証明の概略

1. 定数の極限（`tendsto_const_nhds`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1SelectedHorizonControl"></a>

## 定義 `c1SelectedHorizonControl`

### 式

$$
u_{(t_0,x)}(s)\equiv3
$$

### Lean のコメント（日本語訳）

> 各開始状態と開始時刻に対して選ぶ有限ホライズン制御列。このモデルでは、どの組に対しても最大ゲイン3の定数列を選ぶ。

### 定義の説明

反復ホライズン制御で「その時刻・その状態から解く最適制御」を選ぶ規則です。このモデルでは、どの組でも定数 3 を選びます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1SelectedHorizonControl_measurable"></a>

## 補題 `c1SelectedHorizonControl_measurable`

### 式

$$
(t_0,x)\mapsto u_{(t_0,x)}\ \text{は Borel 可測}
$$

### Lean のコメント（日本語訳）

> 最適制御列の選択は、開始時刻と初期状態についてBorel可測である。

### 補題の説明

選択の規則が可測であること（原文の反復ホライズンの条件の一つ）です。

### 証明の概略

1. 定数関数は可測（`measurable_const`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1SelectedHorizonControl_is_admissible"></a>

## 補題 `c1SelectedHorizonControl_is_admissible`

### 式

$$
u_{(t_0,x)}=u_{\max}
$$

### Lean のコメント（日本語訳）

> 選ばれた制御列は、すべての実数時刻で許容最大ゲイン信号である。

### 補題の説明

選ばれた制御は、許容制御の型の元として、最大ゲイン信号と一致します。

### 証明の概略

1. 値が 0 以上 3 以下であることを確認して、部分型の等式を値の等式に落とす（`Subtype.ext`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1SelectedHorizonControl_rightLimit"></a>

## 補題 `c1SelectedHorizonControl_rightLimit`

### 式

$$
\lim_{s\downarrow t_0}u_{(t_0,x)}(s)=\pi(x,t_0)
$$

### Lean のコメント（日本語訳）

> 選択した最適制御列の右連続代表の開始点右極限は、閉ループfeedbackと一致する。

### 補題の説明

反復ホライズン制御は「各時刻で最適制御を解き、その最初の値だけ使う」方式です。最初の値＝開始点の右極限が、閉ループのフィードバックに一致することを述べます。

### 証明の概略

1. 両辺とも定数 3 なので、定数の極限（`tendsto_const_nhds`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_maximum_gain_attains_finite_horizon_argmin"></a>

## 補題 `c1_maximum_gain_attains_finite_horizon_argmin`

### 式

$$
J(u_{\max})\le J(u)\quad(\forall u\ \text{許容})
$$

### Lean のコメント（日本語訳）

> 正の有限ホライズンで最大ゲインが全可測ゲイン制御の費用を最小化する。可測性・有界性から定義された費用は存在し、点ごとの軌道比較からargminが従う。

### 補題の説明

有限地平で、最大ゲイン 3 が、すべての許容制御の中で費用を**最小**にします（argmin の達成）。

### 証明の概略

1. 各時刻 \(t\) で、最大ゲインの二乗状態は他の制御以下（`c1MaxGain_orbit_sq_le`）。
2. \(1\) を足しても大小は変わらないので、被積分関数の点ごとの不等式（`ofReal_le_ofReal`）。
3. 積分の単調性（`lintegral_mono_ae`）で費用の不等式を得る。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_maximum_gain_finite_cost"></a>

## 補題 `c1_maximum_gain_finite_cost`

### 式

$$
J(u_{\max})<\infty
$$

### Lean のコメント（日本語訳）

> 選択した最大ゲインの有限ホライズン費用は有限である。

### 補題の説明

最大ゲインの費用は無限大ではありません。

### 証明の概略

1. 最大ゲインの軌道の被積分関数は連続な関数 \(f\)。コンパクト区間で可積分。
2. 非負なので、下積分は実数の積分の `ofReal` に一致（`ofReal_integral_eq_lintegral_ofReal`）。
3. `ofReal` は \(\infty\) ではない（`ofReal_lt_top`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1TrajectoryFiniteHorizonCost_eq_controlCost"></a>

## 補題 `c1TrajectoryFiniteHorizonCost_eq_controlCost`

### 式

$$
\text{(ODE の解 }y\text{ の費用)}=J(x-r;\,u)
$$

### Lean のコメント（日本語訳）

> 絶対連続でODEを満たす軌道は積分表示の軌道と一致し、その費用も等しい。

### 補題の説明

ODE の解 \(y\) は積分軌道と一致するので、費用も制御による費用に等しい。

### 証明の概略

1. `c1ControlledState_unique_on_interval_all` で、区間のすべての時刻で \(y\) が積分軌道に一致。
2. 被積分関数が a.e. 一致するので、積分も一致（`lintegral_congr_ae`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_maximum_gain_minimizes_all_ode_trajectories"></a>

## 補題 `c1_maximum_gain_minimizes_all_ode_trajectories`

### 式

$$
J(\text{最大ゲインの軌道})\le J(y)\quad(\forall y:\text{ ODE の解})
$$

### Lean のコメント（日本語訳）

> 有界可測ゲインで動く任意のCarathéodory軌道に対し、最大ゲインfeedbackの費用が最小である。

### 補題の説明

どんな有界可測ゲインが生む軌道 \(y\) と比べても、最大ゲインの軌道の費用が最小です。

### 証明の概略

1. 両側の費用を、前の補題で「制御による費用」に書き換える。
2. `c1_maximum_gain_attains_finite_horizon_argmin` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_selected_trajectory_finite_cost"></a>

## 補題 `c1_selected_trajectory_finite_cost`

### 式

$$
J(\text{選択した軌道})<\infty
$$

### Lean のコメント（日本語訳）

> 選択feedbackで実現するCarathéodory軌道は、各正の有限ホライズンで有限費用を持つ。

### 補題の説明

選んだ軌道の費用は有限です。

### 証明の概略

1. 費用を制御による費用に書き換え（`..._eq_controlCost`）、`c1_maximum_gain_finite_cost` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow"></a>

## 定義 `linearFlow`

### 式

$$
\dot x=-u(x-r),\quad \pi\equiv a,\quad \Phi_{t_0\to t}(x)=r+(x-r)e^{-a(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 制御値は実数で、正の率モデルでは許容制御を `[0,a]` にする。選択feedbackは最大ゲイン `a`。指数式はそのfeedbackの閉ループ解である。

### 定義の説明

定理1の「閉ループ方策の流れ」（`ClosedLoopPolicyFlow`）のデータとして、この一次元モデルを与えたものです。許容制御は \([0,a]\)（\(a\le0\) のときは何でも許容）、選択するフィードバックは \(a\)、ベクトル場は \(-u(x-r)\)、流れは指数で \(r\) に近づく式です。

### 証明の概略

1. 許容性：\(a\le0\) なら左側、そうでなければ \(0\le a\le a\)。
2. 初期値：\(t=t_0\) で指数が 1。
3. やり直し則：\(t-t_0=(s-t_0)+(t-s)\) と指数の加法性（`exp_add`）で式を整理。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1OptimalFeedback_is_hflow_feedback"></a>

## 補題 `c1OptimalFeedback_is_hflow_feedback`

### 式

$$
\text{linearFlow}(3,r).\text{feedback}=\pi
$$

### Lean のコメント（日本語訳）

> 反復ホライズン最適選択と閉ループ flow で使う feedback は同じ定数ゲイン。

### 補題の説明

反復ホライズン最適選択と閉ループ流で使うフィードバックは、同じ定数ゲイン 3 です。

### 証明の概略

1. 両辺とも定数関数 3（`rfl`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1MaxGain_orbit_eq_hflow"></a>

## 補題 `c1MaxGain_orbit_eq_hflow`

### 式

$$
\text{orbit}(x-r)=\Phi_{t_0\to t}(x)-r
$$

### Lean のコメント（日本語訳）

> 最大ゲインの積分軌道は、構成したH-flowの軌道そのもの（目標からの偏差）である。

### 補題の説明

積分で作った軌道と、H-flow の流れが同じものであることを確認します。

### 証明の概略

1. 最大ゲインの累積量を `integral_const` で \(3(t-t_0)\) にして、両辺を式として比べる。

----

<a id="Tomabechi.Consistency.ConsistencyC1.differentiableLinearFlow"></a>

## 定義 `differentiableLinearFlow`

### 式

$$
\frac{d}{dt}\Phi_{t_0\to t}(x)=-a\,(\Phi-r)
$$

### Lean のコメント（日本語訳）

> 同じ線形流は全実数の開始時刻・状態に対して通常微分可能で、その導関数はfeedbackが指定するベクトル場に一致する。

### 定義の説明

`linearFlow` に「全時刻で通常の意味で微分でき、導関数がベクトル場に一致する」という性質を加えた流れです（定理20のモデルに使う）。開始時刻より前の時刻も含めた全実数で定義されているので、開始時刻でも両側微分が取れます。

### 証明の概略

1. 指数の引数 \(-a(s-t_0)\) の微分は \(-a\)。
2. \(\exp\) との合成、定数倍、定数加算の微分を合わせる。
3. `linearFlow` のベクトル場の式と一致することを `ring` で確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_vectorField_lipschitz"></a>

## 補題 `linearFlow_vectorField_lipschitz`

### 式

$$
x\mapsto -a(x-r)\ \text{は }|a|\text{-リプシッツ}
$$

### Lean のコメント（日本語訳）

> 閉ループのベクトル場は状態について大域的にリプシッツで、定数は `|a|`（時刻によらず一様）。

### 補題の説明

閉ループのベクトル場は、状態について大域的にリプシッツ連続で、定数は \(\lvert a\rvert\)（時刻によらない）です。

### 証明の概略

1. 差が \(-a(x-y)\) になることを `ring` で示し、絶対値の積で評価する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.c1_controlled_vectorField_lipschitz"></a>

## 補題 `c1_controlled_vectorField_lipschitz`

### 式

$$
x\mapsto -u(t)(x-r)\ \text{は 3-リプシッツ}
$$

### Lean のコメント（日本語訳）

> 任意の許容可測ゲイン信号に対し、制御ベクトル場は状態について一様な定数3で大域Lipschitzとなる。

### 補題の説明

どんな許容制御でも、ベクトル場のリプシッツ定数は \(\lvert u(t)\rvert\le3\) で抑えられます。解の存在・一意性（ODE 理論）に使う性質です。

### 証明の概略

1. リプシッツ定数 \(\lVert u(t)\rVert\) を示す。
2. \(0\le u(t)\le3\) から \(\lVert u(t)\rVert\le3\)。リプシッツ定数を 3 に弱める（`weaken`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_feedback_measurable"></a>

## 補題 `linearFlow_feedback_measurable`

### 式

$$
(x,t)\mapsto\pi\ \text{は Borel 可測}
$$

### Lean のコメント（日本語訳）

> 選択したfeedbackは定数であり、状態と時刻についてBorel可測である。

### 補題の説明

定数関数なので可測です。

### 証明の概略

1. `measurable_const`。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_has_multiple_controls"></a>

## 補題 `linearFlow_has_multiple_controls`

### 式

$$
0,\ a\ \text{はともに許容、かつ }0\ne a\ (a>0)
$$

### Lean のコメント（日本語訳）

> 正の率のどの場合にも、少なくとも二つの異なる許容制御があるので、制御の集合は一点集合ではない。

### 補題の説明

正の率 \(a>0\) のとき、許容制御は 0 と \(a\) の少なくとも二つあり、制御の集合が一点でないことを示します。

### 証明の概略

1. 許容性は、定義 `linearFlow` を展開して \(0\le0\le a\)、\(0\le a\le a\) を確認。
2. \(0\ne a\) は \(a>0\) から。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_feedback_continuous"></a>

## 補題 `linearFlow_feedback_continuous`

### 式

$$
t\mapsto\pi(x,t)\ \text{は連続}
$$

### Lean のコメント（日本語訳）

> 選んだフィードバックは、どの状態・どの開始時刻でも、連続な（したがって右連続な）時間の代表を持つ。

### 補題の説明

選んだフィードバックは、時刻の関数として連続なので、右連続の代表が取れます。

### 証明の概略

1. 定数関数（`continuous_const`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.maximum_gain_minimizes_quadratic_derivative"></a>

## 補題 `maximum_gain_minimizes_quadratic_derivative`

### 式

$$
-2a(x-r)^2\le -2u(x-r)^2\quad(u\in[0,a])
$$

### Lean のコメント（日本語訳）

> `[0,a]` の全許容制御のうち、選んだ最大ゲインが、二次距離残差の瞬間の微分を最も小さくする。

### 補題の説明

許容制御の中で、最大ゲイン \(a\) が、二次距離残差の**瞬間の微分を最も小さく**（最も速く減るように）します。

### 証明の概略

1. \(a\le 0\) の場合は線形不等式。
2. \(0\le u\le a\) の場合は \((a-u)(x-r)^2\ge0\) の事実から（`nlinarith`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_error"></a>

## 補題 `linearFlow_error`

### 式

$$
\Phi_{t_0\to t}(x)-r=(x-r)\,e^{-a(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 任意の時刻で目標からの誤差は初期誤差に指数因子を掛けたもの。

### 補題の説明

誤差は初期誤差に指数因子を掛けたものです。

### 証明の概略

1. `linearFlow` の定義を展開する（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_distance_nonincreasing"></a>

## 補題 `linearFlow_distance_nonincreasing`

### 式

$$
a\ge0,\ t_0\le t\Rightarrow |\Phi(t)-r|\le|x-r|
$$

### Lean のコメント（日本語訳）

> 正の率なら、開始後の流は目標との距離を拡大しない。

### 補題の説明

\(a\ge0\) なら、時間が進むほど目標への距離は増えません。

### 証明の概略

1. 誤差の式（`linearFlow_error`）の絶対値を取る。
2. \(e^{-a(t-t_0)}\le1\)（`exp_le_one_iff`）なので、積は \(\lvert x-r\rvert\) 以下。

----

<a id="Tomabechi.Consistency.ConsistencyC1.positiveResidualPath"></a>

## 定義 `positiveResidualPath`

### 式

$$
\bigl((x-r)\,e^{-a(s-t_0)}\bigr)^2
$$

### Lean のコメント（日本語訳）

> 同じ流れに沿った Lyapunov 残差（閾値は真に正）。

### 定義の説明

流れに沿った Lyapunov 残差（誤差の二乗）です。閾値が正の場合を扱います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.positiveResidualPath_pos"></a>

## 補題 `positiveResidualPath_pos`

### 式

$$
x\ne r\Rightarrow \text{residual}(s)>0
$$

### Lean のコメント（日本語訳）

> 目標でない初期状態は、有限のどの時刻でも、真に正の残差を持つ。

### 補題の説明

目標でない点から出発すれば、有限時刻では残差は正です（動いていて、まだ目標に着いていない）。

### 証明の概略

1. 二乗が正になるには、中身が 0 でなければよい（`sq_pos_of_ne_zero`）。
2. 積が 0 でないのは、\(x-r\ne0\) と \(\exp\ne0\) から（`mul_ne_zero`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_closedReachable_univ"></a>

## 補題 `linearFlow_closedReachable_univ`

### 式

$$
\overline{\mathrm{Reach}}=\mathbb R
$$

### Lean のコメント（日本語訳）

> このモデルの閉到達集合は `ℝ` 全体である。どの実数点も、非負の絶対開始時刻 `t₀` で既に到達可能である。

### 補題の説明

初期集合を全体 \(\mathbb R\) にすると、閉到達集合は \(\mathbb R\) 全体になります（すべての点が開始時刻 \(t_0\) で既に到達可能）。

### 証明の概略

1. 任意の点 \(y\) について、流れの初期条件（\(t=t_0\) で \(y\) に一致）から、到達可能集合の元であることを示す。
2. 到達可能集合の元は閉包の元（`mem_closedLoopReachableSet_of_mem_reachableAt`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_global_error_bound"></a>

## 補題 `linearFlow_global_error_bound`

### 式

$$
\operatorname{dist}(z,\mathrm{TCZ})^2\le \Phi(z)\quad(C=1)
$$

### Lean のコメント（日本語訳）

> 閉到達集合の全体・全時刻で、正の閾値の TCZ までの距離の二乗は、二次残差にちょうど等しい（`C=1`）。

### 補題の説明

閉到達集合の全体で、正の閾値の TCZ（目標 \(\{r\}\) だけの集合）までの距離の二乗は、二次残差に等しい（定数 \(C=1\)）。誤差境界の全域版です。

### 証明の概略

1. 閉到達集合が全体（前の補題）なので、TCZ は \(\{y\mid 1+(y-r)^2\le1\}=\{r\}\)。
2. 一点集合への距離は \(\lvert z-r\rvert\)（`infDist_singleton`）。二乗は \((z-r)^2\)。
3. 残差の定義 `residual1` を展開して一致を確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1.positiveResidualPath_hasDerivAt"></a>

## 補題 `positiveResidualPath_hasDerivAt`

### 式

$$
\frac{d}{ds}\text{residual}=-2a\,\text{residual}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

残差の微分は \(-2a\) 倍の残差です（下降条件）。補助の補題です。

### 証明の概略

1. 指数の引数の微分は \(-a\)。
2. \(\exp\) と合成、定数倍、二乗（`pow 2`）の微分を合わせ、式を整理（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.positiveResidualPath_ac"></a>

## 補題 `positiveResidualPath_ac`

### 式

$$
\text{residual}\ \text{は }[t_0,T]\text{ で絶対連続}
$$

### Lean のコメント（日本語訳）

> 軌道の残差は、有界などの区間でも絶対連続である。

### 補題の説明

残差は有界な区間で絶対連続です。補助の補題です。

### 証明の概略

1. 残差は C¹ 級（`fun_prop`）。C¹ 関数は絶対連続（`absolutelyContinuousOnInterval`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_theorem1"></a>

## 定理 `linearFlow_theorem1`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{TCZ}^{\mathrm{cl}}\bigr)\le|x-r|\,e^{-a(t-t_0)}\ \to 0
$$

### Lean のコメント（日本語訳）

> このスカラーのアフィン系全体についての、定理1の到達可能 TCZ 評価。到達可能閉包は `initialSet = univ` の選択された流れから得る。TCZ は、正の二次閾値の部分準位集合から導き、その唯一の点は目標 `r` である。

### 補題の説明

定理1（目標への収束）が、この一次元モデルで成り立つことを、三つの結論として示します。(1) 流れは閉到達集合に留まる。(2) 閉到達 TCZ までの距離は \(\lvert x-r\rvert e^{-a(t-t_0)}\) 以下（指数的）。(3) 距離は 0 に収束する。TCZ は、正の二次閾値の部分準位集合（点 \(r\) だけ）です。

### 証明の概略

1. 閉到達集合が全体（`hK`）。TCZ が空でないこと（\(r\) が入る）。
2. 残差が絶対連続（`positiveResidualPath_ac`）、下降 \(\dot\Phi\le-2a\Phi\)（`positiveResidualPath_hasDerivAt`）、誤差境界 \(C=1\)。
3. 定理1の一般形（`theorem1_policy_flow_reachable_tcz_distance_tendsto_zero`）に、これらを前件として渡す。
4. 指数の速さは、一般形の結論の不等式を、初期残差 \((x-r)^2\) で書き換えて、平方根を取って得る。

----

<a id="Tomabechi.Consistency.ConsistencyC1.quadraticDistance_error_bound"></a>

## 補題 `quadraticDistance_error_bound`

### 式

$$
\operatorname{dist}(z,\{r\})\le2\sqrt{\tfrac12(z-r)^2}
$$

### Lean のコメント（日本語訳）

> 二次距離残差に対する定理20用の全時刻誤差評価。

### 補題の説明

定理20で使う誤差の評価です。一点集合への距離は \(\lvert z-r\rvert\)、一方 \(2\sqrt{(z-r)^2/2}=\sqrt2\,\lvert z-r\rvert\) なので、確かに前者が後者以下です。

### 証明の概略

1. \((\lvert z-r\rvert/2)^2\le\tfrac12(z-r)^2\)。
2. 平方根の性質（`le_sqrt_of_sq_le`）で絶対値の評価へ。`nlinarith` で整理。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_intervalReachable_eq"></a>

## 補題 `linearFlow_intervalReachable_eq`

### 式

$$
\overline{\mathrm{Reach}}(\bar B(r,1))=\bar B(r,1)\quad(a=3)
$$

### Lean のコメント（日本語訳）

> 初期条件が閉単位区間のとき、流れが生む閉到達集合は、ちょうどその同じコンパクト区間である。

### 補題の説明

初期集合を閉区間 \([r-1,r+1]\) にすると、流れで到達する点の閉包は、その同じ閉区間です（ゲイン 3）。コンパクトな不変集合の例になります。

### 証明の概略

1. （⊆）到達する点は \(r+(x_0-r)e^{-3(t-t_0)}\)。\(\lvert x_0-r\rvert\le1\)、指数因子は 0〜1 なので、距離は 1 以下。閉球は閉集合なので閉包に含まれる。
2. （⊇）閉球の点は、時刻 \(t_0\) でそのまま到達（流れの初期条件）。

----

<a id="Tomabechi.Consistency.ConsistencyC1.linearFlow_theorem20"></a>

## 定義 `linearFlow_theorem20`

### 式

$$
\text{定理20の結論（一次元モデル）}
$$

### Lean のコメント（日本語訳）

> 非定数のスカラーモデル `D(x)=‖x-r‖²/2`、`P=1`、`s(D)=-D`、単位移動度についての定理20の結論。コンパクトな不変初期区間が、流れが生むちょうどの閉到達集合を与える。

### 定義の説明

定理20（象徴臨場感の方向性）の結論を、一次元モデルで得ます。評価 \(V_0=\tfrac12\lVert y-r\rVert^2\)、臨場感 \(P\equiv1\)、\(s(D)=-D\)、移動度は恒等写像。コンパクトな不変区間（`linearFlow_intervalReachable_eq`）から、閉到達集合が正確に分かります。結論は定理20の一般の「原文条件の入口」（`theorem20_policy_flow_original_condition_conclusion`）の結論です。

### 証明の概略

1. モデルのデータ（微分可能な流れ、\(V_0\)、\(P\)、\(D\)、\(s\)、集合 \(Z=\{r\}\)）を置く。
2. 閉到達集合が閉区間（コンパクト）で、流れで前向き不変であることを示す。
3. \(V_0,P,D\) の勾配、\(D\) の非負性・零点集合 \(=\{r\}\)、\(s\) の微分を確認する。
4. ベクトル場が有効ポテンシャルの勾配の \(-\)（\(\mathrm{id}\) 倍）に一致することを、`effective_potential_hasGradientAt` で示す。有効勾配は \(3(y-r)\)。
5. 定理20の入口に、これらの前件と数値の条件を渡す。

----


## コメント修正記録

`.lean` のコメントの修正はありません。（英語の docstring は、この解説書では日本語訳を載せました。）
