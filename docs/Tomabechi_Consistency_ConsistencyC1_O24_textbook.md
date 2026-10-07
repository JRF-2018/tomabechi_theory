# Tomabechi/Consistency/ConsistencyC1_O24.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_O24.lean`](../Tomabechi/Consistency/ConsistencyC1_O24.lean)（Self・Ego・TCZ を別々の型で持つ三つ組（原文 §2.4）のモデル）。
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
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文 §2.4 は、**Self（自己）・Ego（自我）・TCZ（目標領域）を、別々の型のものとして区別して**扱います。

* **Self**：「可能な世界の集合」を受け取り、評価が閾値以下の世界に絞る**作用素**（意味論的）。
* **Ego**：状態と時刻から制御値を返す**方策**。
* **TCZ**：状態空間の**部分集合**。

三者を同じ数に潰してしまうと、区別が失われます。このファイルは、三者を別の型のまま保存する「三つ組」の構造体を作り、一次元モデル・二主体の合意モデル・最適化した合意モデルで、三つ組を実際に構成します。さらに、「Self が選ぶ TCZ」が定理2の共有 TCZ に一致することを示します。無矛盾性の追加条件 H-flow（軌道・到達集合・TCZ が同じ流れから来る）の土台です。

（ファイル名の `O24` は、原文 §2.4 の条件に対応する作業上の呼び名です。）

### 0.2 このファイルが証明していないこと

* 三つ組は、このモデルでの**具体的な構成**です。原文の一般の Self・Ego・TCZ の定義との同一視ではありません。
* 状態空間は一次元または二主体（箱の中）です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> Mini13 §2.4に合わせ、Selfは可能世界集合を選別する意味論的作用素、Egoは状態と時刻から制御値を返す方策、TCZは状態空間の部分集合として定義する。三者を同じスカラー値に潰さず、`linearFlow 3 0` の到達集合・feedback・目標集合をそれぞれ保存するadapterを構成する。（「Mini13」は、ミニマル13定理版のこと。）

---

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24V0"></a>

## 定義 `c1O24V0`

### 式

$$
V_0(x,t)=1+x^2
$$

### Lean のコメント（日本語訳）

> このモデルの基礎評価。

### 定義の説明

一次元モデルの基礎評価関数です。\(1+x^2\) で、原点で最小値 1 をとります。閾値 \(\theta=1\) とすると、「評価が 1 以下」は \(x=0\) だけです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24Self"></a>

## 定義 `c1O24Self`

### 式

$$
\mathrm{Self}_t(W)=\{x\in W\mid V_0(x,t)\le1\}
$$

### Lean のコメント（日本語訳）

> Selfは可能世界集合を、基礎評価が閾値以下の世界へ絞る意味論的作用素。

### 定義の説明

原文 §2.4 の **Self**（自己）は、「可能な世界の集合」を受け取り、「評価が閾値以下の世界」に絞り込む**作用素**（集合から集合への写像）として定義されます。これは状態でも制御でもなく、型が違います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24Ego"></a>

## 定義 `c1O24Ego`

### 式

$$
\mathrm{Ego}(t,x)=\pi(x,t)
$$

### Lean のコメント（日本語訳）

> Egoは閉ループflowが選択する制御方策。型は `(time, state) → control`。

### 定義の説明

**Ego**（自我）は、状態と時刻から制御値を返す**方策**です。型は「（時刻、状態）→ 制御」。ここでは、閉ループの流れが選ぶフィードバックそのものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24Reachable"></a>

## 定義 `c1O24Reachable`

### 式

$$
\overline{\mathrm{Reach}}
$$

### Lean のコメント（日本語訳）

> flowが生成する閉到達集合。

### 定義の説明

流れが生み出す、閉到達可能な状態の集合です（初期集合を全体にしたもの）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24TCZ"></a>

## 定義 `c1O24TCZ`

### 式

$$
\mathrm{TCZ}(t_0,t)=\mathrm{Self}_t(\overline{\mathrm{Reach}}_{t_0})
$$

### Lean のコメント（日本語訳）

> Selfが閉到達可能世界から選ぶ安定集合を、時刻ごとのTCZとして保持する。

### 定義の説明

**TCZ** は、状態空間の部分集合です。Self が、閉到達可能な世界から選んだ安定な集合として定義します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.C1SelfEgoTCZ"></a>

## 構造体 `C1SelfEgoTCZ`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ})\ \text{の三つ組と、その関係}
$$

### Lean のコメント（日本語訳）

> Self、Ego、TCZを異なる型の三つ組としてまとめる。保存関係は値のフィールドで証明する。

### 定義の説明

Self・Ego・TCZ を**別々の型のまま**、一つにまとめた構造体です（三者を同じスカラー値に潰しません）。フィールドは、`Self`（集合→集合の作用素）、`Ego`（方策）、`TCZ`（時刻ごとの集合）、`reachable`（到達集合）、`flow`（閉ループ流れ）と、関係の証拠（Self が到達集合から TCZ を返す、Ego は流れのフィードバック、TCZ は Self の像）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.linearFlowSelfEgoTCZ"></a>

## 定義 `linearFlowSelfEgoTCZ`

### 式

$$
\text{一次元 H-flow から作った三つ組}
$$

### Lean のコメント（日本語訳）

> 実数H-flowから作る型付き表現三つ組。

### 定義の説明

一次元の流れ `linearFlow 3 0`（目標 \(r=0\)、ゲイン 3）から、上の構造体の値を作ります。各関係は定義から自明です（`rfl`）。

### 証明の概略

1. 各フィールドに、対応する定義を入れる。関係の証拠は定義の展開で成り立つ（`rfl`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24Reachable_eq_univ"></a>

## 補題 `c1O24Reachable_eq_univ`

### 式

$$
\overline{\mathrm{Reach}}=\mathbb R
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉到達集合は、\(\mathbb R\) 全体です（\(t_0\ge0\) のとき）。

### 証明の概略

1. 一次元モデルの `linearFlow_closedReachable_univ` をそのまま使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24TCZ_eq_singleton"></a>

## 補題 `c1O24TCZ_eq_singleton`

### 式

$$
\mathrm{TCZ}=\{0\}
$$

### Lean のコメント（日本語訳）

> 全非負開始時刻で、Selfの選別結果であるTCZはちょうど目標点 `{0}`。

### 補題の説明

Self が選ぶ TCZ は、ちょうど目標点 \(\{0\}\) です。

### 証明の概略

1. 閉到達集合が全体（前の補題）。
2. \(1+x^2\le1\iff x=0\)（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1O24Ego_admissible"></a>

## 補題 `c1O24Ego_admissible`

### 式

$$
\mathrm{Ego}\ \text{は許容制御}
$$

### Lean のコメント（日本語訳）

> 型付き三つ組のEgoが出すfeedbackは、元のflowの許容制御である。

### 補題の説明

Ego が返す制御値は、流れの許容制御です。

### 証明の概略

1. Ego は流れのフィードバックに等しい（関係の証拠）。フィードバックの許容性（`feedback_admissible`）を使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.typedSelfEgoTCZ_exponential"></a>

## 定理 `typedSelfEgoTCZ_exponential`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{TCZ}\bigr)\le|x|\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> Selfが選ぶTCZとEgoが実装するflowを同じ過程として結び、全未来時刻の指数評価を得る。これはスカラーH-flowに対するO24の具体adapterである。

### 補題の説明

Self が選ぶ TCZ と、Ego が実装する流れを、同じ過程として結び、TCZ までの距離の指数評価を得ます。一次元の流れについての、原文 §2.4 の具体的な適用です。

### 証明の概略

1. 一次元モデルの定理1（`linearFlow_theorem1`、率 3、目標 0）を適用する。
2. TCZ が目標点 \(\{0\}\)（`c1O24TCZ_eq_singleton`）なので、距離は \(\lvert x\rvert\) 倍の指数。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusSelf"></a>

## 定義 `c1ConsensusSelf`

### 式

$$
\mathrm{Self}_t(W)=\{x\in W\mid V_0(x)\le1\}
$$

### Lean のコメント（日本語訳）

> 二主体モデルのSelf作用素。可能世界を定理1/2共通残差の零集合へ絞る。

### 定義の説明

二主体モデルの Self です。可能世界の集合を、定理1・2 で共通の残差が 0 の点（\(V_0\le1\)）に絞ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusEgo"></a>

## 定義 `c1ConsensusEgo`

### 式

$$
\mathrm{Ego}(x,t)=()
$$

### Lean のコメント（日本語訳）

> 二主体モデルのEgo方策。値型は合意flowの制御型 `Unit`。

### 定義の説明

二主体の合意の流れの方策です。制御の型は `Unit`（自明）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusReachable"></a>

## 定義 `c1ConsensusReachable`

### 式

$$
\overline{\mathrm{Reach}}(\mathrm{box},t_0)
$$

### Lean のコメント（日本語訳）

> 二主体flowが初期箱から生成する閉到達可能な可能世界集合。

### 定義の説明

箱から出発した流れの、閉到達集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusTCZ"></a>

## 定義 `c1ConsensusTCZ`

### 式

$$
\mathrm{Self}_t(\overline{\mathrm{Reach}})
$$

### Lean のコメント（日本語訳）

> Selfの像として定義する二主体TCZ。

### 定義の説明

Self の像として定義した TCZ です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.C1ConsensusSelfEgoTCZ"></a>

## 構造体 `C1ConsensusSelfEgoTCZ`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ})
$$

### Lean のコメント（日本語訳）

> Self・Ego・TCZを異なる型で持ち、同じ二主体flow上の保存関係を記録する。

### 定義の説明

二主体モデル用の三つ組の構造体です（Self・Ego・TCZ を別の型で持つ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.consensusSelfEgoTCZAdapter"></a>

## 定義 `consensusSelfEgoTCZAdapter`

### 式

$$
\text{二主体の三つ組}
$$

### Lean のコメント（日本語訳）

> 定理1/2を接続した二主体H-flowの型付き表現。

### 定義の説明

二主体の合意の流れから作る三つ組です。

### 証明の概略

1. 各フィールドに対応する定義を入れる。関係の証拠は定義の展開（`rfl`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusSelfTCZ_eq_shared"></a>

## 補題 `c1ConsensusSelfTCZ_eq_shared`

### 式

$$
\mathrm{TCZ}=\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

> 型付きSelfが選ぶ二主体TCZは、定理2で使うsharedTCZそのものである。

### 補題の説明

Self が選ぶ TCZ は、定理2の共有 TCZ に一致します。

### 証明の概略

1. 閉到達集合は箱（`consensusFlow_reachable_closure_eq_box`）。
2. 箱の上で残差が時刻によらないので、\(1+\Phi_2\le1\iff\Phi_2=0\)（両方向を示す）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1ConsensusEgo_admissible"></a>

## 補題 `c1ConsensusEgo_admissible`

### 式

$$
\mathrm{Ego}\ \text{は許容制御}
$$

### Lean のコメント（日本語訳）

> 二主体の型付きEgoは同じH-flowが宣言する許容feedbackである。

### 補題の説明

Ego は、流れが宣言する許容フィードバックです。

### 証明の概略

1. Ego は流れのフィードバックに等しい（関係の証拠）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusSelf"></a>

## 定義 `c1OptimalConsensusSelf`

### 式

$$
\mathrm{Self}_t(W)=\{x\in W\mid V_0(x)\le1\}
$$

### Lean のコメント（日本語訳）

> 最適化合意flow用のSelf作用素。可能世界を同じ時刻の評価水準で選ぶ。

### 定義の説明

最適化した合意の流れ用の Self です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusEgo"></a>

## 定義 `c1OptimalConsensusEgo`

### 式

$$
\mathrm{Ego}(x,t)=3
$$

### Lean のコメント（日本語訳）

> 最適化合意flow用のEgo feedback。

### 定義の説明

最適化した流れのフィードバック（定数 3）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusReachable"></a>

## 定義 `c1OptimalConsensusReachable`

### 式

$$
\overline{\mathrm{Reach}}(\mathrm{box},t_0)
$$

### Lean のコメント（日本語訳）

> 最大ゲインflowが初期箱から生成する閉到達集合。

### 定義の説明

最大ゲインの流れが、箱から生む閉到達集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ"></a>

## 定義 `c1OptimalConsensusTCZ`

### 式

$$
\mathrm{Self}_t(\overline{\mathrm{Reach}})
$$

### Lean のコメント（日本語訳）

> Selfが閉到達可能世界から選ぶ最適化flowのTCZ。

### 定義の説明

最適化した流れの TCZ です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.C1OptimalConsensusAdapter"></a>

## 構造体 `C1OptimalConsensusAdapter`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ},\mathrm{initialSet},\ldots)
$$

### Lean のコメント（日本語訳）

> 最適化flowの型付きSelf・Ego・TCZ adapter。各表現の型を分けて保持する。

### 定義の説明

最適化した流れの三つ組の構造体です。上の三つ組に加えて、初期集合 `initialSet` と、到達集合が「流れから作った閉到達集合」であるという証拠（`reachable_is_closed_loop_closure`）を持ちます。無矛盾性の追加条件 H-flow（軌道と到達集合が同じ流れから来る）の根拠になる構造体です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.optimalConsensusSelfEgoTCZAdapter"></a>

## 定義 `optimalConsensusSelfEgoTCZAdapter`

### 式

$$
\text{最適化した流れの三つ組}
$$

### Lean のコメント（日本語訳）

> 有限地平最大ゲイン最適化と定理2時間変換評価を保持するO24三つ組。

### 定義の説明

最適化した流れ（最大ゲイン 3、初期集合は箱）から作る三つ組です。

### 証明の概略

1. 各フィールドに対応する定義を入れる。到達集合の証拠は定義そのもの（`rfl`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusTCZ_eq_shared"></a>

## 補題 `c1OptimalConsensusTCZ_eq_shared`

### 式

$$
\mathrm{TCZ}=\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

> 最適化flowのSelf選別TCZは、定理2と同じ二主体sharedTCZ。

### 補題の説明

最適化した流れでも、Self が選ぶ TCZ は共有 TCZ に一致します。

### 証明の概略

1. 閉到達集合は箱（`consensusOptimalFlow_reachable_closure_eq_box`）。
2. 前の二主体の補題と同様に、箱の上で \(1+\Phi_2\le1\iff\Phi_2=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusEgo_is_argmin_right_limit"></a>

## 補題 `c1OptimalConsensusEgo_is_argmin_right_limit`

### 式

$$
\lim_{s\downarrow t_0}u_{(t_0,x)}(s)=\mathrm{Ego}(x,t_0)
$$

### Lean のコメント（日本語訳）

> 二主体O24のEgoは有限地平argmin選択の開始点右極限と一致する。

### 補題の説明

Ego は、有限地平の最適制御の選択の、開始点での右極限と一致します（反復ホライズン制御の条件）。

### 証明の概略

1. 最適制御の選択は定数 3（`consensusSelectedHorizonControl`）、Ego も 3。定数の極限（`simpa`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1O24.c1OptimalConsensusO24_distance"></a>

## 補題 `c1OptimalConsensusO24_distance`

### 式

$$
\operatorname{dist}(x(t),\mathrm{TCZ})\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 最適化flowのTCZへの距離評価は、型付きTCZを通して定理2の評価と一致する。

### 補題の説明

三つ組を通して見た TCZ までの距離の評価が、定理2の評価（率 3）と一致します。

### 証明の概略

1. 三つ組の TCZ は共有 TCZ（前の補題）。
2. `consensusOptimalFlow_theorem2_distance` を適用する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
