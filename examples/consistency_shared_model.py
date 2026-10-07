"""
無矛盾性の証明で使った共有モデル N の説明用の再現  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
主張(Lean): 原文の前提を本プロジェクトで型として書き下した条件と、追加の明示条件
      (H-flow・H-sum・H-stage・H-info)を同時に満たす、非退化なモデル N が存在する
      (Tomabechi/Consistency/ConsistencyR123_FinalV14.lean の final_consistency_v14)。

N の中身は、定理群ごとの具体的な小さいモデルを、共通の土台で束ねたもの:
  R1  共通の概念束 L=[0,1]^2。層 n ↦ (n/(n+1), n/(n+1))、頂 (1,1)=「空」。
  C1  二主体合意系 x=(x0,x1)、ゲイン u∈[0,3]: x0'=-(u/2)(x0-x1), x1'=+(u/2)(x0-x1)。
      最適は u=3。共有残差 Φ2=Σmax(xi²-θ,0)+2(x0-x1)²、基礎評価 V0=1+Φ2(R3)。定理1・2・3・4・20。
  C2  完全状態 (q,y)、q=1-e^{-t}, y=t-q²、層重み 2^{-(n+1)}、S=t+1。定理15→23-A。
  C3  第 n 段の谷の中心 (n+1)/(n+2)、滞在 4(n+2)(n+3)、段内は率 1 の勾配流。定理21・22・23-B。
  C4  履歴 h ごとの中心 c_h∈{0,1}、F_h=時刻 1 の勾配流(率 e^-1 の縮小)。正典TCZ=[c_h-1,c_h+1]。定理16→25。
  C5  上位状態 (y0,y1): y0'=-(1/2+k)y0, y1'=3/2、k∈[0,1/2]、最適 k=1/2。W=y0²。定理24→26→27。

限定: Python が確かめるのは、Lean で証明した等式・不等式のいくつかの数値例だけ。
      Lean の N は部品間の保存式(同じ束・同じ V0・同じ軌道など)まで証明しているが、ここでは
      式として見える一部だけを示す。定理16の正典TCZを生成する制御系(速度制御 x'=u, |u|≤1)と
      定理24の有界ゲイン制御系は別の系で、単一の共有制御系ではない。

Lean 対応: Tomabechi/Consistency/(ConsistencyR1_* / C1_* / C2_* / C3_* / C4_* / C5_* / R2_* / R3_* / R123_*)
           代表の存在宣言は ConsistencyR123_FinalV14.lean。
"""
# %% 準備: 共通の部品
import math
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

results = {}                                    # 最後のセルでまとめて確認する


def check(label, ok):
    results[label] = bool(ok)
    print(f"  [{'ok' if ok else 'NG'}] {label}")


# R1 共通の概念束 L=[0,1]^2(座標ごとの順序。底 (0,0)、頂 (1,1))
TOP = (1.0, 1.0)


def layer_point(n):
    """層 n を対角線上の点 (n/(n+1), n/(n+1)) へ。'top' は頂。"""
    if n == "top":
        return TOP
    r = n / (n + 1)
    return (r, r)


def leq(a, b):
    return a[0] <= b[0] and a[1] <= b[1]


# C1 二主体合意系
THETA = 1 / 10        # 定理2の個人閾値(箱 |x_i| ≤ 1/4 の版。共通領域 |x_i| ≤ 3 の版は θ=10)
GAMMA = 2.0           # 辺の結合(有向辺 2 本、各重み γ/2)
U_MAX = 3.0           # 許容ゲインの上限


def phi2(x, theta=THETA):
    """定理2の共有残差 Φ2 = Σ max(x_i² - θ, 0) + γ (x0 - x1)²。"""
    return sum(max(xi**2 - theta, 0.0) for xi in x) + GAMMA * (x[0] - x[1]) ** 2


def V0(x):
    """共有の基礎評価 V0 = 1 + Φ2(定理1・4・20 で同じものを使う)。"""
    return 1.0 + phi2(x)


def consensus_flow(x, t, u=U_MAX):
    """定数ゲイン u の閉ループ流(閉形式)。平均 m を保ち、半差 d を e^{-ut} 倍。"""
    m = (x[0] + x[1]) / 2
    d = (x[0] - x[1]) / 2 * math.exp(-u * t)
    return np.array([m + d, m - d])


def consensus_cost(x, u_signal, T=2.0, n=4000):
    """有限地平の費用 ∫_0^T (1 + d(t)²) dt(d は半差)を、ゲイン信号 u_signal で Euler 積分。"""
    dt = T / n
    d = (x[0] - x[1]) / 2
    total = 0.0
    for k in range(n):
        total += (1 + d**2) * dt
        d -= dt * u_signal(k * dt) * d
    return total


# %% R1 共通の概念束 と C1 二主体合意系(定理1・2・3・4・20)
print("R1 共通の概念束")
pts = [layer_point(n) for n in range(50)]
check("R1: 層の埋め込みは単調", all(leq(pts[i], pts[i + 1]) for i in range(49)))
check("R1: 有限の層はすべて頂の下で、頂に等しくない", all(leq(p, TOP) and p != TOP for p in pts))

print("C1 二主体合意系")
x_init = np.array([0.25, -0.15])               # 箱 |x_i| ≤ 1/4 の点
m = x_init.mean()
gains = {"u=3(最大)": lambda t: 3.0, "u=0": lambda t: 0.0, "u=1.5": lambda t: 1.5,
         "t<1 だけ u=3": lambda t: 3.0 if t < 1 else 0.0,
         "u=1.5+1.5sin5t": lambda t: 1.5 + 1.5 * math.sin(5 * t)}
costs = {k: consensus_cost(x_init, s) for k, s in gains.items()}
for k, c in costs.items():
    print(f"    費用 {k:16s} = {c:.6f}")
check("C1: 最大ゲイン u=3 の費用が、試した他のゲイン信号以下",
      all(costs["u=3(最大)"] <= c + 1e-12 for c in costs.values()))

ts = np.linspace(0, 3, 31)
traj = np.array([consensus_flow(x_init, t) for t in ts])
dist_diag = lambda y: abs(y[0] - y[1]) / math.sqrt(2)  # 共有TCZ(対角線)への Euclid 距離
check("C1: 平均は保存される", np.allclose(traj.mean(axis=1), m))
check("定理1: TCZ への距離 = 初期距離 · e^{-3t}",
      all(abs(dist_diag(y) - dist_diag(x_init) * math.exp(-3 * t)) < 1e-12 for y, t in zip(traj, ts)))
check("定理2: 共有残差 Φ2 = Φ2(0) · e^{-6t}(箱の中では個人項が 0)",
      all(abs(phi2(y) - phi2(x_init) * math.exp(-6 * t)) < 1e-12 for y, t in zip(traj, ts)))

F = phi2(x_init)                                # 定理4: P=e^{-F}, Q=1, κ=1
check("定理4: 実効評価の超過分 F - e^{-F} + 1 は F 以上 2F 以下", F <= 1 + F - math.exp(-F) <= 2 * F)
D = lambda y: (y[0] - y[1]) ** 2                # 定理20: 実効評価 V0 + D = 1 + 3D(箱の中)
check("定理20: 箱の中で実効評価 V0 + D = 1 + 3D", abs(V0(x_init) + D(x_init) - (1 + 3 * D(x_init))) < 1e-12)
check("定理20: 超過分 3D は率 6 で減衰",
      all(abs(3 * D(y) - 3 * D(x_init) * math.exp(-6 * t)) < 1e-12 for y, t in zip(traj, ts)))

cross = lambda a, b: a[0] * b[1] - a[1] * b[0]  # R2: 一点からの到達集合は x と (m,m) を結ぶ線分
check("R2: 軌道は x と (m,m) を結ぶ線分の上にあり、(m,m) へ近づく",
      all(abs(cross(y - x_init, np.array([m, m]) - x_init)) < 1e-12 for y in traj)
      and np.allclose(consensus_flow(x_init, 50.0), [m, m]))
z0 = np.array([0.2, -0.2])                      # 定理3: 零平均の初期点
check("定理3: 零平均の初期点は原点へ率 3 で近づく", np.allclose(consensus_flow(z0, 1.0), z0 * math.exp(-3.0)))

# %% C2 可算層のエントロピー収支(定理15→23-A) と C3 段階の谷(定理21・22・23-B)
print("C2 可算層のエントロピー収支")
q = lambda t: 1 - math.exp(-t)                  # 認知状態
y_env = lambda t: t - q(t) ** 2                 # 環境の観測量
w = [2.0 ** -(n + 1) for n in range(60)]        # 正の層の重み(60 項で打ち切り。総和 1)
layer_part = lambda t: sum(wn * (1 + q(t) ** 2) for wn in w)
S = lambda t: y_env(t) + layer_part(t)
ts2 = np.linspace(0, 5, 51)
check("C2: 一般化エントロピー S(t) = t + 1(生成率 Π = 1)", all(abs(S(t) - (t + 1)) < 1e-12 for t in ts2))
check("H-sum: 有限部分和は一様に有界(≤ 2)",
      all(sum(w[:N]) * (1 + q(t) ** 2) <= 2 for N in range(61) for t in ts2))
check("定理23-A: S が狭義に増えるので、同じ完全状態に戻らない", all(S(a) < S(b) for a, b in zip(ts2, ts2[1:])))

print("C3 段階の谷")
center = lambda n: (n + 1) / (n + 2)            # 第 n 段の谷の中心 rep(n+1)
dwell = lambda n: 4 * (n + 2) * (n + 3)         # 滞在時間
gap = lambda n: 1 / ((n + 2) * (n + 3))         # 次の中心との間隔
check("C3: 中心の間隔は 1/((n+2)(n+3))", all(abs(center(n + 1) - center(n) - gap(n)) < 1e-15 for n in range(30)))
x_stage, stage_end, stage_err = 0.0, [], []     # 最初の段の初期値は 0
for n in range(8):
    x_stage = center(n) + (x_stage - center(n)) * math.exp(-dwell(n))   # 段内の勾配流(率 1)
    stage_end.append(x_stage)
    stage_err.append(abs(x_stage - center(n)))
check("C3: 各段の終点の誤差は、許容誤差(間隔/4)よりずっと小さい",
      all(e <= gap(n) / 4 for n, e in enumerate(stage_err)))
check("C3: 中心の列は単調に上がり、頂の値 1 へ近づく(LUB の階段)",
      all(center(n) < center(n + 1) < 1 for n in range(100)))
H = lambda p: -sum(pi * math.log(pi) for pi in p if pi > 0)
check("C3: ゴールのエントロピー log 2、物理層 0(上位層の条件付き相互情報量は log 2)",
      abs(H([0.5, 0.5]) - math.log(2)) < 1e-15 and H([1.0]) == 0)

# %% C4 自己意識の固定点(定理16→25) と C5 苦・寂静・無明(定理24→26→27)
print("C4 自己意識の固定点")
centers16 = {False: 0.0, True: 1.0}
fixed = {}
for h, ch in centers16.items():
    Fh = lambda x, ch=ch: ch + (x - ch) * math.exp(-1.0)   # 時刻 1 の勾配流
    grid = np.linspace(0, 1, 11)
    check(f"定理16 h={h}: F_h は [0,1] を保ち、率 e^-1 の縮小",
          all(0 <= Fh(a) <= 1 for a in grid)
          and all(abs(Fh(a) - Fh(b)) <= math.exp(-1) * abs(a - b) + 1e-15 for a in grid for b in grid))
    x = 0.37
    for _ in range(60):
        x = Fh(x)
    fixed[h] = x
    check(f"定理16 h={h}: 反復は固定点 c_h = {ch} に幾何収束", abs(x - ch) < 1e-15)
    lo, hi = ch - 1, ch + 1                     # Ω = {V_h ≤ 1/2}
    tau = 10.0                                  # 速度制御 |u|≤1 の到達集合 [1/2-τ, 1/2+τ]
    check(f"定理16 h={h}: 正典TCZ = [c_h-1, c_h+1]",
          (max(0.5 - tau, lo), min(0.5 + tau, hi)) == (lo, hi))
    check(f"定理16 h={h}: 勾配フィードバック u = c_h - x は担体上で |u| ≤ 1",
          all(abs(ch - a) <= 1 for a in np.linspace(lo, hi, 21)))
check("定理25: 履歴ごとの固定点は一致しない(全履歴に共通の固定点はない)", fixed[False] != fixed[True])

print("C5 苦・寂静・無明")
r0, ph0 = 0.8, 0.0                              # 上位状態 (y0, y1)
radius = lambda t, k=0.5: r0 * math.exp(-(0.5 + k) * t)
phase = lambda t: ph0 + 1.5 * t
s = np.linspace(0, 40, 400001)
disc_cost = lambda k: np.trapezoid(np.exp(-s) * 3 * (r0 * np.exp(-(0.5 + k) * s)) ** 2, s)
check("定理24/26: 最適ゲイン k=1/2 の割引費用 = y0² = W", abs(disc_cost(0.5) - r0**2) < 1e-8)
check("定理24: 他のゲイン k=0, 1/4 の費用は最適値以上",
      all(disc_cost(k) >= r0**2 - 1e-9 for k in (0.0, 0.25)))
check("定理24: 下位層の価値 ∫e^{-s}·1 ds = 1 > 0(苦)", abs(np.trapezoid(np.exp(-s), s) - 1) < 1e-8)
ts5 = np.linspace(0, 6, 61)
check("定理26: W(y(t)) = y0² e^{-2t} → 0", all(abs(radius(t) ** 2 - r0**2 * math.exp(-2 * t)) < 1e-12 for t in ts5))
check("定理26: 位相 y1 は 3/2 の速さで動き続ける(動的寂静)", phase(6.0) - phase(0.0) == 9.0)
ok_ref, ok_eta = True, True
for t in ts5:
    y = radius(t)
    u0, utr, drift = np.array([-0.5 * y, 1.5]), np.array([0.5 * y, 1.5]), np.array([-0.5 * y, 0.0])
    ok_ref &= abs(2 * y * (drift + utr)[0]) < 1e-12                 # 基準入力の下の dW/dt
    ok_eta &= abs(np.linalg.norm(u0 - utr) - abs(y)) < 1e-12        # 行 η = u_0 - u_tr = (-y0, 0)
check("定理27: 基準入力 u_tr の下で dW/dt = 0(27-A2)", ok_ref)
check("定理27: 行 η = u_0 - u_tr = (-y0, 0)、|η| = |y0|", ok_eta)

# %% 可視化
fig, ax = plt.subplots(2, 3, figsize=(15, 8.5))

a = ax[0, 0]                                    # R1 共通の概念束
a.add_patch(plt.Rectangle((0, 0), 1, 1, fill=False, color="gray"))
P = np.array([layer_point(n) for n in range(12)])
a.plot(P[:, 0], P[:, 1], "o", color="C0", label="層 n → (n/(n+1), n/(n+1))")
a.plot(*TOP, "*", color="C3", ms=15, label="頂 (1,1)「空」")
a.set_xlim(-0.05, 1.1); a.set_ylim(-0.05, 1.1); a.set_aspect("equal")
a.set_title("R1 共通の概念束 [0,1]²"); a.legend(loc="lower right", fontsize=8)

a = ax[0, 1]                                    # C1 合意
tt = np.linspace(0, 2, 200)
X = np.array([consensus_flow(x_init, t) for t in tt])
a.plot(tt, X[:, 0], label="主体0 $x_0$"); a.plot(tt, X[:, 1], label="主体1 $x_1$")
a.axhline(m, color="gray", ls=":", label="平均 m(保存)")
b = a.twinx()
b.semilogy(tt, [phi2(y) for y in X], "C3--", label="Φ2(対数軸)")
b.set_ylabel("Φ2")
a.set_title("C1 二主体合意(u=3): Φ2 ∝ $e^{-6t}$"); a.set_xlabel("t"); a.legend(loc="center right", fontsize=8)

a = ax[0, 2]                                    # C2 エントロピー
tt = np.linspace(0, 5, 200)
a.plot(tt, [S(t) for t in tt], lw=2, label="S = y + Σ w_n(1+q²) = t+1")
a.plot(tt, [y_env(t) for t in tt], label="環境 y")
a.plot(tt, [layer_part(t) for t in tt], label="層の和 Σ w_n(1+q²)")
a.set_title("C2 可算層のエントロピー収支"); a.set_xlabel("t"); a.legend(fontsize=8)

a = ax[1, 0]                                    # C3 段の階段(段の番号を横軸に)
nn = np.arange(8)
a.step(nn, [center(n) for n in nn], where="mid", color="gray", label="谷の中心 (n+1)/(n+2)")
a.plot(nn, stage_end, "o", color="C0", label="各段の終点")
a.axhline(1, color="C3", ls=":", label="頂の値 1")
a.set_title("C3 段階の谷(LUB の階段)"); a.set_xlabel("段 n"); a.legend(fontsize=8)

a = ax[1, 1]                                    # C4 履歴ごとの固定点
for h, ch in centers16.items():
    for x0 in (0.0, 0.3, 0.7, 1.0):
        seq = [x0]
        for _ in range(8):
            seq.append(ch + (seq[-1] - ch) * math.exp(-1.0))
        a.plot(seq, "o-", ms=3, color="C0" if not h else "C1", alpha=0.7)
a.plot([], [], "C0", label="履歴 h=False(固定点 0)"); a.plot([], [], "C1", label="履歴 h=True(固定点 1)")
a.set_title("C4 自己更新 $F_h$ の反復(率 $e^{-1}$)"); a.set_xlabel("反復回数"); a.legend(fontsize=8)

a = ax[1, 2]                                    # C5 動的寂静
tt = np.linspace(0, 6, 300)
a.plot(tt, [radius(t) ** 2 for t in tt], label="W = y0²(→0)")
a.plot(tt, [abs(radius(t)) for t in tt], "--", label="|η| = |y0|(行)")
b = a.twinx()
b.plot(tt, [phase(t) for t in tt], "C2:", label="位相 y1")
b.set_ylabel("位相 y1")
a.set_title("C5 寂静: W→0、位相は回り続ける"); a.set_xlabel("t"); a.legend(loc="center right", fontsize=8)

plt.tight_layout(); plt.show()

# %% 数値確認
assert all(results.values()), [k for k, v in results.items() if not v]
x_X = np.array([1.3, -2.1])                     # 共通領域 X3 = {|x_i| ≤ 3} の点(θ=10 の版)
assert abs((1 + phi2(x_X, theta=10.0)) - (1 + 2 * (x_X[0] - x_X[1]) ** 2)) < 1e-12   # commonV0X
assert all(abs(center(n) - layer_point(n + 1)[0]) < 1e-15 for n in range(20))       # C3 の中心 = R1 の層の点
assert np.allclose(consensus_flow([0.1, 0.1], 1.0), [0.1, 0.1])                     # 動かない状態がある
assert not np.allclose(consensus_flow([0.2, -0.1], 1.0), [0.2, -0.1])               # 動く状態がある
print(f"全 {len(results)} 項目と共有の確認が通った(数値の確認で、証明ではない)。")
