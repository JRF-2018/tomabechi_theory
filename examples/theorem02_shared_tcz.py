"""
定理2 (共有TCZ収束定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 主体 i=1,2 の状態 x_i, 表象 h_i(x)=x, 不整合 S12=(x1-x2)^2 (=0 ⇔ 表象一致)。
      共有残差 Φ2 = Σ w_i [V0_i - θ_i]+ + γ S12 。
      Φ2 の下降 + 誤差境界があれば dist → 0、各個人残差と不整合も 0 へ。
      ※ 双方向結合だけでは共有収束しない(原文§4「必要な追加条件」): 谷が遠いと
        共有零集合 Ω2 = {Φ2=0} が空で、不整合が正に残る。

V0_i(x) = (x - c_i)^2,  θ=0.1, γ=2。
  ケースA: c=(0, 0)    谷が一致 → 共有零集合 Ω2={(z,z):|z|≤√θ} が非空 → Φ2 → 0 (不整合も 0)
  ケースB: c=(0, 3.0)  谷が遠い → 共有零集合が空   → 不整合が正のまま残る(反例)

Lean 対応:
  Tomabechi/Examples/Theorem2_SubgradientFlow.lean
    A: 下の run() の更新則 ẋ∈-20∂Φ2 (Euler 法の刻みを 0 にした連続時間版)、x(0)=(2,-2)。閾値 √θ の前後で
       率 200・160 に切り替わる対称な厳密軌道を書き下し、AC・a.e.下降 Φ'≤-2Φ (c=1)・誤差境界
       dist(x,Ω2)²≤2Φ2 (全ての x)・Ω2 非空・連結性を満たして、定理2の一般結論 (指数減衰) へ接続する。
  Tomabechi/Examples/Theorem2_SharedTCZ.lean
    A の補助: 合意方策 ẋ_i=-x_i でも同じ前提を証明 (下の「Lean が検証する事実」の確認はこちら)。
    B: すべての x で Φ2 ≥ 3。共有零集合は空で、補題0の前提が満たされえない。
  証明していないもの: Euler 離散化の誤差と、run() の数値出力。
  (旧版の A は c=(0,0.5) だったが、誤差境界を厳密に示すため対称な c=(0,0) に変更。)
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

w, gamma, theta = np.array([1.0, 1.0]), 2.0, 0.1

def run(c, steps=4000, dt=0.002, x0=(2.0, -2.0)):
    c = np.asarray(c, float); x = np.array(x0, float); H = []
    for _ in range(steps):
        V = (x - c)**2
        S = (x[0] - x[1])**2
        phi = (w * np.maximum(V - theta, 0)).sum() + gamma * S
        H.append((phi, S, np.maximum(V - theta, 0).sum()))
        g = w * 2 * (x - c) * (V > theta)                  # [V-θ]+ の劣勾配
        g = g + gamma * 2 * (x[0] - x[1]) * np.array([1.0, -1.0])
        x = x - dt * 20 * g                                # Φ2 の勾配流(共同方策)
    return np.array(H)

A, B = run([0, 0]), run([0, 3.0])

# %% 可視化
fig, ax = plt.subplots(1, 3, figsize=(14, 4))
for H, lab in [(A, "A: 谷が近い"), (B, "B: 谷が遠い")]:
    ax[0].semilogy(H[:, 0] + 1e-16, label=lab); ax[1].semilogy(H[:, 1] + 1e-16, label=lab)
    ax[2].plot(H[:, 2], label=lab)
ax[0].set_title("共有残差 Φ2"); ax[1].set_title("辺の不整合 S12"); ax[2].set_title("個人残差の和")
ax[0].legend(); plt.tight_layout(); plt.show()

# %% 数値確認
print("A: 最終 Φ2=%.2e, S12=%.2e" % (A[-1, 0], A[-1, 1]))
print("B: 最終 Φ2=%.2e, S12=%.2e  (正のまま残る)" % (B[-1, 0], B[-1, 1]))
assert A[-1, 0] < 1e-8 and B[-1, 1] > 0.1

# %% Lean が検証する事実の数値確認
rng = np.random.default_rng(1)
sq = np.sqrt(theta)
def Phi2(x, c): return sum(max((x[i] - c[i])**2 - theta, 0) for i in range(2)) + gamma * (x[0] - x[1])**2
# B: すべての x で Φ2 >= 3
pts = rng.uniform(-6, 8, size=(20000, 2))
print("B: min Φ2 =", min(Phi2(p, [0, 3.0]) for p in pts))
assert all(Phi2(p, [0, 3.0]) >= 3 for p in pts)
# A: 誤差境界 dist(x,Ω2)^2 <= 2Φ2 (sup 距離; Ω2={(z,z):|z|<=√θ})
def dist_to_Omega(x):
    z = np.clip((x[0] + x[1]) / 2, -sq, sq); return max(abs(x[0] - z), abs(x[1] - z))
assert all(dist_to_Omega(p)**2 <= 2 * Phi2(p, [0, 0]) + 1e-9 for p in pts)
# A: 合意方策 ẋ=-x, x(0)=(2,-2) で Φ2' <= -2Φ2
tt = np.linspace(0, 4, 4001); Pt = np.array([Phi2(np.array([2.0, -2.0]) * np.exp(-u), [0, 0]) for u in tt])
dP = np.gradient(Pt, tt)
print("A(合意方策): max(Φ'+2Φ) =", (dP + 2 * Pt)[1:-1].max())
assert (dP + 2 * Pt)[1:-1].max() < 1e-2
