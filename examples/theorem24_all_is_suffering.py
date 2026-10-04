"""
定理24 (一切皆苦定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: J*_{a,ρ}(x,T) = min_π ∫ e^{-ρ(t-T)} V_a(x(t),t) dt, V_a≥0。
      条件24-A: 空未満では V_a=0 を a.e. 永久に保つ方策が存在しない ⇒ J*>0 (24.2)。
      ※ 24-A が無ければ零苦は可能。「毎瞬の主観的苦痛」ではなく最適化後も残る正の残余コスト。

トイ: 1次元 x, 速度制限 |ẋ|≤1。基準(評価の零点)が d(t)=A sin(2πt/6.4) で動き回る。
      V_a(x,t)=max(|x−d(t)|−0.025, 0)² (帯の中なら苦ゼロ)。割引 ρ=1。
      格子 dx=dt=0.05 の動的計画法(価値反復)で J* を数値的に解く。
  A=0.5: d の最大速さ≈0.49<1 → 追従可能(24-A が成り立たない) → J*=0 となる初期状態がある
  A=3.0: d の最大速さ≈2.9>1 → 永久に追従不能(24-A 成立)   → すべての (x,T) で J*>0

Lean 対応: Tomabechi/Examples/Theorem24_Tracking.lean (condition24A_hard / trackable_zero_cost / trackable_value_zero / hard_optimal_value_positive)
  証明範囲: 条件24-Aの検証(A=3)、追従可能(A=0.5)では零苦方策が存在。最適方策の存在・可積分性は仮定。DP の数値 J* は未証明。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

dx = dt = 0.05; rho = 1.0; nphase = 128                # 周期 128*0.05 = 6.4
X = np.arange(-4, 4 + dx / 2, dx)
gamma = np.exp(-rho * dt)

def solve(Aamp, cycles=6):
    phase_t = np.arange(nphase) * dt
    d = Aamp * np.sin(2 * np.pi * phase_t / 6.4)
    cost = np.maximum(np.abs(X[None, :] - d[:, None]) - 0.025, 0) ** 2     # V_a(x, t_s)
    J = np.zeros((nphase, len(X)))
    for _ in range(cycles):                              # 周期系の後ろ向き価値反復
        for s in range(nphase - 1, -1, -1):
            nxt = J[(s + 1) % nphase]
            P = np.pad(nxt, 1, mode="edge")
            best = np.minimum(np.minimum(P[:-2], P[1:-1]), P[2:])   # 動き: -1 / 0 / +1 セル
            J[s] = cost[s] * dt + gamma * best
    return J, d

J_track, d_track = solve(0.5)
J_hard, d_hard = solve(3.0)

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(12, 4))
ax[0].plot(X, J_track[0], label="A=0.5 (追従可能)"); ax[0].plot(X, J_hard[0], label="A=3.0 (追従不能)")
ax[0].set_title("J*(x, T=0)"); ax[0].set_xlabel("x"); ax[0].legend()
ax[1].plot(np.arange(nphase) * dt, d_track, label="d(t) A=0.5"); ax[1].plot(np.arange(nphase) * dt, d_hard, label="d(t) A=3.0")
ax[1].axhline(0, c="gray"); ax[1].set_title("評価の零点 d(t) (|ḋ|>1 は追えない)"); ax[1].legend()
plt.tight_layout(); plt.show()

# %% 数値確認
print("A=0.5: min_{x,T} J* =", J_track.min(), "  / A=3.0: min_{x,T} J* =", J_hard.min())
assert J_track.min() == 0.0          # 24-A なしで零苦が実現可能
assert J_hard.min() > 1e-4           # 24-A のもとで全 (x,T) で J*>0
