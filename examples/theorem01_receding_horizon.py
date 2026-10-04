"""
定理1 (苫米地主定理 / 個人TCZ収束) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 反復ホライズン最適制御 u* = argmin ∫V0 ds を各時刻で解き、先頭 u*(t+) だけ使う。
      補題0の「下降条件 + 誤差境界」が成り立てば dist(x(t), TCZ) → 0。
      ※ argmin であること自体からは収束しない(原文 §3「厳密性」)。

状態: x∈R (1次元), 動力学 x' = u (|u|<=1)。
V0(x) = (x^2-1)^2 + 0.3 x  … 谷が2つ: 大域最小 x≈-1.04 (V<0)、局所最小 x≈+0.96 (V≈+0.29)。
閾値 θ=0 なので TCZ = {V0 <= 0} は左の谷だけ。残差 Φ1 = [V0 - θ]+。

見どころ:
  (A) 左側の谷から出発 → 下降条件が成り立ち Φ1 が 0 に到達
  (B) 右の局所谷から出発 + 短い地平 T=0.6 → argmin を毎回解いているのに TCZ に届かない
      (これは「下降条件が成り立たない」反例。定理1の仮定を外した場合の挙動)
  (C) 同じ出発点でも地平を T=8 に伸ばすと障壁を越えて TCZ に届く。ただし山を越える間は Φ1 が増えるので、
      補題0の下降条件が全区間で成り立つわけではない(確認しているのは「最終的に届いた」という数値の事実のみ)
  (D) Lean が検証する閉ループ: 目標点フィードバック ẋ=-(x+1) (g=-1∈TCZ)、x0=-1/2。
      補題0の前提 Φ'≤-2cΦ (c=2/5)、dist²≤CΦ (C=1/6) を Lean で証明(定理1の一般結論)。
      (B) の反例側: 停留点 x_loc∈(0.9,1) の定数軌道は零フィードバック閉ループの解で、下降条件が破れる。
      ※ 反復ホライズン argmin の (A)(B)(C) の挙動そのものは Lean では証明していない(数値のみ)。
Lean 対応: Tomabechi/Examples/Theorem1_DoubleWell.lean (theoremA / caseB)
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

V0 = lambda x: (x**2 - 1)**2 + 0.3 * x
theta = 0.0
grid = np.linspace(-2, 2, 4001)
rts = np.roots([1, 0, -2, 0.3, 1]); rts = np.sort(rts[np.abs(rts.imag) < 1e-9].real)   # V0=0 の実根
tcz_lo, tcz_hi = rts[0], rts[1]               # TCZ = {V0 <= θ=0} = [tcz_lo, tcz_hi] (厳密な区間端)
dist_tcz = lambda x: max(tcz_lo - x, x - tcz_hi, 0.0)
phi1 = lambda x: max(V0(x) - theta, 0.0)       # 零残差 Φ1

# %% 反復ホライズン制御: 各時刻で「目標点 g まで全速(|u|=1)で進み、着いたら停止」する
#    制御族を比較して ∫V0 ds が最小のものを選び、先頭 u(t+) だけ適用する。
#    (制御族を限った argmin。原文の全許容制御での argmin ではない点に注意)
def receding_horizon(x0, T, dt=0.05, steps=200):
    G = np.linspace(-2, 2, 161)
    s = np.arange(1, int(T / dt) + 1) * dt
    x, traj = x0, [x0]
    for _ in range(steps):
        path = x + np.sign(G - x)[:, None] * np.minimum(s[None, :], np.abs(G - x)[:, None])
        g = G[np.argmin(V0(path).sum(axis=1))]
        x = x + np.sign(g - x) * min(dt, abs(g - x))
        traj.append(x)
    return np.array(traj)

runs = {"(A) 左から出発, T=0.6": receding_horizon(-0.5, 0.6),
        "(B) 右の局所谷から, T=0.6": receding_horizon(1.5, 0.6),
        "(C) 右の局所谷から, T=8.0": receding_horizon(1.5, 8.0)}

# %% 可視化
fig, ax = plt.subplots(1, 3, figsize=(14, 4))
ax[0].plot(grid, V0(grid)); ax[0].axhline(theta, ls="--", c="gray")
ax[0].axvspan(tcz_lo, tcz_hi, alpha=.2, label="TCZ={V0≤θ}")
ax[0].set_ylim(-0.6, 2); ax[0].set_title("V0 と TCZ"); ax[0].legend()
for k, tr in runs.items():
    ax[1].plot(tr, label=k)
    ax[2].plot([phi1(x) for x in tr], label=k)
ax[1].set_title("軌道 x(t)"); ax[1].legend(fontsize=7)
ax[2].set_title("残差 Φ1(t)=[V0-θ]+"); ax[2].set_xlabel("step")
plt.tight_layout(); plt.show()

# %% 数値確認
for k, tr in runs.items():
    print(f"{k}: 最終 x={tr[-1]:+.3f}, dist(x,TCZ)={dist_tcz(tr[-1]):.3f}, Φ1={phi1(tr[-1]):.3f}")
assert dist_tcz(runs["(A) 左から出発, T=0.6"][-1]) < 1e-9
assert dist_tcz(runs["(B) 右の局所谷から, T=0.6"][-1]) > 1.0     # 反例: 届かない
assert dist_tcz(runs["(C) 右の局所谷から, T=8.0"][-1]) < 1e-9

# %% (D) Lean が検証する閉ループ ẋ=-(x+1): 補題0の前提を数値でも確認
t = np.linspace(0, 6, 6001); xD = -1 + 0.5 * np.exp(-t)         # 厳密解 x(t)=-1+½e^{-t}
Phi = np.maximum(V0(xD), 0.0); dPhi = np.gradient(Phi, t)
inside = Phi > 1e-9
print("D: max(Φ'+2cΦ) (c=2/5, ≤0 なら下降条件) =", (dPhi + 0.8 * Phi)[inside][1:-1].max())
assert (dPhi + 0.8 * Phi)[inside][1:-1].max() < 1e-3
dist = np.array([dist_tcz(x) for x in xD])
assert np.all(dist**2 <= Phi / 6 + 1e-9)                          # 誤差境界 dist² ≤ Φ/6 (C=1/6)
assert np.all(dist <= np.sqrt(Phi[0] / 6) * np.exp(-0.4 * t) + 1e-9)   # 定理1の結論 dist ≤ √(CΦ0) e^{-ct}
