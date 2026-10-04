"""
定理4 (苫米地臨場感加重定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: Ṽ = V0 − κ P Q (P∈[0,1] 臨場感, Q∈[-1,1] 価値符号)。点ごとに ∂Ṽ/∂P = −κQ。
      Q>0 なら臨場感を上げると実効コストが下がり、Q<0 なら上がる。
      ※ 介入変数 r が P と Q を同時に動かすなら dṼ/dr = −κ(Q dP/dr + P dQ/dr) で、
        総変化の符号には追加条件が要る(原文「証明」末尾)。

(A) 1次元地形: V0 は x=+1 に最小。x=-1 に臨場感の山 P(x)=exp(-(x+1)^2)。
    Q=+1 なら -1 側の谷が深まり、Q=-1 なら山(障壁)になる。勾配降下の行き先が変わる。
(B) 介入 r: P(r)=r, Q(r)=1−2r。P は増えているのに、r>1/4 では Ṽ が"上がる"。

Lean 対応: Tomabechi/Examples/Theorem4_PresenceWeight.lean
  証明範囲: ∂Ṽ/∂P=-κQ、介入時の符号反転(r>1/4)。Q=±1 の臨界点 (Q=+1: (-0.6,-0.4)、Q=-1: (1,1.5) に一意)、
  初期値 x=-0.8 から出る連続時間の勾配流の大域存在・谷の入口への有限時間到達・谷内の指数減衰 (距離と
  ポテンシャル差)。Q=+1 は閾値 0 の TCZ へ有限時間で入り以後出ず、Q=-1 は閾値 0 の TCZ が空。Q=0 は厳密な閉形式流。
  証明していないもの: Euler 離散軌道・図中の収束先の近似値 (-0.52, +1.10)、他の初期値の挙動、
  一般の非凸ポテンシャルに対する補題0の条件の導出。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

kappa = 2.0
V0 = lambda x: 0.5 * (x - 1)**2
P = lambda x: np.exp(-(x + 1)**2)
Vt = lambda x, Q: V0(x) - kappa * P(x) * Q
dVt = lambda x, Q, h=1e-5: (Vt(x + h, Q) - Vt(x - h, Q)) / (2 * h)

def descend(x, Q, lr=0.05, n=3000):
    for _ in range(n): x -= lr * dVt(x, Q)
    return x

xs = np.linspace(-3, 3, 600)
ends = {Q: descend(-0.8, Q) for Q in (+1, 0, -1)}

# %% (B) 介入 r
r = np.linspace(0, 1, 200)
Vr = 1.0 - kappa * r * (1 - 2 * r)           # V0 を定数1とした実効コスト
dVr = -kappa * ((1 - 2 * r) * 1 + r * (-2))   # −κ(Q dP/dr + P dQ/dr)

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(12, 4))
for Q in (+1, 0, -1): ax[0].plot(xs, Vt(xs, Q), label=f"Q={Q:+d} → 収束先 x={ends[Q]:+.2f}")
ax[0].set_title("実効コスト Ṽ=V0−κPQ (x=-0.8 から勾配降下)"); ax[0].legend(); ax[0].set_ylim(-2, 4)
ax[1].plot(r, Vr, label="Ṽ(r)"); ax[1].plot(r, dVr, label="dṼ/dr"); ax[1].axhline(0, c="gray")
ax[1].axvline(0.25, ls="--", c="k"); ax[1].set_title("P↑でも Ṽ が上がる区間 (r>1/4)"); ax[1].legend()
plt.tight_layout(); plt.show()

# %% 数値確認
print({Q: round(float(v), 3) for Q, v in ends.items()})
assert ends[+1] < 0 < ends[-1]                 # Q の符号で行き先が変わる
assert (dVr[r > 0.3] > 0).all() and (dVr[r < 0.2] < 0).all()
