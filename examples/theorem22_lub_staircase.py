"""
定理22 (苫米地高高度LUB臨場感定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: u_{n+1}=u_n ∨ v_{n+1} (22.1)。新情報 v_{n+1}≰u_n なら u_n≺u_{n+1} (22.3)。
      各段で局所谷(強凸)に収束してから次段へ切り替える。切替状態が次段の吸引域に入ること(可到達性)
      と時間尺度分離が仮定される。※LUB更新の式だけからは到達性は出ない(原文は明示仮定)。

トイ: 束 𝕃=8要素集合の部分集合(ビット)。段 n の谷の中心を x_n=|u_n|(要素数)に取る1次元モデル。
      各段 Ṽ_n(x) = −A exp(−(x−x_n)²/(2σ²)) (ガウス谷; 中心付近で強凸、遠方はほぼ平坦)。
      ẋ=−∇Ṽ_n。段 n は T_n 秒だけ適用して次段へ切替。
  ガウス谷は |x-x_n|<σ で強凸。Lean(Theorem22_LubStaircase.lean)では A=2, σ=3/2、局所球半径 r=1 を使い
  ddwell>0 (強凸) と「前段の終点が次段の局所球内か」を証明している。Theorem22_GaussianStages.lean は
  半径 5/4・曲率下界 1/8 の局所球で、A/C の連続切替軌道を扱う (下の Lean 対応)。
  ケースA: 毎回1要素ずつ新情報 → δ_n=1 ≤ r: 前段の終点が次段の局所球・吸引域内 → 階段を登る
  ケースB: 6要素→2要素 → δ=6=4σ>r: 終点が次段の平坦部 → 時間をかけても動けず階段が止まる(反例)

Lean 対応: Tomabechi/Examples/Theorem22_LubStaircase.lean + Tomabechi/Examples/Gaussian.lean +
  Tomabechi/Examples/Theorem22_GaussianStages.lean
  証明範囲: 束の (22.1)(22.3)、ガウス谷の局所強凸(ddwell>0, r=1<σ=3/2)、前段の終点が次段の局所球内(A)/外(B)。
  連続時間の切替軌道: A の中心列 1,2,3,4,4,… と C の中心列 1,1,2,2,… について、段ごとの ODE 解を 12 秒ずつ
  つないだ軌道、段内の一意性、中心への距離の指数減衰 (率 1/2)、待ち時間条件 (22.5)、各段の 12 秒後の誤差 ≤1/8。
  B は初期値 0 から中心 6 へ向かう大域解が、12 秒後も次の中心 8 の局所球 (半径 5/4) の外にあること。
  証明していないもの: Python の Euler 離散列と数値出力、一般の段階条件から具体ガウスモデルを導くこと、23-B 一般核の適用。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

A, sigma, T_stage, dt = 2.0, 1.5, 12.0, 0.01     # Lean 側 (Theorem22_LubStaircase.lean) と同じ A=2, σ=3/2
popcount = lambda b: bin(b).count("1")

def staircase(new_infos):
    u = 0b00000000; us = [u]
    for v in new_infos:
        u = u | v; us.append(u)                      # u_{n+1} = u_n ∨ v_{n+1}
    centers = [popcount(b) for b in us]
    x, traj, t_switch = float(centers[0]), [], [0]
    for xc in centers[1:]:
        for _ in range(int(T_stage / dt)):
            grad = A * (x - xc) / sigma**2 * np.exp(-(x - xc)**2 / (2 * sigma**2))   # ∇Ṽ_n
            x -= dt * grad; traj.append(x)
        t_switch.append(len(traj))
    return us, centers, np.array(traj), t_switch

casesA = staircase([0b00000001, 0b00000010, 0b00000100, 0b00001000])     # 1要素ずつ
casesB = staircase([0b00111111, 0b11000000])                         # 6要素→2要素
casesC = staircase([0b00000001, 0b00000001, 0b00000011])               # v≤u_n の入力が混じる

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(12, 4))
for (us, cen, tr, ts), lab in [(casesA, "A: 1要素ずつ(δ=1)"), (casesB, "B: 6要素→2要素(δ=6)")]:
    ax[0].plot(np.arange(len(tr)) * dt, tr, label=lab)
    for k, c in enumerate(cen[1:]): ax[0].hlines(c, k * T_stage, (k + 1) * T_stage, ls=":", colors="gray")
ax[0].set_xlabel("t"); ax[0].set_ylabel("x"); ax[0].legend(); ax[0].set_title("段階切替軌道(点線は各段の谷の中心 x_n)")
ax[1].step(range(len(casesC[1])), casesC[1], where="post", label="C: |u_n| (v≤u_n の入力では増えない)")
ax[1].step(range(len(casesA[1])), casesA[1], where="post", label="A: |u_n|"); ax[1].legend(); ax[1].set_title("(22.3): 非包摂入力のときだけ u_n≺u_{n+1}")
plt.tight_layout(); plt.show()

# %% 数値確認
usA, cenA, trA, tsA = casesA
usB, cenB, trB, tsB = casesB
print("A: 各段末の x =", [round(trA[i - 1], 3) for i in tsA[1:]], " 谷中心 =", cenA[1:])
print("B: 各段末の x =", [round(trB[i - 1], 3) for i in tsB[1:]], " 谷中心 =", cenB[1:])
assert all(abs(trA[i - 1] - c) < 0.05 for i, c in zip(tsA[1:], cenA[1:]))        # A: 各谷に到達
assert abs(trB[tsB[1] - 1] - cenB[1]) > 2.5                                     # B: 次の谷に入れない
assert casesC[1] == [0, 1, 1, 2] and casesA[1] == [0, 1, 2, 3, 4]               # (22.3)
