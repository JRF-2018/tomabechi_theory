"""
定理22 / H-stage 不変領域の範囲拡張モデル  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
Lean: Theorem22_InvariantRegion_Model.lean (toy_old_sublevel_barrier_fails ほか)。
意味: 旧入力は「初期値で決まる部分準位集合 {Ṽ≤Ṽ(x0)} 全体」が局所球 U_n の内部障壁を
      満たすことを要求していた。緩和版は「球の内側にある、より小さな前向き不変区間」だけを要求する。
      これは原文定理22の反例ではなく、証明の入力条件(H-stage)の緩和範囲を示す例。

モデル(1次元): Ṽ(x)=x/2 + x²/2 = (x+½)²/2 − 1/8  (谷 x*=−½)、局所球 U=[−1,1]、移動度1、
      閉ループ ẋ=−(x+½)、初期点 x0=½。
  - 旧: 全部分準位 {Ṽ≤Ṽ(x0)}=[−3/2, ½] は U=[−1,1] からはみ出す → 旧条件は成立しない
  - 新: I=[−½,½] は ẋ が内向きで前向き不変、かつ U の内側 → 緩和条件は成立。軌道は I に留まり、
        Ṽ(x(t))−Ṽ(x*) = e^{−2t}(Ṽ(x0)−Ṽ(x*)) と指数減衰(率 γc=1 のとき e^{−2γc t})。

Lean 対応: Tomabechi/Examples/Theorem22_HStage.lean (既存 Theorem22_InvariantRegion_Model.lean の toy* と同一)
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

V = lambda x: x / 2 + x**2 / 2
xstar, x0, ball = -0.5, 0.5, (-1.0, 1.0)

# 旧: 初期の部分準位集合 {V ≤ V(x0)} (区間 [xstar−s, xstar+s], s=|x0−xstar|)
s = abs(x0 - xstar); sub = (xstar - s, xstar + s)
sublevel_inside_ball = ball[0] < sub[0] and sub[1] < ball[1]
# 新: 前向き不変区間 I=[−½,½]
I = (-0.5, 0.5)
field = lambda x: -(x + 0.5)
invariant = field(I[0]) >= 0 and field(I[1]) <= 0                 # 端点で内向き
I_inside_ball = ball[0] < I[0] and I[1] < ball[1]

t = np.linspace(0, 5, 501); x = xstar + (x0 - xstar) * np.exp(-t)  # 厳密解
gap = V(x) - V(xstar); gap_bound = (V(x0) - V(xstar)) * np.exp(-2 * t)

# %% 可視化
xs = np.linspace(-1.8, 1.2, 400)
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].plot(xs, V(xs), c="k"); ax[0].axvspan(*ball, alpha=.1, label="局所球 U=[−1,1]")
ax[0].axvspan(*sub, ymin=0, ymax=.08, color="r", label="旧: 全部分準位(球外へ出る)"); ax[0].axvspan(*I, ymin=.1, ymax=.18, color="g", label="新: 不変区間 I")
ax[0].legend(fontsize=7); ax[0].set_title("Ṽ と 入力範囲の違い")
ax[1].semilogy(t, gap + 1e-16, label="Ṽ(x(t))−Ṽ(x*)"); ax[1].semilogy(t, gap_bound, "--", label="e^{-2t}(...)"); ax[1].legend(); ax[1].set_title("指数減衰")
plt.tight_layout(); plt.show()

# %% 数値確認
print("旧部分準位:", sub, "球の内側?", sublevel_inside_ball, "| 新不変区間:", I, "不変?", invariant, "球の内側?", I_inside_ball)
assert not sublevel_inside_ball and invariant and I_inside_ball
assert np.all((x >= I[0] - 1e-12) & (x <= I[1] + 1e-12)) and np.allclose(gap, gap_bound, atol=1e-12)
