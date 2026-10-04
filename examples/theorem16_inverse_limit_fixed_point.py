"""
定理16 (苫米地自己意識存在・発生定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 層 α の候補集合 K_α(コンパクト凸)と整合的な射影 p で逆極限 SC = lim← K_α。
      層別フィードバック F_α が射影と可換なら連続自己写像 F:SC→SC。
      固定点の「存在」は Schauder–Tychonoff から、「一意性・幾何収束」は縮小率 L<1 を
      仮定したときの Banach から。※縮小性を原文の他条件から導く議論は原文にない。

トイ: K_n=[0,1]^n, 射影 p(x_1..x_{n+1}) = (x_1..x_n)。
      F_n(x)_k = (1-L) c_k + L (x_k + x_{k-1})/2   (x_0:=0) は下三角なので射影と可換。
      → 各層の固定点が互いに射影で一致し、無限列 S*=(s_1,s_2,..) (逆極限の元)を与える。
      収束は d(F^n S0, S*) ≤ L^n d(S0,S*) (sup距離)。
反例(縮小性の欠如): F=恒等写像は連続自己写像だが固定点が一意でない(存在のみ)。
表象: M(S)=x_1, F_Rep(r)=(1-L)c_1+L r/2 とすると M∘F=F_Rep∘M (同変)、M(S*) も固定点。

Lean 対応: Tomabechi/Examples/Theorem16_Tower.lean (theorem16_tower / layer_unique / fixedPoint_satisfies_all_layers)
           Tomabechi/Examples/Theorem16_Identity.lean (恒等写像は固定点が一意でない)
  証明範囲: 逆極限=[0,1]値の有界列空間(sup距離で完備)、縮小率 7/10、同変な表象 M(S)=S_0、一意固定点と幾何収束。
  原文の層条件(Tychonoff+Schauder型の存在)を塔で満たすことの証明は未着手(縮小性があれば Banach で存在も出る)。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

L, N = 0.7, 12
rng = np.random.default_rng(0)
c = rng.uniform(0.1, 0.9, size=N)

def F(x):                                       # 層数 len(x) の層で動く下三角写像
    prev = np.concatenate([[0.0], x[:-1]])
    return (1 - L) * c[:len(x)] + L * (x + prev) / 2

def fixed_point(n, x0, iters=200):
    x = x0[:n].copy(); errs = []
    for _ in range(iters): x = F(x)
    return x

S = fixed_point(N, np.zeros(N))
x_prev_levels = [fixed_point(n, np.ones(n)) for n in range(1, N + 1)]   # 別の初期値でも同じ?
consistency = max(np.abs(x_prev_levels[n][:n] - x_prev_levels[n - 1]).max() for n in range(1, N))

# 幾何収束
x = rng.uniform(0, 1, N); errs = []
for _ in range(40):
    errs.append(np.abs(x - S).max()); x = F(x)
errs = np.array(errs)

# 表象 M(S)=x_1 の同変性
F_rep = lambda r: (1 - L) * c[0] + L * r / 2
x = rng.uniform(0, 1, N)
equiv = abs(F(x)[0] - F_rep(x[0]))

# %% 反例: 恒等写像(縮小でない)
ident = lambda x: x
fp_a, fp_b = np.zeros(N), np.ones(N)           # どちらも固定点 → 一意でない
# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].semilogy(errs, "o-", label="d(F^n S0, S*)"); ax[0].semilogy(errs[0] * L ** np.arange(40), "--", label="L^n d(S0,S*)")
ax[0].set_title("幾何収束 (縮小率 L=0.7)"); ax[0].legend()
ax[1].bar(range(1, N + 1), S); ax[1].set_title("逆極限の元 S* の各層成分 s_k (層を増やしても不変)")
plt.tight_layout(); plt.show()

# %% 数値確認
print("層整合性(射影で一致) 最大差:", consistency)
print("表象の同変性の誤差:", equiv, " M(S*) が F_Rep の固定点:", abs(F_rep(S[0]) - S[0]) < 1e-12)
assert consistency < 1e-12 and equiv < 1e-12 and abs(F_rep(S[0]) - S[0]) < 1e-12
assert (errs[1:] <= errs[:-1] * L + 1e-12).all()
assert np.allclose(ident(fp_a), fp_a) and np.allclose(ident(fp_b), fp_b) and not np.allclose(fp_a, fp_b)
