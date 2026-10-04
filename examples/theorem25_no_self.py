"""
定理25 (諸法無我定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
(25.1) 履歴相対の固定点: 各履歴 h に縮小写像 F_h (固定点 S*_h) があり S*_h≠S*_h' なら、
       全履歴に共通する固定点 S0 は存在しない (固定点は履歴に相対的)。
(25.2) 機能的完備性 25-D: 候補自性 Σ への介入が (Γ, Y+) の同時法則を変えない ⇒ ¬Atman。
       ※ グラフの連結性・包摂構造だけからは無我は出ない(連結グラフの各点に固有の固定属性を
         付けることは可能)。決定的なのは 25-D(原文末尾「証明の射程」)。

(A) 履歴 h∈{0,1,2}, F_h(S)=(1−L)c_h+L S (R², L=0.6)。各 h で S*_h=c_h に収束、共通固定点なし。
(B) 有限SCM(決定論的): Γ∈{0,1}^2 一様(関係状態), 候補自性 Σ∈ℤ(基準は Σ=0), Y = Γ_1 − Γ_2 + β Σ。
      do(Σ=s) 後の (Γ,Y) の同時法則を全事象の列挙で厳密に求め、基準法則と比べる。
      β=0: do(Σ=s) で法則は不変 → 25-D 成立 → Σ は冗長(Atman でない)
      β=1: do(Σ=2) で {Y=2} の確率が 0 → 1/2 に変わる → 25-D 不成立 → 非冗長な「自性」が存在してしまう
      (Lean: Tomabechi/Examples/Theorem25_NoSelf.lean の scm_zero_no_atman / scm_one_has_atman)
(C) 父・母・子の逆役割関係: FatherOf(f,c) ⇔ HasFather(c,f) (25.C1) と、水平グラフの連結性の検査。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

# --- (A) ---
L = 0.6
c = {0: np.array([0.1, 0.9]), 1: np.array([0.8, 0.2]), 2: np.array([0.5, 0.5])}
F = lambda h, S: (1 - L) * c[h] + L * S
def iterate(h, S0, n=60):
    S = np.array(S0, float); path = [S.copy()]
    for _ in range(n): S = F(h, S); path.append(S.copy())
    return np.array(path)
paths = {h: iterate(h, [0.3, 0.3]) for h in c}
common = [S for S in (np.array([a, b]) for a in np.linspace(0, 1, 101) for b in np.linspace(0, 1, 101))
          if all(np.allclose(F(h, S), S, atol=1e-9) for h in c)]

# --- (B) ---
from collections import Counter
from fractions import Fraction
def law(beta, s):                                # do(Σ=s) 後の (Γ,Y) の厳密な同時法則
    cnt = Counter(((g1, g2), int(g1) - int(g2) + beta * s) for g1 in (0, 1) for g2 in (0, 1))
    return {k: Fraction(v, 4) for k, v in cnt.items()}
cands = [-1, 0, 1, 2]
invariant = {beta: all(law(beta, s) == law(beta, 0) for s in cands) for beta in (0, 1)}   # 25-D
p_y2 = {beta: (float(sum(p for (g, y), p in law(beta, 2).items() if y == 2)),
               float(sum(p for (g, y), p in law(beta, 0).items() if y == 2))) for beta in (0, 1)}

# --- (C) ---
people = ["祖父", "父", "母", "子", "叔母"]
father_of = {("祖父", "父"), ("父", "子")}; mother_of = {("母", "子"), ("祖母", "叔母")}
has_father = {(c_, f) for f, c_ in father_of}                       # 逆役割ラベル
edges = [(a, b) for a, b in father_of | mother_of | {("父", "叔母")}] # 叔母は父の姉妹 → 関係辺を1本足す
adj = {p: set() for p in people + ["祖母"]}
for a, b in edges: adj[a].add(b); adj[b].add(a)
seen, stack = set(), ["祖父"]
while stack:
    p = stack.pop()
    if p not in seen: seen.add(p); stack.extend(adj[p])
connected = seen == set(adj)

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
for h, p in paths.items(): ax[0].plot(p[:, 0], p[:, 1], "o-", ms=3, label=f"履歴{h} → S*={c[h]}")
ax[0].set_title("履歴ごとに別の固定点(共通固定点なし)"); ax[0].legend(fontsize=7)
ax[1].bar(["β=0 (25-D成立)", "β=1 (25-D不成立)"], [p_y2[0][0] - p_y2[0][1], p_y2[1][0] - p_y2[1][1]])
ax[1].set_title("do(Σ=2) による P(Y=2) の変化(基準との差)")
plt.tight_layout(); plt.show()

# %% 数値確認
print("共通固定点の個数:", len(common), " 25-D(法則不変):", invariant, " P(Y=2) [do(Σ=2), 基準]:", p_y2, " 関係グラフ連結:", connected)
assert all(np.allclose(paths[h][-1], c[h], atol=1e-9) for h in c) and len(common) == 0
assert invariant == {0: True, 1: False} and p_y2[0] == (0.0, 0.0) and p_y2[1] == (0.5, 0.0)
assert ("子", "父") in has_father and connected
