import Theorem16_25_Core

/-!
# 定理16の Python 例 (`examples/theorem16_inverse_limit_fixed_point.py`) の反例部の Lean 根拠

Python の反例は「恒等写像 `ident` は連続自己写像だが固定点が一意でない（`fp_a=0` と `fp_b=1` がともに固定点）」。
Lean では `Theorem16_25_Core` の既存補題が、コンパクト凸な単位区間上でこれを証明している。
* 存在のみ（一意性は縮小性などの追加条件が必要）: `identity_on_unitInterval_nonunique`
* 自然な距離では縮小写像でない: `identity_on_unitInterval_not_contracting`

これは原文定理16の反例ではなく、「縮小条件を外すと一意性節が成り立たない」ことの例。
-/

namespace Tomabechi.Examples.Theorem16

alias identity_fixedPoints_not_unique := Tomabechi.Theorem16_25.identity_on_unitInterval_nonunique
alias identity_not_contracting := Tomabechi.Theorem16_25.identity_on_unitInterval_not_contracting

end Tomabechi.Examples.Theorem16
