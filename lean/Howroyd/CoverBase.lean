import Howroyd.Weights

namespace Howroyd

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All 1134 vertex equations in the base degree range, with key presence.
    This is a closed finite proposition checked by reduction in the kernel. -/
theorem cover_base : ∀ x y z : Fin 22,
    10 ≤ x.val + y.val + z.val → x.val + y.val + z.val ≤ 21 →
    (x.val + y.val + z.val) % 3 ≠ 0 → Covered ⟨x.val,y.val,z.val⟩ := by
  decide +kernel

#print axioms cover_base

end Howroyd
