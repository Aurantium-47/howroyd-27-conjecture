import Howroyd.Basic

namespace Howroyd

/-- The paper's boundary-sensitive residue compression. -/
def rho (n : Nat) : Nat := if n ≤ 3 then n else 4 + (n - 4) % 3

/-- Three-element sorting network; the key retains all coordinate symmetries. -/
def sortedTriple (a b c : Nat) : Vec :=
  if a ≤ b then
    if b ≤ c then ⟨a,b,c⟩ else if a ≤ c then ⟨a,c,b⟩ else ⟨c,a,b⟩
  else
    if a ≤ c then ⟨b,a,c⟩ else if b ≤ c then ⟨b,c,a⟩ else ⟨c,b,a⟩

/-- Exact transcription of the 89-row CSV. Missing keys remain explicit. -/
def weightTable : Nat → Kind → Nat → Nat → Nat → Option Nat
  | 1, .down, 0, 0, 5 => some 0
  | 1, .down, 0, 1, 4 => some 30
  | 1, .down, 0, 2, 6 => some 0
  | 1, .down, 0, 3, 5 => some 5
  | 1, .down, 0, 4, 4 => some 10
  | 1, .down, 0, 5, 6 => some 3
  | 1, .down, 1, 1, 6 => some 0
  | 1, .down, 1, 2, 5 => some 22
  | 1, .down, 1, 3, 4 => some 13
  | 1, .down, 1, 4, 6 => some 15
  | 1, .down, 1, 5, 5 => some 16
  | 1, .down, 2, 2, 4 => some 3
  | 1, .down, 2, 3, 3 => some 24
  | 1, .down, 2, 3, 6 => some 17
  | 1, .down, 2, 4, 5 => some 12
  | 1, .down, 2, 6, 6 => some 10
  | 1, .down, 3, 3, 5 => some 3
  | 1, .down, 3, 4, 4 => some 24
  | 1, .down, 3, 5, 6 => some 10
  | 1, .down, 4, 4, 6 => some 17
  | 1, .down, 4, 5, 5 => some 17
  | 1, .down, 5, 6, 6 => some 17
  | 1, .up, 0, 0, 6 => some 60
  | 1, .up, 0, 1, 5 => some 0
  | 1, .up, 0, 2, 4 => some 30
  | 1, .up, 0, 3, 6 => some 30
  | 1, .up, 0, 4, 5 => some 25
  | 1, .up, 0, 6, 6 => some 32
  | 1, .up, 1, 1, 4 => some 0
  | 1, .up, 1, 2, 6 => some 0
  | 1, .up, 1, 3, 5 => some 3
  | 1, .up, 1, 4, 4 => some 4
  | 1, .up, 1, 5, 6 => some 3
  | 1, .up, 2, 2, 5 => some 16
  | 1, .up, 2, 3, 4 => some 3
  | 1, .up, 2, 4, 6 => some 8
  | 1, .up, 2, 5, 5 => some 6
  | 1, .up, 3, 3, 3 => some 3
  | 1, .up, 3, 3, 6 => some 17
  | 1, .up, 3, 4, 5 => some 3
  | 1, .up, 3, 6, 6 => some 17
  | 1, .up, 4, 4, 4 => some 3
  | 1, .up, 4, 5, 6 => some 3
  | 1, .up, 5, 5, 5 => some 3
  | 1, .up, 6, 6, 6 => some 3
  | 2, .down, 0, 0, 6 => some 0
  | 2, .down, 0, 1, 5 => some 30
  | 2, .down, 0, 2, 4 => some 0
  | 2, .down, 0, 3, 6 => some 3
  | 2, .down, 0, 4, 5 => some 3
  | 2, .down, 0, 6, 6 => some 6
  | 2, .down, 1, 1, 4 => some 0
  | 2, .down, 1, 2, 6 => some 24
  | 2, .down, 1, 3, 5 => some 15
  | 2, .down, 1, 4, 4 => some 6
  | 2, .down, 1, 5, 6 => some 8
  | 2, .down, 2, 2, 5 => some 3
  | 2, .down, 2, 3, 4 => some 24
  | 2, .down, 2, 4, 6 => some 17
  | 2, .down, 2, 5, 5 => some 3
  | 2, .down, 3, 3, 3 => some 3
  | 2, .down, 3, 3, 6 => some 3
  | 2, .down, 3, 4, 5 => some 10
  | 2, .down, 3, 6, 6 => some 3
  | 2, .down, 4, 4, 4 => some 3
  | 2, .down, 4, 5, 6 => some 3
  | 2, .down, 5, 5, 5 => some 3
  | 2, .down, 6, 6, 6 => some 3
  | 2, .up, 0, 0, 4 => some 60
  | 2, .up, 0, 1, 6 => some 0
  | 2, .up, 0, 2, 5 => some 30
  | 2, .up, 0, 3, 4 => some 30
  | 2, .up, 0, 4, 6 => some 27
  | 2, .up, 0, 5, 5 => some 30
  | 2, .up, 1, 1, 5 => some 0
  | 2, .up, 1, 2, 4 => some 0
  | 2, .up, 1, 3, 6 => some 3
  | 2, .up, 1, 4, 5 => some 9
  | 2, .up, 1, 6, 6 => some 7
  | 2, .up, 2, 2, 6 => some 12
  | 2, .up, 2, 3, 5 => some 3
  | 2, .up, 2, 4, 4 => some 3
  | 2, .up, 2, 5, 6 => some 17
  | 2, .up, 3, 3, 4 => some 3
  | 2, .up, 3, 4, 6 => some 10
  | 2, .up, 3, 5, 5 => some 3
  | 2, .up, 4, 4, 5 => some 17
  | 2, .up, 4, 6, 6 => some 17
  | 2, .up, 5, 5, 6 => some 17
  | _, _, _, _, _ => none

def weightOption (d : Nat) (t : Triangle) : Option Nat :=
  let b := sortedTriple (rho t.base.x) (rho t.base.y) (rho t.base.z)
  weightTable (d % 3) t.kind b.x b.y b.z

/-- The fallback is never used for legal triangles at an allowed degree;
    key completeness is a separate theorem in ExactCover. -/
def weight (d : Nat) (t : Triangle) : Nat := (weightOption d t).getD 0

def localSum (v : Vec) : Nat :=
  (if 0 < v.x then weight v.degree (ux v) else 0) +
  (if 0 < v.y then weight v.degree (uy v) else 0) +
  (if 0 < v.z then weight v.degree (uz v) else 0) +
  (if 0 < v.x ∧ 0 < v.y then weight v.degree (dxy v) else 0) +
  (if 0 < v.x ∧ 0 < v.z then weight v.degree (dxz v) else 0) +
  (if 0 < v.y ∧ 0 < v.z then weight v.degree (dyz v) else 0)

/-- Both the six-term equation and presence of every participating CSV key. -/
def Covered (v : Vec) : Prop :=
  (0 < v.x → (weightOption v.degree (ux v)).isSome = true) ∧
  (0 < v.y → (weightOption v.degree (uy v)).isSome = true) ∧
  (0 < v.z → (weightOption v.degree (uz v)).isSome = true) ∧
  (0 < v.x ∧ 0 < v.y → (weightOption v.degree (dxy v)).isSome = true) ∧
  (0 < v.x ∧ 0 < v.z → (weightOption v.degree (dxz v)).isSome = true) ∧
  (0 < v.y ∧ 0 < v.z → (weightOption v.degree (dyz v)).isSome = true) ∧
  localSum v = 60

instance (v : Vec) : Decidable (Covered v) := by unfold Covered; infer_instance

end Howroyd
