import Howroyd.ExactCover

namespace Howroyd

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def upZeroPair (a b : Nat) : Prop :=
  (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) ∨ (a=1 ∧ b=1) ∨ (a=1 ∧ b=2) ∨ (a=2 ∧ b=1)

def downZeroPair (a b : Nat) : Prop :=
  (a=0 ∧ b=0) ∨ (a=0 ∧ b=2) ∨ (a=2 ∧ b=0) ∨ (a=1 ∧ b=1)

def zeroPattern (k : Kind) (a b c : Nat) : Prop :=
  let pair := match k with | .up => upZeroPair | .down => downZeroPair
  (pair a b ∧ 4 ≤ c) ∨ (pair a c ∧ 4 ≤ b) ∨ (pair b c ∧ 4 ≤ a)

instance (k : Kind) (a b c : Nat) : Decidable (zeroPattern k a b c) := by
  cases k <;> unfold zeroPattern upZeroPair downZeroPair <;> infer_instance

private theorem zero_up_table : ∀ r : Fin 3, ∀ a b c : Fin 7,
    let s := sortedTriple a.val b.val c.val
    let w := weightTable r.val .up s.x s.y s.z
    w.isSome = true → (w.getD 0 = 0 ↔ zeroPattern .up a.val b.val c.val) := by
  decide +kernel

private theorem zero_down_table : ∀ r : Fin 3, ∀ a b c : Fin 7,
    let s := sortedTriple a.val b.val c.val
    let w := weightTable r.val .down s.x s.y s.z
    w.isSome = true → (w.getD 0 = 0 ↔ zeroPattern .down a.val b.val c.val) := by
  decide +kernel

theorem rho_lt_seven (n : Nat) : rho n < 7 := by
  unfold rho
  split_ifs <;> omega

theorem rho_eq_small (n a : Nat) (ha : a ≤ 3) : rho n = a ↔ n = a := by
  unfold rho
  split_ifs <;> omega

theorem rho_ge_four (n : Nat) : 4 ≤ rho n ↔ 4 ≤ n := by
  unfold rho
  split_ifs <;> omega

theorem zeroPattern_rho (k : Kind) (a b c : Nat) :
    zeroPattern k (rho a) (rho b) (rho c) ↔ zeroPattern k a b c := by
  cases k <;> simp only [zeroPattern, upZeroPair, downZeroPair,
    rho_eq_small _ 0 (by omega), rho_eq_small _ 1 (by omega),
    rho_eq_small _ 2 (by omega), rho_ge_four]

/-- The exact zero patterns hold for actual, uncompressed base coordinates. -/
theorem weight_zero_iff (d : Nat) (t : Triangle)
    (hkey : (weightOption d t).isSome = true) :
    weight d t = 0 ↔ zeroPattern t.kind t.base.x t.base.y t.base.z := by
  let r : Fin 3 := ⟨d%3, Nat.mod_lt _ (by omega)⟩
  let a : Fin 7 := ⟨rho t.base.x, rho_lt_seven _⟩
  let b : Fin 7 := ⟨rho t.base.y, rho_lt_seven _⟩
  let c : Fin 7 := ⟨rho t.base.z, rho_lt_seven _⟩
  have ht : weight d t = 0 ↔ zeroPattern t.kind (rho t.base.x) (rho t.base.y)
      (rho t.base.z) := by
    cases hk : t.kind
    · simpa only [weight,weightOption,hk,r,a,b,c] using
        zero_up_table r a b c (by simpa only [weightOption,hk] using hkey)
    · simpa only [weight,weightOption,hk,r,a,b,c] using
        zero_down_table r a b c (by simpa only [weightOption,hk] using hkey)
  exact ht.trans (zeroPattern_rho _ _ _ _)

/-- Positivity needed by the balancing move, with the first coordinate maximal. -/
theorem balancing_weights_x (d x y z : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (hs : x+y+z=d) (hy : y ≤ x) (hz : z ≤ x) (hb : x ≤ d-4) :
    0 < weight d ⟨.up,⟨x-1,y,z⟩⟩ ∧ 0 < weight d ⟨.down,⟨x-2,y,z⟩⟩ := by
  have hx : 4 ≤ x := by omega
  have hu : (Triangle.mk .up ⟨x-1,y,z⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x-2,y,z⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have ku := legal_key_defined d hd hr _ hu
  have kl := legal_key_defined d hd hr _ hl
  have eu := weight_zero_iff d ⟨.up,⟨x-1,y,z⟩⟩ ku
  have el := weight_zero_iff d ⟨.down,⟨x-2,y,z⟩⟩ kl
  have nu : ¬zeroPattern .up (x-1) y z := by
    unfold zeroPattern upZeroPair; omega
  have nl : ¬zeroPattern .down (x-2) y z := by
    unfold zeroPattern downZeroPair; omega
  constructor
  · exact Nat.pos_of_ne_zero (fun h => nu (eu.mp h))
  · exact Nat.pos_of_ne_zero (fun h => nl (el.mp h))

#print axioms weight_zero_iff
#print axioms balancing_weights_x

theorem balancing_weights_y (d x y z : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (hs : x+y+z=d) (hx : x ≤ y) (hz : z ≤ y) (hb : y ≤ d-4) :
    0 < weight d ⟨.up,⟨x,y-1,z⟩⟩ ∧ 0 < weight d ⟨.down,⟨x,y-2,z⟩⟩ := by
  have hy : 4 ≤ y := by omega
  have hu : (Triangle.mk .up ⟨x,y-1,z⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x,y-2,z⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have eu := weight_zero_iff d ⟨.up,⟨x,y-1,z⟩⟩ (legal_key_defined d hd hr _ hu)
  have el := weight_zero_iff d ⟨.down,⟨x,y-2,z⟩⟩ (legal_key_defined d hd hr _ hl)
  have nu : ¬zeroPattern .up x (y-1) z := by
    unfold zeroPattern upZeroPair; omega
  have nl : ¬zeroPattern .down x (y-2) z := by
    unfold zeroPattern downZeroPair; omega
  exact ⟨Nat.pos_of_ne_zero (fun h => nu (eu.mp h)),
    Nat.pos_of_ne_zero (fun h => nl (el.mp h))⟩

theorem balancing_weights_z (d x y z : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (hs : x+y+z=d) (hx : x ≤ z) (hy : y ≤ z) (hb : z ≤ d-4) :
    0 < weight d ⟨.up,⟨x,y,z-1⟩⟩ ∧ 0 < weight d ⟨.down,⟨x,y,z-2⟩⟩ := by
  have hz : 4 ≤ z := by omega
  have hu : (Triangle.mk .up ⟨x,y,z-1⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x,y,z-2⟩).Valid d := by
    simp only [Triangle.Valid, Vec.degree]; omega
  have eu := weight_zero_iff d ⟨.up,⟨x,y,z-1⟩⟩ (legal_key_defined d hd hr _ hu)
  have el := weight_zero_iff d ⟨.down,⟨x,y,z-2⟩⟩ (legal_key_defined d hd hr _ hl)
  have nu : ¬zeroPattern .up x y (z-1) := by
    unfold zeroPattern upZeroPair; omega
  have nl : ¬zeroPattern .down x y (z-2) := by
    unfold zeroPattern downZeroPair; omega
  exact ⟨Nat.pos_of_ne_zero (fun h => nu (eu.mp h)),
    Nat.pos_of_ne_zero (fun h => nl (el.mp h))⟩

end Howroyd
