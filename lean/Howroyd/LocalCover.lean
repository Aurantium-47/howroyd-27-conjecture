import Howroyd.CoverBase

namespace Howroyd

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rho_add_three (n : Nat) (hn : 4 ≤ n) : rho (n + 3) = rho n := by
  unfold rho
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem covered_add_x (x y z : Nat) (hx : 5 ≤ x) :
    Covered ⟨x+3,y,z⟩ ↔ Covered ⟨x,y,z⟩ := by
  have hmod : (x+3+y+z)%3 = (x+y+z)%3 := by omega
  have hsub : x+3-1 = (x-1)+3 := by omega
  have hr := rho_add_three x (by omega)
  have hr' := rho_add_three (x-1) (by omega)
  have hp : 0 < x := by omega
  have hp' : 0 < x+3 := by omega
  simp only [Covered, localSum, weight, weightOption, ux, uy, uz, dxy, dxz, dyz,
    Vec.degree, hmod, hsub, hr, hr', hp, hp']

theorem covered_add_y (x y z : Nat) (hy : 5 ≤ y) :
    Covered ⟨x,y+3,z⟩ ↔ Covered ⟨x,y,z⟩ := by
  have hmod : (x+(y+3)+z)%3 = (x+y+z)%3 := by omega
  have hsub : y+3-1 = (y-1)+3 := by omega
  have hr := rho_add_three y (by omega)
  have hr' := rho_add_three (y-1) (by omega)
  have hp : 0 < y := by omega
  have hp' : 0 < y+3 := by omega
  simp only [Covered, localSum, weight, weightOption, ux, uy, uz, dxy, dxz, dyz,
    Vec.degree, hmod, hsub, hr, hr', hp, hp']

theorem covered_add_z (x y z : Nat) (hz : 5 ≤ z) :
    Covered ⟨x,y,z+3⟩ ↔ Covered ⟨x,y,z⟩ := by
  have hmod : (x+y+(z+3))%3 = (x+y+z)%3 := by omega
  have hsub : z+3-1 = (z-1)+3 := by omega
  have hr := rho_add_three z (by omega)
  have hr' := rho_add_three (z-1) (by omega)
  have hp : 0 < z := by omega
  have hp' : 0 < z+3 := by omega
  simp only [Covered, localSum, weight, weightOption, ux, uy, uz, dxy, dxz, dyz,
    Vec.degree, hmod, hsub, hr, hr', hp, hp']

/-- Infinite-degree proof: beyond degree 21 some coordinate is at least 8;
    subtracting 3 preserves the six keys and their existence conditions. -/
theorem covered_all (d : Nat) : 10 ≤ d → d % 3 ≠ 0 →
    ∀ x y z : Nat, x+y+z=d → Covered ⟨x,y,z⟩ := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hr x y z hs
    by_cases hb : d ≤ 21
    · exact cover_base ⟨x,by omega⟩ ⟨y,by omega⟩ ⟨z,by omega⟩
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
    · have big : 8 ≤ x ∨ 8 ≤ y ∨ 8 ≤ z := by omega
      rcases big with hx | hy | hz
      · have hsmall : x-3+y+z=d-3 := by omega
        have rec := ih (d-3) (by omega) (by omega) (by omega) (x-3) y z hsmall
        have step := (covered_add_x (x-3) y z (by omega)).mpr rec
        simpa only [show x-3+3=x by omega] using step
      · have hsmall : x+(y-3)+z=d-3 := by omega
        have rec := ih (d-3) (by omega) (by omega) (by omega) x (y-3) z hsmall
        have step := (covered_add_y x (y-3) z (by omega)).mpr rec
        simpa only [show y-3+3=y by omega] using step
      · have hsmall : x+y+(z-3)=d-3 := by omega
        have rec := ih (d-3) (by omega) (by omega) (by omega) x y (z-3) hsmall
        have step := (covered_add_z x y (z-3) (by omega)).mpr rec
        simpa only [show z-3+3=z by omega] using step

theorem covered_vertex (v : Vec) (hd : 10 ≤ v.degree) (hr : v.degree % 3 ≠ 0) :
    Covered v := by
  obtain ⟨x,y,z⟩ := v
  exact covered_all (x+y+z) hd hr x y z rfl

#print axioms cover_base
#print axioms covered_all

end Howroyd
