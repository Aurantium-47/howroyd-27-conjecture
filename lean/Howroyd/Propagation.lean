import Howroyd.PositiveWeights
import Howroyd.Saturation
import Howroyd.Balancing

namespace Howroyd

def selected (I : Finset Vec) (v : Vec) : Nat := if v ∈ I then 1 else 0

theorem selected_eq_one (I : Finset Vec) (v : Vec) : selected I v = 1 ↔ v ∈ I := by
  simp [selected]

theorem card_inter_three (I : Finset Vec) (a b c : Vec)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (I ∩ {a,b,c}).card = selected I a + selected I b + selected I c := by
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter]
  by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> by_cases hc : c ∈ I <;>
    simp [Finset.filter_insert, Finset.filter_singleton, selected, ha, hb, hc,
      hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem selected_moveX (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (v : Vec)
    (hv : Body d v) (hy : v.y ≤ v.x) (hz : v.z ≤ v.x) :
    selected I (moveX v) = selected I v := by
  rcases v with ⟨x,y,z⟩
  dsimp only at hy hz
  have hs : x+y+z=d := hv.1
  have hx : 4 ≤ x := by omega
  have hpos := balancing_weights_x d x y z hd hr hs hy hz hv.2.1
  have hu : (Triangle.mk .up ⟨x-1,y,z⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x-2,y,z⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have su := maximum_saturates d hd hr I hI _ hu hpos.1
  have sl := maximum_saturates d hd hr I hI _ hl hpos.2
  have e1 : x-1+1=x := by omega
  have e2 : x-2+1=x-1 := by omega
  simp only [triVertices,e1,e2] at su sl
  rw [card_inter_three] at su sl
  · simp only [moveX]
    omega
  all_goals simp only [ne_eq,Vec.mk.injEq]; omega

theorem selected_moveY (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (v : Vec)
    (hv : Body d v) (hx : v.x ≤ v.y) (hz : v.z ≤ v.y) :
    selected I (moveY v) = selected I v := by
  rcases v with ⟨x,y,z⟩
  dsimp only at hx hz
  have hs : x+y+z=d := hv.1
  have hy : 4 ≤ y := by omega
  have hpos := balancing_weights_y d x y z hd hr hs hx hz hv.2.2.1
  have hu : (Triangle.mk .up ⟨x,y-1,z⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x,y-2,z⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have su := maximum_saturates d hd hr I hI _ hu hpos.1
  have sl := maximum_saturates d hd hr I hI _ hl hpos.2
  have e1 : y-1+1=y := by omega
  have e2 : y-2+1=y-1 := by omega
  simp only [triVertices,e1,e2] at su sl
  rw [card_inter_three] at su sl
  · simp only [moveY]
    omega
  all_goals simp only [ne_eq,Vec.mk.injEq]; omega

theorem selected_moveZ (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (v : Vec)
    (hv : Body d v) (hx : v.x ≤ v.z) (hy : v.y ≤ v.z) :
    selected I (moveZ v) = selected I v := by
  rcases v with ⟨x,y,z⟩
  dsimp only at hx hy
  have hs : x+y+z=d := hv.1
  have hz : 4 ≤ z := by omega
  have hpos := balancing_weights_z d x y z hd hr hs hx hy hv.2.2.2
  have hu : (Triangle.mk .up ⟨x,y,z-1⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have hl : (Triangle.mk .down ⟨x,y,z-2⟩).Valid d := by
    simp only [Triangle.Valid,Vec.degree]; omega
  have su := maximum_saturates d hd hr I hI _ hu hpos.1
  have sl := maximum_saturates d hd hr I hI _ hl hpos.2
  have e1 : z-1+1=z := by omega
  have e2 : z-2+1=z-1 := by omega
  simp only [triVertices,e1,e2] at su sl
  rw [card_inter_three] at su sl
  · simp only [moveZ]
    omega
  all_goals simp only [ne_eq,Vec.mk.injEq]; omega

theorem maximum_preserves_maxMoves (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) : PreservesMaxMoves d (selected I) := by
  intro v w hv hm
  rcases hm with ⟨hy,hz,rfl⟩ | ⟨hx,hz,rfl⟩ | ⟨hx,hy,rfl⟩
  · exact selected_moveX d hd hr I hI v hv hy hz
  · exact selected_moveY d hd hr I hI v hv hx hz
  · exact selected_moveZ d hd hr I hI v hv hx hy

/-- The abstract balancing lemma is now instantiated for genuine maximum sets. -/
theorem maximum_body_color_constancy (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (u v : Vec)
    (hu : Body d u) (hv : Body d v) (hc : color u=color v) :
    selected I u=selected I v := by
  have he : 3*(d/3)+d%3=d := by omega
  have hf := maximum_preserves_maxMoves d hd hr I hI
  have h := body_color_constancy (k:=d/3) (r:=d%3) (by omega) (by omega)
    (selected I) (by simpa only [he] using hf)
    (by simpa only [he] using hu) (by simpa only [he] using hv) hc
  exact h

#print axioms maximum_body_color_constancy

end Howroyd
