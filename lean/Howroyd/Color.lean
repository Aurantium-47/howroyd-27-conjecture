import Howroyd.Geometry

namespace Howroyd

/-- This is integer `x - y` modulo three, written without truncated subtraction. -/
def color (v : Vec) : Nat := (v.x + 2 * v.y) % 3

def colorClass (d j : Nat) : Finset Vec := (vertices d).filter fun v => color v = j

theorem color_lt_three (v : Vec) : color v < 3 := Nat.mod_lt _ (by decide)

theorem color_eq_int_mod (v : Vec) :
    (color v : Int) = ((v.x : Int) - (v.y : Int)) % 3 := by
  unfold color
  omega

theorem color_ne_of_adj {u v : Vec} (hd : u.degree = v.degree)
    (ha : l1Distance u v = 2) : color u ≠ color v := by
  dsimp [Vec.degree] at hd
  dsimp [l1Distance, Nat.dist] at ha
  unfold color
  omega

theorem colorClass_independent (d j : Nat) : Independent (colorClass d j) := by
  intro u hu v hv _ ha
  simp only [colorClass, Finset.mem_filter, mem_vertices] at hu hv
  exact color_ne_of_adj (hu.1.trans hv.1.symm) ha (hu.2.trans hv.2.symm)

theorem triVertices_filter_color_card (t : Triangle) (j : Nat) (hj : j < 3) :
    ((triVertices t).filter fun v => color v = j).card = 1 := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k
  all_goals simp only [triVertices, Finset.filter_insert, Finset.filter_singleton]
  all_goals split_ifs <;> simp [Vec.mk.injEq] <;> dsimp [color] at * <;> omega

theorem colorClass_inter_triangle_card {d j : Nat} {t : Triangle}
    (ht : t.Valid d) (hj : j < 3) : ((colorClass d j) ∩ triVertices t).card = 1 := by
  have heq : colorClass d j ∩ triVertices t =
      (triVertices t).filter (fun v => color v = j) := by
    ext v
    simp only [Finset.mem_inter, colorClass, Finset.mem_filter, mem_vertices]
    exact ⟨fun h => ⟨h.2, h.1.2⟩,
      fun h => ⟨⟨triVertices_degree ht h.1, h.2⟩, h.1⟩⟩
  rw [heq]
  exact triVertices_filter_color_card t j hj

end Howroyd
