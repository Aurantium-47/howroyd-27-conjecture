import Howroyd.Basic

namespace Howroyd

@[simp] theorem l1Distance_self (v : Vec) : l1Distance v v = 0 := by
  simp [l1Distance]

theorem l1Distance_comm (u v : Vec) : l1Distance u v = l1Distance v u := by
  simp [l1Distance, Nat.dist_comm]

theorem adj_irrefl {d : Nat} (v : Vertex d) : ¬Adj v v := by
  simp [Adj]

def graph (d : Nat) : SimpleGraph (Vertex d) where
  Adj := Adj
  symm := by
    intro u v h
    change l1Distance v.val u.val = 2
    rw [l1Distance_comm]
    exact h
  loopless := adj_irrefl

theorem triVertices_card (t : Triangle) : (triVertices t).card = 3 := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp [triVertices, Vec.mk.injEq]

theorem triVertices_degree {d : Nat} {t : Triangle} (ht : t.Valid d)
    {v : Vec} (hv : v ∈ triVertices t) : v.degree = d := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp only [triVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  all_goals rcases hv with rfl | rfl | rfl
  all_goals (simp_all [Triangle.Valid, Vec.degree]; omega)

theorem triVertices_clique {t : Triangle} {u v : Vec}
    (hu : u ∈ triVertices t) (hv : v ∈ triVertices t) (hne : u ≠ v) :
    l1Distance u v = 2 := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp only [triVertices, Finset.mem_insert, Finset.mem_singleton] at hu hv
  all_goals rcases hu with rfl | rfl | rfl
  all_goals rcases hv with rfl | rfl | rfl
  all_goals simp_all [l1Distance, Nat.dist]

theorem Independent.card_inter_triVertices_le_one {I : Finset Vec}
    (hI : Independent I) (t : Triangle) : (I ∩ triVertices t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  by_contra hne
  exact hI u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1 hne
    (triVertices_clique (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hv).2 hne)

theorem triVertices_lowerBound_x (t : Triangle) (n : Nat) :
    (∀ v ∈ triVertices t, n ≤ v.x) ↔ n ≤ t.base.x := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp [triVertices] <;> omega

theorem triVertices_lowerBound_y (t : Triangle) (n : Nat) :
    (∀ v ∈ triVertices t, n ≤ v.y) ↔ n ≤ t.base.y := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp [triVertices] <;> omega

theorem triVertices_lowerBound_z (t : Triangle) (n : Nat) :
    (∀ v ∈ triVertices t, n ≤ v.z) ↔ n ≤ t.base.z := by
  rcases t with ⟨k, ⟨x, y, z⟩⟩
  cases k <;> simp [triVertices] <;> omega

/-- Legal triangle indices do not introduce duplicate geometric triangles. -/
theorem triVertices_injective_of_valid {d : Nat} {t s : Triangle}
    (ht : t.Valid d) (hs : s.Valid d) (heq : triVertices t = triVertices s) : t = s := by
  have hx : t.base.x = s.base.x := by
    apply Nat.le_antisymm
    · apply (triVertices_lowerBound_x s _).mp
      rw [← heq]
      exact (triVertices_lowerBound_x t _).mpr (le_refl _)
    · apply (triVertices_lowerBound_x t _).mp
      rw [heq]
      exact (triVertices_lowerBound_x s _).mpr (le_refl _)
  have hy : t.base.y = s.base.y := by
    apply Nat.le_antisymm
    · apply (triVertices_lowerBound_y s _).mp
      rw [← heq]
      exact (triVertices_lowerBound_y t _).mpr (le_refl _)
    · apply (triVertices_lowerBound_y t _).mp
      rw [heq]
      exact (triVertices_lowerBound_y s _).mpr (le_refl _)
  have hz : t.base.z = s.base.z := by
    apply Nat.le_antisymm
    · apply (triVertices_lowerBound_z s _).mp
      rw [← heq]
      exact (triVertices_lowerBound_z t _).mpr (le_refl _)
    · apply (triVertices_lowerBound_z t _).mp
      rw [heq]
      exact (triVertices_lowerBound_z s _).mpr (le_refl _)
  rcases t with ⟨kt, ⟨xt, yt, zt⟩⟩
  rcases s with ⟨ks, ⟨xs, ys, zs⟩⟩
  simp only at hx hy hz
  subst xs; subst ys; subst zs
  cases kt <;> cases ks <;> simp_all [Triangle.Valid, Vec.degree] <;> omega

theorem mem_incidentTriangles_iff {d : Nat} {v : Vec} (hd : v.degree = d)
    (t : Triangle) : t ∈ incidentTriangles v ↔ t.Valid d ∧ v ∈ triVertices t := by
  rcases v with ⟨x, y, z⟩
  rcases t with ⟨k, ⟨a, b, c⟩⟩
  cases k
  all_goals by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals simp_all [incidentTriangles, ux, uy, uz, dxy, dxz, dyz,
    Triangle.Valid, triVertices, Vec.degree, Triangle.mk.injEq, Vec.mk.injEq]
  all_goals omega

theorem mem_vecBox (d : Nat) (v : Vec) :
    v ∈ vecBox d ↔ v.x ≤ d ∧ v.y ≤ d ∧ v.z ≤ d := by
  unfold vecBox
  constructor
  · intro hv
    obtain ⟨⟨⟨x, y⟩, z⟩, hp, rfl⟩ := Finset.mem_image.mp hv
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range] at hp
    dsimp only
    omega
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨((v.x, v.y), v.z), ?_, by cases v; rfl⟩
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega

@[simp] theorem mem_vertices (d : Nat) (v : Vec) :
    v ∈ vertices d ↔ v.degree = d := by
  simp only [vertices, Finset.mem_filter, mem_vecBox]
  constructor
  · exact fun h => h.2
  · intro h
    dsimp [Vec.degree] at h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

@[simp] theorem mem_triangles (d : Nat) (t : Triangle) :
    t ∈ triangles d ↔ t.Valid d := by
  simp only [triangles, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hb : t.base ∈ vecBox d := by
      rw [mem_vecBox]
      dsimp [Triangle.Valid, Vec.degree] at h
      cases t.kind <;> omega
    cases t with
    | mk k b =>
      cases k
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

/-- Every incident triangle is listed once as an element of the local finite set. -/
theorem triangles_filter_eq_incident {d : Nat} {v : Vec} (hd : v.degree = d) :
    (triangles d).filter (fun t => v ∈ triVertices t) = incidentTriangles v := by
  ext t
  simp only [Finset.mem_filter, mem_triangles, mem_incidentTriangles_iff hd]

/-- The six local terms are an exact expansion of the sum over actual incident triangles. -/
theorem sum_incidentTriangles (f : Triangle → Nat) (v : Vec) :
    (∑ t ∈ incidentTriangles v, f t) =
      (if 0 < v.x then f (ux v) else 0) +
      (if 0 < v.y then f (uy v) else 0) +
      (if 0 < v.z then f (uz v) else 0) +
      (if 0 < v.x ∧ 0 < v.y then f (dxy v) else 0) +
      (if 0 < v.x ∧ 0 < v.z then f (dxz v) else 0) +
      (if 0 < v.y ∧ 0 < v.z then f (dyz v) else 0) := by
  rcases v with ⟨x, y, z⟩
  have hxne : 0 < x → x - 1 ≠ x := by omega
  have hxne' : 0 < x → x ≠ x - 1 := by omega
  have hyne : 0 < y → y - 1 ≠ y := by omega
  have hyne' : 0 < y → y ≠ y - 1 := by omega
  have hzne : 0 < z → z - 1 ≠ z := by omega
  have hzne' : 0 < z → z ≠ z - 1 := by omega
  by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [incidentTriangles, hx, hy, hz, hxne, hxne', hyne, hyne', hzne, hzne',
      Finset.sum_union,
      Finset.disjoint_left, ux, uy, uz, dxy, dxz, dyz,
      Triangle.mk.injEq, Vec.mk.injEq]
  all_goals omega

@[simp] theorem mem_maximumIndependentSets (d : Nat) (I : Finset Vec) :
    I ∈ maximumIndependentSets d ↔ MaximumIndependent d I := by
  classical
  simp only [maximumIndependentSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

end Howroyd


