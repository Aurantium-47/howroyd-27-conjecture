import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Howroyd.ExactCover
import Howroyd.Color

namespace Howroyd

/-- Interchanging finite sums counts each selected vertex with its triangle weights. -/
theorem weighted_incidence (d : Nat) (I : Finset Vec) :
    (∑ t ∈ triangles d, weight d t * (I ∩ triVertices t).card) =
      ∑ v ∈ I, ∑ t ∈ (triangles d).filter (fun t => v ∈ triVertices t), weight d t := by
  calc
    _ = ∑ t ∈ triangles d, ∑ v ∈ I, if v ∈ triVertices t then weight d t else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter, Nat.mul_comm]
    _ = ∑ v ∈ I, ∑ t ∈ triangles d, if v ∈ triVertices t then weight d t else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

/-- The exact cover gives total incidence weight sixty times the selected cardinality. -/
theorem weighted_incidence_eq (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : I ⊆ vertices d) :
    (∑ t ∈ triangles d, weight d t * (I ∩ triVertices t).card) = 60 * I.card := by
  rw [weighted_incidence]
  calc
    _ = ∑ _v ∈ I, 60 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact exact_cover d hd hr v ((mem_vertices d v).mp (hI hv))
    _ = _ := by simp [Nat.mul_comm]

/-- A fixed color class realizes the total weight because it meets every triangle once. -/
theorem total_triangle_weight (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0) :
    (∑ t ∈ triangles d, weight d t) = 60 * (colorClass d 0).card := by
  have hsub : colorClass d 0 ⊆ vertices d := Finset.filter_subset _ _
  calc
    _ = ∑ t ∈ triangles d, weight d t * (colorClass d 0 ∩ triVertices t).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [colorClass_inter_triangle_card ((mem_triangles d t).mp ht) (by decide : 0 < 3)]
      simp
    _ = _ := weighted_incidence_eq d hd hr (colorClass d 0) hsub

/-- Every independent set has cardinality at most that of a color class. -/
theorem independent_card_le_colorClass (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hsub : I ⊆ vertices d) (hI : Independent I) :
    I.card ≤ (colorClass d 0).card := by
  have h : 60 * I.card ≤ 60 * (colorClass d 0).card := by
    rw [← weighted_incidence_eq d hd hr I hsub, ← total_triangle_weight d hd hr]
    apply Finset.sum_le_sum
    intro t _
    simpa using Nat.mul_le_mul_left (weight d t) (hI.card_inter_triVertices_le_one t)
  omega

/-- The standard color class is a maximum independent set. -/
theorem colorClass_maximum (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0) :
    MaximumIndependent d (colorClass d 0) := by
  refine ⟨Finset.filter_subset _ _, colorClass_independent d 0, ?_⟩
  intro I hsub hI
  exact independent_card_le_colorClass d hd hr I hsub hI

/-- A maximum independent set meets every positive-weight triangle exactly once. -/
theorem maximum_saturates (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (t : Triangle)
    (ht : t.Valid d) (hw : 0 < weight d t) : (I ∩ triVertices t).card = 1 := by
  have hcard : I.card = (colorClass d 0).card := by
    apply Nat.le_antisymm
    · exact independent_card_le_colorClass d hd hr I hI.1 hI.2.1
    · exact hI.2.2 _ (Finset.filter_subset _ _) (colorClass_independent d 0)
  have hsum : (∑ s ∈ triangles d, weight d s * (I ∩ triVertices s).card) =
      ∑ s ∈ triangles d, weight d s := by
    rw [weighted_incidence_eq d hd hr I hI.1, total_triangle_weight d hd hr, hcard]
  have hbound := hI.2.1.card_inter_triVertices_le_one t
  by_contra hne
  have hz : (I ∩ triVertices t).card = 0 := by omega
  have hlt : (∑ s ∈ triangles d, weight d s * (I ∩ triVertices s).card) <
      ∑ s ∈ triangles d, weight d s := by
    apply Finset.sum_lt_sum
    · intro s _
      simpa using Nat.mul_le_mul_left (weight d s) (hI.2.1.card_inter_triVertices_le_one s)
    · exact ⟨t, (mem_triangles d t).mpr ht, by simpa [hz] using hw⟩
  omega

/-- Conversely, saturation fixes the cardinality, including triangles of weight zero. -/
theorem saturated_card_eq (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hsub : I ⊆ vertices d)
    (hs : ∀ t : Triangle, t.Valid d → 0 < weight d t → (I ∩ triVertices t).card = 1) :
    I.card = (colorClass d 0).card := by
  have hsum : (∑ t ∈ triangles d, weight d t * (I ∩ triVertices t).card) =
      ∑ t ∈ triangles d, weight d t := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hw : weight d t = 0
    · simp [hw]
    · rw [hs t ((mem_triangles d t).mp ht) (Nat.pos_of_ne_zero hw), Nat.mul_one]
  rw [weighted_incidence_eq d hd hr I hsub, total_triangle_weight d hd hr] at hsum
  omega

/-- For an independent set, maximum cardinality is equivalent to positive-weight saturation. -/
theorem maximum_iff_saturates (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hsub : I ⊆ vertices d) (hI : Independent I) :
    MaximumIndependent d I ↔
      ∀ t : Triangle, t.Valid d → 0 < weight d t → (I ∩ triVertices t).card = 1 := by
  constructor
  · intro hm t ht hw
    exact maximum_saturates d hd hr I hm t ht hw
  · intro hs
    refine ⟨hsub, hI, ?_⟩
    intro J hJ hInd
    rw [saturated_card_eq d hd hr I hsub hs]
    exact independent_card_le_colorClass d hd hr J hJ hInd
#print axioms weighted_incidence
#print axioms independent_card_le_colorClass
#print axioms colorClass_maximum
#print axioms maximum_saturates
#print axioms maximum_iff_saturates

end Howroyd
