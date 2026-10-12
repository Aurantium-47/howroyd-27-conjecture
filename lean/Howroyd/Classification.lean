import Howroyd.Assembly
import Howroyd.Body

namespace Howroyd

/-- Every background color class has the same maximum cardinality. -/
theorem colorClass_card_eq_zero (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (j : Nat) (hj : j < 3) : (colorClass d j).card = (colorClass d 0).card := by
  apply saturated_card_eq d hd hr (colorClass d j) (Finset.filter_subset _ _)
  intro t ht _
  exact colorClass_inter_triangle_card ht hj

theorem maximum_card_eq_colorClass (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (j : Nat) (hj : j < 3) :
    I.card = (colorClass d j).card := by
  rw [colorClass_card_eq_zero d hd hr j hj]
  apply Nat.le_antisymm
  · exact independent_card_le_colorClass d hd hr I hI.1 hI.2.1
  · exact hI.2.2 _ (Finset.filter_subset _ _) (colorClass_independent d 0)

theorem assembled_independent (d : Nat) (hd : 10 ≤ d) (j : Nat) (hj : j < 3)
    (s₀ s₁ s₂ : Finset Corner.Vertex)
    (h₀ : s₀ ∈ Corner.table (relativeIndex d 0 j))
    (h₁ : s₁ ∈ Corner.table (relativeIndex d 1 j))
    (h₂ : s₂ ∈ Corner.table (relativeIndex d 2 j)) :
    Independent (assembly d j s₀ s₁ s₂) := by
  apply independent_of_localCompatible d hd j hj _ (assembly_subset_vertices hd j s₀ s₁ s₂)
    (assembly_body hd j s₀ s₁ s₂)
  intro i
  fin_cases i
  · change Corner.Compatible (relativeIndex d 0 j) (localCorner d 0 (assembly d j s₀ s₁ s₂))
    rw [localCorner_assembly_zero hd]
    exact ((Corner.compatible_at_bound_iff_table _ _).mpr h₀).1
  · change Corner.Compatible (relativeIndex d 1 j) (localCorner d 1 (assembly d j s₀ s₁ s₂))
    rw [localCorner_assembly_one hd]
    exact ((Corner.compatible_at_bound_iff_table _ _).mpr h₁).1
  · change Corner.Compatible (relativeIndex d 2 j) (localCorner d 2 (assembly d j s₀ s₁ s₂))
    rw [localCorner_assembly_two hd]
    exact ((Corner.compatible_at_bound_iff_table _ _).mpr h₂).1

theorem assembled_card (d : Nat) (hd : 10 ≤ d) (j : Nat) (hj : j < 3)
    (s₀ s₁ s₂ : Finset Corner.Vertex)
    (h₀ : s₀ ∈ Corner.table (relativeIndex d 0 j))
    (h₁ : s₁ ∈ Corner.table (relativeIndex d 1 j))
    (h₂ : s₂ ∈ Corner.table (relativeIndex d 2 j)) :
    (assembly d j s₀ s₁ s₂).card = (colorClass d j).card := by
  rw [assembly_card hd, colorClass_card_partition hd j hj]
  rw [((Corner.compatible_at_bound_iff_table _ _).mpr h₀).2,
    ((Corner.compatible_at_bound_iff_table _ _).mpr h₁).2,
    ((Corner.compatible_at_bound_iff_table _ _).mpr h₂).2]

/-- Every combination of a body color and three listed local configurations is maximum. -/
theorem assembled_maximum (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (j : Nat) (hj : j < 3) (s₀ s₁ s₂ : Finset Corner.Vertex)
    (h₀ : s₀ ∈ Corner.table (relativeIndex d 0 j))
    (h₁ : s₁ ∈ Corner.table (relativeIndex d 1 j))
    (h₂ : s₂ ∈ Corner.table (relativeIndex d 2 j)) :
    MaximumIndependent d (assembly d j s₀ s₁ s₂) := by
  refine ⟨assembly_subset_vertices hd j s₀ s₁ s₂,
    assembled_independent d hd j hj s₀ s₁ s₂ h₀ h₁ h₂, ?_⟩
  intro J hJ hInd
  rw [assembled_card d hd j hj s₀ s₁ s₂ h₀ h₁ h₂, colorClass_card_eq_zero d hd hr j hj]
  exact independent_card_le_colorClass d hd hr J hJ hInd

/-- Global maximal cardinality forces each corner to attain its individual local bound. -/
theorem maximum_localCorner_card (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (j : Nat) (hj : j < 3)
    (hbody : AgreesOnBody d I j) (i : Fin 3) :
    (localCorner d i I).card = Corner.maximumSize (relativeIndex d i j) := by
  have h₀ := Corner.compatible_card_le _ _ (localCorner_compatible d hd 0 j hj I hI.2.1 hbody)
  have h₁ := Corner.compatible_card_le _ _ (localCorner_compatible d hd 1 j hj I hI.2.1 hbody)
  have h₂ := Corner.compatible_card_le _ _ (localCorner_compatible d hd 2 j hj I hI.2.1 hbody)
  have hpartition := congrArg Finset.card (eq_assembly_localCorners hd I hI.1 j hbody)
  rw [assembly_card hd] at hpartition
  have hcard := maximum_card_eq_colorClass d hd hr I hI j hj
  rw [colorClass_card_partition hd j hj] at hcard
  fin_cases i
  · change (localCorner d 0 I).card = Corner.maximumSize (relativeIndex d 0 j)
    omega
  · change (localCorner d 1 I).card = Corner.maximumSize (relativeIndex d 1 j)
    omega
  · change (localCorner d 2 I).card = Corner.maximumSize (relativeIndex d 2 j)
    omega

theorem maximum_localCorner_mem_table (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) (j : Nat) (hj : j < 3)
    (hbody : AgreesOnBody d I j) (i : Fin 3) :
    localCorner d i I ∈ Corner.table (relativeIndex d i j) := by
  apply (Corner.compatible_at_bound_iff_table _ _).mp
  exact ⟨localCorner_compatible d hd i j hj I hI.2.1 hbody,
    maximum_localCorner_card d hd hr I hI j hj hbody i⟩

/-- With a specified body color, maximum sets are exactly the assemblies from table rows. -/
theorem maximum_with_body_iff (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (j : Nat) (hj : j < 3) (hbody : AgreesOnBody d I j) :
    MaximumIndependent d I ↔ ∃ s₀ s₁ s₂ : Finset Corner.Vertex,
      s₀ ∈ Corner.table (relativeIndex d 0 j) ∧
      s₁ ∈ Corner.table (relativeIndex d 1 j) ∧
      s₂ ∈ Corner.table (relativeIndex d 2 j) ∧ I = assembly d j s₀ s₁ s₂ := by
  constructor
  · intro hI
    refine ⟨localCorner d 0 I, localCorner d 1 I, localCorner d 2 I, ?_, ?_, ?_, ?_⟩
    · exact maximum_localCorner_mem_table d hd hr I hI j hj hbody 0
    · exact maximum_localCorner_mem_table d hd hr I hI j hj hbody 1
    · exact maximum_localCorner_mem_table d hd hr I hI j hj hbody 2
    · exact eq_assembly_localCorners hd I hI.1 j hbody
  · rintro ⟨s₀, s₁, s₂, h₀, h₁, h₂, rfl⟩
    exact assembled_maximum d hd hr j hj s₀ s₁ s₂ h₀ h₁ h₂

/-- Complete geometric classification, without quotienting vertex labels or symmetries. -/
theorem maximum_eq_assembly (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) :
    ∃ j : Fin 3, ∃ s₀ s₁ s₂ : Finset Corner.Vertex,
      s₀ ∈ Corner.table (relativeIndex d 0 j.val) ∧
      s₁ ∈ Corner.table (relativeIndex d 1 j.val) ∧
      s₂ ∈ Corner.table (relativeIndex d 2 j.val) ∧ I = assembly d j.val s₀ s₁ s₂ := by
  obtain ⟨j, ⟨hj, hbody⟩, _⟩ := maximum_one_color_on_body d hd hr I hI
  exact ⟨⟨j, hj⟩, (maximum_with_body_iff d hd hr I j hj hbody).mp hI⟩

#print axioms assembled_maximum
#print axioms maximum_localCorner_mem_table
#print axioms maximum_with_body_iff
#print axioms maximum_eq_assembly

end Howroyd
