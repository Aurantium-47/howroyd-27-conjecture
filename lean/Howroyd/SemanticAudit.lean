import Howroyd.Main

/-! An expanded statement check and transitive axiom audit of the final theorem. -/

namespace Howroyd

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

example (d : Nat) (hd : 10 ≤ d) (hr : ¬3 ∣ d) :
    ((vertices d).powerset.filter fun I =>
      I ⊆ vertices d ∧ Independent I ∧
      ∀ J : Finset Vec, J ⊆ vertices d → Independent J → J.card ≤ I.card).card = 27 := by
  have he : ((vertices d).powerset.filter fun I =>
      I ⊆ vertices d ∧ Independent I ∧
      ∀ J : Finset Vec, J ⊆ vertices d → Independent J → J.card ≤ I.card) =
      maximumIndependentSets d := by
    ext I
    simp only [maximumIndependentSets, MaximumIndependent, Finset.mem_filter]
  rw [he]
  exact maximum_independent_sets_card d hd hr

#print Howroyd27
#print MaximumIndependent
#print axioms legal_key_defined
#print axioms exact_cover_of_not_dvd
#print axioms maximum_saturates
#print axioms maximum_one_color_on_body
#print axioms Corner.maximum_counts
#print axioms maximum_eq_assembly
#print axioms assembled_maximum
#print axioms assembleChoice_injective
#print axioms maximumIndependentSets_eq_candidates
#print axioms maximum_independent_sets_card
#print axioms howroyd_27

end Howroyd
