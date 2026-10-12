import Howroyd.Classification
import Howroyd.Counting

namespace Howroyd

set_option synthInstance.maxSize 10000

/-- The independent, semantic definition of all maximum sets equals the
    image of the complete labelled corner parametrization. -/
theorem maximumIndependentSets_eq_candidates (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0) :
    maximumIndependentSets d = candidates d := by
  classical
  ext I
  rw [mem_maximumIndependentSets]
  constructor
  · intro hI
    obtain ⟨j,s₀,s₁,s₂,h₀,h₁,h₂,he⟩ := maximum_eq_assembly d hd hr I hI
    have hc : ((s₀,s₁),s₂) ∈ Corner.choices (degreeResidue d) j := by
      rw [Corner.mem_choices]
      simpa only [Corner.relative_eq_relativeIndex d (degreeResidue d) rfl] using
        And.intro h₀ (And.intro h₁ h₂)
    exact Finset.mem_image.mpr ⟨(j,((s₀,s₁),s₂)),
      (Corner.mem_allChoices (degreeResidue d) j _).mpr hc, he.symm⟩
  · intro hI
    obtain ⟨⟨j,⟨⟨s₀,s₁⟩,s₂⟩⟩,hp,rfl⟩ := Finset.mem_image.mp hI
    have hc := (Corner.mem_allChoices (degreeResidue d) j ((s₀,s₁),s₂)).mp hp
    have hs := (Corner.mem_choices (degreeResidue d) j s₀ s₁ s₂).mp hc
    have hs' : s₀ ∈ Corner.table (relativeIndex d 0 j.val) ∧
        s₁ ∈ Corner.table (relativeIndex d 1 j.val) ∧
        s₂ ∈ Corner.table (relativeIndex d 2 j.val) := by
      simpa only [Corner.relative_eq_relativeIndex d (degreeResidue d) rfl] using hs
    exact assembled_maximum d hd hr j.val j.isLt s₀ s₁ s₂ hs'.1 hs'.2.1 hs'.2.2

/-- The all-degree, labelled maximum-independent-set count from the original problem. -/
theorem maximum_independent_sets_card (d : Nat) (hd : 10 ≤ d) (hr : ¬3 ∣ d) :
    (maximumIndependentSets d).card = 27 := by
  have hm : d%3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hr
  rw [maximumIndependentSets_eq_candidates d hd hm]
  exact candidates_card d hd hm

/-- The separately stated original target in Basic.lean is proved. -/
theorem howroyd_27 : Howroyd27 := maximum_independent_sets_card

#print axioms maximumIndependentSets_eq_candidates
#print axioms maximum_independent_sets_card
#print axioms howroyd_27

end Howroyd
