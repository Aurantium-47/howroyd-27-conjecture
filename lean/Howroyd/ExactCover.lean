import Howroyd.LocalCover
import Howroyd.Geometry

namespace Howroyd

private theorem mem_conditional_singleton {α : Type*} [DecidableEq α]
    (p : Prop) [Decidable p] (a b : α) :
    a ∈ (if p then ({b} : Finset α) else ∅) ↔ p ∧ a=b := by
  by_cases h : p <;> simp [h]

theorem incident_key_defined (v : Vec) (hc : Covered v) (t : Triangle)
    (ht : t ∈ incidentTriangles v) : (weightOption v.degree t).isSome = true := by
  simp only [incidentTriangles, Finset.mem_union, mem_conditional_singleton,
    or_assoc] at ht
  rcases ht with ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩
  · exact hc.1 h
  · exact hc.2.1 h
  · exact hc.2.2.1 h
  · exact hc.2.2.2.1 h
  · exact hc.2.2.2.2.1 h
  · exact hc.2.2.2.2.2.1 h

/-- All legal triangles have a CSV entry; the `getD 0` fallback is unreachable. -/
theorem legal_key_defined (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (t : Triangle) (ht : t.Valid d) : (weightOption d t).isSome = true := by
  have hn : (triVertices t).Nonempty := Finset.card_pos.mp (by rw [triVertices_card]; decide)
  obtain ⟨v,hv⟩ := hn
  have he : v.degree = d := triVertices_degree ht hv
  have hc := covered_vertex v (by omega) (by simpa only [he] using hr)
  have hm := (mem_incidentTriangles_iff he t).mpr ⟨ht,hv⟩
  simpa only [he] using incident_key_defined v hc t hm

/-- Exact cover for the actual finite family of legal U/D triangles. -/
theorem exact_cover (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (v : Vec) (hv : v.degree = d) :
    (∑ t ∈ (triangles d).filter (fun t => v ∈ triVertices t), weight d t) = 60 := by
  rw [triangles_filter_eq_incident hv, sum_incidentTriangles]
  have hc := covered_vertex v (by omega) (by simpa only [hv] using hr)
  simpa only [localSum, hv] using hc.2.2.2.2.2.2

theorem legal_weight_nonnegative (d : Nat) (t : Triangle) : 0 ≤ weight d t :=
  Nat.zero_le _

/-- The milestone statement uses divisibility, as in the original problem. -/
theorem exact_cover_of_not_dvd (d : Nat) (hd : 10 ≤ d) (hr : ¬3 ∣ d)
    (v : Vec) (hv : v.degree = d) :
    (∑ t ∈ (triangles d).filter (fun t => v ∈ triVertices t), weight d t) = 60 := by
  apply exact_cover d hd _ v hv
  simpa only [Nat.dvd_iff_mod_eq_zero] using hr

#print axioms legal_key_defined
#print axioms exact_cover
#print axioms exact_cover_of_not_dvd

end Howroyd
