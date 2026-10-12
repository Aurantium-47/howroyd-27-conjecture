import Howroyd.Propagation

namespace Howroyd

def centralTriangle (d : Nat) : Triangle :=
  if d % 3 = 1 then ⟨.up, ⟨d / 3, d / 3, d / 3⟩⟩
  else ⟨.up, ⟨d / 3 + 1, d / 3, d / 3⟩⟩

theorem centralTriangle_valid (d : Nat) (hr : d % 3 ≠ 0) :
    (centralTriangle d).Valid d := by
  unfold centralTriangle
  split_ifs <;> dsimp [Triangle.Valid, Vec.degree] <;> omega

theorem centralTriangle_in_body (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    {v : Vec} (hv : v ∈ triVertices (centralTriangle d)) : Body d v := by
  unfold centralTriangle at hv
  split_ifs at hv
  all_goals simp only [triVertices, Finset.mem_insert, Finset.mem_singleton] at hv
  all_goals rcases hv with rfl | rfl | rfl
  all_goals dsimp [Body, Vec.degree]; omega

theorem centralTriangle_positive (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0) :
    0 < weight d (centralTriangle d) := by
  have hz := weight_zero_iff d (centralTriangle d)
    (legal_key_defined d hd hr _ (centralTriangle_valid d hr))
  have hn : ¬zeroPattern (centralTriangle d).kind (centralTriangle d).base.x
      (centralTriangle d).base.y (centralTriangle d).base.z := by
    unfold centralTriangle
    split_ifs <;> dsimp [zeroPattern, upZeroPair] <;> omega
  exact Nat.pos_of_ne_zero (fun h => hn (hz.mp h))

def AgreesOnBody (d : Nat) (I : Finset Vec) (j : Nat) : Prop :=
  ∀ v : Vec, Body d v → (v ∈ I ↔ color v = j)

theorem body_color_nonempty (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (j : Nat) (hj : j < 3) : ∃ v : Vec, Body d v ∧ color v = j := by
  have hc := triVertices_filter_color_card (centralTriangle d) j hj
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega :
    0 < ((triVertices (centralTriangle d)).filter (fun v => color v = j)).card)
  obtain ⟨hvT, hvC⟩ := Finset.mem_filter.mp hv
  exact ⟨v, centralTriangle_in_body d hd hr hvT, hvC⟩

/-- Every genuine maximum independent set has one uniquely determined body color. -/
theorem maximum_one_color_on_body (d : Nat) (hd : 10 ≤ d) (hr : d % 3 ≠ 0)
    (I : Finset Vec) (hI : MaximumIndependent d I) :
    ∃! j : Nat, j < 3 ∧ AgreesOnBody d I j := by
  let t := centralTriangle d
  have ht : t.Valid d := centralTriangle_valid d hr
  have hb : ∀ v ∈ triVertices t, Body d v := fun v hv => centralTriangle_in_body d hd hr hv
  have hs : (I ∩ triVertices t).card = 1 :=
    maximum_saturates d hd hr I hI t ht (centralTriangle_positive d hd hr)
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hs
  have huI : u ∈ I := by
    have h : u ∈ I ∩ triVertices t := by rw [hu]; simp
    exact (Finset.mem_inter.mp h).1
  have huT : u ∈ triVertices t := by
    have h : u ∈ I ∩ triVertices t := by rw [hu]; simp
    exact (Finset.mem_inter.mp h).2
  have huB := hb u huT
  have hagrees : AgreesOnBody d I (color u) := by
    intro v hv
    constructor
    · intro hvI
      have hc := triVertices_filter_color_card t (color v) (color_lt_three v)
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega :
        0 < ((triVertices t).filter (fun w => color w = color v)).card)
      obtain ⟨hwT, hwC⟩ := Finset.mem_filter.mp hw
      have hwB := hb w hwT
      have he := maximum_body_color_constancy d hd hr I hI w v hwB hv hwC
      have hwI : w ∈ I := (selected_eq_one I w).mp
        (he.trans ((selected_eq_one I v).mpr hvI))
      have hwU : w = u := by
        have hm : w ∈ I ∩ triVertices t := Finset.mem_inter.mpr ⟨hwI, hwT⟩
        rw [hu] at hm
        exact Finset.mem_singleton.mp hm
      exact hwC.symm.trans (congrArg color hwU)
    · intro hc
      have he := maximum_body_color_constancy d hd hr I hI v u hv huB hc
      exact (selected_eq_one I v).mp (he.trans ((selected_eq_one I u).mpr huI))
  refine ⟨color u, ⟨color_lt_three u, hagrees⟩, ?_⟩
  intro j hj
  exact ((hj.2 u huB).mp huI).symm

#print axioms maximum_one_color_on_body

end Howroyd
