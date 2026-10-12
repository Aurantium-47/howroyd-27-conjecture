import Howroyd.CornerExtraction

namespace Howroyd

/-- A body color and three independently specified corner configurations. -/
def assembly (d j : Nat) (s₀ s₁ s₂ : Finset Corner.Vertex) : Finset Vec :=
  bodyPart d j ∪ cornerPart d 0 s₀ ∪ cornerPart d 1 s₁ ∪ cornerPart d 2 s₂

@[simp] theorem mem_bodyPart (d j : Nat) (v : Vec) :
    v ∈ bodyPart d j ↔ Body d v ∧ color v = j := by
  simp [bodyPart]

theorem cornerPart_inCorner {d : Nat} (hd : 10 ≤ d) (i : Fin 3)
    {s : Finset Corner.Vertex} {v : Vec} (hv : v ∈ cornerPart d i s) : InCorner d i v := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
  exact cornerMap_inCorner (by omega) i _ (Corner.coordinates_sum_le p)

theorem cornerPart_card (d : Nat) (i : Fin 3) (s : Finset Corner.Vertex) :
    (cornerPart d i s).card = s.card :=
  Finset.card_image_of_injective s ((cornerMap_injective d i).comp Corner.coordinates_injective)

theorem cornerPart_localCorner (d : Nat) (i : Fin 3) (I : Finset Vec) :
    cornerPart d i (localCorner d i I) = I ∩ cornerVertices d i := by
  ext v
  simp only [cornerPart, localCorner, cornerVertices, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p, rfl⟩
  · rintro ⟨hv, p, rfl⟩
    exact ⟨p, hv, rfl⟩

theorem cornerPart_disjoint_bodyPart {d : Nat} (hd : 10 ≤ d) (i : Fin 3)
    (j : Nat) (s : Finset Corner.Vertex) : Disjoint (bodyPart d j) (cornerPart d i s) := by
  rw [Finset.disjoint_left]
  intro v hb hc
  exact body_not_inCorner hd ((mem_bodyPart d j v).mp hb).1 i (cornerPart_inCorner hd i hc)

theorem cornerParts_disjoint {d : Nat} (hd : 10 ≤ d) {i k : Fin 3} (hik : i ≠ k)
    (s t : Finset Corner.Vertex) : Disjoint (cornerPart d i s) (cornerPart d k t) := by
  rw [Finset.disjoint_left]
  intro v hi hk
  exact corners_disjoint hd hik (cornerPart_inCorner hd i hi) (cornerPart_inCorner hd k hk)

theorem map_mem_cornerPart_iff {d : Nat} (hd : 10 ≤ d) (i k : Fin 3)
    (p : Corner.Vertex) (s : Finset Corner.Vertex) :
    cornerMap d i (Corner.coordinates p) ∈ cornerPart d k s ↔ i = k ∧ p ∈ s := by
  by_cases hik : i = k
  · subst k
    simp only [true_and]
    constructor
    · intro h
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h
      have hpq := Corner.coordinates_injective ((cornerMap_injective d i) heq)
      simpa only [hpq] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · simp only [hik, false_and, iff_false]
    intro h
    exact corners_disjoint hd hik
      (cornerMap_inCorner (by omega) i _ (Corner.coordinates_sum_le p))
      (cornerPart_inCorner hd k h)

theorem map_not_mem_bodyPart {d : Nat} (hd : 10 ≤ d) (i : Fin 3) (j : Nat)
    (p : Corner.Vertex) : cornerMap d i (Corner.coordinates p) ∉ bodyPart d j := by
  intro h
  exact body_not_inCorner hd ((mem_bodyPart d j _).mp h).1 i
    (cornerMap_inCorner (by omega) i _ (Corner.coordinates_sum_le p))

@[simp] theorem localCorner_assembly_zero {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) : localCorner d 0 (assembly d j s₀ s₁ s₂) = s₀ := by
  ext p
  simp [mem_localCorner, assembly, map_mem_cornerPart_iff hd, map_not_mem_bodyPart hd]

@[simp] theorem localCorner_assembly_one {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) : localCorner d 1 (assembly d j s₀ s₁ s₂) = s₁ := by
  ext p
  simp [mem_localCorner, assembly, map_mem_cornerPart_iff hd, map_not_mem_bodyPart hd]

@[simp] theorem localCorner_assembly_two {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) : localCorner d 2 (assembly d j s₀ s₁ s₂) = s₂ := by
  ext p
  simp [mem_localCorner, assembly, map_mem_cornerPart_iff hd, map_not_mem_bodyPart hd]

theorem assembly_body {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) (v : Vec) (hv : Body d v) :
    v ∈ assembly d j s₀ s₁ s₂ ↔ color v = j := by
  have h₀ : v ∉ cornerPart d 0 s₀ := fun h => body_not_inCorner hd hv 0 (cornerPart_inCorner hd 0 h)
  have h₁ : v ∉ cornerPart d 1 s₁ := fun h => body_not_inCorner hd hv 1 (cornerPart_inCorner hd 1 h)
  have h₂ : v ∉ cornerPart d 2 s₂ := fun h => body_not_inCorner hd hv 2 (cornerPart_inCorner hd 2 h)
  simp [assembly, h₀, h₁, h₂, mem_bodyPart, hv]

theorem assembly_subset_vertices {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) : assembly d j s₀ s₁ s₂ ⊆ vertices d := by
  intro v hv
  simp only [assembly, Finset.mem_union] at hv
  rcases hv with ((hb | h₀) | h₁) | h₂
  · exact (mem_vertices d v).mpr ((mem_bodyPart d j v).mp hb).1.1
  · exact (mem_vertices d v).mpr (cornerPart_inCorner hd 0 h₀).1
  · exact (mem_vertices d v).mpr (cornerPart_inCorner hd 1 h₁).1
  · exact (mem_vertices d v).mpr (cornerPart_inCorner hd 2 h₂).1

theorem eq_assembly_localCorners {d : Nat} (hd : 10 ≤ d) (I : Finset Vec)
    (hsub : I ⊆ vertices d) (j : Nat)
    (hbody : ∀ v, Body d v → (v ∈ I ↔ color v = j)) :
    I = assembly d j (localCorner d 0 I) (localCorner d 1 I) (localCorner d 2 I) := by
  ext v
  simp only [assembly, Finset.mem_union, cornerPart_localCorner, Finset.mem_inter,
    mem_cornerVertices (by omega : 3 ≤ d), mem_bodyPart]
  constructor
  · intro hv
    rcases degree_partition hd ((mem_vertices d v).mp (hsub hv)) with hb | ⟨i, hi⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hb, (hbody v hb).mp hv⟩))
    · fin_cases i
      · exact Or.inl (Or.inl (Or.inr ⟨hv, hi⟩))
      · exact Or.inl (Or.inr ⟨hv, hi⟩)
      · exact Or.inr ⟨hv, hi⟩
  · rintro (((⟨hb, hc⟩ | h₀) | h₁) | h₂)
    · exact (hbody v hb).mpr hc
    · exact h₀.1
    · exact h₁.1
    · exact h₂.1

theorem assembly_card {d : Nat} (hd : 10 ≤ d) (j : Nat)
    (s₀ s₁ s₂ : Finset Corner.Vertex) :
    (assembly d j s₀ s₁ s₂).card = (bodyPart d j).card + s₀.card + s₁.card + s₂.card := by
  have hB₀ := cornerPart_disjoint_bodyPart hd 0 j s₀
  have hB₁ := cornerPart_disjoint_bodyPart hd 1 j s₁
  have hB₂ := cornerPart_disjoint_bodyPart hd 2 j s₂
  have h₀₁ := cornerParts_disjoint hd (by decide : (0 : Fin 3) ≠ 1) s₀ s₁
  have h₀₂ := cornerParts_disjoint hd (by decide : (0 : Fin 3) ≠ 2) s₀ s₂
  have h₁₂ := cornerParts_disjoint hd (by decide : (1 : Fin 3) ≠ 2) s₁ s₂
  unfold assembly
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hB₂, h₀₂⟩, h₁₂⟩)]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hB₁, h₀₁⟩)]
  rw [Finset.card_union_of_disjoint hB₀]
  simp only [cornerPart_card]

theorem localCorner_colorClass {d : Nat} (hd : 10 ≤ d) (i : Fin 3) (j : Nat) (hj : j < 3) :
    localCorner d i (colorClass d j) = Corner.localColorSet (relativeIndex d i j) := by
  ext p
  rw [mem_localCorner, Corner.mem_localColorSet]
  have hs := Corner.coordinates_sum_le p
  simp only [colorClass, Finset.mem_filter, mem_vertices]
  rw [cornerMap_degree d i _ (by omega)]
  simp only [true_and]
  exact cornerMap_color_iff d i j hj _ (by omega)

theorem colorClass_eq_assembly {d : Nat} (hd : 10 ≤ d) (j : Nat) (hj : j < 3) :
    colorClass d j = assembly d j
      (Corner.localColorSet (relativeIndex d 0 j))
      (Corner.localColorSet (relativeIndex d 1 j))
      (Corner.localColorSet (relativeIndex d 2 j)) := by
  have h := eq_assembly_localCorners hd (colorClass d j) (Finset.filter_subset _ _) j
    (by intro v hv; simp [colorClass, hv.1])
  simpa only [localCorner_colorClass hd _ j hj] using h

theorem colorClass_card_partition {d : Nat} (hd : 10 ≤ d) (j : Nat) (hj : j < 3) :
    (colorClass d j).card = (bodyPart d j).card +
      Corner.maximumSize (relativeIndex d 0 j) + Corner.maximumSize (relativeIndex d 1 j) +
      Corner.maximumSize (relativeIndex d 2 j) := by
  rw [colorClass_eq_assembly hd j hj, assembly_card hd]
  simp only [Corner.localColorSet_card]

#print axioms assembly_card
#print axioms eq_assembly_localCorners
#print axioms localCorner_assembly_zero

end Howroyd
