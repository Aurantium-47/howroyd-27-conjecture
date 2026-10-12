import Howroyd.CornerGeometry
import Howroyd.Saturation

namespace Howroyd

def cornerPart (d : Nat) (i : Fin 3) (s : Finset Corner.Vertex) : Finset Vec :=
  s.image fun p => cornerMap d i (Corner.coordinates p)

def localCorner (d : Nat) (i : Fin 3) (I : Finset Vec) : Finset Corner.Vertex :=
  Finset.univ.filter fun p => cornerMap d i (Corner.coordinates p) ∈ I

def bodyPart (d j : Nat) : Finset Vec :=
  (bodyVertices d).filter fun v => color v = j

@[simp] theorem mem_localCorner (d : Nat) (i : Fin 3) (I : Finset Vec)
    (p : Corner.Vertex) :
    p ∈ localCorner d i I ↔ cornerMap d i (Corner.coordinates p) ∈ I := by
  simp [localCorner]

theorem exists_corner_preimage_mem {d : Nat} (hd : 10 ≤ d) (i : Fin 3)
    (I : Finset Vec) {v : Vec} (hv : InCorner d i v) (hvI : v ∈ I) :
    ∃ p ∈ localCorner d i I, cornerMap d i (Corner.coordinates p) = v := by
  have hm := (mem_cornerVertices (by omega : 3 ≤ d) i v).mpr hv
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hm
  exact ⟨p, (mem_localCorner d i I p).mpr (hp ▸ hvI), hp⟩

theorem independent_forbids_edge {I : Finset Vec} (hI : Independent I)
    {u v : Vec} (hu : u ∈ I) (hv : v ∈ I) : l1Distance u v ≠ 2 := by
  intro ha
  have hne : u ≠ v := by
    intro he
    subst v
    simp at ha
  exact hI u hu v hv hne ha

theorem localCorner_compatible (d : Nat) (hd : 10 ≤ d) (i : Fin 3)
    (j : Nat) (hj : j < 3) (I : Finset Vec) (hI : Independent I)
    (hbody : ∀ v, Body d v → (v ∈ I ↔ color v = j)) :
    Corner.Compatible (relativeIndex d i j) (localCorner d i I) := by
  constructor
  · intro p hp q hq ha
    have hpI := (mem_localCorner d i I p).mp hp
    have hqI := (mem_localCorner d i I q).mp hq
    have hpD : (Corner.coordinates p).1 + (Corner.coordinates p).2 ≤ d := by
      have := Corner.coordinates_sum_le p
      omega
    have hqD : (Corner.coordinates q).1 + (Corner.coordinates q).2 ≤ d := by
      have := Corner.coordinates_sum_le q
      omega
    exact independent_forbids_edge hI hpI hqI
      ((cornerMap_adjacency d i _ _ hpD hqD).mp ha)
  · intro p hp q hq ha
    have hpI := (mem_localCorner d i I p).mp hp
    have hpD : (Corner.coordinates p).1 + (Corner.coordinates p).2 ≤ d := by
      have := Corner.coordinates_sum_le p
      omega
    have hqD : (Corner.outerPoint q).1 + (Corner.outerPoint q).2 ≤ d := by
      have := Corner.outerPoint_sum q
      omega
    have hqC := (cornerMap_color_iff d i j hj _ hqD).mpr hq
    have hqI := (hbody _ (outerPoint_in_body hd i q)).mpr hqC
    exact independent_forbids_edge hI hpI hqI
      ((cornerMap_adjacency d i _ _ hpD hqD).mp ha)

theorem body_corner_not_adj (d : Nat) (hd : 10 ≤ d) (i : Fin 3)
    (j : Nat) (hj : j < 3) (I : Finset Vec)
    (hbody : ∀ v, Body d v → (v ∈ I ↔ color v = j))
    (hlocal : Corner.Compatible (relativeIndex d i j) (localCorner d i I))
    {u v : Vec} (hu : Body d u) (hv : InCorner d i v) (huI : u ∈ I) (hvI : v ∈ I) :
    l1Distance u v ≠ 2 := by
  intro ha
  have har : l1Distance v u = 2 := (l1Distance_comm v u).trans ha
  obtain ⟨p, hp, hpm⟩ := exists_corner_preimage_mem hd i I hv hvI
  obtain ⟨q, hqm⟩ := corner_body_neighbor_layer hd i hv hu har
  have hpD : (Corner.coordinates p).1 + (Corner.coordinates p).2 ≤ d := by
    have := Corner.coordinates_sum_le p
    omega
  have hqD : (Corner.outerPoint q).1 + (Corner.outerPoint q).2 ≤ d := by
    have := Corner.outerPoint_sum q
    omega
  have hqC : color (cornerMap d i (Corner.outerPoint q)) = j := by
    rw [← hqm]
    exact (hbody u hu).mp huI
  have hqR := (cornerMap_color_iff d i j hj _ hqD).mp hqC
  apply hlocal.2 p hp q hqR
  apply (cornerMap_adjacency d i _ _ hpD hqD).mpr
  rw [hpm, ← hqm]
  exact har

/-- Independence of the assembled set follows from the local compatibility predicates. -/
theorem independent_of_localCompatible (d : Nat) (hd : 10 ≤ d) (j : Nat)
    (hj : j < 3) (I : Finset Vec) (hsub : I ⊆ vertices d)
    (hbody : ∀ v, Body d v → (v ∈ I ↔ color v = j))
    (hlocal : ∀ i : Fin 3, Corner.Compatible (relativeIndex d i j) (localCorner d i I)) :
    Independent I := by
  intro u hu v hv _ ha
  have huD := (mem_vertices d u).mp (hsub hu)
  have hvD := (mem_vertices d v).mp (hsub hv)
  rcases degree_partition hd huD with huB | ⟨i, huC⟩
  · rcases degree_partition hd hvD with hvB | ⟨i, hvC⟩
    · exact color_ne_of_adj (huD.trans hvD.symm) ha
        (((hbody u huB).mp hu).trans ((hbody v hvB).mp hv).symm)
    · exact body_corner_not_adj d hd i j hj I hbody (hlocal i) huB hvC hu hv ha
  · rcases degree_partition hd hvD with hvB | ⟨k, hvC⟩
    · exact body_corner_not_adj d hd i j hj I hbody (hlocal i) hvB huC hv hu
        ((l1Distance_comm v u).trans ha)
    · by_cases hik : i = k
      · subst k
        obtain ⟨p, hp, hpm⟩ := exists_corner_preimage_mem hd i I huC hu
        obtain ⟨q, hq, hqm⟩ := exists_corner_preimage_mem hd i I hvC hv
        have hpD : (Corner.coordinates p).1 + (Corner.coordinates p).2 ≤ d := by
          have := Corner.coordinates_sum_le p
          omega
        have hqD : (Corner.coordinates q).1 + (Corner.coordinates q).2 ≤ d := by
          have := Corner.coordinates_sum_le q
          omega
        apply (hlocal i).1 p hp q hq
        apply (cornerMap_adjacency d i _ _ hpD hqD).mpr
        simpa only [hpm, hqm] using ha
      · exact no_edge_between_corners hd hik huC hvC ha

#print axioms localCorner_compatible
#print axioms independent_of_localCompatible

end Howroyd
