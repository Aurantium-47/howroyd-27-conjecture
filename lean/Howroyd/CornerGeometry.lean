import Howroyd.Balancing
import Howroyd.Corner

namespace Howroyd

/-- The three coordinate maps in the paper, indexed in order by 0, 1, 2. -/
def cornerMap (d : Nat) (i : Fin 3) (p : Corner.Point) : Vec :=
  if i.val = 0 then ⟨d - p.1 - p.2, p.1, p.2⟩
  else if i.val = 1 then ⟨p.2, d - p.1 - p.2, p.1⟩
  else ⟨p.1, p.2, d - p.1 - p.2⟩

def cornerCoords (i : Fin 3) (v : Vec) : Corner.Point :=
  if i.val = 0 then (v.y, v.z)
  else if i.val = 1 then (v.z, v.x)
  else (v.x, v.y)

def InCorner (d : Nat) (i : Fin 3) (v : Vec) : Prop :=
  v.degree = d ∧
    (if i.val = 0 then d - 3 ≤ v.x else if i.val = 1 then d - 3 ≤ v.y
    else d - 3 ≤ v.z)

def cornerVertices (d : Nat) (i : Fin 3) : Finset Vec :=
  Finset.univ.image fun p : Corner.Vertex => cornerMap d i (Corner.coordinates p)

def bodyVertices (d : Nat) : Finset Vec :=
  (vertices d).filter fun v => v.x ≤ d - 4 ∧ v.y ≤ d - 4 ∧ v.z ≤ d - 4

theorem cornerCoords_map (d : Nat) (i : Fin 3) (p : Corner.Point) :
    cornerCoords i (cornerMap d i p) = p := by
  fin_cases i <;> simp [cornerMap, cornerCoords]

theorem cornerMap_injective (d : Nat) (i : Fin 3) :
    Function.Injective (cornerMap d i) := by
  intro p q hpq
  simpa only [cornerCoords_map] using congrArg (cornerCoords i) hpq

theorem cornerMap_degree (d : Nat) (i : Fin 3) (p : Corner.Point)
    (hp : p.1 + p.2 ≤ d) : (cornerMap d i p).degree = d := by
  fin_cases i <;> simp [cornerMap, Vec.degree] <;> omega

theorem cornerMap_coords {d : Nat} (i : Fin 3) {v : Vec} (hv : v.degree = d) :
    cornerMap d i (cornerCoords i v) = v := by
  rcases v with ⟨x, y, z⟩
  fin_cases i <;> simp [cornerMap, cornerCoords, Vec.mk.injEq] <;>
    dsimp [Vec.degree] at hv <;> omega

theorem cornerCoords_sum_le {d : Nat} (i : Fin 3) {v : Vec} (hv : v.degree = d) :
    (cornerCoords i v).1 + (cornerCoords i v).2 ≤ d := by
  fin_cases i <;> simp [cornerCoords] <;> dsimp [Vec.degree] at hv <;> omega

theorem inCorner_iff_coords {d : Nat} (_hd : 3 ≤ d) (i : Fin 3) (v : Vec) :
    InCorner d i v ↔ v.degree = d ∧
      (cornerCoords i v).1 + (cornerCoords i v).2 ≤ 3 := by
  fin_cases i <;> simp [InCorner, cornerCoords, Vec.degree] <;> omega

theorem cornerMap_inCorner {d : Nat} (hd : 3 ≤ d) (i : Fin 3) (p : Corner.Point)
    (hp : p.1 + p.2 ≤ 3) : InCorner d i (cornerMap d i p) := by
  rw [inCorner_iff_coords hd, cornerCoords_map]
  exact ⟨cornerMap_degree d i p (by omega), hp⟩

@[simp] theorem mem_cornerVertices {d : Nat} (hd : 3 ≤ d) (i : Fin 3) (v : Vec) :
    v ∈ cornerVertices d i ↔ InCorner d i v := by
  simp only [cornerVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    exact cornerMap_inCorner hd i _ (Corner.coordinates_sum_le p)
  · intro hv
    have hs := (inCorner_iff_coords hd i v).mp hv
    obtain ⟨p, hp⟩ := Corner.coordinates_surjective _ _ hs.2
    refine ⟨p, ?_⟩
    rw [hp]
    exact cornerMap_coords i hs.1

@[simp] theorem mem_bodyVertices (d : Nat) (v : Vec) :
    v ∈ bodyVertices d ↔ Body d v := by
  simp [bodyVertices, Body]

theorem degree_partition {d : Nat} (hd : 10 ≤ d) {v : Vec} (hv : v.degree = d) :
    Body d v ∨ ∃ i : Fin 3, InCorner d i v := by
  by_cases hx : v.x ≤ d - 4
  · by_cases hy : v.y ≤ d - 4
    · by_cases hz : v.z ≤ d - 4
      · exact Or.inl ⟨hv, hx, hy, hz⟩
      · exact Or.inr ⟨2, hv, by simp; omega⟩
    · exact Or.inr ⟨1, hv, by simp; omega⟩
  · exact Or.inr ⟨0, hv, by simp; omega⟩

theorem body_not_inCorner {d : Nat} (hd : 10 ≤ d) {v : Vec} (hv : Body d v)
    (i : Fin 3) : ¬ InCorner d i v := by
  fin_cases i <;> simp [InCorner] <;> dsimp [Body] at hv <;> omega

theorem corners_disjoint {d : Nat} (hd : 10 ≤ d) {i j : Fin 3} (hij : i ≠ j)
    {v : Vec} (hi : InCorner d i v) : ¬ InCorner d j v := by
  fin_cases i <;> fin_cases j <;> simp_all [InCorner, Vec.degree] <;> omega

theorem no_edge_between_corners {d : Nat} (hd : 10 ≤ d) {i j : Fin 3} (hij : i ≠ j)
    {u v : Vec} (hu : InCorner d i u) (hv : InCorner d j v) : l1Distance u v ≠ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [InCorner, Vec.degree, l1Distance, Nat.dist] <;> omega

theorem cornerMap_adjacency (d : Nat) (i : Fin 3) (p q : Corner.Point)
    (hp : p.1 + p.2 ≤ d) (hq : q.1 + q.2 ≤ d) :
    Corner.Adjacent p q ↔ l1Distance (cornerMap d i p) (cornerMap d i q) = 2 := by
  have h := Corner.adjacent_iff_barycentric_distance d p q hp hq
  fin_cases i <;>
    simpa [cornerMap, l1Distance, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem outerPoint_in_body {d : Nat} (hd : 10 ≤ d) (i : Fin 3) (p : Fin 5) :
    Body d (cornerMap d i (Corner.outerPoint p)) := by
  have hs := Corner.outerPoint_sum p
  fin_cases i <;> simp [cornerMap, Body, Vec.degree] <;> omega

theorem corner_body_neighbor_layer {d : Nat} (hd : 10 ≤ d) (i : Fin 3)
    {u v : Vec} (hu : InCorner d i u) (hv : Body d v) (ha : l1Distance u v = 2) :
    ∃ p : Fin 5, v = cornerMap d i (Corner.outerPoint p) := by
  have hs : (cornerCoords i v).1 + (cornerCoords i v).2 = 4 := by
    fin_cases i <;> simp [cornerCoords] <;>
      simp_all [InCorner, Body, Vec.degree, l1Distance, Nat.dist] <;> omega
  obtain ⟨p, hp⟩ := Corner.outerPoint_surjective _ _ hs
  refine ⟨p, ?_⟩
  rw [hp]
  exact (cornerMap_coords i hv.1).symm

def cornerOffset (d : Nat) (i : Fin 3) : Nat :=
  if i.val = 0 then d % 3 else if i.val = 1 then (2 * d) % 3 else 0

def relativeIndex (d : Nat) (i : Fin 3) (j : Nat) : Fin 3 :=
  ⟨(j + (3 - cornerOffset d i)) % 3, Nat.mod_lt _ (by decide)⟩

theorem cornerMap_color (d : Nat) (i : Fin 3) (p : Corner.Point)
    (hp : p.1 + p.2 ≤ d) :
    color (cornerMap d i p) = (cornerOffset d i + p.1 + 2 * p.2) % 3 := by
  fin_cases i <;> simp [cornerMap, cornerOffset, color] <;> omega

theorem cornerMap_color_iff (d : Nat) (i : Fin 3) (j : Nat) (hj : j < 3)
    (p : Corner.Point) (hp : p.1 + p.2 ≤ d) :
    color (cornerMap d i p) = j ↔
      Corner.relativeColor p = ((relativeIndex d i j).val : Int) := by
  rw [cornerMap_color d i p hp]
  fin_cases i <;> simp [cornerOffset, relativeIndex, Corner.relativeColor] <;> omega

end Howroyd
