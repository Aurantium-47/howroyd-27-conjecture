import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The ten-vertex corner problem

This module is independent of the global triangular graph.  Its predicates
describe independent sets compatible with the selected colour of the entire
outer layer.  Maximality means *maximum cardinality*, not inclusion maximality.

All finite checks use Lean's kernel through `decide`; no native computation is
used as a proof rule.  The connection with corners of the global graph is a
separate theorem and is not asserted here.
-/

namespace Howroyd.Corner

abbrev Point := ℕ × ℕ

/-- The ten pairs of nonnegative integers with coordinate sum at most three. -/
abbrev Vertex := {p : Fin 4 × Fin 4 // p.1.val + p.2.val ≤ 3}

def coordinates (v : Vertex) : Point := (v.val.1.val, v.val.2.val)

/-- The six directions ±(1,0), ±(0,1), and ±(1,-1). -/
def Adjacent (u v : Point) : Prop :=
  (u.1 + 1 = v.1 ∧ u.2 = v.2) ∨
  (v.1 + 1 = u.1 ∧ u.2 = v.2) ∨
  (u.1 = v.1 ∧ u.2 + 1 = v.2) ∨
  (u.1 = v.1 ∧ v.2 + 1 = u.2) ∨
  (u.1 + 1 = v.1 ∧ v.2 + 1 = u.2) ∨
  (v.1 + 1 = u.1 ∧ u.2 + 1 = v.2)

instance : DecidableRel Adjacent := fun u v => by
  unfold Adjacent
  infer_instance

theorem adjacent_irrefl (v : Point) : ¬ Adjacent v v := by
  simp [Adjacent]

theorem adjacent_symm (u v : Point) (h : Adjacent u v) : Adjacent v u := by
  unfold Adjacent at *
  omega

/-- The local six-direction graph is exactly the triangular lattice L1 graph. -/
theorem adjacent_iff_distance (u v : Point) :
    Adjacent u v ↔ Nat.dist u.1 v.1 + Nat.dist u.2 v.2 +
      Nat.dist (u.1 + u.2) (v.1 + v.2) = 2 := by
  unfold Adjacent Nat.dist
  omega

/-- This also covers a corner vertex compared with a vertex of the outer layer. -/
theorem adjacent_iff_barycentric_distance (d : ℕ) (u v : Point)
    (hu : u.1 + u.2 ≤ d) (hv : v.1 + v.2 ≤ d) :
    Adjacent u v ↔ Nat.dist (d - u.1 - u.2) (d - v.1 - v.2) +
      Nat.dist u.1 v.1 + Nat.dist u.2 v.2 = 2 := by
  unfold Adjacent Nat.dist
  omega

/-- The difference uses integers; in particular this is not natural subtraction. -/
def relativeColor (v : Point) : ℤ := ((v.1 : ℤ) - (v.2 : ℤ)) % 3

def outerPoint (p : Fin 5) : Point := (p.val, 4 - p.val)

def Independent (s : Finset Vertex) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ Adjacent (coordinates u) (coordinates v)

def Compatible (δ : Fin 3) (s : Finset Vertex) : Prop :=
  Independent s ∧ ∀ v ∈ s, ∀ p : Fin 5,
    relativeColor (outerPoint p) = (δ.val : ℤ) →
      ¬ Adjacent (coordinates v) (outerPoint p)

instance (s : Finset Vertex) : Decidable (Independent s) :=
  inferInstanceAs (Decidable (∀ u ∈ s, ∀ v ∈ s,
    ¬ Adjacent (coordinates u) (coordinates v)))

instance (δ : Fin 3) (s : Finset Vertex) : Decidable (Compatible δ s) :=
  inferInstanceAs (Decidable (Independent s ∧ ∀ v ∈ s, ∀ p : Fin 5,
    relativeColor (outerPoint p) = (δ.val : ℤ) →
      ¬ Adjacent (coordinates v) (outerPoint p)))

/-- Maximum cardinality among all independent, outer-layer-compatible sets. -/
def IsMaximum (δ : Fin 3) (s : Finset Vertex) : Prop :=
  Compatible δ s ∧ ∀ t : Finset Vertex, Compatible δ t → t.card ≤ s.card

private def vertex (p q : Fin 4) (h : p.val + q.val ≤ 3) : Vertex :=
  ⟨(p, q), h⟩

private def v00 : Vertex := vertex 0 0 (by decide)
private def v01 : Vertex := vertex 0 1 (by decide)
private def v02 : Vertex := vertex 0 2 (by decide)
private def v03 : Vertex := vertex 0 3 (by decide)
private def v10 : Vertex := vertex 1 0 (by decide)
private def v11 : Vertex := vertex 1 1 (by decide)
private def v12 : Vertex := vertex 1 2 (by decide)
private def v20 : Vertex := vertex 2 0 (by decide)
private def v21 : Vertex := vertex 2 1 (by decide)
private def v30 : Vertex := vertex 3 0 (by decide)

/-- The seven proposed answers; the semantic predicate above does not use this table. -/
def table (δ : Fin 3) : Finset (Finset Vertex) :=
  if δ.val = 0 then {{v00, v03, v11, v30}}
  else if δ.val = 1 then
    {{v00, v02, v20}, {v00, v02, v21}, {v02, v10, v21}}
  else {{v00, v02, v20}, {v00, v12, v20}, {v01, v12, v20}}

def maximumSize (δ : Fin 3) : ℕ := if δ.val = 0 then 4 else 3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem vertex_count : Fintype.card Vertex = 10 := by decide

theorem coordinates_sum_le (v : Vertex) :
    (coordinates v).1 + (coordinates v).2 ≤ 3 := v.property

theorem coordinates_injective : Function.Injective coordinates := by
  intro u v h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst h
  · apply Fin.ext
    exact congrArg Prod.snd h

theorem coordinates_surjective (p q : ℕ) (h : p + q ≤ 3) :
    ∃ v : Vertex, coordinates v = (p, q) := by
  refine ⟨⟨(⟨p, by omega⟩, ⟨q, by omega⟩), h⟩, rfl⟩

theorem outerPoint_sum (p : Fin 5) :
    (outerPoint p).1 + (outerPoint p).2 = 4 := by
  unfold outerPoint
  have := p.isLt
  simp only
  omega

theorem outerPoint_surjective (p q : ℕ) (h : p + q = 4) :
    ∃ i : Fin 5, outerPoint i = (p, q) := by
  refine ⟨⟨p, by omega⟩, ?_⟩
  simp only [outerPoint, Prod.mk.injEq, true_and]
  omega

/-- Exhaustive bound on all 2^10 subsets, checked by the kernel. -/
theorem compatible_card_le : ∀ (δ : Fin 3) (s : Finset Vertex),
    Compatible δ s → s.card ≤ maximumSize δ := by
  intro δ
  fin_cases δ <;> decide +kernel

/-- At the bound, compatibility and independence give exactly the stated rows. -/
theorem compatible_at_bound_iff_table : ∀ (δ : Fin 3) (s : Finset Vertex),
    (Compatible δ s ∧ s.card = maximumSize δ) ↔ s ∈ table δ := by
  intro δ
  fin_cases δ <;> decide +kernel

theorem table_nonempty : ∀ δ : Fin 3, (table δ).Nonempty := by decide

/-- Exact semantic characterization of *all* maximum cardinality sets. -/
theorem isMaximum_iff_table (δ : Fin 3) (s : Finset Vertex) :
    IsMaximum δ s ↔ s ∈ table δ := by
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := table_nonempty δ
    have ht' := (compatible_at_bound_iff_table δ t).mpr ht
    apply (compatible_at_bound_iff_table δ s).mp
    refine ⟨hs.1, Nat.le_antisymm (compatible_card_le δ s hs.1) ?_⟩
    simpa only [ht'.2] using hs.2 t ht'.1
  · intro hs
    have hs' := (compatible_at_bound_iff_table δ s).mpr hs
    refine ⟨hs'.1, ?_⟩
    intro t ht
    simpa only [hs'.2] using compatible_card_le δ t ht

theorem maximum_card (δ : Fin 3) (s : Finset Vertex) (h : IsMaximum δ s) :
    s.card = maximumSize δ :=
  ((compatible_at_bound_iff_table δ s).mpr ((isMaximum_iff_table δ s).mp h)).2

theorem table_counts : ∀ δ : Fin 3,
    (table δ).card = if δ.val = 0 then 1 else 3 := by decide

instance (δ : Fin 3) (s : Finset Vertex) : Decidable (IsMaximum δ s) :=
  inferInstanceAs (Decidable (Compatible δ s ∧ ∀ t : Finset Vertex,
    Compatible δ t → t.card ≤ s.card))

/-- The collection being counted is defined from the graph, not from the table. -/
def maximumSets (δ : Fin 3) : Finset (Finset Vertex) :=
  Finset.univ.filter (IsMaximum δ)

theorem maximumSets_eq_table (δ : Fin 3) : maximumSets δ = table δ := by
  ext s
  simp only [maximumSets, Finset.mem_filter, Finset.mem_univ, true_and]
  exact isMaximum_iff_table δ s

theorem maximum_counts (δ : Fin 3) :
    (maximumSets δ).card = if δ.val = 0 then 1 else 3 := by
  rw [maximumSets_eq_table]
  exact table_counts δ

/-- The restriction of the background colour to the corner. -/
def localColorSet (δ : Fin 3) : Finset Vertex :=
  Finset.univ.filter fun v => relativeColor (coordinates v) = (δ.val : ℤ)

theorem mem_localColorSet (δ : Fin 3) (v : Vertex) :
    v ∈ localColorSet δ ↔ relativeColor (coordinates v) = (δ.val : ℤ) := by
  simp only [localColorSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem localColorSet_mem_table : ∀ δ : Fin 3, localColorSet δ ∈ table δ := by
  decide +kernel

theorem localColorSet_card (δ : Fin 3) : (localColorSet δ).card = maximumSize δ :=
  ((compatible_at_bound_iff_table δ _).mpr (localColorSet_mem_table δ)).2

theorem localColorSet_compatible (δ : Fin 3) : Compatible δ (localColorSet δ) :=
  ((compatible_at_bound_iff_table δ _).mpr (localColorSet_mem_table δ)).1

#print axioms compatible_card_le
#print axioms compatible_at_bound_iff_table
#print axioms isMaximum_iff_table
#print axioms maximum_card
#print axioms maximum_counts
#print axioms localColorSet_card
#print axioms localColorSet_compatible

end Howroyd.Corner
