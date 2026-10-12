import Howroyd.CornerGeometry

/-!
# The finite parameter set of all corner choices

This module counts labelled choices, retaining the body colour as part of each
parameter.  Identifying these parameters with maximum independent sets of the
global graph requires the separate assembly and classification theorems.
-/

namespace Howroyd.Corner

set_option synthInstance.maxSize 10000

/-- The colours of the three corner vertices are r, -r, and 0 modulo three. -/
def cornerColor (r i : Fin 3) : Fin 3 :=
  if i.val = 0 then r
  else if i.val = 1 then ⟨(3 - r.val) % 3, Nat.mod_lt _ (by decide)⟩
  else 0

/-- The extra 3 makes natural subtraction an exact representative of j-c. -/
def relative (r j i : Fin 3) : Fin 3 :=
  ⟨(j.val + 3 - (cornerColor r i).val) % 3, Nat.mod_lt _ (by decide)⟩

theorem relative_eq_int_mod (r j i : Fin 3) :
    ((relative r j i).val : ℤ) = ((j.val : ℤ) - (cornerColor r i).val) % 3 := by
  have hc := (cornerColor r i).isLt
  have hj := j.isLt
  simp only [relative]
  omega

theorem cornerColor_eq_offset (d : ℕ) (r : Fin 3) (hr : d % 3 = r.val)
    (i : Fin 3) : (cornerColor r i).val = cornerOffset d i := by
  have hb := r.isLt
  fin_cases i <;> simp [cornerColor, cornerOffset] <;> omega

theorem relative_eq_relativeIndex (d : ℕ) (r : Fin 3) (hr : d % 3 = r.val)
    (j i : Fin 3) : relative r j i = relativeIndex d i j.val := by
  apply Fin.ext
  have hb : cornerOffset d i < 3 := by
    rw [← cornerColor_eq_offset d r hr i]
    exact (cornerColor r i).isLt
  simp only [relative, relativeIndex, cornerColor_eq_offset d r hr i]
  omega

abbrev CornerTriple := (Finset Vertex × Finset Vertex) × Finset Vertex

def choices (r j : Fin 3) : Finset CornerTriple :=
  ((table (relative r j 0)).product (table (relative r j 1))).product
    (table (relative r j 2))

def allChoices (r : Fin 3) : Finset (Fin 3 × CornerTriple) :=
  Finset.univ.biUnion fun j => (choices r j).image fun cs => (j, cs)

theorem mem_choices (r j : Fin 3) (s₀ s₁ s₂ : Finset Vertex) :
    ((s₀, s₁), s₂) ∈ choices r j ↔
      s₀ ∈ table (relative r j 0) ∧ s₁ ∈ table (relative r j 1) ∧
      s₂ ∈ table (relative r j 2) := by
  constructor
  · intro h
    have h' := Finset.mem_product.mp h
    have h'' := Finset.mem_product.mp h'.1
    exact ⟨h''.1, h''.2, h'.2⟩
  · rintro ⟨h₀, h₁, h₂⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h₀, h₁⟩, h₂⟩

theorem mem_allChoices (r j : Fin 3) (cs : CornerTriple) :
    (j, cs) ∈ allChoices r ↔ cs ∈ choices r j := by
  simp [allChoices]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem choices_card : ∀ (r j : Fin 3), r ≠ 0 → (choices r j).card = 9 := by
  decide +kernel

theorem allChoices_card : ∀ r : Fin 3, r ≠ 0 → (allChoices r).card = 27 := by
  decide +kernel

theorem relative_maximumSize_sum : ∀ (r j : Fin 3), r ≠ 0 →
    maximumSize (relative r j 0) + maximumSize (relative r j 1) +
      maximumSize (relative r j 2) = 10 := by
  decide +kernel

theorem choices_card_sum (r j : Fin 3) (hr : r ≠ 0) (cs : CornerTriple)
    (hc : cs ∈ choices r j) : cs.1.1.card + cs.1.2.card + cs.2.card = 10 := by
  have h := (mem_choices r j cs.1.1 cs.1.2 cs.2).mp hc
  have h₀ := ((compatible_at_bound_iff_table (relative r j 0) _).mpr h.1).2
  have h₁ := ((compatible_at_bound_iff_table (relative r j 1) _).mpr h.2.1).2
  have h₂ := ((compatible_at_bound_iff_table (relative r j 2) _).mpr h.2.2).2
  rw [h₀, h₁, h₂]
  exact relative_maximumSize_sum r j hr

#print axioms choices_card
#print axioms allChoices_card
#print axioms choices_card_sum

end Howroyd.Corner
