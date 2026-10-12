import Howroyd.Assembly
import Howroyd.Body
import Howroyd.CornerProducts

namespace Howroyd

set_option synthInstance.maxSize 10000

def degreeResidue (d : Nat) : Fin 3 := ⟨d%3, Nat.mod_lt _ (by decide)⟩

def assembleChoice (d : Nat) (p : Fin 3 × Corner.CornerTriple) : Finset Vec :=
  assembly d p.1.val p.2.1.1 p.2.1.2 p.2.2

/-- All parameters remain labelled by the body color and the three coordinates. -/
def candidates (d : Nat) : Finset (Finset Vec) :=
  (Corner.allChoices (degreeResidue d)).image (assembleChoice d)

/-- No two labelled parameter choices collapse to the same global vertex set. -/
theorem assembleChoice_injective (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0) :
    Function.Injective (assembleChoice d) := by
  rintro ⟨j,⟨⟨a₀,a₁⟩,a₂⟩⟩ ⟨k,⟨⟨b₀,b₁⟩,b₂⟩⟩ he
  change assembly d j.val a₀ a₁ a₂ = assembly d k.val b₀ b₁ b₂ at he
  have hcard := triVertices_filter_color_card (centralTriangle d) j.val j.isLt
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega :
    0 < ((triVertices (centralTriangle d)).filter (fun v => color v = j.val)).card)
  obtain ⟨hvt,hvj⟩ := Finset.mem_filter.mp hv
  have hvbody := centralTriangle_in_body d hd hr hvt
  have hva := (assembly_body hd j.val a₀ a₁ a₂ v hvbody).mpr hvj
  have hvb : v ∈ assembly d k.val b₀ b₁ b₂ := by rw [← he]; exact hva
  have hjk : j = k := Fin.ext (hvj.symm.trans
    ((assembly_body hd k.val b₀ b₁ b₂ v hvbody).mp hvb))
  have h₀ := congrArg (localCorner d 0) he
  have h₁ := congrArg (localCorner d 1) he
  have h₂ := congrArg (localCorner d 2) he
  simp only [localCorner_assembly_zero hd] at h₀
  simp only [localCorner_assembly_one hd] at h₁
  simp only [localCorner_assembly_two hd] at h₂
  exact Prod.ext hjk (Prod.ext (Prod.ext h₀ h₁) h₂)

theorem candidates_card (d : Nat) (hd : 10 ≤ d) (hr : d%3 ≠ 0) :
    (candidates d).card = 27 := by
  unfold candidates
  rw [Finset.card_image_of_injective _ (assembleChoice_injective d hd hr)]
  apply Corner.allChoices_card
  intro he
  have hv := congrArg Fin.val he
  exact hr hv

#print axioms assembleChoice_injective
#print axioms candidates_card

end Howroyd
