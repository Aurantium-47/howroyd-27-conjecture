import Howroyd.Color
import Mathlib.Tactic.Linarith

/-!
# Constancy on each body colour under balancing moves

The hypothesis `PreservesMaxMoves` is an explicit hypothesis of the general
function theorem, to be discharged later using positive-weight saturation.
It is not an axiom and no property of maximum independent sets is assumed here.
-/

namespace Howroyd

def Body (d : ℕ) (v : Vec) : Prop :=
  v.degree = d ∧ v.x ≤ d - 4 ∧ v.y ≤ d - 4 ∧ v.z ≤ d - 4

def moveX (v : Vec) : Vec := ⟨v.x - 2, v.y + 1, v.z + 1⟩
def moveY (v : Vec) : Vec := ⟨v.x + 1, v.y - 2, v.z + 1⟩
def moveZ (v : Vec) : Vec := ⟨v.x + 1, v.y + 1, v.z - 2⟩

def MaxMove (v w : Vec) : Prop :=
  (v.y ≤ v.x ∧ v.z ≤ v.x ∧ w = moveX v) ∨
  (v.x ≤ v.y ∧ v.z ≤ v.y ∧ w = moveY v) ∨
  (v.x ≤ v.z ∧ v.y ≤ v.z ∧ w = moveZ v)

def PreservesMaxMoves (d : ℕ) (f : Vec → ℕ) : Prop :=
  ∀ v w, Body d v → MaxMove v w → f w = f v

def potential (v : Vec) : ℕ := v.x * v.x + v.y * v.y + v.z * v.z

def Terminal (k : ℕ) (v : Vec) : Prop :=
  v.x ≤ k + 1 ∧ v.y ≤ k + 1 ∧ v.z ≤ k + 1

theorem maxMove_preserves_body {d : ℕ} (hd : 10 ≤ d) {v w : Vec}
    (hv : Body d v) (hm : MaxMove v w) : Body d w := by
  rcases hm with ⟨hy, hz, rfl⟩ | ⟨hx, hz, rfl⟩ | ⟨hx, hy, rfl⟩ <;>
    simp only [Body, Vec.degree, moveX, moveY, moveZ] at * <;> omega

theorem maxMove_preserves_color {d : ℕ} (hd : 10 ≤ d) {v w : Vec}
    (hv : Body d v) (hm : MaxMove v w) : color w = color v := by
  rcases hm with ⟨hy, hz, rfl⟩ | ⟨hx, hz, rfl⟩ | ⟨hx, hy, rfl⟩ <;>
    simp only [Body, Vec.degree, moveX, moveY, moveZ, color] at * <;> omega

private theorem moveX_decreases {k r : ℕ} (hr : r ≤ 2) {v : Vec}
    (hs : v.degree = 3 * k + r) (hx : k + 2 ≤ v.x) :
    potential (moveX v) < potential v := by
  have he : v.x - 2 + 2 = v.x := by omega
  have he2 := congrArg (fun n : ℕ => n * n) he
  have hd : 2 * (3 * k + r) + 6 < 6 * v.x := by omega
  simp only [Vec.degree] at hs
  simp only [potential, moveX]
  nlinarith

private theorem moveY_decreases {k r : ℕ} (hr : r ≤ 2) {v : Vec}
    (hs : v.degree = 3 * k + r) (hy : k + 2 ≤ v.y) :
    potential (moveY v) < potential v := by
  have he : v.y - 2 + 2 = v.y := by omega
  have he2 := congrArg (fun n : ℕ => n * n) he
  have hd : 2 * (3 * k + r) + 6 < 6 * v.y := by omega
  simp only [Vec.degree] at hs
  simp only [potential, moveY]
  nlinarith

private theorem moveZ_decreases {k r : ℕ} (hr : r ≤ 2) {v : Vec}
    (hs : v.degree = 3 * k + r) (hz : k + 2 ≤ v.z) :
    potential (moveZ v) < potential v := by
  have he : v.z - 2 + 2 = v.z := by omega
  have he2 := congrArg (fun n : ℕ => n * n) he
  have hd : 2 * (3 * k + r) + 6 < 6 * v.z := by omega
  simp only [Vec.degree] at hs
  simp only [potential, moveZ]
  nlinarith

theorem exists_decreasing_maxMove {k r : ℕ} (hr : r ≤ 2) {v : Vec}
    (hs : v.degree = 3 * k + r) (hn : ¬ Terminal k v) :
    ∃ w, MaxMove v w ∧ potential w < potential v := by
  by_cases hxy : v.y ≤ v.x
  · by_cases hxz : v.z ≤ v.x
    · refine ⟨moveX v, Or.inl ⟨hxy, hxz, rfl⟩, moveX_decreases hr hs ?_⟩
      unfold Terminal at hn
      omega
    · refine ⟨moveZ v, Or.inr (Or.inr ⟨by omega, by omega, rfl⟩),
        moveZ_decreases hr hs ?_⟩
      unfold Terminal at hn
      omega
  · by_cases hyz : v.z ≤ v.y
    · refine ⟨moveY v, Or.inr (Or.inl ⟨by omega, hyz, rfl⟩),
        moveY_decreases hr hs ?_⟩
      unfold Terminal at hn
      omega
    · refine ⟨moveZ v, Or.inr (Or.inr ⟨by omega, by omega, rfl⟩),
        moveZ_decreases hr hs ?_⟩
      unfold Terminal at hn
      omega

/-- The square potential gives a terminating, colour-preserving normalization. -/
theorem exists_terminal {k r : ℕ} (hk : 3 ≤ k) (hr : r = 1 ∨ r = 2)
    (f : Vec → ℕ) (hf : PreservesMaxMoves (3 * k + r) f) (v : Vec)
    (hv : Body (3 * k + r) v) :
    ∃ t, Body (3 * k + r) t ∧ Terminal k t ∧ color t = color v ∧ f t = f v := by
  have hd : 10 ≤ 3 * k + r := by omega
  have hr' : r ≤ 2 := by omega
  generalize hm : potential v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases ht : Terminal k v
    · exact ⟨v, hv, ht, rfl, rfl⟩
    · obtain ⟨w, hmove, hlt⟩ := exists_decreasing_maxMove hr' hv.1 ht
      have hw := maxMove_preserves_body hd hv hmove
      obtain ⟨t, htb, htt, htc, htf⟩ := ih (potential w) (by omega) w hw rfl
      refine ⟨t, htb, htt, htc.trans (maxMove_preserves_color hd hv hmove), ?_⟩
      exact htf.trans (hf v w hv hmove)

/-- Enumerating the nonnegative deficits from (k+1,k+1,k+1), whose sum is two. -/
theorem terminal_one_classification {k : ℕ} (hk : 1 ≤ k) {v : Vec}
    (hs : v.degree = 3 * k + 1) (ht : Terminal k v) :
    v = ⟨k + 1, k, k⟩ ∨ v = ⟨k, k + 1, k⟩ ∨ v = ⟨k, k, k + 1⟩ ∨
    v = ⟨k - 1, k + 1, k + 1⟩ ∨ v = ⟨k + 1, k - 1, k + 1⟩ ∨
    v = ⟨k + 1, k + 1, k - 1⟩ := by
  rcases v with ⟨x, y, z⟩
  simp only [Vec.degree, Terminal, Vec.mk.injEq] at *
  omega

/-- In the second residue class the deficits have sum one. -/
theorem terminal_two_classification {k : ℕ} {v : Vec}
    (hs : v.degree = 3 * k + 2) (ht : Terminal k v) :
    v = ⟨k, k + 1, k + 1⟩ ∨ v = ⟨k + 1, k, k + 1⟩ ∨
    v = ⟨k + 1, k + 1, k⟩ := by
  rcases v with ⟨x, y, z⟩
  simp only [Vec.degree, Terminal, Vec.mk.injEq] at *
  omega

private theorem terminal_one_body (k : ℕ) (hk : 3 ≤ k) :
    Body (3 * k + 1) ⟨k + 1, k, k⟩ ∧
    Body (3 * k + 1) ⟨k, k + 1, k⟩ ∧
    Body (3 * k + 1) ⟨k, k, k + 1⟩ := by
  simp only [Body, Vec.degree]
  omega

/-- The two terminal points of each colour are joined by one permitted move. -/
theorem terminal_one_constancy {k : ℕ} (hk : 3 ≤ k) (f : Vec → ℕ)
    (hf : PreservesMaxMoves (3 * k + 1) f) {u v : Vec}
    (hu : Body (3 * k + 1) u) (hv : Body (3 * k + 1) v)
    (htu : Terminal k u) (htv : Terminal k v) (hc : color u = color v) :
    f u = f v := by
  have hb := terminal_one_body k hk
  have hx : f ⟨k - 1, k + 1, k + 1⟩ = f ⟨k + 1, k, k⟩ := by
    have h := hf ⟨k + 1, k, k⟩ (moveX ⟨k + 1, k, k⟩) hb.1
      (Or.inl ⟨by simp, by simp, rfl⟩)
    simpa only [moveX, show k + 1 - 2 = k - 1 by omega] using h
  have hy : f ⟨k + 1, k - 1, k + 1⟩ = f ⟨k, k + 1, k⟩ := by
    have h := hf ⟨k, k + 1, k⟩ (moveY ⟨k, k + 1, k⟩) hb.2.1
      (Or.inr (Or.inl ⟨by simp, by simp, rfl⟩))
    simpa only [moveY, show k + 1 - 2 = k - 1 by omega] using h
  have hz : f ⟨k + 1, k + 1, k - 1⟩ = f ⟨k, k, k + 1⟩ := by
    have h := hf ⟨k, k, k + 1⟩ (moveZ ⟨k, k, k + 1⟩) hb.2.2
      (Or.inr (Or.inr ⟨by simp, by simp, rfl⟩))
    simpa only [moveZ, show k + 1 - 2 = k - 1 by omega] using h
  rcases terminal_one_classification (by omega : 1 ≤ k) hu.1 htu with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases terminal_one_classification (by omega : 1 ≤ k) hv.1 htv with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [color] at hc <;> omega

theorem terminal_two_constancy {k : ℕ} {u v : Vec}
    (hu : u.degree = 3 * k + 2) (hv : v.degree = 3 * k + 2)
    (htu : Terminal k u) (htv : Terminal k v) (hc : color u = color v) :
    u = v := by
  rcases terminal_two_classification hu htu with rfl | rfl | rfl <;>
    rcases terminal_two_classification hv htv with rfl | rfl | rfl <;>
    simp only [color] at hc <;> first | rfl | omega

/-- All parameters, with invariance explicitly exposed as a hypothesis. -/
theorem body_color_constancy {k r : ℕ} (hk : 3 ≤ k) (hr : r = 1 ∨ r = 2)
    (f : Vec → ℕ) (hf : PreservesMaxMoves (3 * k + r) f) {u v : Vec}
    (hu : Body (3 * k + r) u) (hv : Body (3 * k + r) v)
    (hc : color u = color v) : f u = f v := by
  obtain ⟨tu, hbu, htu, hcu, hfu⟩ := exists_terminal hk hr f hf u hu
  obtain ⟨tv, hbv, htv, hcv, hfv⟩ := exists_terminal hk hr f hf v hv
  have hct : color tu = color tv := hcu.trans (hc.trans hcv.symm)
  have heq : f tu = f tv := by
    rcases hr with rfl | rfl
    · exact terminal_one_constancy hk f hf hbu hbv htu htv hct
    · exact congrArg f (terminal_two_constancy hbu.1 hbv.1 htu htv hct)
  exact hfu.symm.trans (heq.trans hfv)

theorem body_color_constancy_of_nondvd {d : ℕ} (hd : 10 ≤ d) (hn : ¬ 3 ∣ d)
    (f : Vec → ℕ) (hf : PreservesMaxMoves d f) {u v : Vec}
    (hu : Body d u) (hv : Body d v) (hc : color u = color v) : f u = f v := by
  have hm : d % 3 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have hk : 3 ≤ d / 3 := by omega
  have hr : d % 3 = 1 ∨ d % 3 = 2 := by omega
  have he : 3 * (d / 3) + d % 3 = d := by omega
  exact body_color_constancy hk hr f (by simpa only [he] using hf)
    (by simpa only [he] using hu) (by simpa only [he] using hv) hc

#print axioms maxMove_preserves_body
#print axioms exists_terminal
#print axioms body_color_constancy
#print axioms body_color_constancy_of_nondvd

end Howroyd
