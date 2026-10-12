import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Dist
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace Howroyd

structure Vec where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

def Vec.degree (v : Vec) : Nat := v.x + v.y + v.z

inductive Kind where
  | up
  | down
  deriving DecidableEq, Repr

structure Triangle where
  kind : Kind
  base : Vec
  deriving DecidableEq, Repr

def Triangle.Valid (d : Nat) (t : Triangle) : Prop :=
  t.base.degree + (match t.kind with | .up => 1 | .down => 2) = d

instance (d : Nat) (t : Triangle) : Decidable (t.Valid d) :=
  inferInstanceAs (Decidable (_ = _))

def triVertices (t : Triangle) : Finset Vec :=
  let b := t.base
  match t.kind with
  | .up => {⟨b.x + 1, b.y, b.z⟩, ⟨b.x, b.y + 1, b.z⟩, ⟨b.x, b.y, b.z + 1⟩}
  | .down => {⟨b.x + 1, b.y + 1, b.z⟩, ⟨b.x + 1, b.y, b.z + 1⟩,
      ⟨b.x, b.y + 1, b.z + 1⟩}

def ux (v : Vec) : Triangle := ⟨.up, ⟨v.x - 1, v.y, v.z⟩⟩
def uy (v : Vec) : Triangle := ⟨.up, ⟨v.x, v.y - 1, v.z⟩⟩
def uz (v : Vec) : Triangle := ⟨.up, ⟨v.x, v.y, v.z - 1⟩⟩
def dxy (v : Vec) : Triangle := ⟨.down, ⟨v.x - 1, v.y - 1, v.z⟩⟩
def dxz (v : Vec) : Triangle := ⟨.down, ⟨v.x - 1, v.y, v.z - 1⟩⟩
def dyz (v : Vec) : Triangle := ⟨.down, ⟨v.x, v.y - 1, v.z - 1⟩⟩

def incidentTriangles (v : Vec) : Finset Triangle :=
  (if 0 < v.x then {ux v} else ∅) ∪
  (if 0 < v.y then {uy v} else ∅) ∪
  (if 0 < v.z then {uz v} else ∅) ∪
  (if 0 < v.x ∧ 0 < v.y then {dxy v} else ∅) ∪
  (if 0 < v.x ∧ 0 < v.z then {dxz v} else ∅) ∪
  (if 0 < v.y ∧ 0 < v.z then {dyz v} else ∅)

def l1Distance (u v : Vec) : Nat :=
  Nat.dist u.x v.x + Nat.dist u.y v.y + Nat.dist u.z v.z

abbrev Vertex (d : Nat) := {v : Vec // v.degree = d}

def Adj {d : Nat} (u v : Vertex d) : Prop := l1Distance u.val v.val = 2

def vecBox (d : Nat) : Finset Vec :=
  (((Finset.range (d + 1)).product (Finset.range (d + 1))).product
    (Finset.range (d + 1))).image fun p => ⟨p.1.1, p.1.2, p.2⟩

def vertices (d : Nat) : Finset Vec := (vecBox d).filter fun v => v.degree = d

def triangles (d : Nat) : Finset Triangle :=
  (((vecBox d).image fun b => Triangle.mk .up b) ∪
    ((vecBox d).image fun b => Triangle.mk .down b)).filter fun t => t.Valid d

def Independent (I : Finset Vec) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ v → l1Distance u v ≠ 2

def MaximumIndependent (d : Nat) (I : Finset Vec) : Prop :=
  I ⊆ vertices d ∧ Independent I ∧
    ∀ J : Finset Vec, J ⊆ vertices d → Independent J → J.card ≤ I.card

noncomputable def maximumIndependentSets (d : Nat) : Finset (Finset Vec) := by
  classical
  exact (vertices d).powerset.filter (MaximumIndependent d)

/-- The independently stated original target, using labeled graph independent sets. -/
def Howroyd27 : Prop :=
  ∀ d : Nat, 10 ≤ d → ¬3 ∣ d → (maximumIndependentSets d).card = 27


end Howroyd


