# Lean proof of the 27-set theorem

This project proves that, for every natural number `d >= 10` with `3 ∤ d`, the graph on nonnegative integer triples of sum `d`, adjacent at L1 distance 2, has exactly **27 maximum-cardinality independent sets**. Vertices retain their coordinate labels; no quotient by rotations or reflections is taken.

The final declarations in [`Howroyd/Main.lean`](Howroyd/Main.lean) are:

```lean
theorem maximum_independent_sets_card (d : Nat) (hd : 10 ≤ d) (hr : ¬3 ∣ d) :
    (maximumIndependentSets d).card = 27

theorem howroyd_27 : Howroyd27
```

`Howroyd27` and `maximumIndependentSets` are defined in [`Howroyd/Basic.lean`](Howroyd/Basic.lean) directly from the graph and maximum cardinality, independently of the later classification. The proof includes an exact weighted cover for all permitted degrees, saturation, the body-color classification, the complete corner classification, and the bijective count. The already-known uniqueness branch `3 ∣ d` is outside this project's scope.

## Build and check

Install [Lean using elan](https://github.com/leanprover/elan). The checked-in toolchain selects Lean **4.19.0**. The dependency manifest pins mathlib **v4.19.0**, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and its dependencies.

From this `lean` directory, run:

```sh
lake exe cache get
lake build
lake env lean -j 2 -s 131072 Howroyd/Audit.lean
lake env lean -j 2 -s 131072 Howroyd/SemanticAudit.lean
```

The first command obtains mathlib's compiled dependency cache. `lake build` compiles the proof. `Audit.lean` prints the graph definitions, target, and transitive axiom dependencies. `SemanticAudit.lean` checks an expanded formulation of the count over all independent vertex sets. The resource arguments limit workers and increase thread-stack space; they do not bypass proof checking.

## Proof dependencies

For both final theorems, the transitive axiom list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are the standard axioms used here. There are no unfinished proof placeholders or additional mathematical axioms. Finite checks use kernel reduction (`decide` / `decide +kernel`), not native computation. The unbounded degree parameter is handled by proofs, including strong induction, rather than finite sampling.

Verification uses Lean's normal kernel checking with the pinned dependencies. No additional external proof kernel has been used. As with any formalization, the graph definitions and statement should also be compared with the mathematical question.

Lean and mathlib are external dependencies, not vendored here. Their licenses are available upstream: [Lean 4.19.0 license](https://github.com/leanprover/lean4/blob/v4.19.0/LICENSE), [mathlib v4.19.0 license](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/LICENSE). Further dependency versions and source URLs are recorded in [`lake-manifest.json`](lake-manifest.json).
