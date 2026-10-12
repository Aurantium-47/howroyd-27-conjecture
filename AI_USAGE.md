# AI use and verification record

Version: 13 October 2026. This describes the verification completed for this public research draft.

The mathematical argument and exact certificate were generated using AI. AI was also used for mathematical review, source checking, manuscript preparation, and formalization.

## What has been checked

- The 89-entry exact certificate and finite corner tables were checked using integer arithmetic.
- A separately written graph/triangle implementation reproduced the specified structural checks through degree 60, and a certificate-independent dynamic program reproduced the full-graph counts through degree 20.
- AI mathematical review addressed the all-degree reduction, positivity needed by balancing moves, body classification, and completeness of the corner count.
- The Lean 4 proof of the 27-set theorem for every `d >= 10` with `3` not dividing `d` has compiled locally. Its reported axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. The source and build instructions are in [lean/README.md](lean/README.md); the final theorem is in [lean/Howroyd/Main.lean](lean/Howroyd/Main.lean).
- The cited 2026 sources were examined in the versions identified in the manuscript. This was a targeted literature assessment, not an exhaustive priority certification.

The commands and recorded results are provided in [README.md](README.md) and [results](results). They require Python 3.10 or later and its standard library.

The known divisible-by-three branch is not proved in this Lean project. No external independent kernel check or human mathematical expert review has been completed. The Python reruns establish reproducibility of the finite checks; the all-degree 27-set claim has both the manuscript's argument and a locally compiled formal proof. AI review does not establish journal acceptance, and formalization does not establish scholarly priority.
