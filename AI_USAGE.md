# AI use and verification record

Version: 13 October 2026. This describes the work actually completed for this public research draft.

## Roles

- A human operator supplied the research objective, selected the webpage Pro service, and transferred prompts and files. The project did not rely on the operator to supply the mathematical proof steps.
- An exploratory ChatGPT Pro conversation proposed the Howroyd target, produced the proof draft and rational certificate, and supplied the original verifier.
- A separate ChatGPT Pro conversation assessed the submitted argument, returned ACCEPT, wrote an additional structural checker and whole-graph dynamic program, and identified relevant literature and a local correction to the cited Machacek proof.
- Codex coordinated source checks, preserved the original materials, inspected and reran the programs, and prepared the English LaTeX manuscript and reproducibility package. Dedicated contexts handled the source checks and program reproduction. The mathematical content of the manuscript is traced to the submitted proof and explicit review elaborations in `editorial_changes.md`.

The two Pro conversations do not establish reviewer independence across model families. No specific underlying model snapshot is asserted here because a verified snapshot identifier was not captured in the project record.

## What has been checked

- The 89-entry exact certificate and finite corner tables were checked using integer arithmetic.
- A separately written graph/triangle implementation reproduced the specified structural checks through degree 60, and a certificate-independent dynamic program reproduced the full-graph counts through degree 20.
- The mathematical review addressed the all-degree reduction, positivity needed by balancing moves, bulk classification, and the completeness of the corner count.
- The two newly identified 2026 sources were read in the relevant versions and checked for coverage of the claimed result. This was a targeted literature assessment, not an exhaustive priority certification.

No full proof-assistant formalization or human mathematical expert review has been completed. Finite Python checks are not described as Lean verification. The local rerun checks reproducibility; it is not a second independent all-degree proof.

## Timing and cost record

The exploration page displayed 49m47s of thinking and the mathematical review page displayed 16m49s. These are interface observations for two successful conversations, not total project effort, a complete attempt history, or token counts. Reliable per-run token consumption was not available. There were no paid API calls for the local preparation and reproduction described here.

The initial search, certificate generation, mathematical proof, later review, and local editing are distinct stages. The draft does not attribute invented mathematical work to a human author or claim that a model verdict establishes publication acceptance.
