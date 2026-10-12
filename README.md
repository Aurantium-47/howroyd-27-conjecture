# Howroyd's 27-set conjecture: proof and complete classification

**An AI-generated, computer-assisted proof of the remaining 27-set case of a conjecture recorded by Andrew Howroyd in 2018.** This repository contains the mathematical manuscript, an exact rational certificate, and reproducible checks.

[Read the paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [中文介绍](README.zh-CN.md) · [AI use and verification](AI_USAGE.md)

## An eight-year-old question, with a concrete answer

Howroyd recorded the conjecture in [OEIS A297557 on 1 January 2018](https://oeis.org/A297557/internal). John Machacek subsequently stated it as Conjecture 1.1 and proved the divisible-by-three branch in [*Unique maximum independent sets in graphs on monomials of a fixed degree*](https://arxiv.org/abs/2010.11112v2), first posted in 2020 and published in 2021.

The result presented here addresses the other two residue classes: **there are exactly 27 maximum independent sets, and the proof describes every one of them.** It uses a finite exact certificate together with a mathematical argument covering every allowed graph size. This is not an extrapolation from computing a long sequence of examples.

As of this draft's 13 October 2026 literature checks, we did not locate an earlier proof of the full 27-count statement. The date of the conjecture does not establish that nobody has solved it in the intervening years. Related maximum-size formulas and the general weighted-cover method are already known and are credited in the paper.

## The theorem

Let $G_3(d)$ have vertex set

$$V_d=\{(x_1,x_2,x_3)\in\mathbb Z_{\ge0}^3:x_1+x_2+x_3=d\},$$

with two distinct vertices adjacent when their $\ell_1$ distance is $2$. Write $a_3(d)$ for the number of **maximum-cardinality** independent sets, counted as labeled vertex sets, without quotienting by symmetry.

The manuscript proves

$$a_3(d)=27\qquad\text{for }d\ge10\text{ with }3\nmid d.$$

Together with Machacek's already-proved branch, this yields Howroyd's formula for all $d\ge9$: one maximum set when $3\mid d$, and 27 otherwise.

The classification is explicit: away from three small corners, every maximum set agrees with exactly one of three natural color classes. Each background has $1\times3\times3=9$ compatible corner extensions. Thus $3\times9=27$.

## Proof materials and checks

- [main.pdf](main.pdf) / [main.tex](main.tex): the proof, classification, full 89-entry certificate, references, and verification status.
- [howroyd_cover_weights.csv](howroyd_cover_weights.csv): 89 rational triangle weights, all with denominator 60.
- [verify_howroyd_certificate.py](verify_howroyd_certificate.py): exact integer checks of the certificate, base equations, and corner cases.
- [referee_checks.py](referee_checks.py): a separately written structural check and a whole-graph dynamic program.
- [results](results): recorded local outputs. [MANIFEST_SHA256.json](MANIFEST_SHA256.json) identifies the distributed file contents.

Run from this directory with Python 3.10 or later; no third-party Python packages are required:

```sh
python verify_howroyd_certificate.py
python referee_checks.py structural --csv howroyd_cover_weights.csv
python referee_checks.py dp --max-degree 20
```

All three commands passed locally. Structural checks cover the allowed degrees through 60. The dynamic program independently counts maximum sets for every degree from 0 through 20, without using the certificate or the classification. The proof for all degrees rests on the manuscript's coordinate reduction and balancing argument, not on finite checks alone.

The CSV and referee program are unchanged from the reviewed materials. Only three documentation/output filename references in the original verifier were changed to point to `main.tex`; its algorithm is unchanged.

## Public draft and AI research record

**Release status: public research draft, open to corrections.** The submitted proof received an ACCEPT assessment in a separate ChatGPT Pro conversation. This is an AI mathematical review, not journal acceptance or human expert peer review. Full proof-assistant formalization has not been completed.

The human operator supplied the objective and relayed material. ChatGPT Pro generated the mathematical argument and certificate; a separate Pro conversation reviewed them and supplied additional checks. Codex coordinated source checks, reproduction, and manuscript preparation. See [AI_USAGE.md](AI_USAGE.md) and [editorial_changes.md](editorial_changes.md) for the recorded roles and editing history.

The initial public version is preserved in Git history and a release tag; later corrections will be recorded in [CHANGELOG.md](CHANGELOG.md). A public timestamp records availability of a version; it does not, by itself, establish mathematical correctness or scholarly priority. Please cite a specific commit or release when discussing the result. Concrete corrections and references to prior solutions are welcome through repository issues.

Repository maintainer: [Aurantium-47](https://github.com/Aurantium-47). Manuscript author metadata and an additional redistribution license have not yet been set.

## Primary sources

1. [OEIS A297557](https://oeis.org/A297557/internal): Howroyd's 2018 conjecture.
2. [Machacek, arXiv:2010.11112v2](https://arxiv.org/abs/2010.11112v2): Conjecture 1.1 and the divisible-by-three branch. The paper includes a clearly labeled local correction to a deletion statement in this arXiv version.
3. [Zabokritskiy, arXiv:2607.13733v3](https://arxiv.org/abs/2607.13733v3): related weighted local-cover methods and maximum-size results.
4. [Kreindel, Barouch Essayag, and Zabokritskiy, arXiv:2601.05636v2](https://arxiv.org/abs/2601.05636v2): related multiset-code size and uniqueness results.

The general covering method and maximum-size formula are not claimed as new. The contribution presented here is the count and complete classification in the remaining two residue classes.
