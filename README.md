# A multiplicity bound for three sparse cubes

Let $g_1,g_2,g_3$ be real polynomials with at most two nonzero monomials each, and let each $s_i$ be $+1$ or $-1$. If

$$
P(x)=s_1g_1(x)^3+s_2g_2(x)^3+s_3g_3(x)^3
$$

is nonzero, every positive real root of $P$ has multiplicity at most **nine**. The degrees and coefficients of the three polynomials are unrestricted.

This repository gives a Lean proof of the multiplicity bound posed as `L-gct-234` by the public P vs NP project. It also gives an exact rational certificate for the associated Taylor equations. [Public problem statement](https://data.pequalnp.com/data/lemma/L-gct-234.3830c091c201.json) · [Lean theorem](lean/SparseCubes.lean) · [Rational certificates and their checks](certificates/README.md)

## How the proof works

A root of multiplicity at least ten forces the first ten shifted moments to vanish. A binomial cube contributes at most four frequencies. The proof handles vanishing inputs and coincident means separately. For three distinct means, interpolation reduces the remaining case to two polynomial identities. Explicit integer cofactors certify both identities, and Lean proves that the computations on the coefficient lists agree with evaluation over the reals. [Shifted moments](lean/SparseCubes/Moments.lean) · [Reduction to the two charts](lean/SparseCubes/ChartDistinct.lean) · [Certificate checker](lean/SparseCubes/CertificateKernel.lean)

## Verify from source

With Elan installed, run from the repository root. The project pins Lean 4.36.0 and mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```sh
cd lean
lake exe cache get
lake build
lake env lean Verify.lean
```

The last command checks the public proposition by type ascription and prints the axioms used by `PEqualNP.Outside.L_gct_234`. They are `propext`, `Classical.choice`, and `Quot.sound`. [Exact type comparison](lean/Verify.lean)

## Replay the proof export

The [v1.0.0 release](https://github.com/Aargau/three-sparse-cubes/releases/tag/v1.0.0) includes the standalone proof export as a Zstandard archive. Put `L_gct_234.ndjson.zst` in the repository root. From the `lean` directory, run:

```sh
zstd -d ../L_gct_234.ndjson.zst -o ../L_gct_234.ndjson
leanchecker --from-export ../L_gct_234.ndjson
python -B ../scripts/check_lean_sparse_cube_export.py ../L_gct_234.ndjson PEqualNP.Outside.L_gct_234
```

The first checker is supplied by Lean. The Python wrapper runs Nanoda, an independent type checker implemented in Rust. Both accepted this export. Nanoda 0.4.17 checked **19,942 declarations** with zero errors using the three-axiom allowlist. To generate a fresh export after the source build, run `lake env leanexport SparseCubes -- PEqualNP.Outside.L_gct_234 > proof.ndjson` in a shell with byte-preserving redirection, such as Bash or PowerShell 7.4 or later. [Kernel replay transcripts](verification/kernel-replay.txt)

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `L_gct_234.ndjson.zst` | 42,211,603 | `8cc5ef5a4b129a4a3c915205e5526ca2dc26811cce347c0390c751f180b835da` |
| `L_gct_234.ndjson` | 324,778,005 | `8e73cd3df00998554074974ffa86c8cce9aad11b9da6fcd79a8e9d632a2f1446` |

## Contributors and acknowledgments

Justin Bronder directed the research and the cross-model verification effort, including the decision to pursue an exact rational certificate. OpenAI GPT-6.2 Astra agents working in Codex contributed mathematical derivations, computation, formalization, and fresh-context review. Google Gemini 4 Carbon High reviewed intermediate steps and suggested a finite-field Gröbner-basis experiment on the Taylor equations. Anthropic Claude Opus 5.5 reviewed the rational argument and an earlier snapshot of the Lean proof. The kernel checks above were run separately from those model reviews.

The public problem statement comes from the P vs NP project. This is an independent release of the multi-file proof and its certificates.
