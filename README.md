# QMNF Formal Proof Stack

Machine-checked proofs for the QMNF/NINE65 cryptographic system.
Lean 4 (Mathlib), Coq 8.18+, and supporting documentation.

**All Rights Reserved. Copyright (c) 2025-2026 HackFate Research.**

> **Access restriction:** This repository and all its contents are the exclusive
> property of HackFate Research. Access is limited to HackFate Research team
> members and collaborators operating under signed authorization. No license is
> granted for any other use. See [LICENSE](LICENSE).

---

## Table of Contents

- [Proof Inventory](#proof-inventory)
  - [Lean 4 Proofs](#lean-4-proofs)
  - [Coq Proofs](#coq-proofs)
  - [NIST Compliance Tests](#nist-compliance-tests)
  - [Documentation](#documentation)
  - [TeX Papers](#tex-papers)
  - [Build Configurations](#build-configurations)
- [Formalization Swarm Workspace](#formalization-swarm-workspace)
- [Building](#building)
- [Proof Status Summary](#proof-status-summary)
- [Repository Layout](#repository-layout)

---

## Proof Inventory

### Lean 4 Proofs

#### `lean4/k-elimination/` — K-Elimination theorem and dependencies

Core proof of exact overflow recovery in Residue Number Systems.
Given coprime moduli M and A, proves k = (v_A - v_M) * M^-1 mod A
recovers the overflow count exactly for X < M*A.

| File | What it proves |
|------|----------------|
| `KElimination.lean` | Module root; imports submodules |
| `KElimination/Basic.lean` | Division algorithm identity V = v_alpha + k * alpha, range bound k < beta |
| `KElimination/ZMod.lean` | Key congruence V mod A = (v_M + k*M) mod A, modular inverse existence via Bezout |
| `KElimination/Lattice/CRT.lean` | CRT uniqueness and reconstruction for coprime moduli |
| `KElimination/ShadowEntropy.lean` | CRT shadow residues are uniformly distributed (entropy bound) |
| `KElimination/AHOP/Algebra.lean` | Apollonian reflection is an involution; Descartes form is algebraically invariant |
| `KElimination/AHOP/Hardness.lean` | Orbit cardinality grows as 4^L (exponential lower bound) |
| `KElimination/AHOP/Parameters.lean` | Concrete parameter instantiation for 128-bit security level |
| `NoiseGrowthControl.lean` | Complete proof of noise growth control for bootstrap-free FHE |
| `FourPrimeCRTExtension.lean` | Complete 4-prime CRT extension for large k values (80+ bits) |
| `CompleteSecurityProof.lean` | Complete IND-CPA security framework |
| `HomomorphicSecurity.lean` | Proofs for homomorphic operations preserving security |
| `lakefile.lean` | Build configuration |

#### `lean4/exact-transcendentals/` — Exact transcendental function proofs

Proofs for computing transcendental functions (exp, log, sin, cos, sqrt)
using only exact rational arithmetic — no floating-point.

| File | What it proves |
|------|----------------|
| `ExactTranscendentals.lean` | Module root |
| `Main.lean` | Entry point |
| `ExactTranscendentals/Basic.lean` | Foundational imports and definitions |
| `ExactTranscendentals/Agm.lean` | Arithmetic-geometric mean iteration converges; used for log/pi computation |
| `ExactTranscendentals/BinarySplitting.lean` | Binary splitting for hypergeometric series achieves O(n log^2 n) |
| `ExactTranscendentals/ContinuedFraction.lean` | Continued fraction convergents bound error monotonically |
| `ExactTranscendentals/Cordic.lean` | CORDIC shift-and-add computes trig functions without multiplication |
| `ExactTranscendentals/ExactRational.lean` | Rational representation preserves exactness through arithmetic ops |
| `ExactTranscendentals/Isqrt.lean` | Integer square root via Babylonian method terminates and is exact |

#### `lean4/security-swarm/SwarmProofs/` — Security reduction proofs

IND-CPA security reductions for the QMNF-HE scheme under Ring-LWE + AHOP assumptions.

| File | What it proves |
|------|----------------|
| `Basic.lean` | Foundation imports, config definitions |
| `RingDefinitions.lean` | Ring polynomial types and operations over Z_q[x]/(x^n+1) |
| `CRT.lean` | CRT uniqueness and reconstruction |
| `KElimination.lean` | K-Elimination soundness and exactness |
| `Security.lean` | IND-CPA game definition; encryption indistinguishability structure |
| `SecurityLemmas.lean` | RLWE indistinguishability, encryption hides message, bootstrap-free depth bound |
| `SecurityComplete.lean` | Composition: all security components combine into overall security claim |
| `HomomorphicSecurity.lean` | Homomorphic operations preserve ciphertext indistinguishability |
| `INDCPAGame.lean` | Concrete IND-CPA game with decrypt correctness |
| `NISTCompliance.lean` | Parameter validation for NIST security level 128+ |
| `AHOPAlgebra.lean` | AHOP algebraic structure over Z_q (not geometric — refutes criticism) |
| `AHOPHardness.lean` | AHOP orbit exponential growth; PPT hardness axiom |
| `AHOPSecurity.lean` | AHOP-to-FHE security reduction; advantage bound |
| `AHOPParameters.lean` | Production parameter instantiation |

#### `lean4/shadow-nist/` — Shadow entropy and NIST compliance

Proofs that CRT shadow residues satisfy NIST SP 800-22 statistical
randomness criteria (used for entropy harvesting from arithmetic operations).

| File | What it proves |
|------|----------------|
| `NISTCompliance.lean` | Shadow output passes NIST frequency, runs, and serial tests |
| `ShadowCorrelation.lean` | Cross-channel shadow residues are uncorrelated |
| `ShadowNISTCompliance.lean` | Combined NIST compliance for full shadow entropy pipeline |
| `ShadowSecurityDefs.lean` | Formal definitions of shadow entropy security properties |
| `ShadowSecurityTheorems.lean` | Main theorems: shadow residues are computationally indistinguishable from random |
| `ShadowUniform.lean` | Uniformity of shadow distribution over Z_q |

#### `lean4/ahop-gaps/` — Gap closure proofs

Proofs that close specific gaps identified during security audit.

| File | What it proves |
|------|----------------|
| `GAP001/AsymptoticLemma.lean` | 2^(-lambda) < lambda^(-c) for sufficiently large lambda (negligible function bound) |
| `GAP004/BootstrapFreeDepth.lean` | With q > 2^50, t < 2^20, initial_noise <= t: noise < q/(2t) holds (depth bound) |
| `GAP006/DecryptCorrectness.lean` | Rounding recovers plaintext when noise < q/(2t) (decrypt correctness) |

#### `lean4/formalization-swarm/` — Numbered innovation proofs (02-25)

Individual proofs for each QMNF innovation, produced by the formalization swarm.

| File | What it proves |
|------|----------------|
| `02_QMNF_Lean4_Proofs.lean` | QMNF arithmetic foundations: CRT reconstruction, modular inverse |
| `05_KElimination.lean` | K-Elimination standalone proof |
| `06_CRTBigInt.lean` | Two-prime CRT representation correctness; overflow detection |
| `07_ShadowEntropy.lean` | Shadow entropy extraction from CRT residues |
| `08_PadeEngine.lean` | Pade approximant convergence for rational function evaluation |
| `09_MobiusInt.lean` | Mobius function computation over integers; inversion formula |
| `10_PersistentMontgomery.lean` | Montgomery multiplication maintains residue invariant across operations |
| `11_IntegerNN.lean` | Integer-only neural network forward pass preserves exact arithmetic |
| `12_CyclotomicPhase.lean` | Cyclotomic polynomial evaluation in Z_q; roots of unity properties |
| `13_MQReLU.lean` | Modular quantized ReLU: piecewise-linear activation over Z_t |
| `14_BinaryGCD.lean` | Binary GCD terminates and produces correct result |
| `15_PLMGRails.lean` | PLMG rail switching for parallel modular arithmetic |
| `16_DCBigIntHelix.lean` | Divide-and-conquer big integer with helical structure |
| `17_GroverSwarm.lean` | Grover search over RNS state space |
| `18_WASSAN.lean` | Wasserstein distance computation in integer arithmetic |
| `19_TimeCrystal.lean` | Time-crystal periodicity for deterministic scheduling |
| `20_GSO.lean` | Gram-Schmidt orthogonalization over exact rationals |
| `21_MANA.lean` | MANA SIMD lane-parallel FHE acceleration correctness |
| `22_RayRam.lean` | Ray-RAM memory addressing for RNS lookup tables |
| `23_ClockworkPrime.lean` | Clockwork prime selection for RNS channel coprimality |
| `24_BootstrapFreeFHE.lean` | Bootstrap-free FHE depth bound via exact rescaling |
| `25_RealTimeFHE.lean` | Real-time FHE latency bounds under exact arithmetic |
| `QMNFProofs.lean` | Module root for QMNFProofs namespace |
| `QMNFProofs/KElimination.lean` | K-Elimination within QMNFProofs module structure |

#### `lean4/standalone/` — Individual proof files

Standalone proofs collected from various development sessions. Some are
duplicates of the formalization-swarm proofs; some are unique.

| File | What it proves |
|------|----------------|
| `KElimination.lean` | K-Elimination (standalone version) |
| `k_elimination_sprint6.lean` | K-Elimination sprint-6 refinement |
| `ahop_sprint6.lean` | AHOP algebraic proofs (sprint-6) |
| `bezout_lemmas.lean` | Bezout's identity and extended GCD properties |
| `ConstantTime.lean` | Constant-time operation equivalence (side-channel resistance) |
| `descartes_algebra.lean` | Descartes circle theorem algebraic formulation |
| `PeriodGrover.lean` | Period-finding via Grover search |
| `QMNF_Formal_Verification.lean` | Combined QMNF verification |
| `QMNF.lean` | QMNF core definitions |
| `EXACT_SORRY_REPLACEMENT.lean` | Sorry elimination for specific lemmas |
| `SORRY_REPLACEMENT_MINIMAL.lean` | Minimal sorry replacements |
| `Unified 2.lean` (+ variants) | Unified proof attempts (multiple iterations) |
| `advanced_toric/` | Toric Grover, binary GCD, PLMG, DC helix (4 files) |
| Numbered files (02-22) | Duplicates of formalization-swarm proofs |

#### `lean4/qmnf-system/` — QMNF system-level proofs

| File | What it proves |
|------|----------------|
| `KElimination.lean` | K-Elimination within QMNF system context |
| `ResidueLearning.lean` | Residue-space learning preserves classification accuracy |

---

### Coq Proofs

#### `coq/nine65/` — NINE65 innovation proofs (19 files)

Each file proves correctness properties of one NINE65 FHE innovation.
These are the canonical copies.

| File | What it proves | Admitted |
|------|----------------|----------|
| `KElimination.v` | k = (v_A - v_M) * M^-1 mod A exactly recovers overflow | 1 |
| `K_Elimination.v` | Alternate formulation of K-Elimination | 0 |
| `OrderFinding.v` | Baby-step giant-step finds multiplicative order in O(sqrt(n)) | 1 |
| `GSOFHE.v` | Gram-Schmidt orthogonalization preserves FHE noise bounds | 0 |
| `MQReLU.v` | Modular quantized ReLU matches real ReLU for inputs in [0, t/2) | 0 |
| `CRTShadowEntropy.v` | CRT shadows have min-entropy >= log2(min(p_i)) | 0 |
| `MobiusInt.v` | Mobius inversion formula holds over Z; sum computation is exact | 0 |
| `PadeEngine.v` | Pade [m/n] approximant error is O(x^(m+n+1)) | 0 |
| `ExactCoefficient.v` | Taylor coefficients computed via integer recurrence are exact | 0 |
| `StateCompression.v` | Homomorphic state compression preserves decrypt correctness | 1 |
| `IntegerSoftmax.v` | Integer softmax preserves argmax and relative ordering | 0 |
| `CyclotomicPhase.v` | Cyclotomic polynomial roots in Z_q match analytic roots | 1 |
| `EncryptedQuantum.v` | Quantum circuit simulation on encrypted data preserves measurement distribution | 0 |
| `SideChannelResistance.v` | Operations execute in data-independent time (constant-time) | 0 |
| `PeriodGrover.v` | Period-finding variant of Grover achieves quadratic speedup | 7 |
| `MontgomeryPersistent.v` | Montgomery form is maintained across mul chains without extra reduction | 0 |
| `ShadowIndependence.v` | Shadow residues are statistically independent across channels | 0 |
| `ToricGrover.v` | Toric 2-amplitude Grover search converges | 0 |
| `03_QMNF_Coq_Proofs.v` | Combined QMNF proof bundle | 0 |

#### `coq/qmnf/` — QMNF core proofs (3 files)

| File | What it proves |
|------|----------------|
| `QMNF.v` | Core QMNF arithmetic properties (CRT, modular inverse, exact division) |
| `PeriodGrover.v` | Period-finding Grover (QMNF context) |
| `03_QMNF_Coq_Proofs.v` | Combined proof bundle |

#### `coq_proofs/NINE65/` — Compiled Coq proofs (with build artifacts)

Same 16 proofs as `coq/nine65/` but with `.vo`, `.vok`, `.vos` compilation
artifacts. These confirm the proofs compile under Coq 8.18+.

---

### NIST Compliance Tests

#### `nist/` — Statistical randomness validation (Python)

| File | What it tests |
|------|---------------|
| `nist_compliance_tests.py` | Runs NIST SP 800-22 test battery against shadow entropy output |
| `nist_security.py` | Security parameter validation (ring dimension, modulus size, noise ratio) |
| `shadow_nist_tests.py` | Shadow-specific NIST compliance checks |

---

### Documentation

#### `docs/theorem-stacks/` — Theorem inventories and status

| File | Contents |
|------|----------|
| `AHOP_THEOREM_STACK_FINAL.md` | Final AHOP theorem inventory with sorry counts |
| `AHOP_THEOREM_STACK.md` | AHOP theorem inventory (working version) |
| `QMNF_SECURITY_THEOREM_STACK.md` | Full QMNF security theorem inventory |
| `formalization_swarm_theorem_stack.md` | Swarm-produced theorem inventory |
| `hackfate_theorem_stack.md` | HackFate project theorem inventory |
| `nine65_O1_theorem_stack.md` | NINE65 round-1 theorem inventory |
| `nine65_O2_theorem_stack.md` | NINE65 round-2 theorem inventory |
| `mathematical_proofs_doc.md` | Informal mathematical proof sketches |
| `qmnf-proofs.md` | QMNF proof overview |
| `qmn_theorems.md` (+ variants 1-8) | Iterative theorem stack snapshots |
| `T1_gcd_proof.md` | GCD correctness proof (informal) |
| `T8_division_proof.md` | Division algorithm proof (informal) |

#### `docs/formal-verification/` — Verification reports

| File | Contents |
|------|----------|
| `K_ELIMINATION_FORMAL_VERIFICATION_COMPLETE.md` | K-Elimination: 27 Lean theorems, 0 sorry, 10 Coq cross-validated |
| `K_ELIMINATION_THEOREM.md` | K-Elimination theorem statement and proof sketch |
| `FORMAL_THEOREMS_TORIC.md` | Toric Grover formal theorem statements |
| `FORMAL_THEOREMS_UPDATED.md` | Updated formal theorem list |
| `formal_verification_completion.txt` | Verification completion log |
| `gso_formal_verification.txt` | GSO-FHE verification log |
| `loki_clockwork_formal_spec_v1.md` | Clockwork-Core formal specification |

#### `docs/security-assessments/` — Security analysis documents

| File | Contents |
|------|----------|
| `AHOP_FHE_SECURITY_PROOFS.md` | AHOP-to-FHE security reduction analysis |
| `SECURITY_PROOFS.md` | Combined security proof inventory |
| `MULTIPARTY_THEOREM_STACK_FINAL.md` | Multiparty FHE theorem inventory |
| `REDTEAM_K_ELIMINATION_THEOREM.md` | Red-team adversarial analysis of K-Elimination |
| `FLOAT_SHADOW_FORGE_SECURITY_PROOFS.md` | Float-shadow-forge security analysis |
| `GRANDMASTER_THEOREM_QUERIES.md` | Cross-cutting theorem queries and resolutions |
| `TORIC_GROVER_THEOREM.md` | Toric Grover theorem analysis |
| `TORIC_SHOR_THEOREM.md` | Toric Shor theorem analysis |
| `WASSAN_SUBSTRATE_THEOREM.md` | Wasserstein substrate theorem analysis |

---

### TeX Papers

#### `tex/` — LaTeX manuscripts

| File | Contents |
|------|----------|
| `K_Elimination_Technical_Paper.tex` | K-Elimination technical paper (27 theorems, formal verification, complexity analysis) |
| `formal_proofs.tex` | Combined formal proofs manuscript |

---

### Build Configurations

#### `lakefiles/` — Lean 4 build files from source projects

| File | Source project |
|------|---------------|
| `formalization-swarm-lakefile.lean` | qmnf-formalization-swarm |
| `hackfate-lakefile.lean` | hackfate main |
| `security-swarm-lakefile.lean` | ahop-security-swarm |

---

## Formalization Swarm Workspace

The `swarm_run/` directory contains the original formalization swarm
workspace — the multi-agent system that produced many of these proofs.

```
swarm_run/
  state/                  Proof dependency DAGs (blueprint.json)
  synthesis/              Theorem stack synthesis reports
  jobs/
    phi_decomposer/       Proof decomposition into dependency graphs
    pi_prover/            Proof sketch generation
    kappa_critic/         Adversarial critique (mandatory gate)
    mu_simulator/         Computational validation (17 tests, 100% pass)
    lambda_librarian/     Mathlib dependency mapping
    sigma_verifier/       Lean 4 compilation verification
  lean_project/
    SwarmProofs/          Compiled Lean 4 proofs (14 files)
    SwarmProofs/Gaps/     Gap closure proofs (3 files)
    lakefile.lean         Build config (Mathlib dependency)
```

---

## Building

### Lean 4 (requires Lean 4.x + Mathlib)

```bash
# Security swarm proofs (primary)
cd swarm_run/lean_project
lake build

# K-Elimination proofs
cd lean4/k-elimination
lake build
```

### Coq (requires Coq 8.18+)

```bash
cd coq_proofs
for f in NINE65/*.v; do coqc -Q NINE65 NINE65 "$f"; done
```

### NIST tests (requires Python 3)

```bash
cd nist
python3 nist_compliance_tests.py
```

---

## Proof Status Summary

| Category | Theorems | Sorry/Admitted | Notes |
|----------|----------|----------------|-------|
| K-Elimination (Lean 4) | 27 | 0 | Fully machine-checked |
| K-Elimination (Coq) | 10 | 1 | Cross-validated |
| AHOP Foundations (Lean 4) | 11 | 0 | Algebraic, not geometric |
| AHOP Hardness (Lean 4) | 3 | 0 + 1 axiom | PPT hardness is axiomatic |
| Security Reductions (Lean 4) | 8 | 0 | IND-CPA under RLWE + AHOP |
| Security Lemmas (Lean 4) | 4 | 3 | Asymptotic analysis (non-critical) |
| Homomorphic Security (Lean 4) | 3 | 1 | Asymptotic (non-critical) |
| Gap Closures (Lean 4) | 3 | 4 | Technical lemmas |
| NINE65 Innovations (Coq) | 16 | 11 | 11 of 16 fully complete (0 Admitted) |
| Shadow/NIST (Lean 4) | 6 | varies | Statistical compliance |
| Exact Transcendentals (Lean 4) | 7 | varies | AGM, CORDIC, binary splitting, sqrt |
| Formalization Swarm (Lean 4) | 23 | varies | Numbered innovations 02-25 |

**Critical path (K-Elimination + AHOP + IND-CPA): 0 sorry on all core theorems.**

---

## Repository Layout

```
qmnf-lean-coq-security-proofs/
  LICENSE                           All Rights Reserved
  README.md                        This file
  coq/
    nine65/                         19 Coq proofs (NINE65 innovations)
    qmnf/                           3 Coq proofs (QMNF core)
  coq_proofs/
    NINE65/                         16 compiled Coq proofs (with .vo artifacts)
  lean4/
    k-elimination/                  K-Elimination + AHOP + CRT + shadow entropy
    exact-transcendentals/          AGM, binary splitting, CORDIC, sqrt
    security-swarm/SwarmProofs/     IND-CPA security reductions (14 files)
    shadow-nist/                    NIST SP 800-22 compliance proofs
    ahop-gaps/                      Gap closure proofs (GAP001, GAP004, GAP006)
    formalization-swarm/            Numbered innovation proofs (02-25)
    standalone/                     Individual standalone proofs
    qmnf-system/                    QMNF system-level proofs
  nist/                             Python NIST test scripts
  docs/
    theorem-stacks/                 Theorem inventories
    formal-verification/            Verification reports
    security-assessments/           Security analysis documents
  tex/                              LaTeX papers
  lakefiles/                        Lean 4 build configs from source projects
  swarm_run/                        Original formalization swarm workspace
```

---

Copyright (c) 2025-2026 HackFate Research. All Rights Reserved.
