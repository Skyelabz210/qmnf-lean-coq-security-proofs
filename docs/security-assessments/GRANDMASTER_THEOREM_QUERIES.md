### Component: Dual-RNS K-Elimination reconstruction

**Required Theorem**: kElimination_core
**File**: proofs/coq/KElimination.v:137
**Status**: PROVED

**Statement**:
```coq
Theorem kElimination_core : forall X M A : nat,
  coprime M A -> X < M * A ->
  let vM := X mod M in
  let vA := X mod A in
  let k := ((vA - vM) * inv_mod M A) mod A in
  X = vM + k * M.
```

**Coq Preconditions**:
1. coprime M A
2. X < M * A
3. M > 0, A > 0 (implicit)

**Rust Mapping**:
- nat -> u128
- Precondition -> `Nine65Error::NotCoprime`, `RangeOverflow`, `ModulusZero`, `AnchorZero`
- Postcondition -> debug_assert in `DualRNSContext::extract_k_*`

**If ADMITTED**: N/A

### Component: Exact division in dual coefficients

**Required Theorem**: div_exact
**File**: proofs/coq/ExactCoefficient.v:99
**Status**: PROVED

**Statement**:
```coq
Theorem div_exact : forall a : DualCoeff, forall d : nat,
  d > 0 -> Nat.divide d a.(dc_exact) ->
  (dual_div a d).(dc_exact) * d = a.(dc_exact).
```

**Coq Preconditions**:
1. d > 0
2. d divides a.dc_exact

**Rust Mapping**:
- nat -> u128
- Precondition -> `Nine65Error::InexactDivision`, `ModulusZero`
- Postcondition -> exact division in `exact_divide` and `KAnchor::exact_divide`

**If ADMITTED**: N/A

### Component: GSO-FHE depth bound

**Required Theorem**: depth_50_achievable
**File**: proofs/coq/GSOFHE.v:197
**Status**: PROVED

**Statement**:
```coq
Theorem depth_50_achievable : forall (config : GSOConfig) (init : NoiseEstimate),
  (* see file for full statement *)
```

**Coq Preconditions**:
1. Config thresholds consistent
2. init <= collapse threshold

**Rust Mapping**:
- Preconditions -> `Nine65Error::NoiseOverflow`, `DepthExceeded`
- Usage -> `crates/nine65/src/ops/gso_fhe.rs`

**If ADMITTED**: N/A

### Component: Persistent Montgomery multiplication

**Required Theorem**: mont_mul_correct
**File**: proofs/coq/MontgomeryPersistent.v:303
**Status**: PROVED

**Statement**:
```coq
Theorem mont_mul_correct : forall (p : MontParams) (x y : nat),
  p.(M) > 1 ->
  p.(R) >= p.(M) ->
  x < p.(M) -> y < p.(M) ->
  (* see file for full statement *)
```

**Coq Preconditions**:
1. M > 1
2. R >= M
3. x,y < M

**Rust Mapping**:
- nat -> u64/u128
- Preconditions -> parameter checks in Montgomery context setup

**If ADMITTED**: N/A

### Component: CRT Shadow entropy reconstruction

**Required Theorem**: shadow_reconstruction
**File**: proofs/coq/CRTShadowEntropy.v:43
**Status**: PROVED

**Statement**:
```coq
Theorem shadow_reconstruction : forall a b m : nat,
  (* see file for full statement *)
```

**Coq Preconditions**:
1. m > 0
2. a,b within modulus bounds

**Rust Mapping**:
- Usage -> `crates/nine65/src/entropy/crt_shadow.rs`
- Preconditions -> modulus checks when computing shadow signatures

**If ADMITTED**: N/A

### Component: Order finding (Fermat's little theorem)

**Required Theorem**: fermat_little
**File**: proofs/coq/OrderFinding.v:477
**Status**: ADMITTED

**Statement**:
```coq
Theorem fermat_little : forall a p : nat,
  is_prime p -> coprime a p ->
  Nat.pow a (p - 1) mod p = 1.
```

**Coq Preconditions**:
1. is_prime p
2. coprime a p

**Rust Mapping**:
- Preconditions -> `Nine65Error::NotCoprimeToModulus` checks
- Usage -> `crates/nine65/src/arithmetic/order_finding.rs`

**If ADMITTED**: Requires proof completion or explicit allowlist

### Component: State compression ratio bound

**Required Theorem**: sparse_20_compression
**File**: proofs/coq/StateCompression.v:171
**Status**: ADMITTED

**Statement**:
```coq
Theorem sparse_20_compression : compression_ratio_sparse 20 > ten_thousand.
```

**Coq Preconditions**:
1. Definitions of compression_ratio_sparse and ten_thousand

**Rust Mapping**:
- Usage -> `crates/nine65/src/quantum/taxonomy.rs` documentation claims

**If ADMITTED**: Requires proof completion or explicit allowlist
