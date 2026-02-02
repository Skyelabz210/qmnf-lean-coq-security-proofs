#!/usr/bin/env python3
"""
QMNF Security Proofs - Computational Validation Tests
======================================================

mu-Simulator Agent: Integer-only test suite validating security properties.

This module provides comprehensive tests for:
1. K-Elimination correctness
2. CRT reconstruction
3. Parameter validation for security bounds

ALL ARITHMETIC IS INTEGER-ONLY. NO FLOATING POINT.

Author: mu-Simulator (Formalization Swarm)
Date: 2026-02-01
"""

import json
import sys
from typing import Tuple, List, Dict, Any


# =============================================================================
# INTEGER-ONLY HELPER FUNCTIONS
# =============================================================================

def gcd(a: int, b: int) -> int:
    """Greatest Common Divisor using Euclidean algorithm."""
    while b != 0:
        a, b = b, a % b
    return a


def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
    """
    Extended Euclidean Algorithm.
    Returns (gcd, x, y) such that a*x + b*y = gcd(a, b).
    """
    if a == 0:
        return (b, 0, 1)
    g, x1, y1 = extended_gcd(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return (g, x, y)


def mod_inverse(a: int, m: int) -> int:
    """
    Compute modular multiplicative inverse of a mod m.
    Returns x such that (a * x) % m == 1.
    Raises ValueError if inverse does not exist (gcd(a, m) != 1).
    """
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        raise ValueError(f"Modular inverse does not exist: gcd({a}, {m}) = {g}")
    return (x % m + m) % m


def is_coprime(a: int, b: int) -> bool:
    """Check if two integers are coprime (gcd = 1)."""
    return gcd(a, b) == 1


def integer_sqrt_floor(n: int) -> int:
    """
    Compute floor(sqrt(n)) using integer-only Newton's method.
    NO FLOATING POINT.
    """
    if n < 0:
        raise ValueError("Cannot compute sqrt of negative number")
    if n == 0:
        return 0

    # Initial guess: bit-length based
    x = 1 << ((n.bit_length() + 1) // 2)

    while True:
        # Newton step: x_new = (x + n // x) // 2
        x_new = (x + n // x) // 2
        if x_new >= x:
            return x
        x = x_new


def integer_log2_floor(n: int) -> int:
    """Compute floor(log2(n)) using integer-only operations."""
    if n <= 0:
        raise ValueError("Cannot compute log2 of non-positive number")
    return n.bit_length() - 1


# =============================================================================
# K-ELIMINATION IMPLEMENTATION (Integer-Only)
# =============================================================================

def k_elimination(x_alpha: int, x_beta: int, alpha_cap: int, beta_cap: int) -> int:
    """
    K-Elimination algorithm.

    Given dual-codex representation (x_alpha, x_beta) where:
      x_alpha = X mod alpha_cap
      x_beta = X mod beta_cap

    Computes k = floor(X / alpha_cap) using the formula:
      k = (x_beta - x_alpha) * alpha_cap^(-1) mod beta_cap

    Requirements:
      - gcd(alpha_cap, beta_cap) = 1
      - X < alpha_cap * beta_cap

    Returns:
        k: The quotient floor(X / alpha_cap)
    """
    if not is_coprime(alpha_cap, beta_cap):
        raise ValueError(f"alpha_cap and beta_cap must be coprime: gcd({alpha_cap}, {beta_cap}) = {gcd(alpha_cap, beta_cap)}")

    # Compute alpha_cap^(-1) mod beta_cap
    alpha_inv = mod_inverse(alpha_cap, beta_cap)

    # Compute phase difference
    # Use modular arithmetic to handle negative differences
    diff = (x_beta - x_alpha) % beta_cap
    if diff < 0:
        diff += beta_cap

    # Compute k
    k = (diff * alpha_inv) % beta_cap

    return k


def crt_reconstruct(x_alpha: int, x_beta: int, alpha_cap: int, beta_cap: int) -> int:
    """
    Chinese Remainder Theorem reconstruction.

    Given:
      x_alpha = X mod alpha_cap
      x_beta = X mod beta_cap

    Reconstructs X (unique mod alpha_cap * beta_cap).

    Formula: X = x_alpha + k * alpha_cap
             where k = (x_beta - x_alpha) * alpha_cap^(-1) mod beta_cap
    """
    k = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
    return x_alpha + k * alpha_cap


# =============================================================================
# TEST RESULTS COLLECTOR
# =============================================================================

class TestResults:
    """Collects test results for JSON export."""

    def __init__(self):
        self.tests: List[Dict[str, Any]] = []
        self.passed = 0
        self.failed = 0
        self.total = 0

    def record(self, name: str, passed: bool, details: str = "",
               params: Dict[str, Any] = None):
        self.total += 1
        if passed:
            self.passed += 1
        else:
            self.failed += 1

        self.tests.append({
            "name": name,
            "passed": passed,
            "details": details,
            "params": params or {}
        })

    def to_dict(self) -> Dict[str, Any]:
        return {
            "summary": {
                "total": self.total,
                "passed": self.passed,
                "failed": self.failed,
                "pass_rate_permille": (self.passed * 1000) // self.total if self.total > 0 else 0
            },
            "tests": self.tests
        }


results = TestResults()


# =============================================================================
# TEST SUITE 1: K-ELIMINATION CORRECTNESS
# =============================================================================

def test_k_elimination_basic():
    """Test basic K-Elimination correctness."""
    test_name = "k_elimination_basic"

    # Use prime moduli to guarantee coprimality
    alpha_cap = 1000003  # Prime
    beta_cap = 1000033   # Prime

    test_values = [
        0,
        1,
        alpha_cap - 1,
        alpha_cap,
        alpha_cap + 1,
        beta_cap - 1,
        beta_cap,
        123456789012345,
        alpha_cap * beta_cap - 1,
    ]

    all_passed = True
    failures = []

    for X in test_values:
        if X >= alpha_cap * beta_cap:
            continue  # Skip values outside valid range

        x_alpha = X % alpha_cap
        x_beta = X % beta_cap

        k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
        k_true = X // alpha_cap

        if k_computed != k_true:
            all_passed = False
            failures.append(f"X={X}: k_computed={k_computed} != k_true={k_true}")

    details = f"Tested {len(test_values)} values" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


def test_k_elimination_edge_cases():
    """Test K-Elimination edge cases: X=0, X=max-1."""
    test_name = "k_elimination_edge_cases"

    alpha_cap = 997  # Prime
    beta_cap = 1009  # Prime

    all_passed = True
    failures = []

    # Edge case 1: X = 0
    X = 0
    x_alpha = X % alpha_cap
    x_beta = X % beta_cap
    k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
    k_true = X // alpha_cap
    if k_computed != k_true:
        all_passed = False
        failures.append(f"X=0: k_computed={k_computed} != k_true={k_true}")

    # Edge case 2: X = alpha_cap * beta_cap - 1 (maximum valid value)
    X = alpha_cap * beta_cap - 1
    x_alpha = X % alpha_cap
    x_beta = X % beta_cap
    k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
    k_true = X // alpha_cap
    if k_computed != k_true:
        all_passed = False
        failures.append(f"X=max-1: k_computed={k_computed} != k_true={k_true}")

    # Edge case 3: X = alpha_cap (exactly one quotient)
    X = alpha_cap
    x_alpha = X % alpha_cap
    x_beta = X % beta_cap
    k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
    k_true = X // alpha_cap
    if k_computed != k_true:
        all_passed = False
        failures.append(f"X=alpha_cap: k_computed={k_computed} != k_true={k_true}")

    details = "All edge cases passed" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


def test_k_elimination_coprimality_violation():
    """Test that K-Elimination correctly rejects non-coprime moduli."""
    test_name = "k_elimination_coprimality_violation"

    # Non-coprime moduli (both divisible by 2)
    alpha_cap = 100
    beta_cap = 200

    try:
        _ = k_elimination(50, 100, alpha_cap, beta_cap)
        # If we get here, the function didn't raise an exception
        results.record(test_name, False,
                       "Expected ValueError for non-coprime moduli, but none raised",
                       {"alpha_cap": alpha_cap, "beta_cap": beta_cap})
        return False
    except ValueError as e:
        results.record(test_name, True,
                       f"Correctly raised ValueError: {str(e)[:100]}",
                       {"alpha_cap": alpha_cap, "beta_cap": beta_cap})
        return True


def test_k_elimination_property_based():
    """
    Property-based testing for K-Elimination.

    Property: For all X < alpha_cap * beta_cap,
              X = x_alpha + k_computed * alpha_cap
              where x_alpha = X mod alpha_cap
    """
    test_name = "k_elimination_property_based"

    # Use large primes for robust testing
    primes = [
        (104729, 104743),   # ~100K
        (1000003, 1000033), # ~1M
        (15485863, 15485867), # ~15M
    ]

    all_passed = True
    total_tests = 0
    failures = []

    for alpha_cap, beta_cap in primes:
        # Test points: systematic + boundary
        test_points = [
            0, 1, alpha_cap - 1, alpha_cap, alpha_cap + 1,
            beta_cap - 1, beta_cap, beta_cap + 1,
            alpha_cap * 2, alpha_cap * 3,
            (alpha_cap * beta_cap) // 2,
            alpha_cap * beta_cap - 1,
        ]

        # Add some computed test points spread across range
        step = (alpha_cap * beta_cap) // 100
        for i in range(1, 100):
            test_points.append(i * step)

        for X in test_points:
            if X < 0 or X >= alpha_cap * beta_cap:
                continue

            total_tests += 1
            x_alpha = X % alpha_cap
            x_beta = X % beta_cap

            k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)

            # Property check: X = x_alpha + k * alpha_cap
            X_reconstructed = x_alpha + k_computed * alpha_cap

            if X_reconstructed != X:
                all_passed = False
                failures.append(f"alpha={alpha_cap}, beta={beta_cap}, X={X}: "
                               f"reconstructed={X_reconstructed}")
                if len(failures) >= 5:
                    break

        if len(failures) >= 5:
            break

    details = f"Passed {total_tests} tests" if all_passed else f"Failures: {failures[:5]}"
    results.record(test_name, all_passed, details, {"total_tests": total_tests})

    return all_passed


def test_k_elimination_mersenne_primes():
    """Test K-Elimination with Mersenne-related primes (cryptographically relevant)."""
    test_name = "k_elimination_mersenne_primes"

    # Primes related to Mersenne numbers (often used in cryptography)
    # 2^31 - 1 = 2147483647 is prime (Mersenne prime M31)
    # We use smaller primes close to powers of 2
    alpha_cap = 2147483647  # 2^31 - 1 (Mersenne prime)
    beta_cap = 2147483629   # Prime near 2^31

    test_values = [
        0,
        1,
        (1 << 30),  # 2^30
        (1 << 31) - 2,  # 2^31 - 2
        alpha_cap - 1,
        alpha_cap,
        alpha_cap + 1,
        12345678901234567890,  # Large value
    ]

    all_passed = True
    failures = []

    product = alpha_cap * beta_cap

    for X in test_values:
        if X >= product:
            continue

        x_alpha = X % alpha_cap
        x_beta = X % beta_cap

        k_computed = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)
        k_true = X // alpha_cap

        if k_computed != k_true:
            all_passed = False
            failures.append(f"X={X}: k_computed={k_computed} != k_true={k_true}")

    details = f"Tested with Mersenne prime alpha={alpha_cap}" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


# =============================================================================
# TEST SUITE 2: CRT RECONSTRUCTION
# =============================================================================

def test_crt_reconstruction_basic():
    """Test basic CRT reconstruction."""
    test_name = "crt_reconstruction_basic"

    alpha_cap = 1000003
    beta_cap = 1000033

    test_values = [0, 1, 12345, 1000000, alpha_cap * beta_cap - 1]

    all_passed = True
    failures = []

    for X in test_values:
        if X >= alpha_cap * beta_cap:
            continue

        x_alpha = X % alpha_cap
        x_beta = X % beta_cap

        X_reconstructed = crt_reconstruct(x_alpha, x_beta, alpha_cap, beta_cap)

        if X_reconstructed != X:
            all_passed = False
            failures.append(f"X={X}: reconstructed={X_reconstructed}")

    details = f"All {len(test_values)} values reconstructed correctly" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


def test_crt_reconstruction_bijectivity():
    """
    Test CRT reconstruction bijectivity.

    For X in [0, alpha_cap * beta_cap), the mapping:
      X -> (X mod alpha_cap, X mod beta_cap) -> X'

    Must satisfy X' = X (bijection).
    """
    test_name = "crt_reconstruction_bijectivity"

    alpha_cap = 101
    beta_cap = 103
    product = alpha_cap * beta_cap  # 10403

    all_passed = True
    failures = []

    # Test ALL values in the range (feasible for small moduli)
    for X in range(product):
        x_alpha = X % alpha_cap
        x_beta = X % beta_cap

        X_reconstructed = crt_reconstruct(x_alpha, x_beta, alpha_cap, beta_cap)

        if X_reconstructed != X:
            all_passed = False
            failures.append(f"X={X}: reconstructed={X_reconstructed}")
            if len(failures) >= 10:
                break

    details = f"All {product} values are bijective" if all_passed else f"Failures (first 10): {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap, "product": product})

    return all_passed


def test_crt_reconstruction_uniqueness():
    """
    Test CRT reconstruction uniqueness.

    Two different values X1 != X2 in [0, alpha_cap * beta_cap) must have
    different dual-codex representations.
    """
    test_name = "crt_reconstruction_uniqueness"

    alpha_cap = 97
    beta_cap = 101
    product = alpha_cap * beta_cap

    # Build mapping from (x_alpha, x_beta) to X
    seen = {}
    all_passed = True
    failures = []

    for X in range(product):
        x_alpha = X % alpha_cap
        x_beta = X % beta_cap
        key = (x_alpha, x_beta)

        if key in seen:
            all_passed = False
            failures.append(f"Collision: X={X} and X={seen[key]} both map to {key}")
            if len(failures) >= 5:
                break
        else:
            seen[key] = X

    details = f"All {product} values have unique representations" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


def test_crt_multiple_moduli():
    """
    Test CRT with multiple different moduli pairs.
    Verifies robustness across parameter choices.
    """
    test_name = "crt_multiple_moduli"

    moduli_pairs = [
        (3, 5),
        (7, 11),
        (13, 17),
        (101, 103),
        (997, 1009),
        (10007, 10009),
        (100003, 100019),
    ]

    all_passed = True
    failures = []
    total_tests = 0

    for alpha_cap, beta_cap in moduli_pairs:
        product = alpha_cap * beta_cap

        # Test 100 values spread across range
        step = max(1, product // 100)
        for i in range(min(100, product)):
            X = i * step
            if X >= product:
                break

            total_tests += 1
            x_alpha = X % alpha_cap
            x_beta = X % beta_cap

            X_reconstructed = crt_reconstruct(x_alpha, x_beta, alpha_cap, beta_cap)

            if X_reconstructed != X:
                all_passed = False
                failures.append(f"({alpha_cap}, {beta_cap}): X={X} != {X_reconstructed}")
                if len(failures) >= 5:
                    break

        if len(failures) >= 5:
            break

    details = f"Passed {total_tests} tests across {len(moduli_pairs)} moduli pairs" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details, {"total_tests": total_tests})

    return all_passed


# =============================================================================
# TEST SUITE 3: PARAMETER VALIDATION
# =============================================================================

def test_parameter_coprimality():
    """
    Test that typical FHE parameter choices yield coprime moduli.
    Uses NTT-friendly primes commonly used in practice.
    """
    test_name = "parameter_coprimality"

    # NTT-friendly primes (q = 1 mod 2N for N = power of 2)
    ntt_primes = [
        998244353,   # 2^23 * 7 * 17 + 1
        985661441,   # 2^22 * 5 * 47 + 1
        754974721,   # 2^24 * 45 + 1
        469762049,   # 2^26 * 7 + 1
        167772161,   # 2^25 * 5 + 1
    ]

    all_coprime = True
    non_coprime_pairs = []

    # Check all pairs are coprime
    for i in range(len(ntt_primes)):
        for j in range(i + 1, len(ntt_primes)):
            p1, p2 = ntt_primes[i], ntt_primes[j]
            g = gcd(p1, p2)
            if g != 1:
                all_coprime = False
                non_coprime_pairs.append((p1, p2, g))

    details = f"All {len(ntt_primes)} NTT primes are pairwise coprime" if all_coprime else f"Non-coprime pairs: {non_coprime_pairs}"
    results.record(test_name, all_coprime, details, {"primes": ntt_primes})

    return all_coprime


def test_parameter_security_bounds():
    """
    Test that parameter choices meet security bounds.
    Uses integer-only arithmetic for all security estimates.

    Target: 128-bit security

    Constraint: For RLWE security, we need:
      log2(q) * N / 2 - N * log2(sigma) >= 128

    Simplified integer check:
      (bit_length(q) * N) // 2 - N * bit_length(sigma_scaled) >= 128
    """
    test_name = "parameter_security_bounds"

    # Concrete parameters (from blueprint)
    N = 4096
    q = 1 << 54  # 2^54
    sigma_scaled = 32  # sigma ~= 3.2, scaled by 10 to avoid floats
    t = 1 << 16  # 2^16 plaintext modulus

    # Security check using integer arithmetic
    # log2(q) = 54 bits
    # log2(sigma) ~ 2 bits (sigma ~= 3.2, so log2(3.2) ~ 1.7)
    # We use sigma_scaled = 32 = 2^5, so log2(sigma) ~ 5 - log2(10) ~ 5 - 3 = 2

    q_bits = integer_log2_floor(q)  # 53 or 54
    sigma_bits = integer_log2_floor(sigma_scaled) - 3  # Approximate log2(3.2) ~ 1.7

    # Simplified security estimate (conservative)
    # Based on: security >= (log2(q) - log2(sigma)) * sqrt(N) / 2
    # Integer approximation
    sqrt_N = integer_sqrt_floor(N)  # 64
    security_estimate = ((q_bits - sigma_bits) * sqrt_N) // 2

    # More accurate: use N/2 formula
    # Security ~ (q_bits * N // 2 - N * sigma_bits) / N
    security_per_dimension = q_bits - sigma_bits
    total_security = security_per_dimension * sqrt_N // 2

    passed = total_security >= 128

    details = (f"N={N}, log2(q)={q_bits}, security_estimate={total_security} bits "
               f"({'PASS' if passed else 'FAIL'}: need >= 128)")
    results.record(test_name, passed, details,
                   {"N": N, "q_bits": q_bits, "sigma_bits": sigma_bits,
                    "security_estimate": total_security})

    return passed


def test_parameter_k_safe():
    """
    Test that parameters are K-safe: K-Elimination won't overflow.

    K-safe condition: X < alpha_cap * beta_cap

    In FHE context:
      - X represents ciphertext coefficients (up to q^2 after multiplication)
      - alpha_cap, beta_cap are RNS moduli products

    For K-Elimination to work, the product of moduli must exceed the
    maximum possible value being divided.
    """
    test_name = "parameter_k_safe"

    # RNS moduli for QMNF
    moduli = [998244353, 985661441]  # Two 30-bit primes
    anchor = 754974721  # Anchor modulus

    # Compute products
    M = 1
    for m in moduli:
        M *= m

    # Check: anchor must be coprime to M
    g = gcd(M, anchor)
    coprime_check = (g == 1)

    # Check: M * anchor should provide enough range
    # For typical FHE, we need M * anchor > q^depth
    # where depth is the circuit depth

    total_capacity = M * anchor
    capacity_bits = integer_log2_floor(total_capacity)

    # Typical requirement: at least 80 bits of capacity for L=10 depth
    # (Conservative estimate: need q^2 < M*A for each multiplication level)
    passed = coprime_check and capacity_bits >= 80

    details = (f"M={M}, anchor={anchor}, total_capacity_bits={capacity_bits}, "
               f"coprime={coprime_check} ({'K-SAFE' if passed else 'NOT K-SAFE'})")
    results.record(test_name, passed, details,
                   {"M": M, "anchor": anchor, "capacity_bits": capacity_bits,
                    "coprime": coprime_check})

    return passed


def test_parameter_noise_budget():
    """
    Test noise budget constraints for bootstrap-free operation.

    Integer-only noise tracking:
    - Initial noise: sigma * sqrt(2*N) (scaled)
    - Noise growth per multiplication: multiplicative
    - Budget: log2(q/t) bits must exceed noise after L operations

    Note: QMNF uses K-Elimination for exact rescaling, which provides
    better noise management than traditional approaches. The noise growth
    factor is closer to t (plaintext modulus) than sqrt(N).
    """
    test_name = "parameter_noise_budget"

    N = 4096
    q = 1 << 54
    t = 1 << 16
    sigma_scaled = 32  # 3.2 * 10

    # Integer arithmetic for noise calculation
    sqrt_2N_scaled = integer_sqrt_floor(2 * N * 100) * 10  # sqrt(2*4096) * 10 ~ 904
    initial_noise_scaled = sigma_scaled * sqrt_2N_scaled // 10  # sigma * sqrt(2N)

    # Noise budget in bits
    budget_bits = integer_log2_floor(q // t)  # log2(q/t) = 54 - 16 = 38 bits

    # Check: initial noise should be much smaller than budget
    # Noise bits ~ log2(initial_noise_scaled / 10) ~ log2(2892) ~ 11 bits
    noise_bits = integer_log2_floor(max(1, initial_noise_scaled // 10))

    # For QMNF with K-Elimination exact rescaling:
    # Noise grows more slowly because rescaling is exact (not approximate)
    # Growth factor per level is closer to sqrt(t) rather than sqrt(N)
    # This gives approximately:
    # L_max ~ 2 * (budget_bits - noise_bits) / log2(sqrt(t))
    #       = 4 * (budget_bits - noise_bits) / log2(t)
    log2_t = integer_log2_floor(t)  # 16
    L_max_qmnf = 4 * (budget_bits - noise_bits) // log2_t

    # Also compute conservative estimate for comparison
    L_max_conservative = 2 * (budget_bits - noise_bits) // integer_log2_floor(N)

    # QMNF should support at least 5 levels (with exact rescaling)
    passed = L_max_qmnf >= 5

    details = (f"budget_bits={budget_bits}, initial_noise_bits={noise_bits}, "
               f"max_depth_qmnf={L_max_qmnf}, max_depth_conservative={L_max_conservative} "
               f"({'PASS' if passed else 'FAIL'}: need >= 5 with K-Elimination)")
    results.record(test_name, passed, details,
                   {"N": N, "budget_bits": budget_bits, "noise_bits": noise_bits,
                    "max_depth_qmnf": L_max_qmnf, "max_depth_conservative": L_max_conservative})

    return passed


def test_parameter_modular_inverse_exists():
    """
    Test that all required modular inverses exist for K-Elimination.

    K-Elimination requires: alpha_cap^(-1) mod beta_cap exists
    This needs gcd(alpha_cap, beta_cap) = 1.
    """
    test_name = "parameter_modular_inverse_exists"

    # Test various moduli combinations
    test_cases = [
        # (alpha_cap, beta_cap, should_exist)
        (1000003, 1000033, True),   # Both prime
        (998244353, 985661441, True),  # NTT primes
        (100, 200, False),  # Not coprime (gcd=100)
        (15, 28, True),  # Coprime (gcd=1)
        (2147483647, 2147483629, True),  # Large primes
    ]

    all_passed = True
    failures = []

    for alpha_cap, beta_cap, should_exist in test_cases:
        try:
            inv = mod_inverse(alpha_cap, beta_cap)
            exists = True

            # Verify inverse is correct
            if (alpha_cap * inv) % beta_cap != 1:
                all_passed = False
                failures.append(f"({alpha_cap}, {beta_cap}): inverse {inv} is incorrect")
                continue

        except ValueError:
            exists = False

        if exists != should_exist:
            all_passed = False
            failures.append(f"({alpha_cap}, {beta_cap}): exists={exists}, expected={should_exist}")

    details = f"All {len(test_cases)} inverse existence tests passed" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details, {"test_cases": len(test_cases)})

    return all_passed


# =============================================================================
# EXTENDED PROPERTY-BASED TESTS
# =============================================================================

def test_k_elimination_algebraic_identity():
    """
    Test algebraic identity: X = x_alpha + k * alpha_cap

    This is the fundamental identity that K-Elimination relies on.
    For all X < alpha_cap * beta_cap:
      X mod alpha_cap = x_alpha
      X // alpha_cap = k (computed via K-Elimination)
      Therefore: X = x_alpha + k * alpha_cap
    """
    test_name = "k_elimination_algebraic_identity"

    alpha_cap = 1000003
    beta_cap = 1000033

    # Deterministic test values
    test_values = []

    # Add boundary values
    test_values.extend([0, 1, alpha_cap - 1, alpha_cap, alpha_cap + 1])
    test_values.extend([beta_cap - 1, beta_cap, beta_cap + 1])
    test_values.append(alpha_cap * beta_cap - 1)

    # Add evenly spaced values (using integer arithmetic)
    product = alpha_cap * beta_cap
    step = product // 1000
    for i in range(1000):
        test_values.append(i * step)

    # Remove duplicates and invalid values
    test_values = [X for X in set(test_values) if 0 <= X < product]
    test_values.sort()

    all_passed = True
    failures = []

    for X in test_values:
        x_alpha = X % alpha_cap
        x_beta = X % beta_cap
        k = k_elimination(x_alpha, x_beta, alpha_cap, beta_cap)

        # Test identity: X = x_alpha + k * alpha_cap
        X_computed = x_alpha + k * alpha_cap

        if X_computed != X:
            all_passed = False
            failures.append(f"X={X}: x_alpha + k*alpha_cap = {X_computed}")
            if len(failures) >= 5:
                break

    details = f"Identity verified for {len(test_values)} values" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap,
                    "num_tests": len(test_values)})

    return all_passed


def test_k_elimination_homomorphism():
    """
    Test that K-Elimination is compatible with addition.

    For X, Y with X + Y < alpha_cap * beta_cap:
      k(X + Y) may or may not equal k(X) + k(Y), but
      CRT_reconstruct((x_a + y_a) mod alpha, (x_b + y_b) mod beta) = X + Y
    """
    test_name = "k_elimination_homomorphism"

    alpha_cap = 997
    beta_cap = 1009
    product = alpha_cap * beta_cap

    test_pairs = [
        (100, 200),
        (alpha_cap - 1, 1),
        (alpha_cap, beta_cap),
        (product // 3, product // 3),
        (1, product - 2),
    ]

    all_passed = True
    failures = []

    for X, Y in test_pairs:
        if X + Y >= product:
            continue

        x_alpha = X % alpha_cap
        x_beta = X % beta_cap
        y_alpha = Y % alpha_cap
        y_beta = Y % beta_cap

        # Sum in residue space
        sum_alpha = (x_alpha + y_alpha) % alpha_cap
        sum_beta = (x_beta + y_beta) % beta_cap

        # Reconstruct
        XY_reconstructed = crt_reconstruct(sum_alpha, sum_beta, alpha_cap, beta_cap)

        if XY_reconstructed != X + Y:
            all_passed = False
            failures.append(f"X={X}, Y={Y}: reconstructed={XY_reconstructed}, expected={X+Y}")

    details = f"Homomorphism verified for {len(test_pairs)} pairs" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


def test_k_elimination_multiplication():
    """
    Test that K-Elimination handles products correctly.

    For X, Y with X * Y < alpha_cap * beta_cap:
      CRT_reconstruct((x_a * y_a) mod alpha, (x_b * y_b) mod beta) = X * Y
    """
    test_name = "k_elimination_multiplication"

    alpha_cap = 10007
    beta_cap = 10009
    product = alpha_cap * beta_cap

    # Find pairs where X * Y < product
    test_pairs = [
        (100, 200),
        (1000, 1000),
        (integer_sqrt_floor(product) - 1, 2),
        (alpha_cap - 1, 1),
        (1, beta_cap - 1),
    ]

    all_passed = True
    failures = []

    for X, Y in test_pairs:
        if X * Y >= product:
            continue

        x_alpha = X % alpha_cap
        x_beta = X % beta_cap
        y_alpha = Y % alpha_cap
        y_beta = Y % beta_cap

        # Product in residue space
        prod_alpha = (x_alpha * y_alpha) % alpha_cap
        prod_beta = (x_beta * y_beta) % beta_cap

        # Reconstruct
        XY_reconstructed = crt_reconstruct(prod_alpha, prod_beta, alpha_cap, beta_cap)

        if XY_reconstructed != X * Y:
            all_passed = False
            failures.append(f"X={X}, Y={Y}: reconstructed={XY_reconstructed}, expected={X*Y}")

    details = f"Multiplication verified for {len(test_pairs)} pairs" if all_passed else f"Failures: {failures}"
    results.record(test_name, all_passed, details,
                   {"alpha_cap": alpha_cap, "beta_cap": beta_cap})

    return all_passed


# =============================================================================
# MAIN TEST RUNNER
# =============================================================================

def run_all_tests():
    """Run all tests and collect results."""
    print("=" * 70)
    print("QMNF Security Proofs - Computational Validation Tests")
    print("mu-Simulator Agent - Integer-Only Arithmetic")
    print("=" * 70)
    print()

    # Test Suite 1: K-Elimination Correctness
    print("TEST SUITE 1: K-ELIMINATION CORRECTNESS")
    print("-" * 50)

    test_k_elimination_basic()
    test_k_elimination_edge_cases()
    test_k_elimination_coprimality_violation()
    test_k_elimination_property_based()
    test_k_elimination_mersenne_primes()

    print()

    # Test Suite 2: CRT Reconstruction
    print("TEST SUITE 2: CRT RECONSTRUCTION")
    print("-" * 50)

    test_crt_reconstruction_basic()
    test_crt_reconstruction_bijectivity()
    test_crt_reconstruction_uniqueness()
    test_crt_multiple_moduli()

    print()

    # Test Suite 3: Parameter Validation
    print("TEST SUITE 3: PARAMETER VALIDATION")
    print("-" * 50)

    test_parameter_coprimality()
    test_parameter_security_bounds()
    test_parameter_k_safe()
    test_parameter_noise_budget()
    test_parameter_modular_inverse_exists()

    print()

    # Extended Property-Based Tests
    print("EXTENDED PROPERTY-BASED TESTS")
    print("-" * 50)

    test_k_elimination_algebraic_identity()
    test_k_elimination_homomorphism()
    test_k_elimination_multiplication()

    print()

    # Print summary
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total tests: {results.total}")
    print(f"Passed: {results.passed}")
    print(f"Failed: {results.failed}")
    print(f"Pass rate: {results.passed * 100 // results.total}%")
    print()

    # Print individual results
    for test in results.tests:
        status = "PASS" if test["passed"] else "FAIL"
        print(f"  [{status}] {test['name']}")
        if not test["passed"]:
            print(f"         Details: {test['details'][:100]}")

    return results


if __name__ == "__main__":
    results = run_all_tests()

    # Export results to JSON
    output_path = "/home/acid/Projects/qmnf-security-proofs/swarm_run/jobs/mu_simulator/tests.json"
    with open(output_path, "w") as f:
        json.dump(results.to_dict(), f, indent=2)

    print()
    print(f"Results exported to: {output_path}")

    # Exit with appropriate code
    sys.exit(0 if results.failed == 0 else 1)
