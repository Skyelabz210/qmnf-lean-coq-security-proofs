#!/usr/bin/env python3
"""
QMNF NIST Security Compliance Validator
========================================

Computational validation tests for NIST security compliance.
Implements lattice security estimation using INTEGER-ONLY arithmetic.

This module validates:
1. Lattice security parameters (simplified lattice-estimator style)
2. Root Hermite factor delta estimation
3. BKZ block size estimation for attacks
4. Classical and quantum security bit levels
5. Compliance with NIST post-quantum security categories

QMNF MANDATE: All arithmetic uses integers or scaled rational representations.
NO FLOATING-POINT OPERATIONS.

Author: mu-Simulator (Formalization Swarm)
Date: 2026-02-02
"""

import sys
from typing import Tuple, Dict, Any, List


# =============================================================================
# QMNF PARAMETERS TO VALIDATE
# =============================================================================

# Ring dimension (power of 2 for NTT efficiency)
N_RING_DIM = 4096

# Ciphertext modulus: 2^54 - 33
# This is a prime suitable for NTT operations
Q_MODULUS = (1 << 54) - 33  # 18014398509481951

# Plaintext modulus (Fermat prime F4 = 2^16 + 1)
T_PLAINTEXT = 65537

# Error standard deviation (discrete Gaussian width)
# Represented as scaled integer: 32/10 = 3.2
SIGMA_NUMER = 32
SIGMA_DENOM = 10


# =============================================================================
# INTEGER-ONLY HELPER FUNCTIONS
# =============================================================================

def gcd(a: int, b: int) -> int:
    """Greatest Common Divisor using Euclidean algorithm."""
    a, b = abs(a), abs(b)
    while b != 0:
        a, b = b, a % b
    return a


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


def integer_log2_scaled(n: int, scale: int = 1000000) -> int:
    """
    Compute log2(n) * scale using integer arithmetic.

    Uses the identity: log2(n) = k + log2(1 + f) where n = 2^k * (1 + f)
    and approximates log2(1 + f) using integer arithmetic.

    Returns an integer representing log2(n) scaled by `scale`.
    """
    if n <= 0:
        raise ValueError("Cannot compute log2 of non-positive number")

    # Get the integer part
    k = n.bit_length() - 1

    # Compute the fractional part
    # n / 2^k = 1 + f, where 0 <= f < 1
    # We compute f * scale
    remainder = n - (1 << k)  # This is f * 2^k

    if remainder == 0:
        return k * scale

    # Approximate log2(1 + f) for small f:
    # log2(1 + f) ~ f / ln(2) ~ f * 1.4427
    # But we'll use a more accurate series expansion
    # log2(1 + x) = (1/ln2) * (x - x^2/2 + x^3/3 - ...)

    # Compute f_scaled = f * scale = (remainder * scale) / 2^k
    f_scaled = (remainder * scale) // (1 << k)

    # ln(2) ~ 693147/1000000 (scaled)
    # 1/ln(2) ~ 1442695/1000000
    LN2_INVERSE_SCALED = 1442695  # 1/ln(2) * 1000000

    # First-order approximation: log2(1+f) ~ f/ln(2)
    # For better accuracy, use: log2(1+f) ~ f/ln(2) - f^2/(2*ln(2)) + ...
    f_term = (f_scaled * LN2_INVERSE_SCALED) // scale

    # Second-order correction (negative)
    f2_correction = (f_scaled * f_scaled * LN2_INVERSE_SCALED) // (2 * scale * scale)

    log2_frac = f_term - f2_correction

    return k * scale + log2_frac


def integer_ln_scaled(n: int, scale: int = 1000000) -> int:
    """
    Compute ln(n) * scale using integer arithmetic.
    ln(n) = log2(n) * ln(2)
    """
    log2_val = integer_log2_scaled(n, scale)
    # ln(2) ~ 693147/1000000
    LN2_SCALED = 693147
    return (log2_val * LN2_SCALED) // scale


def rational_to_scaled(numer: int, denom: int, scale: int = 1000000) -> int:
    """Convert a rational number to a scaled integer representation."""
    return (numer * scale) // denom


# =============================================================================
# LATTICE SECURITY ESTIMATION (Integer-Only)
# =============================================================================

class LatticeSecurityEstimator:
    """
    Simplified lattice security estimator using integer-only arithmetic.

    This implements core security estimation similar to the lattice-estimator
    but using QMNF-compliant integer arithmetic.

    Key concepts:
    - Root Hermite factor (delta): measures lattice reduction quality
    - BKZ block size (beta): parameter for lattice reduction algorithm
    - Security bits: log2 of attack complexity
    """

    # Scaling factor for fixed-point arithmetic
    SCALE = 1000000

    # ln(2) * SCALE
    LN2 = 693147

    # pi * SCALE (for volume computations)
    PI = 3141593

    def __init__(self, n: int, q: int, sigma_numer: int, sigma_denom: int):
        """
        Initialize the estimator with lattice parameters.

        Args:
            n: Ring dimension
            q: Ciphertext modulus
            sigma_numer: Error stddev numerator (sigma = numer/denom)
            sigma_denom: Error stddev denominator
        """
        self.n = n
        self.q = q
        self.sigma_numer = sigma_numer
        self.sigma_denom = sigma_denom

        # Precompute log2(q) * SCALE
        self.log2_q_scaled = integer_log2_scaled(q, self.SCALE)

        # Precompute log2(n) * SCALE
        self.log2_n_scaled = integer_log2_scaled(n, self.SCALE)

    def compute_root_hermite_factor(self) -> Tuple[int, int]:
        """
        Compute the root Hermite factor delta.

        For LWE-based schemes, the target shortest vector has length:
            ||b_1|| ~ delta^n * det(L)^(1/n)

        For the primal attack on LWE:
            delta ~ (q/sigma)^(1/n) * (some constants)

        Returns:
            Tuple (delta_scaled, SCALE) where delta = delta_scaled / SCALE

        Using the approximation:
            delta ~ (q / (sqrt(2*pi*e) * sigma))^(1/n)
        """
        # sqrt(2*pi*e) ~ 4.13273 ~ 4132730 / 1000000
        SQRT_2PIE_SCALED = 4132730

        # Compute q / (sqrt(2*pi*e) * sigma)
        # = q * sigma_denom / (sqrt(2*pi*e) * sigma_numer)
        # In scaled arithmetic:
        numerator = self.q * self.sigma_denom * self.SCALE
        denominator = SQRT_2PIE_SCALED * self.sigma_numer // self.SCALE

        if denominator == 0:
            denominator = 1

        ratio = numerator // denominator

        # Now compute ratio^(1/n)
        # Using: x^(1/n) = 2^(log2(x)/n)
        log2_ratio = integer_log2_scaled(max(ratio, 1), self.SCALE)
        log2_delta = log2_ratio // self.n

        # Compute 2^(log2_delta / SCALE)
        # = 2^(integer_part) * 2^(fractional_part)
        integer_part = log2_delta // self.SCALE
        frac_part = log2_delta % self.SCALE

        # 2^frac where frac is in [0, 1)
        # Using Taylor: 2^x ~ 1 + x*ln(2) + (x*ln(2))^2/2 + ...
        # For small x: 2^x ~ 1 + 0.693*x
        two_to_frac = self.SCALE + (frac_part * self.LN2) // self.SCALE

        delta_scaled = (1 << integer_part) * two_to_frac

        return (delta_scaled, self.SCALE)

    def estimate_bkz_block_size(self) -> int:
        """
        Estimate the BKZ block size beta required for a successful attack.

        Using the primal uSVP attack model from standard lattice security analysis.

        For RLWE/LWE, the security analysis involves:
        1. The attacker constructs a lattice of dimension d from m LWE samples
        2. The lattice has a unique short vector (error) of norm ~sigma*sqrt(d)
        3. BKZ-beta finds vectors of length ~delta(beta)^d * det(L)^(1/d)
        4. Attack succeeds when delta(beta)^d * det(L)^(1/d) <= sigma*sqrt(d)

        The optimal attack dimension d and required beta depend on n, q, sigma.

        For the primal attack with optimal d:
            d_opt ~ n * log2(q) / log2(q/sigma)
            beta ~ n / log2(q/sigma) (approximately)

        Key insight: SMALLER q/sigma ratio = HARDER attack (more noise)
        LARGER n = HARDER attack (higher dimension)

        Standard FHE parameters achieve different security levels:
        - TFHE/BFV low: n=1024, q~2^27  -> ~80-bit security
        - BFV medium:   n=4096, q~2^109 -> ~128-bit security
        - BFV high:     n=8192, q~2^218 -> ~192-bit security

        The scaling relationship (from lattice-estimator):
            security_bits ~ 0.265 * beta (quantum)
            security_bits ~ 0.292 * beta (classical)

        For n=4096:
            - log2(q)=54:  beta should give ~50-60 bit security
            - log2(q)=109: beta should give ~128 bit security

        This means:
            - For 128-bit: beta ~ 128/0.292 ~ 438
            - For 55-bit:  beta ~ 55/0.292 ~ 188

        Heuristic: beta ~ n / (2 * log2(q/sigma))
        For n=4096, sigma=3.2:
            - q=2^54:  beta ~ 4096 / (2 * 52) ~ 39 (too low, need correction)
            - q=2^109: beta ~ 4096 / (2 * 107) ~ 19 (too low)

        Better model: security comes from the hardness gap, not just parameters.
        Use empirical fit: beta ~ n / log2(q/sigma) * correction_factor

        After calibration with known parameter sets:
            beta ~ n / (log2(q) - log2(sigma) - 4)

        Returns:
            Estimated BKZ block size beta
        """
        # Compute log2(q) unscaled
        log2_q = integer_log2_floor(self.q) + 1  # e.g., 54 for q ~ 2^54

        # log2(sigma) ~ log2(3.2) ~ 1.68
        log2_sigma = 2  # Using 2 as integer approximation for 1.68

        # log2(q/sigma) ~ log2(q) - log2(sigma)
        log2_ratio = log2_q - log2_sigma

        if log2_ratio <= 4:
            return 1024  # Very high security (noise dominates)

        # Empirical model: beta ~ n / (log2_ratio - 2) * factor
        # Calibrated to match:
        #   n=4096, log2(q)=54:  beta ~ 188 (gives ~55 bit security)
        #   n=4096, log2(q)=109: beta ~ 438 (gives ~128 bit security)

        # Solving: 188 = 4096 / (52 - c) and 438 = 4096 / (107 - c)
        # From first: 52 - c = 4096/188 ~ 21.8, so c ~ 30
        # From second: 107 - c = 4096/438 ~ 9.4, so c ~ 97.6
        # These don't match, so the relationship is not linear

        # Better model: beta ~ n * log2_ratio / (n/k + log2_ratio^2)
        # where k is a tuning constant

        # Even simpler empirical fit:
        # For n=4096: beta scales roughly as 4 * log2_ratio
        #   log2_ratio=52:  beta ~ 188 -> factor ~ 3.6
        #   log2_ratio=107: beta ~ 438 -> factor ~ 4.1

        # Use: beta ~ 4.1 * log2_ratio for n=4096, scaling with sqrt(n/4096)
        # 4.1 ~ 41/10
        factor_numer = 41
        factor_denom = 10
        beta_estimate = (factor_numer * log2_ratio) // factor_denom

        # Scale by n / 4096 for other ring dimensions
        if self.n != 4096:
            beta_estimate = (beta_estimate * self.n) // 4096

        # Clamp to reasonable range [50, 1024]
        return max(50, min(beta_estimate, 1024))

    def estimate_classical_security_bits(self) -> int:
        """
        Estimate classical security bits.

        The cost of BKZ-beta is approximately:
            T_classical ~ 2^(0.292 * beta) core operations

        Using more precise estimate:
            log2(T) ~ 0.292 * beta (for sieving)
            log2(T) ~ 0.187 * beta^2 / n + ... (for enumeration)

        We use the sieving model as it's more favorable to attacker.

        Returns:
            Estimated classical security bits
        """
        beta = self.estimate_bkz_block_size()

        # Cost exponent for sieving: 0.292 * beta
        # 0.292 ~ 292000 / 1000000
        SIEVING_CONSTANT = 292000

        security_bits = (SIEVING_CONSTANT * beta) // self.SCALE

        return security_bits

    def estimate_quantum_security_bits(self) -> int:
        """
        Estimate quantum security bits.

        Quantum speedup via Grover's algorithm roughly gives:
            T_quantum ~ sqrt(T_classical) for search problems

        For lattice sieving, the quantum speedup is:
            log2(T_quantum) ~ 0.265 * beta (quantum sieving)

        Returns:
            Estimated quantum security bits
        """
        beta = self.estimate_bkz_block_size()

        # Quantum sieving constant: 0.265 ~ 265000 / 1000000
        QUANTUM_SIEVING_CONSTANT = 265000

        security_bits = (QUANTUM_SIEVING_CONSTANT * beta) // self.SCALE

        return security_bits

    def get_full_report(self) -> Dict[str, Any]:
        """Generate a comprehensive security report."""
        delta_scaled, scale = self.compute_root_hermite_factor()
        beta = self.estimate_bkz_block_size()
        classical_bits = self.estimate_classical_security_bits()
        quantum_bits = self.estimate_quantum_security_bits()

        # Compute delta as a decimal string for display
        delta_integer = delta_scaled // scale
        delta_frac = delta_scaled % scale
        delta_str = f"{delta_integer}.{delta_frac:06d}"

        return {
            "parameters": {
                "n": self.n,
                "q": self.q,
                "q_bits": integer_log2_floor(self.q) + 1,
                "sigma": f"{self.sigma_numer}/{self.sigma_denom}",
            },
            "security_estimates": {
                "root_hermite_factor_delta": delta_str,
                "bkz_block_size_beta": beta,
                "classical_security_bits": classical_bits,
                "quantum_security_bits": quantum_bits,
            },
            "nist_compliance": {
                "classical_target": 128,
                "quantum_target": 64,
                "classical_compliant": classical_bits >= 128,
                "quantum_compliant": quantum_bits >= 64,
            }
        }


# =============================================================================
# ML-KEM-1024 COMPARISON
# =============================================================================

def get_mlkem_1024_parameters() -> Dict[str, Any]:
    """
    Return ML-KEM-1024 (CRYSTALS-Kyber) parameters for comparison.

    ML-KEM-1024 targets NIST Level 5 security (256-bit classical).
    """
    return {
        "name": "ML-KEM-1024",
        "n": 256,  # Module rank k=4, ring dimension n=256
        "k": 4,    # Module rank
        "q": 3329,
        "eta1": 2,
        "eta2": 2,
        "d_u": 11,
        "d_v": 5,
        "classical_security_target": 256,
        "quantum_security_target": 128,
    }


def compare_with_mlkem() -> Dict[str, Any]:
    """
    Compare QMNF parameters with ML-KEM-1024.

    QMNF uses larger ring dimension (4096) but aims for similar
    security level.
    """
    qmnf_estimator = LatticeSecurityEstimator(
        N_RING_DIM, Q_MODULUS, SIGMA_NUMER, SIGMA_DENOM
    )
    qmnf_report = qmnf_estimator.get_full_report()

    mlkem = get_mlkem_1024_parameters()

    return {
        "qmnf": qmnf_report,
        "mlkem_1024_reference": mlkem,
        "comparison": {
            "qmnf_ring_dim": N_RING_DIM,
            "mlkem_effective_dim": mlkem["n"] * mlkem["k"],  # 1024
            "security_ratio": (
                qmnf_report["security_estimates"]["classical_security_bits"],
                mlkem["classical_security_target"]
            ),
        }
    }


# =============================================================================
# VALIDATION TESTS
# =============================================================================

class NISTSecurityValidator:
    """
    Validator for NIST security compliance.
    """

    def __init__(self):
        self.test_results: List[Dict[str, Any]] = []

    def run_test(self, name: str, passed: bool, details: str, value: Any = None):
        """Record a test result."""
        result = {
            "name": name,
            "passed": passed,
            "details": details,
        }
        if value is not None:
            result["value"] = value
        self.test_results.append(result)

    def test_ring_dimension(self) -> bool:
        """Verify ring dimension is power of 2 and sufficient."""
        is_power_of_2 = (N_RING_DIM & (N_RING_DIM - 1)) == 0
        is_sufficient = N_RING_DIM >= 1024
        passed = is_power_of_2 and is_sufficient

        self.run_test(
            "Ring Dimension (n)",
            passed,
            f"n={N_RING_DIM}, power_of_2={is_power_of_2}, >=1024={is_sufficient}",
            N_RING_DIM
        )
        return passed

    def test_modulus_primality(self) -> bool:
        """Verify q is prime and suitable for NTT."""
        # Miller-Rabin primality test (deterministic for our size)
        def is_prime(n: int) -> bool:
            if n < 2:
                return False
            if n == 2:
                return True
            if n % 2 == 0:
                return False

            # Write n-1 as 2^r * d
            r, d = 0, n - 1
            while d % 2 == 0:
                r += 1
                d //= 2

            # Witnesses for deterministic test up to 2^64
            witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

            for a in witnesses:
                if a >= n:
                    continue

                x = pow(a, d, n)
                if x == 1 or x == n - 1:
                    continue

                for _ in range(r - 1):
                    x = pow(x, 2, n)
                    if x == n - 1:
                        break
                else:
                    return False

            return True

        is_prime_q = is_prime(Q_MODULUS)

        # Check if q = 1 mod 2n (required for NTT)
        ntt_compatible = (Q_MODULUS % (2 * N_RING_DIM)) == 1

        passed = is_prime_q and ntt_compatible

        self.run_test(
            "Modulus Primality & NTT Compatibility",
            passed,
            f"q={Q_MODULUS}, is_prime={is_prime_q}, q=1 mod {2*N_RING_DIM}: {ntt_compatible}",
            {"q": Q_MODULUS, "prime": is_prime_q, "ntt_compat": ntt_compatible}
        )
        return passed

    def test_plaintext_modulus(self) -> bool:
        """Verify plaintext modulus is Fermat prime."""
        # t = 65537 = 2^16 + 1 (Fermat prime F4)
        is_fermat_f4 = T_PLAINTEXT == (1 << 16) + 1

        self.run_test(
            "Plaintext Modulus (Fermat Prime)",
            is_fermat_f4,
            f"t={T_PLAINTEXT}, is_F4={is_fermat_f4}",
            T_PLAINTEXT
        )
        return is_fermat_f4

    def test_error_distribution(self) -> bool:
        """Verify error distribution is within NIST recommendations."""
        # sigma should be in range [2.0, 4.0] for practical security
        # sigma = 3.2 is well within this range
        sigma_scaled = (SIGMA_NUMER * 100) // SIGMA_DENOM  # 320 = 3.20

        in_range = 200 <= sigma_scaled <= 400  # [2.0, 4.0]

        self.run_test(
            "Error Distribution (sigma)",
            in_range,
            f"sigma={SIGMA_NUMER}/{SIGMA_DENOM}={sigma_scaled/100}, range=[2.0, 4.0]",
            {"sigma_numer": SIGMA_NUMER, "sigma_denom": SIGMA_DENOM}
        )
        return in_range

    def test_classical_security(self) -> bool:
        """Verify classical security >= 128 bits."""
        estimator = LatticeSecurityEstimator(
            N_RING_DIM, Q_MODULUS, SIGMA_NUMER, SIGMA_DENOM
        )
        bits = estimator.estimate_classical_security_bits()

        passed = bits >= 128

        self.run_test(
            "Classical Security",
            passed,
            f"Estimated {bits} bits (target >= 128)",
            bits
        )
        return passed

    def test_quantum_security(self) -> bool:
        """Verify quantum security >= 64 bits (NIST Category 1+)."""
        estimator = LatticeSecurityEstimator(
            N_RING_DIM, Q_MODULUS, SIGMA_NUMER, SIGMA_DENOM
        )
        bits = estimator.estimate_quantum_security_bits()

        passed = bits >= 64

        self.run_test(
            "Quantum Security (NIST Category 1+)",
            passed,
            f"Estimated {bits} bits (target >= 64 for Category 1)",
            bits
        )
        return passed

    def test_mlkem_alignment(self) -> bool:
        """Verify parameters align with ML-KEM-1024 security level."""
        estimator = LatticeSecurityEstimator(
            N_RING_DIM, Q_MODULUS, SIGMA_NUMER, SIGMA_DENOM
        )
        qmnf_classical = estimator.estimate_classical_security_bits()

        # ML-KEM-1024 targets 256-bit classical security
        # QMNF should be at least comparable (within 50% range)
        mlkem_target = 256

        # For alignment, we require QMNF >= 128 (ML-KEM-1024 / 2)
        # This puts us at least in NIST Category 3
        passed = qmnf_classical >= 128

        self.run_test(
            "ML-KEM-1024 Security Alignment",
            passed,
            f"QMNF: {qmnf_classical} bits vs ML-KEM-1024 target: {mlkem_target} bits",
            {"qmnf_bits": qmnf_classical, "mlkem_target": mlkem_target}
        )
        return passed

    def run_all_tests(self) -> Dict[str, Any]:
        """Run all validation tests."""
        self.test_results = []

        tests = [
            ("Ring Dimension", self.test_ring_dimension),
            ("Modulus Primality", self.test_modulus_primality),
            ("Plaintext Modulus", self.test_plaintext_modulus),
            ("Error Distribution", self.test_error_distribution),
            ("Classical Security", self.test_classical_security),
            ("Quantum Security", self.test_quantum_security),
            ("ML-KEM Alignment", self.test_mlkem_alignment),
        ]

        all_passed = True
        for name, test_func in tests:
            try:
                passed = test_func()
                if not passed:
                    all_passed = False
            except Exception as e:
                self.run_test(name, False, f"Exception: {str(e)}")
                all_passed = False

        return {
            "all_passed": all_passed,
            "total_tests": len(self.test_results),
            "passed_tests": sum(1 for r in self.test_results if r["passed"]),
            "results": self.test_results,
        }


# =============================================================================
# NIST CATEGORY ASSESSMENT
# =============================================================================

def assess_nist_category(classical_bits: int, quantum_bits: int) -> Dict[str, Any]:
    """
    Determine NIST post-quantum security category.

    NIST Categories (based on equivalent symmetric key security):
    - Category 1: 128-bit classical (AES-128)
    - Category 2: 128-bit classical (SHA-256 collision)
    - Category 3: 192-bit classical (AES-192)
    - Category 4: 192-bit classical (SHA-384 collision)
    - Category 5: 256-bit classical (AES-256)

    Quantum security targets:
    - Category 1: 64-bit quantum (Grover on AES-128)
    - Category 3: 96-bit quantum
    - Category 5: 128-bit quantum
    """
    categories = {
        1: {"classical": 128, "quantum": 64, "name": "Category 1 (AES-128 equivalent)"},
        2: {"classical": 128, "quantum": 64, "name": "Category 2 (SHA-256/collision equivalent)"},
        3: {"classical": 192, "quantum": 96, "name": "Category 3 (AES-192 equivalent)"},
        4: {"classical": 192, "quantum": 96, "name": "Category 4 (SHA-384/collision equivalent)"},
        5: {"classical": 256, "quantum": 128, "name": "Category 5 (AES-256 equivalent)"},
    }

    achieved_category = 0
    for cat in [5, 4, 3, 2, 1]:
        req = categories[cat]
        if classical_bits >= req["classical"] and quantum_bits >= req["quantum"]:
            achieved_category = cat
            break

    return {
        "achieved_category": achieved_category,
        "category_name": categories.get(achieved_category, {}).get("name", "Below Category 1"),
        "classical_bits": classical_bits,
        "quantum_bits": quantum_bits,
        "categories": categories,
    }


# =============================================================================
# PARAMETER RECOMMENDATIONS
# =============================================================================

def compute_recommended_parameters() -> Dict[str, Any]:
    """
    Compute recommended parameters that would meet NIST Category 1+.

    For RLWE security, the key relationship is:
        security ~ n * log2(q/sigma) / log2(q)

    For 128-bit classical security with BKZ-sieving:
        beta >= 128 / 0.292 ~ 438

    The root Hermite factor must be small enough that:
        delta^n < q / (sigma * sqrt(2*pi*e))
    """
    # NIST Category 1 compliant parameters (similar to BFV/BGV standard)
    recommended_sets = [
        {
            "name": "QMNF-128 (Category 1)",
            "n": 4096,
            # q ~ 2^109 for n=4096 to achieve 128-bit security
            # Using modulus chain: product of several ~27-bit primes
            "q_description": "~2^109 (modulus chain of 4 x ~27-bit primes)",
            "q_bits": 109,
            "t": 65537,
            "sigma_numer": 32,
            "sigma_denom": 10,
            "classical_target": 128,
            "quantum_target": 64,
        },
        {
            "name": "QMNF-192 (Category 3)",
            "n": 8192,
            # q ~ 2^218 for n=8192
            "q_description": "~2^218 (modulus chain)",
            "q_bits": 218,
            "t": 65537,
            "sigma_numer": 32,
            "sigma_denom": 10,
            "classical_target": 192,
            "quantum_target": 96,
        },
        {
            "name": "QMNF-256 (Category 5)",
            "n": 16384,
            # q ~ 2^438 for n=16384
            "q_description": "~2^438 (modulus chain)",
            "q_bits": 438,
            "t": 65537,
            "sigma_numer": 32,
            "sigma_denom": 10,
            "classical_target": 256,
            "quantum_target": 128,
        },
    ]

    return {"recommended_parameter_sets": recommended_sets}


def estimate_required_modulus_bits(n: int, target_classical_bits: int) -> int:
    """
    Estimate required modulus bit-size for given ring dimension and security target.

    Using the LWE hardness estimate:
        log2(q) ~ n * target_bits / (n - target_bits * C)

    where C ~ 0.292 for sieving.

    Simplified heuristic:
        For 128-bit security: log2(q) ~ n / 37
        For 192-bit security: log2(q) ~ n / 25
        For 256-bit security: log2(q) ~ n / 18
    """
    SCALE = 1000

    if target_classical_bits >= 256:
        # q_bits ~ n / 18
        ratio = 18 * SCALE
    elif target_classical_bits >= 192:
        # q_bits ~ n / 25
        ratio = 25 * SCALE
    else:
        # q_bits ~ n / 37
        ratio = 37 * SCALE

    q_bits = (n * SCALE) // ratio
    return q_bits


# =============================================================================
# NTT-COMPATIBLE PRIME FINDER
# =============================================================================

def find_ntt_prime(bits: int, n: int) -> int:
    """
    Find a prime q such that:
    - q has approximately `bits` bits
    - q = 1 (mod 2n) for NTT compatibility

    Uses only integer arithmetic.
    """
    # Start near 2^bits
    start = 1 << bits

    # q must be 1 mod 2n
    modulus = 2 * n
    remainder = start % modulus
    if remainder != 1:
        candidate = start + (modulus - remainder + 1)
    else:
        candidate = start

    # Miller-Rabin primality test
    def is_prime_mr(p: int) -> bool:
        if p < 2:
            return False
        if p == 2:
            return True
        if p % 2 == 0:
            return False

        r, d = 0, p - 1
        while d % 2 == 0:
            r += 1
            d //= 2

        witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

        for a in witnesses:
            if a >= p:
                continue
            x = pow(a, d, p)
            if x == 1 or x == p - 1:
                continue
            for _ in range(r - 1):
                x = pow(x, 2, p)
                if x == p - 1:
                    break
            else:
                return False
        return True

    # Search for prime
    for _ in range(10000):  # Limit iterations
        if is_prime_mr(candidate):
            return candidate
        candidate += modulus

    return 0  # Not found


def suggest_compliant_modulus() -> Dict[str, Any]:
    """
    Suggest a NIST-compliant modulus for the given ring dimension.
    """
    n = N_RING_DIM
    target_bits = 128

    # For n=4096 and 128-bit security, we need ~109 bit modulus
    # But using a single prime is impractical; real implementations use modulus chains
    # Here we find a suitable prime for demonstration

    required_bits = estimate_required_modulus_bits(n, target_bits)

    # Find an NTT-compatible prime
    suggested_prime = find_ntt_prime(required_bits, n)

    # Also estimate for the original parameters
    current_bits = integer_log2_floor(Q_MODULUS) + 1
    current_security = estimate_security_from_params(n, current_bits)

    return {
        "current_modulus_bits": current_bits,
        "current_estimated_security": current_security,
        "required_bits_for_128_security": required_bits,
        "suggested_prime": suggested_prime,
        "suggested_prime_bits": suggested_prime.bit_length() if suggested_prime else 0,
    }


def estimate_security_from_params(n: int, q_bits: int) -> int:
    """
    Estimate security level from n and log2(q).

    Using the calibrated BKZ model:
        beta ~ 4.1 * (log2(q) - 2) for n=4096
        security ~ 0.292 * beta (classical)

    For n=4096:
        q_bits=54:  beta ~ 4.1 * 52 ~ 213, security ~ 62 bits
        q_bits=110: beta ~ 4.1 * 108 ~ 443, security ~ 129 bits
    """
    # log2(sigma) ~ 2 for sigma ~ 3.2
    log2_ratio = q_bits - 2

    if log2_ratio <= 0:
        return 1024  # Very high security

    # beta ~ 4.1 * log2_ratio * n / 4096
    beta = (41 * log2_ratio * n) // (10 * 4096)

    # Classical security ~ 0.292 * beta ~ beta * 292 / 1000
    security = (beta * 292) // 1000

    return security


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def print_report(report: Dict[str, Any]) -> None:
    """Print a formatted security report."""
    print("=" * 70)
    print("QMNF NIST SECURITY COMPLIANCE REPORT")
    print("=" * 70)
    print()

    print("PARAMETERS:")
    print("-" * 40)
    params = report.get("parameters", {})
    print(f"  Ring Dimension (n):      {params.get('n', 'N/A')}")
    print(f"  Ciphertext Modulus (q):  {params.get('q', 'N/A')}")
    print(f"  Modulus Bit Size:        {params.get('q_bits', 'N/A')} bits")
    print(f"  Plaintext Modulus (t):   {T_PLAINTEXT}")
    print(f"  Error Std Dev (sigma):   {params.get('sigma', 'N/A')}")
    print()

    print("SECURITY ESTIMATES:")
    print("-" * 40)
    sec = report.get("security_estimates", {})
    print(f"  Root Hermite Factor (delta): {sec.get('root_hermite_factor_delta', 'N/A')}")
    print(f"  BKZ Block Size (beta):       {sec.get('bkz_block_size_beta', 'N/A')}")
    print(f"  Classical Security:          {sec.get('classical_security_bits', 'N/A')} bits")
    print(f"  Quantum Security:            {sec.get('quantum_security_bits', 'N/A')} bits")
    print()

    print("NIST COMPLIANCE:")
    print("-" * 40)
    compliance = report.get("nist_compliance", {})
    classical_ok = compliance.get('classical_compliant', False)
    quantum_ok = compliance.get('quantum_compliant', False)
    print(f"  Classical Target (>= 128 bits): {'PASS' if classical_ok else 'FAIL'}")
    print(f"  Quantum Target (>= 64 bits):    {'PASS' if quantum_ok else 'FAIL'}")
    print()


def print_validation_results(results: Dict[str, Any]) -> None:
    """Print validation test results."""
    print("VALIDATION TEST RESULTS:")
    print("-" * 40)

    for test in results.get("results", []):
        status = "PASS" if test["passed"] else "FAIL"
        print(f"  [{status}] {test['name']}")
        print(f"         {test['details']}")

    print()
    total = results.get("total_tests", 0)
    passed = results.get("passed_tests", 0)
    print(f"  Total: {passed}/{total} tests passed")
    print()


def print_nist_category(category_info: Dict[str, Any]) -> None:
    """Print NIST category assessment."""
    print("NIST POST-QUANTUM CATEGORY ASSESSMENT:")
    print("-" * 40)
    print(f"  Achieved: {category_info['category_name']}")
    print(f"  Classical Security: {category_info['classical_bits']} bits")
    print(f"  Quantum Security:   {category_info['quantum_bits']} bits")
    print()

    print("  Reference Categories:")
    for cat, info in sorted(category_info["categories"].items()):
        print(f"    {info['name']}: {info['classical']} classical / {info['quantum']} quantum")
    print()


def print_recommendations(suggestions: Dict[str, Any]) -> None:
    """Print parameter recommendations."""
    print("PARAMETER ANALYSIS & RECOMMENDATIONS:")
    print("-" * 40)
    print(f"  Current modulus bits:             {suggestions['current_modulus_bits']}")
    print(f"  Current estimated security:       ~{suggestions['current_estimated_security']} bits")
    print(f"  Required bits for 128-bit sec:    ~{suggestions['required_bits_for_128_security']}")
    if suggestions['suggested_prime']:
        print(f"  Suggested NTT-compatible prime:")
        print(f"    Value: {suggestions['suggested_prime']}")
        print(f"    Bits:  {suggestions['suggested_prime_bits']}")
    print()


def print_compliant_parameters() -> None:
    """Print compliant parameter recommendations."""
    print("RECOMMENDED NIST-COMPLIANT PARAMETER SETS:")
    print("-" * 40)
    recommendations = compute_recommended_parameters()

    for params in recommendations["recommended_parameter_sets"]:
        print(f"\n  {params['name']}:")
        print(f"    n (ring dimension):  {params['n']}")
        print(f"    log2(q) (modulus):   {params['q_bits']} bits")
        print(f"    q structure:         {params['q_description']}")
        print(f"    t (plaintext mod):   {params['t']}")
        print(f"    sigma (error):       {params['sigma_numer']}/{params['sigma_denom']}")
        print(f"    Classical target:    {params['classical_target']} bits")
        print(f"    Quantum target:      {params['quantum_target']} bits")
    print()


def run_compliant_test() -> Dict[str, Any]:
    """
    Run tests with NIST-compliant parameters (n=4096, q~2^109).
    """
    # NIST Category 1 compliant parameters
    n_compliant = 4096
    # A realistic ~109-bit prime that is 1 mod 8192
    # 2^109 = 649037107316853453566312041152512
    # Find q = k * 8192 + 1 near 2^109
    q_compliant = find_ntt_prime(109, n_compliant)

    if q_compliant == 0:
        # Fallback to a known good prime
        # This is 2^109 rounded up to nearest q = 1 mod 8192
        q_compliant = 649037107316853453566312048353281  # Approximately

    estimator = LatticeSecurityEstimator(
        n_compliant, q_compliant, SIGMA_NUMER, SIGMA_DENOM
    )

    return estimator.get_full_report()


def main() -> int:
    """Main entry point."""
    print()
    print("*" * 70)
    print("*  QMNF NIST SECURITY COMPLIANCE VALIDATOR")
    print("*  Integer-Only Lattice Security Estimation")
    print("*" * 70)
    print()

    # ==========================================================================
    # PHASE 1: Test provided parameters
    # ==========================================================================
    print("=" * 70)
    print("PHASE 1: VALIDATING PROVIDED PARAMETERS")
    print("=" * 70)
    print()

    # Create estimator and generate report
    estimator = LatticeSecurityEstimator(
        N_RING_DIM, Q_MODULUS, SIGMA_NUMER, SIGMA_DENOM
    )
    report = estimator.get_full_report()

    # Print main report
    print_report(report)

    # Run validation tests
    validator = NISTSecurityValidator()
    validation_results = validator.run_all_tests()
    print_validation_results(validation_results)

    # Assess NIST category
    classical_bits = report["security_estimates"]["classical_security_bits"]
    quantum_bits = report["security_estimates"]["quantum_security_bits"]
    category_info = assess_nist_category(classical_bits, quantum_bits)
    print_nist_category(category_info)

    # ==========================================================================
    # PHASE 2: Parameter Analysis and Recommendations
    # ==========================================================================
    print()
    print("=" * 70)
    print("PHASE 2: PARAMETER ANALYSIS & RECOMMENDATIONS")
    print("=" * 70)
    print()

    suggestions = suggest_compliant_modulus()
    print_recommendations(suggestions)
    print_compliant_parameters()

    # ==========================================================================
    # PHASE 3: Test with compliant parameters
    # ==========================================================================
    print()
    print("=" * 70)
    print("PHASE 3: VALIDATION WITH COMPLIANT PARAMETERS")
    print("=" * 70)
    print()

    # Find a compliant prime
    compliant_q = find_ntt_prime(109, N_RING_DIM)
    if compliant_q > 0:
        print(f"Testing with compliant parameters:")
        print(f"  n = {N_RING_DIM}")
        print(f"  q = {compliant_q} ({compliant_q.bit_length()} bits)")
        print(f"  q mod {2*N_RING_DIM} = {compliant_q % (2*N_RING_DIM)} (should be 1)")
        print()

        compliant_estimator = LatticeSecurityEstimator(
            N_RING_DIM, compliant_q, SIGMA_NUMER, SIGMA_DENOM
        )
        compliant_report = compliant_estimator.get_full_report()

        print("COMPLIANT PARAMETER SECURITY ESTIMATES:")
        print("-" * 40)
        sec = compliant_report.get("security_estimates", {})
        print(f"  Root Hermite Factor (delta): {sec.get('root_hermite_factor_delta', 'N/A')}")
        print(f"  BKZ Block Size (beta):       {sec.get('bkz_block_size_beta', 'N/A')}")
        print(f"  Classical Security:          {sec.get('classical_security_bits', 'N/A')} bits")
        print(f"  Quantum Security:            {sec.get('quantum_security_bits', 'N/A')} bits")
        print()

        compliance = compliant_report.get("nist_compliance", {})
        classical_ok = compliance.get('classical_compliant', False)
        quantum_ok = compliance.get('quantum_compliant', False)
        print("NIST COMPLIANCE WITH COMPLIANT PARAMETERS:")
        print("-" * 40)
        print(f"  Classical Target (>= 128 bits): {'PASS' if classical_ok else 'FAIL'}")
        print(f"  Quantum Target (>= 64 bits):    {'PASS' if quantum_ok else 'FAIL'}")
        print()

        compliant_classical = compliant_report["security_estimates"]["classical_security_bits"]
        compliant_quantum = compliant_report["security_estimates"]["quantum_security_bits"]
        compliant_category = assess_nist_category(compliant_classical, compliant_quantum)
        print(f"  Achieved Category: {compliant_category['category_name']}")
        print()

    # ==========================================================================
    # FINAL SUMMARY
    # ==========================================================================
    print()
    print("=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print()

    print("PROVIDED PARAMETERS (q = 2^54 - 33):")
    print(f"  - Classical Security: {classical_bits} bits")
    print(f"  - Quantum Security:   {quantum_bits} bits")
    print(f"  - NIST Compliant: {'YES' if validation_results['all_passed'] else 'NO'}")
    print()

    print("ANALYSIS:")
    if not validation_results['all_passed']:
        print("  The provided parameters do not meet NIST Category 1 requirements.")
        print("  The 54-bit modulus is insufficient for n=4096 ring dimension.")
        print()
        print("RECOMMENDATION:")
        print(f"  For n={N_RING_DIM} with 128-bit classical security:")
        print(f"  - Use modulus with ~{suggestions['required_bits_for_128_security']} bits")
        print(f"  - Or use modulus chain (product of ~27-bit primes)")
        print()
    else:
        print("  All tests passed. Parameters are NIST compliant.")
        print()

    # Final verdict
    print("=" * 70)
    if validation_results["all_passed"]:
        print("VERDICT: PROVIDED PARAMETERS ARE NIST COMPLIANT")
        print("=" * 70)
        return 0
    else:
        print("VERDICT: PROVIDED PARAMETERS REQUIRE ADJUSTMENT FOR NIST COMPLIANCE")
        print("         See recommendations above for compliant parameter sets.")
        print("=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
