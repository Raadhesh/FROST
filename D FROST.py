#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Educational FROST KeyGen + Signing Experiments (Ristretto255 + SHA-512), Python 3.6.2 compatible.

This is a refactor of the authoritative Ed25519+SHA-512 script where:
  - All group operations are moved to the prime-order Ristretto255 group.
  - All protocol hashing remains SHA-512 (KeyGen PoK, rho, Schnorr challenge).

Implementation notes:
  - Ristretto255 group operations are performed using libsodium via ctypes:
      * crypto_core_ristretto255_is_valid_point
      * crypto_core_ristretto255_add / sub
      * crypto_scalarmult_ristretto255 / _base
  - Scalars remain in the Ed25519/Ristretto scalar field order ℓ, encoded little-endian (32 bytes).
  - Point encodings are 32-byte Ristretto encodings; transcripts use these encodings unchanged in size.

WARNING: Educational only (NOT production-grade):
- Deterministic RNG mode (when --seed is used) is NOT cryptographically secure.
- No authenticated network; broadcast/p2p are simulated with Python dicts.
- Simplified hash-to-scalar (not a ciphersuite-defined hash-to-field).
- No robust complaint/blame; failures raise.
"""

from __future__ import print_function

import argparse
import ctypes
import ctypes.util
import glob
import hashlib
import os
import random
import secrets
import statistics
import time

# Optional: PyNaCl can help ensure libsodium is installed (especially on Windows wheels).
try:
    import nacl  # noqa: F401
except Exception:
    nacl = None


# =============================================================================
# libsodium loader (ctypes) for Ristretto255 primitives
# =============================================================================

def _load_libsodium():
    """
    Load libsodium with ctypes in a cross-platform(ish) way.

    Strategy:
      1) ctypes.util.find_library("sodium")
      2) common library names
      3) search inside the installed 'nacl' package directory for bundled libsodium (common on Windows wheels)

    Raises RuntimeError if libsodium can't be loaded.
    """
    candidates = []

    found = ctypes.util.find_library("sodium")
    if found:
        candidates.append(found)

    # Common names (varies by platform)
    candidates.extend([
        "libsodium.so",
        "libsodium.so.23",
        "libsodium.dylib",
        "libsodium.dll",
        "libsodium-23.dll",
        "sodium.dll",
    ])

    # Search inside PyNaCl package for a bundled libsodium (especially on Windows).
    try:
        import nacl as _nacl
        base = os.path.dirname(_nacl.__file__)
        for pat in ("**/libsodium*.dll", "**/libsodium*.so*", "**/libsodium*.dylib"):
            candidates.extend(glob.glob(os.path.join(base, pat), recursive=True))
    except Exception:
        pass

    last_err = None
    for name in candidates:
        try:
            lib = ctypes.CDLL(name)
            # Ensure we can call sodium_init
            if not hasattr(lib, "sodium_init"):
                continue
            # Initialize libsodium
            lib.sodium_init.restype = ctypes.c_int
            lib.sodium_init.argtypes = []
            lib.sodium_init()
            return lib
        except Exception as e:
            last_err = e

    raise RuntimeError(
        "Could not load libsodium for Ristretto255 operations. "
        "Install/upgrade libsodium (>= 1.0.18) or install PyNaCl (pip install pynacl). "
        "Last error: {}".format(last_err)
    )
#

_SODIUM = _load_libsodium()

# Define ctypes signatures for the Ristretto255 APIs we use.
_U8 = ctypes.c_ubyte
_U8P = ctypes.POINTER(_U8)

# int crypto_core_ristretto255_is_valid_point(const unsigned char *p);
_SODIUM.crypto_core_ristretto255_is_valid_point.restype = ctypes.c_int
_SODIUM.crypto_core_ristretto255_is_valid_point.argtypes = [_U8P]

# int crypto_core_ristretto255_add(unsigned char *r, const unsigned char *p, const unsigned char *q);
_SODIUM.crypto_core_ristretto255_add.restype = ctypes.c_int
_SODIUM.crypto_core_ristretto255_add.argtypes = [_U8P, _U8P, _U8P]

# int crypto_core_ristretto255_sub(unsigned char *r, const unsigned char *p, const unsigned char *q);
_SODIUM.crypto_core_ristretto255_sub.restype = ctypes.c_int
_SODIUM.crypto_core_ristretto255_sub.argtypes = [_U8P, _U8P, _U8P]

# int crypto_scalarmult_ristretto255(unsigned char *q, const unsigned char *n, const unsigned char *p);
_SODIUM.crypto_scalarmult_ristretto255.restype = ctypes.c_int
_SODIUM.crypto_scalarmult_ristretto255.argtypes = [_U8P, _U8P, _U8P]

# int crypto_scalarmult_ristretto255_base(unsigned char *q, const unsigned char *n);
_SODIUM.crypto_scalarmult_ristretto255_base.restype = ctypes.c_int
_SODIUM.crypto_scalarmult_ristretto255_base.argtypes = [_U8P, _U8P]


def _as_u8_32(b):
    if not isinstance(b, (bytes, bytearray)) or len(b) != 32:
        raise ValueError("Expected 32-byte buffer")
    return (_U8 * 32).from_buffer_copy(bytes(b))


def _out_u8_32():
    return (_U8 * 32)()


# =============================================================================
# Ristretto255 scalar/point utilities (educational; SHA-512 kept)
# =============================================================================

# Ristretto255 uses the same prime scalar field order as Ed25519
L = 2**252 + 27742317777372353535851937790883648493
SCALAR_BYTES = 32
POINT_BYTES = 32

# Ristretto255 identity has canonical encoding of 32 zero bytes
RISTRETTO_IDENTITY = b"\x00" * 32

# Domain separation tags (SHA-512 everywhere) - kept as SHA512 tags
DST_KEYGEN_POK = b"FROST_KEYGEN_POK_SHA512"
DST_SIGN_RHO = b"FROST_SIGN_RHO_SHA512"
DST_SIGN_CHALLENGE = b"FROST_SIGN_CHALLENGE_SHA512"


def int_to_bytes_be(x, length):
    return int(x).to_bytes(length, "big")


def scalar_reduce(x):
    return int(x) % L


def scalar_add(a, b):
    return (int(a) + int(b)) % L


def scalar_sub(a, b):
    return (int(a) - int(b)) % L


def scalar_mul(a, b):
    return (int(a) * int(b)) % L


def scalar_inv(a):
    a = int(a) % L
    if a == 0:
        raise ZeroDivisionError("No inverse for 0 mod ℓ")
    return pow(a, L - 2, L)


def scalar_to_bytes_le(a):
    return (int(a) % L).to_bytes(SCALAR_BYTES, "little")


def scalar_from_bytes_le(b):
    if len(b) != SCALAR_BYTES:
        raise ValueError("Scalar bytes must be 32 bytes")
    return int.from_bytes(b, "little") % L


def point_is_valid(P_bytes):
    if not isinstance(P_bytes, (bytes, bytearray)) or len(P_bytes) != POINT_BYTES:
        return False
    try:
        p = _as_u8_32(P_bytes)
        return _SODIUM.crypto_core_ristretto255_is_valid_point(p) == 1
    except Exception:
        return False


def point_from_bytes(P_bytes):
    P_bytes = bytes(P_bytes)
    if len(P_bytes) != POINT_BYTES:
        raise ValueError("Point bytes must be 32 bytes")
    if not point_is_valid(P_bytes):
        raise ValueError("Invalid Ristretto255 point encoding")
    return P_bytes


def point_to_bytes(P):
    return bytes(P)


def point_eq(P, Q):
    return bytes(P) == bytes(Q)


def point_add(P, Q):
    P = bytes(P)
    Q = bytes(Q)
    out = _out_u8_32()
    p = _as_u8_32(P)
    q = _as_u8_32(Q)
    rc = _SODIUM.crypto_core_ristretto255_add(out, p, q)
    if rc != 0:
        raise RuntimeError("libsodium ristretto add failed")
    return bytes(out)


def point_sub(P, Q):
    P = bytes(P)
    Q = bytes(Q)
    out = _out_u8_32()
    p = _as_u8_32(P)
    q = _as_u8_32(Q)
    rc = _SODIUM.crypto_core_ristretto255_sub(out, p, q)
    if rc != 0:
        raise RuntimeError("libsodium ristretto sub failed")
    return bytes(out)


def point_mul_base(k):
    # [k]B in Ristretto255 (libsodium canonical basepoint)
    out = _out_u8_32()
    kb = _as_u8_32(scalar_to_bytes_le(k))
    rc = _SODIUM.crypto_scalarmult_ristretto255_base(out, kb)
    if rc != 0:
        raise RuntimeError("libsodium ristretto base scalar mult failed")
    return bytes(out)


def point_mul(P, k):
    # [k]P in Ristretto255
    P = bytes(P)
    out = _out_u8_32()
    kb = _as_u8_32(scalar_to_bytes_le(k))
    p = _as_u8_32(P)
    rc = _SODIUM.crypto_scalarmult_ristretto255(out, kb, p)
    if rc != 0:
        raise RuntimeError("libsodium ristretto scalar mult failed (invalid point?)")
    return bytes(out)


# Sanity: identity should be valid and equal to [0]B
if not point_is_valid(RISTRETTO_IDENTITY):
    raise RuntimeError("RISTRETTO_IDENTITY encoding is not valid under libsodium")
if not point_eq(point_mul_base(0), RISTRETTO_IDENTITY):
    raise RuntimeError("Identity check failed: [0]B != identity in this backend")


# =============================================================================
# Deterministic RNG wrapper (for reproducible experiments; NOT secure)
# =============================================================================

class ExperimentRNG(object):
    """
    A tiny wrapper that can use either:
      - secrets.SystemRandom / secrets.randbelow (default, non-deterministic), or
      - random.Random(seed) (deterministic, reproducible; NOT cryptographically secure).
    """
    def __init__(self, seed=None):
        self.seed = seed
        self._rnd = random.Random(seed) if seed is not None else None

    def randbelow(self, n):
        if self._rnd is None:
            return secrets.randbelow(n)
        return self._rnd.randrange(n)

    def sample(self, population, k):
        if self._rnd is None:
            return secrets.SystemRandom().sample(population, k)
        return self._rnd.sample(population, k)


def rand_scalar_nonzero(rng):
    # sample uniformly from Z_ℓ^* (non-zero)
    return rng.randbelow(L - 1) + 1


# =============================================================================
# SHA-512 hash-to-scalar (non-zero) in Z_ℓ (UNCHANGED)
# =============================================================================

def hash_to_scalar_nonzero_sha512(domain, *parts):
    """
    c = SHA512(domain || 0x00 || ctr || (len||part)... ) mod ℓ
    retry if c == 0
    """
    ctr = 0
    while True:
        h = hashlib.sha512()
        h.update(domain)
        h.update(b"\x00")
        h.update(int_to_bytes_be(ctr, 4))
        for p in parts:
            if not isinstance(p, (bytes, bytearray)):
                raise TypeError("hash parts must be bytes")
            h.update(int_to_bytes_be(len(p), 4))
            h.update(bytes(p))
        c = int.from_bytes(h.digest(), "big") % L
        if c != 0:
            return c
        ctr += 1


# =============================================================================
# Polynomial / Shamir utilities over Z_ℓ
# =============================================================================

def eval_poly(coeffs, x):
    # f(x) = sum_{j=0..t-1} a_j * x^j mod ℓ
    acc = 0
    power = 1
    x = int(x) % L
    for a_j in coeffs:
        acc = (acc + (int(a_j) % L) * power) % L
        power = (power * x) % L
    return acc


def lagrange_coeff_at_zero(i, S):
    # λ_i = Π_{j in S, j != i} (0 - j) / (i - j) mod ℓ
    num = 1
    den = 1
    i = int(i) % L
    for j in S:
        j = int(j) % L
        if j == i:
            continue
        num = (num * (-j % L)) % L
        den = (den * ((i - j) % L)) % L
    return (num * scalar_inv(den)) % L


def shamir_reconstruct_secret_at_zero(shares):
    S = list(shares.keys())
    secret = 0
    for i, si in shares.items():
        lam = lagrange_coeff_at_zero(i, S)
        secret = (secret + lam * (int(si) % L)) % L
    return secret


# =============================================================================
# KeyGen message types (simple Python 3.6.2 classes)
# =============================================================================

class SchnorrPoK(object):
    # σ_i = (R_i, μ_i)
    def __init__(self, R, mu):
        self.R = bytes(R)        # Ristretto point encoding (32B)
        self.mu = int(mu) % L    # scalar


class KeyGenBroadcast(object):
    # C~_i and σ_i
    def __init__(self, dealer_id, C_tilde, sigma):
        self.dealer_id = int(dealer_id)
        self.C_tilde = list(C_tilde)   # list of Ristretto points φ_{i0..i,t-1}
        self.sigma = sigma             # SchnorrPoK


# =============================================================================
# Feldman share verification over Ristretto points (KeyGen Round 2 Step 2)
# =============================================================================

def feldman_verify_share_point(C_tilde_dealer, receiver_id, share_value):
    """
    Check:
      Left:  [ f_dealer(receiver_id) ] B
      Right: Σ_{k=0..t-1} [ receiver_id^k ] φ_{dealer,k}
    """
    receiver_id = int(receiver_id)
    share_value = int(share_value) % L

    left = point_mul_base(share_value)

    rhs = RISTRETTO_IDENTITY
    power = 1  # receiver_id^0
    for phi_k in C_tilde_dealer:
        term = point_mul(phi_k, power)
        rhs = point_add(rhs, term)
        power = (power * receiver_id) % L

    return point_eq(left, rhs)


# =============================================================================
# Participant: KeyGen + (Educational) Signing state
# =============================================================================

class Participant(object):
    """
    KeyGen state:
      - a_{i0..i,t-1} : polynomial coefficients
      - C~_i          : commitments φ_{ij} = [a_{ij}]B  (Ristretto points)
      - σ_i           : PoK of a_{i0}
      - s_i           : long-lived secret share
      - Y_i           : public key share [s_i]B (Ristretto point)

    Signing (ephemeral) state per trial/signing:
      - d_i, e_i      : nonces (scalars)
      - D_i, E_i      : commitments ([d_i]B, [e_i]B) (Ristretto points)
    """

    def __init__(self, i, n, t, ctx_phi):
        self.i = int(i)
        self.n = int(n)
        self.t = int(t)
        self.ctx_phi = str(ctx_phi)

        # Round 1 internal state
        self.a = None
        self.C_tilde = None
        self.sigma = None

        # Keep own share from own polynomial
        self._self_share_from_own_poly = None

        # Outputs after Round 2
        self.s_i = None
        self.Y_i = None

        # Signing ephemeral state (set during preprocess)
        self._nonce_d = None
        self._nonce_e = None
        self.D_i = None
        self.E_i = None

    # -------- KeyGen Round 1 Step 1 + Step 3 --------
    def round1_sample_poly_and_commit(self, rng):
        self.a = [rand_scalar_nonzero(rng) for _ in range(self.t)]
        self.C_tilde = [point_mul_base(aij) for aij in self.a]

    # -------- KeyGen Round 1 Step 2 --------
    def round1_generate_pok_of_a_i0(self, rng):
        if self.a is None or self.C_tilde is None:
            raise RuntimeError("Must run round1_sample_poly_and_commit() first.")

        a_i0 = self.a[0]
        phi_i0 = self.C_tilde[0]

        k = rand_scalar_nonzero(rng)
        R = point_mul_base(k)

        # Context Φ included here (anti-replay / domain separation)
        c = hash_to_scalar_nonzero_sha512(
            DST_KEYGEN_POK,
            int_to_bytes_be(self.i, 4),
            self.ctx_phi.encode("utf-8"),
            point_to_bytes(phi_i0),
            point_to_bytes(R),
        )

        mu = scalar_add(k, scalar_mul(a_i0, c))
        self.sigma = SchnorrPoK(R=R, mu=mu)

    # -------- KeyGen Round 1 Step 4 --------
    def round1_broadcast(self):
        if self.C_tilde is None or self.sigma is None:
            raise RuntimeError("Round 1 not complete.")
        return KeyGenBroadcast(dealer_id=self.i, C_tilde=self.C_tilde, sigma=self.sigma)

    # -------- KeyGen Round 1 Step 5 --------
    def round1_verify_others_pok(self, broadcasts):
        for dealer_id, msg in broadcasts.items():
            if int(dealer_id) == self.i:
                continue

            R = msg.sigma.R
            mu = msg.sigma.mu
            phi_l0 = msg.C_tilde[0]

            c = hash_to_scalar_nonzero_sha512(
                DST_KEYGEN_POK,
                int_to_bytes_be(int(dealer_id), 4),
                self.ctx_phi.encode("utf-8"),
                point_to_bytes(phi_l0),
                point_to_bytes(R),
            )

            # Check: R ?= [μ]B - [c]φ_{ℓ0}
            g_mu = point_mul_base(mu)
            cphi = point_mul(phi_l0, c)
            right = point_sub(g_mu, cphi)

            if not point_eq(R, right):
                raise RuntimeError("PoK verification failed at P{} for dealer P{}".format(self.i, dealer_id))

    # -------- KeyGen Round 2 Step 1 --------
    def round2_send_shares(self):
        if self.a is None:
            raise RuntimeError("Round 1 polynomial not generated.")
        shares = {}
        for l_id in range(1, self.n + 1):
            shares[l_id] = eval_poly(self.a, l_id)

        self._self_share_from_own_poly = shares[self.i]
        self.a = None  # educational deletion
        return shares

    # -------- KeyGen Round 2 Step 2 + Step 3 + Step 4 --------
    def round2_receive_verify_and_finalize(self, broadcasts, shares_from_all_dealers):
        if self._self_share_from_own_poly is None:
            raise RuntimeError("Must run round2_send_shares() first.")

        # Step 2: verify all incoming shares
        for dealer_id in range(1, self.n + 1):
            C_tilde_dealer = broadcasts[dealer_id].C_tilde
            share_value = shares_from_all_dealers[dealer_id]  # f_dealer(i)
            if not feldman_verify_share_point(C_tilde_dealer, self.i, share_value):
                raise RuntimeError("Share verification failed at P{} for dealer P{}".format(self.i, dealer_id))

        # Step 3: s_i = Σ f_dealer(i) mod ℓ
        s_i = 0
        for dealer_id in range(1, self.n + 1):
            s_i = scalar_add(s_i, shares_from_all_dealers[dealer_id])

        self.s_i = s_i

        # Step 4: Y_i = [s_i]B
        self.Y_i = point_mul_base(self.s_i)

    # =============================================================================
    # Signing experiments (educational FROST-style)
    # =============================================================================

    def preprocess_nonces_and_commitments(self, rng):
        """
        Preprocess (educational):
          d_i, e_i ← Z_ℓ^*
          D_i = [d_i]B,  E_i = [e_i]B   (Ristretto points)
        """
        self._nonce_d = rand_scalar_nonzero(rng)
        self._nonce_e = rand_scalar_nonzero(rng)
        self.D_i = point_mul_base(self._nonce_d)
        self.E_i = point_mul_base(self._nonce_e)
        return self.D_i, self.E_i

    def sign_share(self, rho_i, challenge_c, lambda_i):
        """
        Produce a signature share (educational Schnorr threshold share):

          z_i = d_i + rho_i*e_i + (lambda_i * s_i * c)  mod ℓ
        """
        if self._nonce_d is None or self._nonce_e is None or self.s_i is None:
            raise RuntimeError("Missing nonces or secret share; run preprocess and KeyGen first.")

        z_i = self._nonce_d
        z_i = scalar_add(z_i, scalar_mul(rho_i, self._nonce_e))
        z_i = scalar_add(z_i, scalar_mul(lambda_i, scalar_mul(self.s_i, challenge_c)))

        # Erase nonces (educational hygiene)
        self._nonce_d = None
        self._nonce_e = None

        return z_i


# =============================================================================
# KeyGen orchestrator
# =============================================================================

def frost_keygen(n, t, ctx_phi, rng):
    n = int(n)
    t = int(t)
    if not (1 <= t <= n):
        raise ValueError("Require 1 <= t <= n")

    participants = {}
    for i in range(1, n + 1):
        participants[i] = Participant(i=i, n=n, t=t, ctx_phi=ctx_phi)

    # ----- Round 1 -----
    broadcasts = {}
    for i, Pi in participants.items():
        Pi.round1_sample_poly_and_commit(rng)     # Step 1 + Step 3
        Pi.round1_generate_pok_of_a_i0(rng)       # Step 2
        broadcasts[i] = Pi.round1_broadcast()     # Step 4

    for i, Pi in participants.items():
        Pi.round1_verify_others_pok(broadcasts)   # Step 5

    # ----- Round 2 -----
    mailbox = {}
    for i in range(1, n + 1):
        mailbox[i] = {}

    for dealer_id, Pi in participants.items():
        shares = Pi.round2_send_shares()
        for receiver_id, share_val in shares.items():
            mailbox[receiver_id][dealer_id] = share_val

    for receiver_id, Pi in participants.items():
        Pi.round2_receive_verify_and_finalize(
            broadcasts=broadcasts,
            shares_from_all_dealers=mailbox[receiver_id],
        )

    # Round 2 Step 4: group public key Y = Σ φ_{j0}
    Y = RISTRETTO_IDENTITY
    for j in range(1, n + 1):
        phi_j0 = broadcasts[j].C_tilde[0]
        Y = point_add(Y, phi_j0)

    return participants, Y


# =============================================================================
# Signing helpers (subset selection, binding factors, challenge, aggregate, verify)
# =============================================================================

def choose_signer_subset(n, t, alpha, rng):
    n = int(n)
    t = int(t)
    alpha = int(alpha)
    if not (t <= alpha <= n):
        raise ValueError("Require t <= alpha <= n")
    S = rng.sample(list(range(1, n + 1)), alpha)
    S = sorted([int(x) for x in S])
    return S


def encode_commitment_list(S, commitments):
    """
    Deterministic transcript encoding of commitments for a signer subset S.

    commitments[i] = (D_i_bytes, E_i_bytes) where each is a 32-byte Ristretto encoding.
    Encoding: for i in sorted(S): i(4B big-endian) || D_i(32B) || E_i(32B)
    """
    out = b""
    for i in sorted(S):
        D_i, E_i = commitments[i]
        out += int_to_bytes_be(i, 4) + point_to_bytes(D_i) + point_to_bytes(E_i)
    return out


def compute_binding_factors(ctx_phi, message_bytes, S, commitments):
    """
    Compute per-signer binding factors rho_i.

    Educational approach:
      rho_i = H_to_Zℓ*( DST_SIGN_RHO, i, Φ, m, encode_commitment_list(S, commitments) )
    """
    transcript = encode_commitment_list(S, commitments)
    rho = {}
    for i in S:
        rho[i] = hash_to_scalar_nonzero_sha512(
            DST_SIGN_RHO,
            int_to_bytes_be(i, 4),
            ctx_phi.encode("utf-8"),
            message_bytes,
            transcript,
        )
    return rho


def compute_group_commitment_R(S, commitments, rho):
    """
    Compute:
      R = Σ_{i in S} ( D_i + [rho_i] E_i )
    """
    R = RISTRETTO_IDENTITY
    for i in S:
        D_i, E_i = commitments[i]
        R_i = point_add(D_i, point_mul(E_i, rho[i]))
        R = point_add(R, R_i)
    return R


def compute_challenge(ctx_phi, Y, R, message_bytes):
    """
    Schnorr challenge:
      c = H_to_Zℓ*( DST_SIGN_CHALLENGE, Φ, Y, R, m )
    """
    return hash_to_scalar_nonzero_sha512(
        DST_SIGN_CHALLENGE,
        ctx_phi.encode("utf-8"),
        point_to_bytes(Y),
        point_to_bytes(R),
        message_bytes,
    )


def aggregate_signature_shares(S, z_shares):
    """
    Aggregate:
      z = Σ_{i in S} z_i mod ℓ
    """
    z = 0
    for i in S:
        z = scalar_add(z, z_shares[i])
    return z


def verify_schnorr_signature(Y, ctx_phi, message_bytes, signature):
    """
    Verify a Schnorr signature (R, z) against public key Y:

      [z]B ?= R + [c]Y
      c = H_to_Zℓ*( DST_SIGN_CHALLENGE, Φ, Y, R, m )
    """
    R, z = signature
    c = compute_challenge(ctx_phi, Y, R, message_bytes)
    left = point_mul_base(z)
    right = point_add(R, point_mul(Y, c))
    return point_eq(left, right)


# =============================================================================
# Runtime instrumentation helpers
# =============================================================================

def ms(dt_seconds):
    return 1000.0 * dt_seconds


def mean_median(values):
    if not values:
        return 0.0, 0.0
    return float(statistics.mean(values)), float(statistics.median(values))


# =============================================================================
# Main (CLI + trials)
# =============================================================================

def parse_args():
    p = argparse.ArgumentParser(description="Educational FROST KeyGen + signing experiments (Ristretto255 + SHA-512).")
    p.add_argument("--n", type=int, default=10, help="Number of participants (n). Default: 10.")
    p.add_argument("--t", type=int, default=5, help="Threshold (t). Default: 5.")
    p.add_argument("--alpha", type=int, default=None, help="Signer subset size (alpha), t <= alpha <= n. Default: alpha=t.")
    p.add_argument("--trials", type=int, default=1, help="Number of trials (default 1).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible randomness (NOT secure).")
    p.add_argument("--message", type=str, default="test", help="Message to sign (default 'test').")
    return p.parse_args()


def main():
    # --- Setup timing (argument parsing + RNG seeding) ---
    t_setup_start = time.perf_counter()

    args = parse_args()
    n = int(args.n)
    t = int(args.t)
    alpha = int(args.alpha) if args.alpha is not None else int(t)
    trials = int(args.trials)
    seed = args.seed
    msg_str = args.message
    message_bytes = msg_str.encode("utf-8")

    if not (1 <= t <= n):
        raise ValueError("Require 1 <= t <= n")
    if not (t <= alpha <= n):
        raise ValueError("Require t <= alpha <= n")
    if trials < 1:
        raise ValueError("Require --trials >= 1")

    # Setup completed
    t_setup_end = time.perf_counter()
    setup_ms = ms(t_setup_end - t_setup_start)

    # Containers for summary stats across trials (ms)
    stats = {
        "setup_ms": [],
        "keygen_ms": [],
        "preprocess_ms": [],
        "sign_ms": [],
        "aggregate_ms": [],
        "verify_ms": [],
        "total_ms": [],
        "preprocess_per_participant_ms": [],
        "sign_per_participant_ms": [],
    }

    print("=== Configuration ===")
    print("n={}, t={}, alpha={}, trials={}, seed={}, message={!r}".format(n, t, alpha, trials, seed, msg_str))
    print("Note: if --seed is set, RNG is deterministic for reproducibility (NOT secure).")
    print("")

    # --- Trials ---
    for trial in range(1, trials + 1):
        trial_seed = None if seed is None else (int(seed) + int(trial))
        rng = ExperimentRNG(seed=trial_seed)

        t_total_start = time.perf_counter()

        # --- KeyGen ---
        t_keygen_start = time.perf_counter()
        ctx_phi = "FROST demo context (Phi)"
        participants, Y = frost_keygen(n=n, t=t, ctx_phi=ctx_phi, rng=rng)
        t_keygen_end = time.perf_counter()
        keygen_ms = ms(t_keygen_end - t_keygen_start)

        # --- Random subset selection (S) ---
        S = choose_signer_subset(n=n, t=t, alpha=alpha, rng=rng)

        # --- Preprocess (per signer) ---
        commitments = {}
        preprocess_pp = {}
        t_preprocess_start = time.perf_counter()
        for i in S:
            Pi = participants[i]
            t0 = time.perf_counter()
            D_i, E_i = Pi.preprocess_nonces_and_commitments(rng)
            t1 = time.perf_counter()
            commitments[i] = (D_i, E_i)
            preprocess_pp[i] = ms(t1 - t0)
        t_preprocess_end = time.perf_counter()
        preprocess_ms_total = ms(t_preprocess_end - t_preprocess_start)

        # --- Aggregator computations ---
        agg_ms_total = 0.0
        t_agg_1_start = time.perf_counter()

        rho = compute_binding_factors(ctx_phi, message_bytes, S, commitments)
        R = compute_group_commitment_R(S, commitments, rho)
        c = compute_challenge(ctx_phi, Y, R, message_bytes)

        lambdas = {}
        for i in S:
            lambdas[i] = lagrange_coeff_at_zero(i, S)

        t_agg_1_end = time.perf_counter()
        agg_ms_total += ms(t_agg_1_end - t_agg_1_start)

        # --- Sign (per signer) ---
        z_shares = {}
        sign_pp = {}
        t_sign_start = time.perf_counter()
        for i in S:
            Pi = participants[i]
            t0 = time.perf_counter()
            z_i = Pi.sign_share(rho_i=rho[i], challenge_c=c, lambda_i=lambdas[i])
            t1 = time.perf_counter()
            z_shares[i] = z_i
            sign_pp[i] = ms(t1 - t0)
        t_sign_end = time.perf_counter()
        sign_ms_total = ms(t_sign_end - t_sign_start)

        # --- Aggregate (combine shares) ---
        t_agg_2_start = time.perf_counter()
        z = aggregate_signature_shares(S, z_shares)
        signature = (R, z)
        t_agg_2_end = time.perf_counter()
        agg_ms_total += ms(t_agg_2_end - t_agg_2_start)

        # --- Verify ---
        t_verify_start = time.perf_counter()
        ok = verify_schnorr_signature(Y, ctx_phi, message_bytes, signature)
        t_verify_end = time.perf_counter()
        verify_ms = ms(t_verify_end - t_verify_start)

        # --- End-to-end trial total ---
        t_total_end = time.perf_counter()
        total_ms = ms(t_total_end - t_total_start)

        # --- Print per trial ---
        print("=== Trial {}/{} ===".format(trial, trials))
        print("Trial seed: {}".format(trial_seed))
        print("Chosen signer subset S (alpha={}): {}".format(alpha, S))
        print("Verification succeeded? {}".format(ok))
        print("")
        print("Runtimes (ms):")
        print("  setup_ms       : {:.3f}".format(setup_ms))
        print("  keygen_ms      : {:.3f}".format(keygen_ms))
        print("  preprocess_ms  : {:.3f}   (per signer: {})".format(
            preprocess_ms_total,
            ", ".join(["P{}={:.3f}".format(i, preprocess_pp[i]) for i in S])
        ))
        print("  sign_ms        : {:.3f}   (per signer: {})".format(
            sign_ms_total,
            ", ".join(["P{}={:.3f}".format(i, sign_pp[i]) for i in S])
        ))
        print("  aggregate_ms   : {:.3f}".format(agg_ms_total))
        print("  verify_ms      : {:.3f}".format(verify_ms))
        print("  total_ms       : {:.3f}".format(total_ms))
        print("")

        # --- Collect stats ---
        stats["setup_ms"].append(setup_ms)
        stats["keygen_ms"].append(keygen_ms)
        stats["preprocess_ms"].append(preprocess_ms_total)
        stats["sign_ms"].append(sign_ms_total)
        stats["aggregate_ms"].append(agg_ms_total)
        stats["verify_ms"].append(verify_ms)
        stats["total_ms"].append(total_ms)

        for i in S:
            stats["preprocess_per_participant_ms"].append(preprocess_pp[i])
            stats["sign_per_participant_ms"].append(sign_pp[i])

    # --- Summary ---
    print("=== Summary (mean / median over {} trials) ===".format(trials))
    rows = [
        ("setup_ms", stats["setup_ms"]),
        ("keygen_ms", stats["keygen_ms"]),
        ("preprocess_ms", stats["preprocess_ms"]),
        ("sign_ms", stats["sign_ms"]),
        ("aggregate_ms", stats["aggregate_ms"]),
        ("verify_ms", stats["verify_ms"]),
        ("total_ms", stats["total_ms"]),
        ("preprocess_per_participant_ms", stats["preprocess_per_participant_ms"]),
        ("sign_per_participant_ms", stats["sign_per_participant_ms"]),
    ]
    for name, vals in rows:
        mu, med = mean_median(vals)
        print("  {:28s}  mean={:10.3f}   median={:10.3f}".format(name, mu, med))


if __name__ == "__main__":
    main()
