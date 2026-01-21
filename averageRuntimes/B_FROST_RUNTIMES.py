#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Educational FROST KeyGen + Signing Experiments (Ed448 + SHAKE256), Python 3.6.2 compatible.

Refactor goals (minimal/traceable migration from the Ed25519+SHA-512 starting script):
  1) Replace all group operations with Ed448 (edwards448) over F_p:
       - p = 2^448 - 2^224 - 1
       - a = -1
       - d = -39081
       - Base point B (RFC 8032 Ed448)
       - Prime-order subgroup order ℓ (L_ED448)
       - Standard EdDSA-style point encoding (57 bytes):
           encode y (little-endian), store sign(x) in MSB of last byte
  2) Replace all protocol hashing with SHAKE256:
       - KeyGen PoK challenge
       - Signing binding-factor / rho derivation
       - Schnorr challenge derivation
       - Any hash-to-scalar
     using:
       hash_to_scalar_nonzero_shake256(domain, outlen, *parts) -> int

Preserved features (same experiment logic as starting script):
  - Random signer-subset selection (alpha, t <= alpha <= n)
  - Preprocess -> Sign shares -> Aggregate -> Verify flow
  - Runtime instrumentation (setup/keygen/preprocess/sign/aggregate/verify/total) with mean/median summary
  - Python 3.6.2 compatibility (no dataclasses; time.perf_counter())

WARNING: Educational only (NOT production-grade):
  - Pure-Python curve arithmetic is NOT constant-time and not hardened.
  - Deterministic RNG mode (when --seed is used) is NOT cryptographically secure.
  - No authenticated network; broadcast/p2p are simulated with dicts.
  - Simplified hash-to-scalar (not a ciphersuite-defined hash-to-field).
  - No robust complaint/blame; failures raise.

Performance note:
  - Pure-Python Ed448 arithmetic is slower than library-backed Ed25519.
  - Keep n/t/trials modest for interactive experiments.
"""

from __future__ import print_function

import argparse
import hashlib
import random
import secrets
import statistics
import time


# =============================================================================
# Ed448 (edwards448) parameters and field/scalar utilities
# =============================================================================

# Field prime p = 2^448 - 2^224 - 1
P = (1 << 448) - (1 << 224) - 1

# Twisted Edwards parameters for RFC 8032 Ed448 (edwards448): a = +1, d = -39081
A = 1 % P                           # +1 mod p
D = (P - 39081) % P                 # -39081 mod p

# Ed448 subgroup order ℓ (prime order of the base point subgroup), per RFC 8032
L_ED448 = (1 << 446) - 13818066809895115352007386748515426880336692474882178609894547503885

SCALAR_BYTES = 57
POINT_BYTES = 57

# SHAKE256 output length choice:
# 114 bytes is the Ed448 EdDSA digest length (RFC 8032). 114 bytes = 912 bits >> 446 bits,
# so reduction bias mod ℓ is negligible for educational purposes.
HASH_OUTLEN = 114

# Domain separation tags (SHAKE256 everywhere)
DST_KEYGEN_POK = b"FROST_KEYGEN_POK_SHAKE256"
DST_SIGN_RHO = b"FROST_SIGN_RHO_SHAKE256"
DST_SIGN_CHALLENGE = b"FROST_SIGN_CHALLENGE_SHAKE256"


def int_to_bytes_be(x, length):
    return int(x).to_bytes(length, "big")


def fe(x):
    """Field element reduction mod p."""
    return int(x) % P


def fe_add(x, y):
    return (int(x) + int(y)) % P


def fe_sub(x, y):
    return (int(x) - int(y)) % P


def fe_mul(x, y):
    return (int(x) * int(y)) % P


def fe_inv(x):
    """Multiplicative inverse mod p (p is prime)."""
    x = int(x) % P
    if x == 0:
        raise ZeroDivisionError("No inverse for 0 mod p")
    return pow(x, P - 2, P)


def fe_neg(x):
    return (-int(x)) % P


def fe_is_square(x):
    """
    Euler criterion: x is a quadratic residue mod p iff x^((p-1)/2) == 1 (or x==0).
    """
    x = int(x) % P
    if x == 0:
        return True
    return pow(x, (P - 1) // 2, P) == 1


def fe_sqrt(x):
    """
    Square root in F_p for p ≡ 3 (mod 4). For edwards448 prime, p % 4 == 3 holds.
    If sqrt exists, return r such that r^2 == x mod p, else return None.
    """
    x = int(x) % P
    if x == 0:
        return 0
    # For p ≡ 3 mod 4: sqrt(x) = x^((p+1)/4)
    r = pow(x, (P + 1) // 4, P)
    if (r * r) % P != x:
        return None
    return r


def scalar_reduce(x):
    return int(x) % L_ED448


def scalar_add(a, b):
    return (int(a) + int(b)) % L_ED448


def scalar_sub(a, b):
    return (int(a) - int(b)) % L_ED448


def scalar_mul(a, b):
    return (int(a) * int(b)) % L_ED448


def scalar_inv(a):
    a = int(a) % L_ED448
    if a == 0:
        raise ZeroDivisionError("No inverse for 0 mod ℓ")
    return pow(a, L_ED448 - 2, L_ED448)


def scalar_to_bytes_le(a):
    return (int(a) % L_ED448).to_bytes(SCALAR_BYTES, "little")


def scalar_from_bytes_le(b):
    if len(b) != SCALAR_BYTES:
        raise ValueError("Scalar bytes must be 57 bytes")
    return int.from_bytes(b, "little") % L_ED448


# =============================================================================
# Ed448 point representation (extended coordinates) + operations
# =============================================================================

class Point(object):
    """
    Extended coordinates for twisted Edwards curves:
      (X : Y : Z : T) with x = X/Z, y = Y/Z, and T = XY/Z.

    For Ed448 (a=+1), we use complete addition/doubling formulas (educational).
    """

    def __init__(self, X, Y, Z, T):
        self.X = fe(X)
        self.Y = fe(Y)
        self.Z = fe(Z)
        self.T = fe(T)

    @staticmethod
    def identity():
        # (x,y) = (0,1) => (X,Y,Z,T) = (0,1,1,0)
        return Point(0, 1, 1, 0)

    @staticmethod
    def from_affine(x, y):
        x = fe(x)
        y = fe(y)
        return Point(x, y, 1, fe_mul(x, y))

    def to_affine(self):
        zinv = fe_inv(self.Z)
        x = fe_mul(self.X, zinv)
        y = fe_mul(self.Y, zinv)
        return x, y

    def is_on_curve(self):
        # Check: a*x^2 + y^2 == 1 + d*x^2*y^2   (mod p)
        x, y = self.to_affine()
        x2 = fe_mul(x, x)
        y2 = fe_mul(y, y)
        left = fe_add(fe_mul(A, x2), y2)                   # a*x^2 + y^2
        right = fe_add(1, fe_mul(D, fe_mul(x2, y2)))       # 1 + d*x^2*y^2
        return left == right

    def encode(self):
        """
        Standard EdDSA-style encoding (57 bytes):
          - Encode y in little-endian,
          - Set MSB of last byte to sign(x) (x mod 2).
        """
        x, y = self.to_affine()
        y_bytes = int(y).to_bytes(POINT_BYTES, "little")
        sign = int(x) & 1
        last = y_bytes[-1]
        last = (last & 0x7F) | (sign << 7)
        return y_bytes[:-1] + bytes([last])

    @staticmethod
    def decode(s):
        """
        Decode 57-byte Ed448 point encoding:
          - y = little-endian with top bit cleared
          - sign = top bit
          - recover x from curve equation:
              x^2 = (1 - y^2) / (a - d y^2)   mod p
          - choose x with correct sign bit
        """
        if not isinstance(s, (bytes, bytearray)) or len(s) != POINT_BYTES:
            raise ValueError("Point encoding must be 57 bytes")
        s = bytes(s)
        sign = (s[-1] >> 7) & 1
        y_bytes = bytearray(s)
        y_bytes[-1] &= 0x7F
        y = int.from_bytes(bytes(y_bytes), "little")
        if y >= P:
            raise ValueError("Invalid encoding: y out of range")

        y2 = fe_mul(y, y)
        num = fe_sub(1, y2)                                # 1 - y^2
        den = fe_sub(A, fe_mul(D, y2))                     # a - d*y^2
        if den == 0:
            raise ValueError("Invalid encoding: denominator is 0")

        x2 = fe_mul(num, fe_inv(den))
        x = fe_sqrt(x2)
        if x is None:
            raise ValueError("Invalid encoding: no square root for x^2")

        if (int(x) & 1) != sign:
            x = fe_neg(x)

        Pnt = Point.from_affine(x, y)
        if not Pnt.is_on_curve():
            raise ValueError("Decoded point is not on curve")
        return Pnt


# Base point B (RFC 8032 Ed448)
B_x = 224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710
B_y = 298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660
BASE_POINT = Point.from_affine(B_x, B_y)

if not BASE_POINT.is_on_curve():
    raise RuntimeError("BASE_POINT is not on the curve; check (p,a,d) or base point coordinates.")

ED448_IDENTITY = Point.identity()


def point_to_bytes(Pt):
    return Pt.encode()


def point_from_bytes(b):
    return Point.decode(b)


def point_eq(Pt, Qt):
    return (fe_mul(Pt.X, Qt.Z) == fe_mul(Qt.X, Pt.Z)) and (fe_mul(Pt.Y, Qt.Z) == fe_mul(Qt.Y, Pt.Z))


def point_neg(Pt):
    return Point(fe_neg(Pt.X), Pt.Y, Pt.Z, fe_neg(Pt.T))


def point_add(P1, P2):
    A_ = fe_mul(P1.X, P2.X)
    B_ = fe_mul(P1.Y, P2.Y)
    C_ = fe_mul(D, fe_mul(P1.T, P2.T))
    D_ = fe_mul(P1.Z, P2.Z)

    E_ = fe_sub(fe_sub(fe_mul(fe_add(P1.X, P1.Y), fe_add(P2.X, P2.Y)), A_), B_)
    F_ = fe_sub(D_, C_)
    G_ = fe_add(D_, C_)
    H_ = fe_sub(B_, fe_mul(A, A_))   # B - a*A

    X3 = fe_mul(E_, F_)
    Y3 = fe_mul(G_, H_)
    Z3 = fe_mul(F_, G_)
    T3 = fe_mul(E_, H_)

    return Point(X3, Y3, Z3, T3)


def point_sub(P1, P2):
    return point_add(P1, point_neg(P2))


def point_double(P1):
    A_ = fe_mul(P1.X, P1.X)
    B_ = fe_mul(P1.Y, P1.Y)
    C_ = fe_mul(2, fe_mul(P1.Z, P1.Z))
    D_ = fe_mul(A, A_)  # a*A
    E_ = fe_sub(fe_sub(fe_mul(fe_add(P1.X, P1.Y), fe_add(P1.X, P1.Y)), A_), B_)
    G_ = fe_add(D_, B_)
    F_ = fe_sub(G_, C_)
    H_ = fe_sub(D_, B_)

    X3 = fe_mul(E_, F_)
    Y3 = fe_mul(G_, H_)
    Z3 = fe_mul(F_, G_)
    T3 = fe_mul(E_, H_)

    return Point(X3, Y3, Z3, T3)


def point_mul(Pt, k):
    k = int(k) % L_ED448
    if k == 0:
        return ED448_IDENTITY
    Q = ED448_IDENTITY
    N = Pt
    while k > 0:
        if k & 1:
            Q = point_add(Q, N)
        N = point_double(N)
        k >>= 1
    return Q


def point_mul_base(k):
    return point_mul(BASE_POINT, k)


if not point_eq(point_mul(BASE_POINT, L_ED448), Point.identity()):
    raise RuntimeError("Subgroup order check failed: [L_ED448]B != identity (scalar mul / params bug).")

# =============================================================================
# Deterministic RNG wrapper (for reproducible experiments; NOT secure)
# =============================================================================

class ExperimentRNG(object):
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
    return rng.randbelow(L_ED448 - 1) + 1


# =============================================================================
# SHAKE256 hash-to-scalar (non-zero) in Z_ℓ
# =============================================================================

def hash_to_scalar_nonzero_shake256(domain, outlen, *parts):
    ctr = 0
    outlen = int(outlen)
    if outlen <= 0:
        raise ValueError("outlen must be positive")
    while True:
        h = hashlib.shake_256()
        h.update(domain)
        h.update(b"\x00")
        h.update(int_to_bytes_be(ctr, 4))
        for p in parts:
            if not isinstance(p, (bytes, bytearray)):
                raise TypeError("hash parts must be bytes")
            h.update(int_to_bytes_be(len(p), 4))
            h.update(bytes(p))
        digest = h.digest(outlen)
        c = int.from_bytes(digest, "big") % L_ED448
        if c != 0:
            return c
        ctr += 1


# =============================================================================
# Polynomial / Shamir utilities over Z_ℓ
# =============================================================================

def eval_poly(coeffs, x):
    acc = 0
    power = 1
    x = int(x) % L_ED448
    for a_j in coeffs:
        acc = (acc + (int(a_j) % L_ED448) * power) % L_ED448
        power = (power * x) % L_ED448
    return acc


def lagrange_coeff_at_zero(i, S):
    num = 1
    den = 1
    i = int(i) % L_ED448
    for j in S:
        j = int(j) % L_ED448
        if j == i:
            continue
        num = (num * (-j % L_ED448)) % L_ED448
        den = (den * ((i - j) % L_ED448)) % L_ED448
    return (num * scalar_inv(den)) % L_ED448


def shamir_reconstruct_secret_at_zero(shares):
    S = list(shares.keys())
    secret = 0
    for i, si in shares.items():
        lam = lagrange_coeff_at_zero(i, S)
        secret = (secret + lam * (int(si) % L_ED448)) % L_ED448
    return secret


# =============================================================================
# KeyGen message types (simple Python 3.6.2 classes)
# =============================================================================

class SchnorrPoK(object):
    def __init__(self, R, mu):
        self.R = R                 # Point
        self.mu = int(mu) % L_ED448


class KeyGenBroadcast(object):
    def __init__(self, dealer_id, C_tilde, sigma):
        self.dealer_id = int(dealer_id)
        self.C_tilde = list(C_tilde)   # list of Points
        self.sigma = sigma             # SchnorrPoK


# =============================================================================
# Feldman share verification over EC points (KeyGen Round 2 Step 2)
# =============================================================================

def feldman_verify_share_point(C_tilde_dealer, receiver_id, share_value):
    receiver_id = int(receiver_id)
    share_value = int(share_value) % L_ED448

    left = point_mul_base(share_value)

    rhs = ED448_IDENTITY
    power = 1
    for phi_k in C_tilde_dealer:
        term = point_mul(phi_k, power)
        rhs = point_add(rhs, term)
        power = (power * receiver_id) % L_ED448

    return point_eq(left, rhs)


# =============================================================================
# Participant: KeyGen + (Educational) Signing state
# =============================================================================

class Participant(object):
    def __init__(self, i, n, t, ctx_phi):
        self.i = int(i)
        self.n = int(n)
        self.t = int(t)
        self.ctx_phi = str(ctx_phi)

        self.a = None
        self.C_tilde = None
        self.sigma = None

        self._self_share_from_own_poly = None

        self.s_i = None
        self.Y_i = None

        self._nonce_d = None
        self._nonce_e = None
        self.D_i = None
        self.E_i = None

    def round1_sample_poly_and_commit(self, rng):
        self.a = [rand_scalar_nonzero(rng) for _ in range(self.t)]
        self.C_tilde = [point_mul_base(aij) for aij in self.a]

    def round1_generate_pok_of_a_i0(self, rng):
        if self.a is None or self.C_tilde is None:
            raise RuntimeError("Must run round1_sample_poly_and_commit() first.")

        a_i0 = self.a[0]
        phi_i0 = self.C_tilde[0]

        k = rand_scalar_nonzero(rng)
        R = point_mul_base(k)

        c = hash_to_scalar_nonzero_shake256(
            DST_KEYGEN_POK,
            HASH_OUTLEN,
            int_to_bytes_be(self.i, 4),
            self.ctx_phi.encode("utf-8"),
            point_to_bytes(phi_i0),
            point_to_bytes(R),
        )

        mu = scalar_add(k, scalar_mul(a_i0, c))
        self.sigma = SchnorrPoK(R=R, mu=mu)

    def round1_broadcast(self):
        if self.C_tilde is None or self.sigma is None:
            raise RuntimeError("Round 1 not complete.")
        return KeyGenBroadcast(dealer_id=self.i, C_tilde=self.C_tilde, sigma=self.sigma)

    def round1_verify_others_pok(self, broadcasts):
        for dealer_id, msg in broadcasts.items():
            if int(dealer_id) == self.i:
                continue

            R = msg.sigma.R
            mu = msg.sigma.mu
            phi_l0 = msg.C_tilde[0]

            c = hash_to_scalar_nonzero_shake256(
                DST_KEYGEN_POK,
                HASH_OUTLEN,
                int_to_bytes_be(int(dealer_id), 4),
                self.ctx_phi.encode("utf-8"),
                point_to_bytes(phi_l0),
                point_to_bytes(R),
            )

            g_mu = point_mul_base(mu)
            cphi = point_mul(phi_l0, c)
            right = point_sub(g_mu, cphi)

            if not point_eq(R, right):
                raise RuntimeError("PoK verification failed at P{} for dealer P{}".format(self.i, dealer_id))

    def round2_send_shares(self):
        if self.a is None:
            raise RuntimeError("Round 1 polynomial not generated.")
        shares = {}
        for l_id in range(1, self.n + 1):
            shares[l_id] = eval_poly(self.a, l_id)

        self._self_share_from_own_poly = shares[self.i]
        self.a = None
        return shares

    def round2_receive_verify_and_finalize(self, broadcasts, shares_from_all_dealers):
        if self._self_share_from_own_poly is None:
            raise RuntimeError("Must run round2_send_shares() first.")

        for dealer_id in range(1, self.n + 1):
            C_tilde_dealer = broadcasts[dealer_id].C_tilde
            share_value = shares_from_all_dealers[dealer_id]
            if not feldman_verify_share_point(C_tilde_dealer, self.i, share_value):
                raise RuntimeError("Share verification failed at P{} for dealer P{}".format(self.i, dealer_id))

        s_i = 0
        for dealer_id in range(1, self.n + 1):
            s_i = scalar_add(s_i, shares_from_all_dealers[dealer_id])

        self.s_i = s_i
        self.Y_i = point_mul_base(self.s_i)

    def preprocess_nonces_and_commitments(self, rng):
        self._nonce_d = rand_scalar_nonzero(rng)
        self._nonce_e = rand_scalar_nonzero(rng)
        self.D_i = point_mul_base(self._nonce_d)
        self.E_i = point_mul_base(self._nonce_e)
        return self.D_i, self.E_i

    def sign_share(self, rho_i, challenge_c, lambda_i):
        if self._nonce_d is None or self._nonce_e is None or self.s_i is None:
            raise RuntimeError("Missing nonces or secret share; run preprocess and KeyGen first.")

        z_i = self._nonce_d
        z_i = scalar_add(z_i, scalar_mul(rho_i, self._nonce_e))
        z_i = scalar_add(z_i, scalar_mul(lambda_i, scalar_mul(self.s_i, challenge_c)))

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

    broadcasts = {}
    for i, Pi in participants.items():
        Pi.round1_sample_poly_and_commit(rng)
        Pi.round1_generate_pok_of_a_i0(rng)
        broadcasts[i] = Pi.round1_broadcast()

    for i, Pi in participants.items():
        Pi.round1_verify_others_pok(broadcasts)

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

    Y = ED448_IDENTITY
    for j in range(1, n + 1):
        phi_j0 = broadcasts[j].C_tilde[0]
        Y = point_add(Y, phi_j0)

    return participants, Y


# =============================================================================
# Signing helpers
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
    out = b""
    for i in sorted(S):
        D_i, E_i = commitments[i]
        out += int_to_bytes_be(i, 4) + point_to_bytes(D_i) + point_to_bytes(E_i)
    return out


def compute_binding_factors(ctx_phi, message_bytes, S, commitments):
    transcript = encode_commitment_list(S, commitments)
    rho = {}
    for i in S:
        rho[i] = hash_to_scalar_nonzero_shake256(
            DST_SIGN_RHO,
            HASH_OUTLEN,
            int_to_bytes_be(i, 4),
            ctx_phi.encode("utf-8"),
            message_bytes,
            transcript,
        )
    return rho


def compute_group_commitment_R(S, commitments, rho):
    R = ED448_IDENTITY
    for i in S:
        D_i, E_i = commitments[i]
        R_i = point_add(D_i, point_mul(E_i, rho[i]))
        R = point_add(R, R_i)
    return R


def compute_challenge(ctx_phi, Y, R, message_bytes):
    return hash_to_scalar_nonzero_shake256(
        DST_SIGN_CHALLENGE,
        HASH_OUTLEN,
        ctx_phi.encode("utf-8"),
        point_to_bytes(Y),
        point_to_bytes(R),
        message_bytes,
    )


def aggregate_signature_shares(S, z_shares):
    z = 0
    for i in S:
        z = scalar_add(z, z_shares[i])
    return z


def verify_schnorr_signature(Y, ctx_phi, message_bytes, signature):
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


def mean_only(values):
    if not values:
        return 0.0
    return float(statistics.mean(values))


# =============================================================================
# Main (CLI + trials)
# =============================================================================

def parse_args():
    p = argparse.ArgumentParser(description="Educational FROST KeyGen + signing experiments (Ed448 + SHAKE256).")
    p.add_argument("--n", type=int, default=10, help="Number of participants (n). Default: 10.")
    p.add_argument("--t", type=int, default=5, help="Threshold (t). Default: 5.")
    p.add_argument("--alpha", type=int, default=None, help="Signer subset size (alpha), t <= alpha <= n. Default: alpha=t.")
    # CHANGED: default trials -> 10
    p.add_argument("--trials", type=int, default=10, help="Number of trials (default 10).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible randomness (NOT secure).")
    p.add_argument("--message", type=str, default="test", help="Message to sign (default 'test').")
    return p.parse_args()


def main():
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

    t_setup_end = time.perf_counter()
    setup_ms = ms(t_setup_end - t_setup_start)

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
    print("Curve: Ed448 (edwards448), Hash: SHAKE256, HASH_OUTLEN={} bytes".format(HASH_OUTLEN))
    print("Note: if --seed is set, RNG is deterministic for reproducibility (NOT secure).")
    print("")

    for trial in range(1, trials + 1):
        trial_seed = None if seed is None else (int(seed) + int(trial))
        rng = ExperimentRNG(seed=trial_seed)

        t_total_start = time.perf_counter()

        t_keygen_start = time.perf_counter()
        ctx_phi = "FROST demo context (Phi)"
        participants, Y = frost_keygen(n=n, t=t, ctx_phi=ctx_phi, rng=rng)
        t_keygen_end = time.perf_counter()
        keygen_ms = ms(t_keygen_end - t_keygen_start)

        S = choose_signer_subset(n=n, t=t, alpha=alpha, rng=rng)

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

        t_agg_2_start = time.perf_counter()
        z = aggregate_signature_shares(S, z_shares)
        signature = (R, z)
        t_agg_2_end = time.perf_counter()
        agg_ms_total += ms(t_agg_2_end - t_agg_2_start)

        t_verify_start = time.perf_counter()
        ok = verify_schnorr_signature(Y, ctx_phi, message_bytes, signature)
        t_verify_end = time.perf_counter()
        verify_ms = ms(t_verify_end - t_verify_start)

        t_total_end = time.perf_counter()
        total_ms = ms(t_total_end - t_total_start)

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
        print("Group public key Y (Ed448 encoding, hex): {}".format(point_to_bytes(Y).hex()))
        print("Signature R (hex): {}".format(point_to_bytes(signature[0]).hex()))
        print("Signature z (int mod ℓ): {}".format(signature[1]))
        print("")

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

    # CHANGED: average-only block explicitly for 10 trials
    if trials == 10:
        print("=== Averages over 10 trials ===")
        print("  setup_ms                      : {:10.3f}".format(mean_only(stats["setup_ms"])))
        print("  keygen_ms                     : {:10.3f}".format(mean_only(stats["keygen_ms"])))
        print("  preprocess_ms                 : {:10.3f}".format(mean_only(stats["preprocess_ms"])))
        print("  sign_ms                       : {:10.3f}".format(mean_only(stats["sign_ms"])))
        print("  aggregate_ms                  : {:10.3f}".format(mean_only(stats["aggregate_ms"])))
        print("  verify_ms                     : {:10.3f}".format(mean_only(stats["verify_ms"])))
        print("  total_ms                      : {:10.3f}".format(mean_only(stats["total_ms"])))
        print("  preprocess_per_participant_ms : {:10.3f}".format(mean_only(stats["preprocess_per_participant_ms"])))
        print("  sign_per_participant_ms       : {:10.3f}".format(mean_only(stats["sign_per_participant_ms"])))
        print("")

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
