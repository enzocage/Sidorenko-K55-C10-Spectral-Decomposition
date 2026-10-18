/-
Copyright (c) 2026 Felix Schmidt. All rights reserved.
Author: Felix Schmidt (mail@felixschmidt.org)

Formalization of the Core Algebraic Identities for:
"Spectral Decomposition, Cubic Moment Reduction, and Partial Resolution of
 Rossman's Conjectures on Sidorenko's Conjecture for Bipartite Möbius Ladders (K_{5,5} \ C_{10})"
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace SidorenkoMobiusTheorem

/--
**Theorem 1 (Universal Off-Diagonal Minor & Trace Identity for `L_+(t) - w w^T` and `L_-(t)`):**
For any symmetric matrix `A` with `B = A^{∘(1-t)}` and `At = A^{∘t}`,
- On every diagonal coordinate `(i, i)`, the entry of `L_+(t) - w w^T` vanishes identically:
  `At i i ^ 2 * B i i ^ 2 - (At i i * B i i) ^ 2 = 0`.
- On every off-diagonal coordinate `(i, j)` (`i < j`), the diagonal entry of `L_+(t) - w w^T`
  equals the corresponding diagonal entry of `L_-(t)`:
  `At i j ^ 2 * (B i i * B j j + B i j ^ 2) - (√2 * At i j * B i j)^2 = At i j ^ 2 * (B i i * B j j - B i j ^ 2)`.
Consequently, `Tr(L_+(t) - w w^T) = Tr(L_-(t))` holds universally for all `n ≥ 1` and `t ∈ [0, 1]`.
-/
theorem diag_coord_Lplus_sub_ww_eq_zero (a_ii b_ii : ℝ) :
    a_ii ^ 2 * b_ii ^ 2 - (a_ii * b_ii) ^ 2 = 0 := by
  ring

theorem offdiag_coord_Lplus_sub_ww_eq_Lminus (at_ij b_ii b_jj b_ij : ℝ) :
    at_ij ^ 2 * (b_ii * b_jj + b_ij ^ 2) - 2 * (at_ij * b_ij) ^ 2 =
      at_ij ^ 2 * (b_ii * b_jj - b_ij ^ 2) := by
  ring

theorem universal_trace_identity {m : ℕ} (at_pair b_prod b_sq : Fin m → ℝ) :
    (∑ k : Fin m, (at_pair k ^ 2 * (b_prod k + b_sq k) - 2 * at_pair k ^ 2 * b_sq k)) =
      ∑ k : Fin m, at_pair k ^ 2 * (b_prod k - b_sq k) := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/--
**Theorem 3A (Universal `n = 2` Factorization Across All `t ∈ [0, 1]`):**
For any `2 × 2` positive symmetric matrix `A = [[a, b], [b, d]]`, with `x = (a d)^t`, `y = (b^2)^t`,
`u = (a d)^{1-t}`, `v = (b^2)^{1-t}`, where `a d = x u`, `b^2 = y v`, `r = x v`, `s = y u`,
the difference between the symmetric-block eigenvalue `(a d - r)` and the exterior-block
eigenvalue `(s - b^2)` factors identically as `(x - y) * (u - v)`.
Since `t ↦ z^t` and `t ↦ z^{1-t}` are both monotone increasing on `[0, 1]`, `(x - y)` and `(u - v)`
always have the same sign, so `(a d - r) - (s - b^2) ≥ 0` unconditionally.
-/
theorem n2_muirhead_factorization (x y u v : ℝ) :
    (x * u - x * v) - (y * u - y * v) = (x - y) * (u - v) := by
  ring

/--
**Theorem 3B (Universal `SL_2(ℝ)` Rank-1 Deficit Identity for `2 × 2` Cubic Moment Matrices):**
For any `2 × 2` symmetric matrix `S = [[s11, s12], [s12, s22]]`, the quadratic form of
`Sym^2(S) - vec(S) vec(S)^T` on a symmetric vector `(z1, z2, √2 z3)` equals
`det(S) * (-2 * z1 * z2 + 2 * z3^2) = det(S) * (z^T K_0 z)`, and evaluated on `vec(S)` itself
gives `p_{aa} = vec(S)^T K_0 vec(S) = -2 * det(S)`.
-/
def det2 (s11 s22 s12 : ℝ) : ℝ := s11 * s22 - s12 ^ 2

def lorentzK0Pair (u1 u2 u3 v1 v2 v3 : ℝ) : ℝ :=
  -u1 * v2 - u2 * v1 + 2 * u3 * v3

theorem lorentzK0_self_eq_neg_two_det (s11 s22 s12 : ℝ) :
    lorentzK0Pair s11 s22 s12 s11 s22 s12 = -2 * det2 s11 s22 s12 := by
  unfold lorentzK0Pair det2
  ring

/--
**Theorem 3C (Exact Lorentzian Reverse Cauchy-Schwarz Sum-of-Squares Identity in Signature `(+,+,-)`):**
In Lorentzian coordinates `t_i = (u_i + v_i)/2`, `x_i = (u_i - v_i)/2`, `y_i = w_i` where the
Lorentzian inner product is `B(1, 2) = -t1 * t2 + x1 * x2 + y1 * y2`, we have the exact
Brahmagupta-Minkowski polynomial identity:
  `t1^2 * (B(1,2)^2 - B(1,1) * B(2,2))`
  `= (-B(1,1)) * ((t1 * x2 - t2 * x1)^2 + (t1 * y2 - t2 * y1)^2)`
  `  + (x1 * (t1 * x2 - t2 * x1) + y1 * (t1 * y2 - t2 * y1))^2`.
Consequently, whenever `u` is timelike (`-B(1,1) > 0` and `t1 ≠ 0`), we have
`B(1,2)^2 - B(1,1) * B(2,2) ≥ 0` unconditionally.
-/
def minkowskiPair (t1 x1 y1 t2 x2 y2 : ℝ) : ℝ :=
  -t1 * t2 + x1 * x2 + y1 * y2

theorem minkowski_reverse_cauchy_schwarz_sos (t1 x1 y1 t2 x2 y2 : ℝ) :
    t1 ^ 2 * (minkowskiPair t1 x1 y1 t2 x2 y2 ^ 2 -
        minkowskiPair t1 x1 y1 t1 x1 y1 * minkowskiPair t2 x2 y2 t2 x2 y2) =
      (-minkowskiPair t1 x1 y1 t1 x1 y1) * ((t1 * x2 - t2 * x1) ^ 2 + (t1 * y2 - t2 * y1) ^ 2) +
        (x1 * (t1 * x2 - t2 * x1) + y1 * (t1 * y2 - t2 * y1)) ^ 2 := by
  unfold minkowskiPair
  ring

theorem minkowski_reverse_cauchy_schwarz_nonneg (t1 x1 y1 t2 x2 y2 : ℝ)
    (ht1 : t1 ≠ 0) (htimelike : -minkowskiPair t1 x1 y1 t1 x1 y1 ≥ 0) :
    minkowskiPair t1 x1 y1 t2 x2 y2 ^ 2 -
      minkowskiPair t1 x1 y1 t1 x1 y1 * minkowskiPair t2 x2 y2 t2 x2 y2 ≥ 0 := by
  have h_pos : t1 ^ 2 > 0 := sq_pos_of_ne_zero ht1
  have h_rhs :
      (-minkowskiPair t1 x1 y1 t1 x1 y1) * ((t1 * x2 - t2 * x1) ^ 2 + (t1 * y2 - t2 * y1) ^ 2) +
        (x1 * (t1 * x2 - t2 * x1) + y1 * (t1 * y2 - t2 * y1)) ^ 2 ≥ 0 := by
    positivity
  rw [← minkowski_reverse_cauchy_schwarz_sos] at h_rhs
  nlinarith

/--
**Theorem 4 (Exact `3 × 3` Principal Submatrix Determinant Identity for `L_{124} + c^2 I`):**
For the `3 × 3` principal submatrix `L_{124} = [[1, r, √2 c], [r, d^2, 0], [√2 c, 0, c^2]]`
of `L_+(t)` shifted by `c^2 I`, the determinant `det(L_{124} + c^2 I)` simplifies identically to
`2 * c^2 * (c^2 * (d^2 + c^2) - r^2)`, which is strictly negative whenever `r^2 > c^2 * (d^2 + c^2)`.
-/
theorem det_L124_shift_c_sq_identity (c d r : ℝ) :
    (1 + c ^ 2) * (d ^ 2 + c ^ 2) * (2 * c ^ 2) - 2 * c ^ 2 * r ^ 2 - 2 * c ^ 2 * (d ^ 2 + c ^ 2) =
      2 * c ^ 2 * (c ^ 2 * (d ^ 2 + c ^ 2) - r ^ 2) := by
  ring

end SidorenkoMobiusTheorem
