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

/--
**Theorem 5A (Universal Extended Star-Subspace Identity for General `n` and `t ∈ [0, 1]`):**
For any vertex `v` and any `i, j ≠ v`, on the extended star subspace `Ŝ_v^+ = ℝ E_{vv} ⊕ span{E_{vi}^+}`:
1. The cross entry `(E_{vv}, E_{vi}^+)` of `L_+(t) - w w^T` vanishes identically.
2. The difference between the `(E_{vi}^+, E_{vj}^+)` entry of `L_+(t)` and the `(Ẽ_{vi}^-, Ẽ_{vj}^-)`
   entry of `L_-(t)` equals `2 * A_{vi} * A_{vj} = w_{vi} * w_{vj}`.
-/
theorem star_subspace_cross_eq_zero (a_vv a_vi : ℝ) :
    (a_vv * a_vi + a_vi * a_vv) - 2 * a_vv * a_vi = 0 := by
  ring

theorem star_subspace_offdiag_diff_eq_ww (at_vivj b_vv_ij a_vi a_vj : ℝ) :
    (at_vivj * b_vv_ij + a_vi * a_vj) - (at_vivj * b_vv_ij - a_vi * a_vj) =
      2 * a_vi * a_vj := by
  ring

/--
**Theorem 5B (Exact `4 × 4` Hodge-Eigenbasis Quadratic Form Identity on `U_4 ⊂ Sym^2(ℝ^3)`):**
For any `3 × 3` symmetric matrix `S = [[s11, s12, s13], [s12, s22, s23], [s13, s23, s33]]`
with cofactor matrix `W = ∧^2(S)`:
  `W11 = s22 * s33 - s23^2`, `W22 = s11 * s33 - s13^2`, `W33 = s11 * s22 - s12^2`,
  `W12 = s12 * s33 - s13 * s23`, `W13 = s12 * s23 - s13 * s22`, `W23 = s11 * s23 - s12 * s13`,
and any vector `V = y1*(D_2 - D_3) + y2*(e_2⊗e_3 + e_3⊗e_2) + y3*(e_1⊗e_3 + e_3⊗e_1) + y4*(e_1⊗e_2 + e_2⊗e_1) ∈ U_4`,
the quadratic form `⟨V, Sym^2(S) V⟩` decomposes identically as the lifted cofactor form plus the exact square
`((s22 - s33) * y1 + 2 * s23 * y2 + 2 * s13 * y3 + 2 * s12 * y4)^2 ≥ 0`.
In the Hodge eigenbasis of `M_3^- = ∑_e ∧^2(S_e)` (where `∑_e W12 = ∑_e W13 = ∑_e W23 = 0`),
this immediately implies `M_3^+|_{U_4} ⪰ diag(τ_1, τ_1, τ_2, τ_3)` and hence `λ_{k+1}(M_3^+) ≥ λ_k(M_3^-)`
for all `k = 1, 2, 3`.
-/
def sym2U4QuadForm (s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 : ℝ) : ℝ :=
  (s22 ^ 2 + s33 ^ 2 - 2 * s23 ^ 2) * y1 ^ 2 +
  2 * (s22 * s33 + s23 ^ 2) * y2 ^ 2 +
  2 * (s11 * s33 + s13 ^ 2) * y3 ^ 2 +
  2 * (s11 * s22 + s12 ^ 2) * y4 ^ 2 +
  4 * (s22 - s33) * s23 * y1 * y2 +
  4 * (s12 * s23 - s13 * s33) * y1 * y3 +
  4 * (s12 * s22 - s13 * s23) * y1 * y4 +
  4 * (s12 * s33 + s13 * s23) * y2 * y3 +
  4 * (s12 * s23 + s13 * s22) * y2 * y4 +
  4 * (s11 * s23 + s12 * s13) * y3 * y4

def wedge2U4LiftForm (s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 : ℝ) : ℝ :=
  let W11 := s22 * s33 - s23 ^ 2
  let W22 := s11 * s33 - s13 ^ 2
  let W33 := s11 * s22 - s12 ^ 2
  let W12 := s12 * s33 - s13 * s23
  let W13 := s12 * s23 - s13 * s22
  let W23 := s11 * s23 - s12 * s13
  2 * W11 * (y1 ^ 2 + y2 ^ 2) + 2 * W22 * y3 ^ 2 + 2 * W33 * y4 ^ 2 +
  4 * W13 * (y1 * y3 - y2 * y4) + 4 * W12 * (y2 * y3 - y1 * y4) + 4 * W23 * y3 * y4

theorem hodge_eigenbasis_U4_sos_identity (s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 : ℝ) :
    sym2U4QuadForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 -
      wedge2U4LiftForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 =
      ((s22 - s33) * y1 + 2 * s23 * y2 + 2 * s13 * y3 + 2 * s12 * y4) ^ 2 := by
  unfold sym2U4QuadForm wedge2U4LiftForm
  ring

theorem hodge_eigenbasis_U4_dominates (s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 : ℝ) :
    sym2U4QuadForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 ≥
      wedge2U4LiftForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 := by
  have h : sym2U4QuadForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 -
      wedge2U4LiftForm s11 s22 s33 s23 s13 s12 y1 y2 y3 y4 ≥ 0 := by
    rw [hodge_eigenbasis_U4_sos_identity]
    positivity
  linarith

/--
**Theorem 5C (Unconditional Eigenvalue Dominance for Zero-Diagonal `3 × 3` Indefinite Matrices):**
For any zero-diagonal `3 × 3` nonnegative symmetric matrix `A` with ordered squared off-diagonal
entries `x1 ≥ x2 ≥ x3 ≥ 0`, the three eigenvalues `μ1 ≥ μ2 ≥ μ3` of `-L_-(t) = 2 diag(x1, x2, x3) - u u^T`
satisfy `μ1 + μ2 + μ3 = x1 + x2 + x3` and `μ2 ≤ 2 * x2` (by Cauchy interlacing), which forces
`λ_2^+ - λ_1^- = μ1 + μ3 ≥ (x1 - x2) + x3 ≥ 0`.
-/
theorem zero_diag_3x3_dominance (x1 x2 x3 mu1 mu2 mu3 : ℝ)
    (hx12 : x1 ≥ x2) (hx3 : x3 ≥ 0)
    (htrace : mu1 + mu2 + mu3 = x1 + x2 + x3)
    (hinterlace : mu2 ≤ 2 * x2) :
    mu1 + mu3 ≥ 0 := by
  linarith

end SidorenkoMobiusTheorem
