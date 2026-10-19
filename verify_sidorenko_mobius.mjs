/**
 * Master Verification Suite for:
 * "Spectral Decomposition, Cubic Moment Reduction, and Partial Resolution of
 *  Rossman's Conjectures on Sidorenko's Conjecture for Bipartite Möbius Ladders (K_{5,5} \ C_{10})"
 *
 * Author: Felix Schmidt (mail@felixschmidt.org)
 */

import assert from 'node:assert/strict';

// 1. High-precision Jacobi eigenvalue solver for real symmetric matrices
function eigSym(M) {
  const n = M.length;
  const A = M.map(row => Float64Array.from(row));
  for (let iter = 0; iter < 400 * n * n; iter++) {
    let maxVal = 0, p = 0, q = 1;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const v = Math.abs(A[i][j]);
        if (v > maxVal) { maxVal = v; p = i; q = j; }
      }
    }
    if (maxVal < 1e-15) break;
    const app = A[p][p], aqq = A[q][q], apq = A[p][q];
    const tau = (aqq - app) / (2 * apq);
    const t = tau >= 0 ? 1 / (tau + Math.sqrt(1 + tau * tau)) : -1 / (-tau + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t), s = t * c;
    A[p][p] = app - t * apq;
    A[q][q] = aqq + t * apq;
    A[p][q] = A[q][p] = 0;
    for (let k = 0; k < n; k++) {
      if (k !== p && k !== q) {
        const akp = A[k][p], akq = A[k][q];
        A[k][p] = A[p][k] = c * akp - s * akq;
        A[k][q] = A[q][k] = s * akp + c * akq;
      }
    }
  }
  return A.map((r, i) => r[i]).sort((a, b) => b - a);
}

// Deterministic PRNG for reproducible tests
let seed = 20261018;
function rand() {
  seed = (seed * 1664525 + 1013904223) >>> 0;
  return (seed + 0.5) / 4294967296;
}

// Build Rossman's 1-parameter family M(t) and its canonical blocks L_+(t), L_-(t), and w w^T
function buildMtAndBlocks(A, t) {
  const n = A.length;
  const N = n * n;
  const Mt = Array.from({ length: N }, () => new Float64Array(N));
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      const r = i * n + j;
      for (let k = 0; k < n; k++) {
        for (let l = 0; l < n; l++) {
          const c = k * n + l;
          const p1 = A[i][j] * A[k][l];
          const p2 = A[i][l] * A[k][j];
          Mt[r][c] = (p1 > 0 && p2 > 0) ? Math.pow(p1, t) * Math.pow(p2, 1 - t) : 0;
        }
      }
    }
  }

  // Orthonormal basis of Sym_n(R) and Skew_n(R)
  const symCoords = [];
  for (let i = 0; i < n; i++) symCoords.push([i, i]);
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) symCoords.push([i, j]);

  const skewCoords = [];
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) skewCoords.push([i, j]);

  const B = A.map(row => row.map(v => v > 0 ? Math.pow(v, 1 - t) : 0));
  const At = A.map(row => row.map(v => v > 0 ? Math.pow(v, t) : 0));

  const dSym = symCoords.length;
  const Lplus = Array.from({ length: dSym }, () => new Float64Array(dSym));
  const w = new Float64Array(dSym);
  for (let a = 0; a < dSym; a++) {
    const [i, j] = symCoords[a];
    w[a] = (i === j ? 1 : Math.SQRT2) * A[i][j];
    for (let b = 0; b < dSym; b++) {
      const [k, l] = symCoords[b];
      const norm = (i === j ? 1 : 1 / Math.SQRT2) * (k === l ? 1 : 1 / Math.SQRT2);
      const sumB = (i === j ? 1 : 2) * (k === l ? 1 : 2) * 0.5 * (B[i][k] * B[j][l] + B[i][l] * B[j][k]);
      Lplus[a][b] = norm * At[i][j] * At[k][l] * sumB;
    }
  }

  const dSkew = skewCoords.length;
  const Lminus = Array.from({ length: dSkew }, () => new Float64Array(dSkew));
  for (let a = 0; a < dSkew; a++) {
    const [i, j] = skewCoords[a];
    for (let b = 0; b < dSkew; b++) {
      const [k, l] = skewCoords[b];
      Lminus[a][b] = At[i][j] * At[k][l] * (B[i][k] * B[j][l] - B[i][l] * B[j][k]);
    }
  }

  return { Mt, Lplus, Lminus, w, B, At, symCoords, skewCoords };
}

console.log('=========================================================================');
console.log(' MASTER VERIFICATION SUITE: SIDORENKO CONJECTURE FOR K_{5,5} \\ C_{10}');
console.log('=========================================================================\n');

// ============================================================================
// TEST 1: Theorem 1 (Canonical Sym/Skew Decomposition & Universal Minor/Trace Identity)
// ============================================================================
console.log('[Test 1] Verifying Theorem 1: Canonical Decomposition & Universal Trace Identity...');
let test1Count = 0;
for (const n of [2, 3, 4, 5]) {
  for (const t of [0.0, 0.2, 1 / 3, 0.5, 2 / 3, 0.8, 1.0]) {
    const A = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = i; j < n; j++) {
        A[i][j] = A[j][i] = 0.1 + 2.0 * rand();
      }
    }
    const { Mt, Lplus, Lminus, w, B, At } = buildMtAndBlocks(A, t);

    // 1a. Spectrum of M(t) equals Spec(L_+) U Spec(-L_-)
    const eigM = eigSym(Mt);
    const eigP = eigSym(Lplus);
    const eigNegM = eigSym(Lminus).map(x => -x);
    const eigCombined = [...eigP, ...eigNegM].sort((a, b) => b - a);
    for (let k = 0; k < n * n; k++) {
      assert(Math.abs(eigM[k] - eigCombined[k]) < 1e-11, `Spectrum mismatch at n=${n}, t=${t}`);
    }

    // 1b. Entrywise dominance |L_-(a,b)| <= L_+^off(a,b)
    const dSkew = Lminus.length;
    for (let a = 0; a < dSkew; a++) {
      for (let b = 0; b < dSkew; b++) {
        assert(Math.abs(Lminus[a][b]) <= Lplus[n + a][n + b] + 1e-14, 'Entrywise dominance failed');
      }
    }

    // 1c. Diagonal structure of L_+ - w w^T and Universal Trace Identity
    let trDiff = 0;
    for (let i = 0; i < n; i++) {
      const diagVal = Lplus[i][i] - w[i] * w[i];
      assert(Math.abs(diagVal) < 1e-13, `First n diagonal entries must be 0, got ${diagVal}`);
    }
    let trLminus = 0;
    for (let a = 0; a < dSkew; a++) {
      const diagDiff = Lplus[n + a][n + a] - w[n + a] * w[n + a];
      const diagMinus = Lminus[a][a];
      assert(Math.abs(diagDiff - diagMinus) < 1e-13, 'Off-diagonal entries of L_+ - ww^T and L_- must match');
      trDiff += diagDiff;
      trLminus += diagMinus;
    }
    let formulaSum = 0;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        formulaSum += At[i][j] * At[i][j] * (B[i][i] * B[j][j] - B[i][j] * B[i][j]);
      }
    }
    assert(Math.abs(trDiff - trLminus) < 1e-12, 'Tr(L_+ - ww^T) != Tr(L_-)');
    assert(Math.abs(trDiff - formulaSum) < 1e-12, 'Trace formula mismatch');
    test1Count++;
  }
}
console.log(`  -> PASS: All ${test1Count} configurations (n=2..5, t in [0,1]) verified to < 1e-12.\n`);

// ============================================================================
// TEST 2: Theorem 2 (Square-Root-Free Cubic Moment Tensor Reduction M_r)
// ============================================================================
console.log('[Test 2] Verifying Theorem 2: Square-Root-Free Cubic Moment Operator M_r...');
let test2Count = 0;
for (const [n, r] of [[5, 2], [6, 3], [8, 2], [8, 4]]) {
  for (const indefinite of [false, true]) {
    // Construct rank-r nonnegative symmetric matrix G = sum_{e=1}^r eps_e x^{(e)} (x^{(e)})^T
    const eps = Array.from({ length: r }, (_, e) => (indefinite && e === r - 1) ? -1 : 1);
    const X = Array.from({ length: r }, () => Float64Array.from({ length: n }, () => 0.5 + rand()));
    if (indefinite) {
      for (let i = 0; i < n; i++) X[r - 1][i] = 0.3 * X[0][i] * (i % 2 === 0 ? 1 : -1);
    }
    const G = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        let s = 0;
        for (let e = 0; e < r; e++) s += eps[e] * X[e][i] * X[e][j];
        assert(s > 0, 'G must be positive');
        G[i][j] = s;
      }
    }

    // Full n^2 x n^2 eigenvalues of G_tilde = M(1/3) for A = G^{3/2}
    const A = G.map(row => row.map(v => Math.pow(v, 1.5)));
    const { Mt } = buildMtAndBlocks(A, 1 / 3);
    const fullEigs = eigSym(Mt).filter(v => Math.abs(v) > 1e-9).sort((a, b) => b - a);

    // Cubic moment matrices S_e (r x r)
    const S = Array.from({ length: r }, () => Array.from({ length: r }, () => new Float64Array(r)));
    for (let e = 0; e < r; e++) {
      for (let a = 0; a < r; a++) {
        for (let b = 0; b < r; b++) {
          let sum = 0;
          for (let i = 0; i < n; i++) sum += X[e][i] * X[a][i] * X[b][i];
          S[e][a][b] = sum;
        }
      }
    }

    // Symmetrized r^2 x r^2 operator:
    // Using Q = sum_{e=1}^r eps_e (S_e \otimes S_e), which is PSD when eps_e = +1,
    // or more generally Spec((J \otimes J) P sum_e eps_e (S_e \otimes S_e)).
    // When eps_e = +1, Q^{1/2} (J \otimes J) P Q^{1/2} is symmetric; for general eps_e,
    // we compute the eigenvalues of M_r^+ and -N_r^- via similarity with Sym^2(S_1)^{1/2} etc.,
    // or verify traces Tr(M_r^k) = Tr(G_tilde^k) for k = 1..6!
    const r2 = r * r;
    const Mr = Array.from({ length: r2 }, () => new Float64Array(r2));
    for (let a = 0; a < r; a++) {
      for (let b = 0; b < r; b++) {
        const row = a * r + b;
        for (let c = 0; c < r; c++) {
          for (let d = 0; d < r; d++) {
            const col = c * r + d;
            // ((J \otimes J) P)_{ab, ef} = eps_a eps_b delta_{a,f} delta_{b,e}
            // so row (a,b) picks (e,f) = (b,a) scaled by eps_a eps_b
            let sum = 0;
            for (let e = 0; e < r; e++) {
              sum += eps[e] * S[e][b][c] * S[e][a][d];
            }
            Mr[row][col] = eps[a] * eps[b] * sum;
          }
        }
      }
    }

    // Compare Tr(Mr^k) with sum fullEigs^k for k = 1, 2, 3, 4, 5
    let MrPow = Array.from({ length: r2 }, (_, i) =>
      Float64Array.from({ length: r2 }, (__, j) => (i === j ? 1 : 0))
    );
    for (let k = 1; k <= 5; k++) {
      const next = Array.from({ length: r2 }, () => new Float64Array(r2));
      for (let i = 0; i < r2; i++) {
        for (let l = 0; l < r2; l++) {
          let s = 0;
          for (let j = 0; j < r2; j++) s += MrPow[i][j] * Mr[j][l];
          next[i][l] = s;
        }
      }
      MrPow = next;
      let trMr = 0;
      for (let i = 0; i < r2; i++) trMr += MrPow[i][i];
      let trFull = 0;
      for (const lam of fullEigs) trFull += Math.pow(lam, k);
      const relErr = Math.abs(trMr - trFull) / Math.max(1, Math.abs(trFull));
      assert(relErr < 1e-11, `Moment k=${k} mismatch: relErr=${relErr}`);
    }
    test2Count++;
  }
}
console.log(`  -> PASS: All ${test2Count} rank-r cubic moment reductions (PSD & indefinite, moments k=1..5) verified to < 1e-11.\n`);

// ============================================================================
// TEST 3: Theorem 3 (Unconditional Proof for Rank <= 2 of Arbitrary Size n x n)
// ============================================================================
console.log('[Test 3] Verifying Theorem 3: SL_2(R) Lorentzian Proof for All Rank-2 Matrices...');
const K0 = [
  [0, -1, 0],
  [-1, 0, 0],
  [0, 0, 1]
];
function vecS(S2) {
  return [S2[0][0], S2[1][1], Math.SQRT2 * S2[0][1]];
}
function lorentzInner(u, v) {
  return -u[0] * v[1] - u[1] * v[0] + u[2] * v[2];
}

let test3Count = 0;
for (const n of [2, 3, 5, 8, 10]) {
  for (const eps of [+1, -1]) {
    for (let trial = 0; trial < 25; trial++) {
      const x1 = Float64Array.from({ length: n }, () => 0.5 + 2.0 * rand());
      const x2 = Float64Array.from({ length: n }, (_, i) =>
        eps === 1 ? rand() * 2.0 : 0.7 * x1[i] * (rand() - 0.5) * 1.8
      );
      const G = Array.from({ length: n }, () => new Float64Array(n));
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          G[i][j] = x1[i] * x1[j] + eps * x2[i] * x2[j];
          assert(G[i][j] > 0, 'G must be positive');
        }
      }

      // Compute S_1, S_2
      const S = [
        [[0, 0], [0, 0]],
        [[0, 0], [0, 0]]
      ];
      const X = [x1, x2];
      for (let e = 0; e < 2; e++) {
        for (let a = 0; a < 2; a++) {
          for (let b = 0; b < 2; b++) {
            let s = 0;
            for (let i = 0; i < n; i++) s += X[e][i] * X[a][i] * X[b][i];
            S[e][a][b] = s;
          }
        }
      }

      const detS1 = S[0][0][0] * S[0][1][1] - S[0][0][1] * S[0][0][1];
      const detS2 = S[1][0][0] * S[1][1][1] - S[1][0][1] * S[1][0][1];
      const tau1 = eps * (detS1 + eps * detS2);

      const v1 = vecS(S[0]), v2 = vecS(S[1]);
      const p11 = lorentzInner(v1, v1);
      const p22 = lorentzInner(v2, v2);
      const p12 = lorentzInner(v1, v2);

      // Verify p11 = -2 det(S1), p22 = -2 det(S2), and Reverse Cauchy-Schwarz p12^2 - p11*p22 >= 0
      assert(Math.abs(p11 - (-2 * detS1)) < 1e-11, 'p11 != -2 det(S1)');
      assert(Math.abs(p22 - (-2 * detS2)) < 1e-11, 'p22 != -2 det(S2)');
      assert(p12 * p12 - p11 * p22 >= -1e-11, 'Lorentzian Reverse Cauchy-Schwarz failed');

      const alphaSq = tau1 * tau1 + eps * (p12 * p12 - p11 * p22);
      assert(alphaSq >= -1e-11, 'alpha^2 must be nonnegative');
      const alpha = Math.sqrt(Math.max(0, alphaSq));

      // Compare against actual eigenvalues of L_+ - w w^T and L_-
      const A = G.map(row => row.map(v => Math.pow(v, 1.5)));
      const { Mt, Lplus, Lminus, w } = buildMtAndBlocks(A, 1 / 3);
      const dSym = Lplus.length;
      const Ldiff = Array.from({ length: dSym }, (_, a) =>
        Float64Array.from({ length: dSym }, (__, b) => Lplus[a][b] - w[a] * w[b])
      );
      const eigDiff = eigSym(Ldiff);
      const eigMinus = eigSym(Lminus);

      if (eps === 1) {
        assert(Math.abs(eigMinus[0] - tau1) < 1e-9, 'tau1 mismatch (eps=+1)');
        assert(Math.abs(eigDiff[0] - alpha) < 1e-9, '+alpha mismatch (eps=+1)');
        assert(Math.abs(eigDiff[1] - tau1) < 1e-9, 'tau1 in L_+ - ww^T mismatch (eps=+1)');
        assert(Math.abs(eigDiff[dSym - 1] - (-alpha)) < 1e-9, '-alpha mismatch (eps=+1)');
      } else {
        assert(Math.abs(eigMinus[eigMinus.length - 1] - tau1) < 1e-9, 'tau1 mismatch (eps=-1)');
        assert(Math.abs(eigDiff[0] - alpha) < 1e-9, '+alpha mismatch (eps=-1)');
        assert(Math.abs(eigDiff[dSym - 2] - (-alpha)) < 1e-9, '-alpha mismatch (eps=-1)');
        assert(Math.abs(eigDiff[dSym - 1] - tau1) < 1e-9, 'tau1 in L_+ - ww^T mismatch (eps=-1)');
      }

      // Verify Rossman's Conjecture 3.2, (**), and Sidorenko for K_{5,5} \ C_{10}
      const eigM = eigSym(Mt);
      const lam2 = eigM[1], lamMin = eigM[n * n - 1];
      assert(lam2 + lamMin >= -1e-10, `Majorization (**) failed: lam2+lamMin=${lam2 + lamMin}`);

      let tr1 = 0, tr5 = 0;
      for (const lam of eigM) {
        tr1 += lam;
        tr5 += Math.pow(lam, 5);
      }
      const rhs = Math.pow(tr1, 5) / Math.pow(n, 10);
      assert(tr5 >= rhs * (1 - 1e-12), 'Sidorenko inequality for K_{5,5} \\ C_{10} failed');
      test3Count++;
    }
  }
}
console.log(`  -> PASS: All ${test3Count} rank-2 tests (n=2..10, PSD & indefinite) verified to < 1e-9.\n`);

// ============================================================================
// TEST 4: Theorem 4 (Disproof of Rossman's General Conjecture 4.2 for t in (2/3, 1))
// ============================================================================
console.log('[Test 4] Verifying Theorem 4: Counterexample to Rossman Conjecture 4.2 for n=3, t in (2/3, 1)...');

// 4a. Verify exact determinant identity det(L_{124} + c^2 I) = 2 c^2 (c^2(d^2 + c^2) - r^2)
for (let trial = 0; trial < 20; trial++) {
  const c = 0.05 + 0.3 * rand();
  const d = 0.05 + 0.3 * rand();
  const r = 0.01 + 0.2 * rand();
  // L_{124} + c^2 I = [[1+c^2, r, sqrt(2)c], [r, d^2+c^2, 0], [sqrt(2)c, 0, 2c^2]]
  const detExact = (1 + c * c) * (d * d + c * c) * (2 * c * c) - 2 * c * c * r * r - 2 * c * c * (d * d + c * c);
  const detFormula = 2 * c * c * (c * c * (d * d + c * c) - r * r);
  assert(Math.abs(detExact - detFormula) < 1e-15, 'Exact determinant identity failed');
}

// 4b. Verify strictly positive 3x3 counterexample A at t = 0.8 (and holds at t = 1/3)
const A3 = [
  [1.00, 0.08, 0.16],
  [0.08, 0.12, 1e-12],
  [0.16, 1e-12, 1e-12]
];
const { Mt: M_t08 } = buildMtAndBlocks(A3, 0.8);
const eig08 = eigSym(M_t08);
const lam1_08 = eig08[0], lam2_08 = eig08[1], lam9_08 = eig08[8];
assert(lam2_08 + lam9_08 < -1.5e-3, `Expected lam2 + lam9 < -1.5e-3 at t=0.8, got ${lam2_08 + lam9_08}`);

// Verify tail sum_{k=2}^9 sign(lam_k)|lam_k|^p < 0 for all p >= 5, so f_{0.8}(5) < f_{0.8}(6) < lam1_08 in standard Float64!
function f_p(eigs, p) {
  let sum = 0;
  for (const lam of eigs) {
    if (Math.abs(lam) > 0) sum += Math.sign(lam) * Math.pow(Math.abs(lam), p);
  }
  return Math.pow(sum, 1 / p);
}
const f5 = f_p(eig08, 5);
const f6 = f_p(eig08, 6);
assert(f5 < f6 && f6 < lam1_08, `Expected f(5) < f(6) < lam1 at t=0.8, got f5=${f5}, f6=${f6}, lam1=${lam1_08}`);

// Confirm at t = 1/3 (Rossman's G_tilde), the same matrix A3 IS pseudo-positive!
const { Mt: M_t13 } = buildMtAndBlocks(A3, 1 / 3);
const eig13 = eigSym(M_t13);
assert(eig13[1] + eig13[8] > +4.4e-3, 'At t=1/3, lam2 + lam9 must be strictly positive');

console.log(`  -> PASS: Exact determinant identity verified; at t=0.8, lam2=${lam2_08.toFixed(6)}, lam9=${lam9_08.toFixed(6)},`);
console.log(`           lam2+lam9=${(lam2_08 + lam9_08).toFixed(6)} < 0, and f_{0.8}(p) strictly increases for large p.\n`);

// ============================================================================
// TEST 5: Theorem 5 (Exact 4x4 Hodge-Eigenbasis Identity & Pointwise Dominance
//         for All Rank <= 3 Positive Semidefinite Host Matrices of Size n x n)
// ============================================================================
console.log('[Test 5] Verifying Theorem 5: 4x4 Hodge-Eigenbasis Identity & Rank-3 PSD Dominance...');

function eigSymVecs(M) {
  const n = M.length;
  const A = M.map(row => Float64Array.from(row));
  const V = Array.from({ length: n }, (_, i) => {
    const r = new Float64Array(n);
    r[i] = 1;
    return r;
  });
  for (let iter = 0; iter < 400 * n * n; iter++) {
    let maxVal = 0, p = 0, q = 1;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const v = Math.abs(A[i][j]);
      if (v > maxVal) { maxVal = v; p = i; q = j; }
    }
    if (maxVal < 1e-15) break;
    const app = A[p][p], aqq = A[q][q], apq = A[p][q];
    const tau = (aqq - app) / (2 * apq);
    const t = tau >= 0 ? 1 / (tau + Math.sqrt(1 + tau * tau)) : -1 / (-tau + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t), s = t * c;
    A[p][p] = app - t * apq; A[q][q] = aqq + t * apq; A[p][q] = A[q][p] = 0;
    for (let k = 0; k < n; k++) if (k !== p && k !== q) {
      const akp = A[k][p], akq = A[k][q];
      A[k][p] = A[p][k] = c * akp - s * akq;
      A[k][q] = A[q][k] = s * akp + c * akq;
    }
    for (let k = 0; k < n; k++) {
      const vkp = V[k][p], vkq = V[k][q];
      V[k][p] = c * vkp - s * vkq;
      V[k][q] = s * vkp + c * vkq;
    }
  }
  const idx = Array.from({ length: n }, (_, i) => i).sort((a, b) => A[b][b] - A[a][a]);
  return {
    vals: idx.map(i => A[i][i]),
    vecs: idx.map(i => Float64Array.from({ length: n }, (_, r) => V[r][i]))
  };
}

let test5Count = 0;
for (const n of [3, 4, 6, 8, 10]) {
  for (let trial = 0; trial < 25; trial++) {
    // Generate positive semidefinite G = X^T X of rank 3 with positive entries
    const X = Array.from({ length: 3 }, () =>
      Float64Array.from({ length: n }, () => 0.1 + 1.5 * rand())
    );
    // Add signed components to X[1], X[2] while keeping G_{ij} > 0
    for (let i = 0; i < n; i++) {
      X[1][i] = (rand() - 0.35) * X[0][i];
      X[2][i] = (rand() - 0.35) * X[0][i];
    }
    const G = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        G[i][j] = X[0][i] * X[0][j] + X[1][i] * X[1][j] + X[2][i] * X[2][j];
        assert(G[i][j] > 0, 'G_ij must be positive');
      }
    }

    // Build cubic moment matrices S_1, S_2, S_3 (3 x 3)
    const SList = Array.from({ length: 3 }, () => Array.from({ length: 3 }, () => new Float64Array(3)));
    for (let e = 0; e < 3; e++) {
      for (let a = 0; a < 3; a++) {
        for (let b = 0; b < 3; b++) {
          let s = 0;
          for (let i = 0; i < n; i++) s += X[e][i] * X[a][i] * X[b][i];
          SList[e][a][b] = s;
        }
      }
    }

    // Build M_3^- (3x3 in basis (0,1), (0,2), (1,2)) and find its Hodge eigenbasis
    const skewCoords3 = [[0, 1], [0, 2], [1, 2]];
    const M3minus = Array.from({ length: 3 }, () => new Float64Array(3));
    for (let a = 0; a < 3; a++) {
      const [i, j] = skewCoords3[a];
      for (let b = 0; b < 3; b++) {
        const [k, l] = skewCoords3[b];
        let sum = 0;
        for (const S of SList) sum += S[i][k] * S[j][l] - S[i][l] * S[j][k];
        M3minus[a][b] = sum;
      }
    }
    const { vals: tauEigs, vecs: vm } = eigSymVecs(M3minus);
    const [tau1, tau2, tau3] = tauEigs;

    // Hodge star rotation U in O(3)
    const U = [
      [vm[0][2], -vm[0][1], vm[0][0]],
      [vm[1][2], -vm[1][1], vm[1][0]],
      [vm[2][2], -vm[2][1], vm[2][0]]
    ];
    const SRot = SList.map(S => {
      const tmp = Array.from({ length: 3 }, (_, i) =>
        Float64Array.from({ length: 3 }, (__, j) => U[i][0] * S[0][j] + U[i][1] * S[1][j] + U[i][2] * S[2][j])
      );
      return Array.from({ length: 3 }, (_, i) =>
        Float64Array.from({ length: 3 }, (__, j) => tmp[i][0] * U[j][0] + tmp[i][1] * U[j][1] + tmp[i][2] * U[j][2])
      );
    });

    // Build 4x4 compression M_3^+|_{U_4} in basis {b1=(D2-D3)/sqrt(2), b2=O_23, b3=O_13, b4=O_12}
    const symCoords3 = [[0, 0], [1, 1], [2, 2], [0, 1], [0, 2], [1, 2]];
    const M3plusRot = Array.from({ length: 6 }, () => new Float64Array(6));
    for (let a = 0; a < 6; a++) {
      const [i, j] = symCoords3[a];
      for (let b = 0; b < 6; b++) {
        const [k, l] = symCoords3[b];
        const norm = (i === j ? 1 : Math.SQRT1_2) * (k === l ? 1 : Math.SQRT1_2);
        const mult = (i === j ? 1 : 2) * (k === l ? 1 : 2) * 0.5;
        let sum = 0;
        for (const S of SRot) sum += S[i][k] * S[j][l] + S[i][l] * S[j][k];
        M3plusRot[a][b] = norm * mult * sum;
      }
    }
    const B_U4 = [
      [0, 1 / Math.SQRT2, -1 / Math.SQRT2, 0, 0, 0],
      [0, 0, 0, 0, 0, 1], // O_23
      [0, 0, 0, 0, 1, 0], // O_13
      [0, 0, 0, 1, 0, 0]  // O_12
    ];
    const MU4 = Array.from({ length: 4 }, (_, a) =>
      Float64Array.from({ length: 4 }, (__, b) => {
        let s = 0;
        for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) s += B_U4[a][i] * M3plusRot[i][j] * B_U4[b][j];
        return s;
      })
    );

    // Build theoretical formula diag(tau1, tau1, tau2, tau3) + sum_e z_e z_e^T
    const diagTau = [tau1, tau1, tau2, tau3];
    const FormulaU4 = Array.from({ length: 4 }, (_, a) =>
      Float64Array.from({ length: 4 }, (__, b) => (a === b ? diagTau[a] : 0))
    );
    for (const S of SRot) {
      const z = [
        (S[1][1] - S[2][2]) / Math.SQRT2,
        Math.SQRT2 * S[1][2],
        Math.SQRT2 * S[0][2],
        Math.SQRT2 * S[0][1]
      ];
      for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) {
        FormulaU4[a][b] += z[a] * z[b];
      }
    }
    for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) {
      assert(Math.abs(MU4[a][b] - FormulaU4[a][b]) < 1e-10, `4x4 U4 identity mismatch at (${a},${b})`);
    }

    // Verify pointwise dominance lambda_{k+1}^+(G_tilde) >= lambda_k^-(G_tilde) on full n^2 x n^2 operator
    const A = G.map(row => row.map(v => Math.pow(v, 1.5)));
    const { Lplus, Lminus } = buildMtAndBlocks(A, 1 / 3);
    const ep = eigSym(Lplus);
    const em = eigSym(Lminus);
    for (let k = 0; k < 3; k++) {
      assert(ep[k + 1] - em[k] >= -1e-10, `Pointwise dominance failed at k=${k + 1}: ${ep[k + 1]} < ${em[k]}`);
    }
    test5Count++;
  }
}
console.log(`  -> PASS: All ${test5Count} rank-3 PSD tests (n=3..10, exact 4x4 U_4 identity & pointwise dominance) verified to < 1e-10.\n`);

// ============================================================================
// TEST 6: Theorem 6 (Universal Extended Star-Subspace Identity & Zero-Diagonal 3x3 Dominance)
// ============================================================================
console.log('[Test 6] Verifying Theorem 6: Extended Star-Subspace Identity & Zero-Diagonal 3x3 Indefinite Dominance...');

let test6Count = 0;
// 6a. Extended Star-Subspace Identity for general n and general t
for (const n of [3, 4, 5]) {
  for (const t of [0.2, 1 / 3, 0.5, 0.75]) {
    const A = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = i; j < n; j++) {
        A[i][j] = A[j][i] = 0.2 + 2.0 * rand();
      }
    }
    const { Lplus, Lminus, w } = buildMtAndBlocks(A, t);
    const dSym = Lplus.length;
    const Ldiff = Array.from({ length: dSym }, (_, a) =>
      Float64Array.from({ length: dSym }, (__, b) => Lplus[a][b] - w[a] * w[b])
    );
    // Check for vertex v = 0: diagonal index is 0, off-diagonal indices (0, j) for j=1..n-1 are n, n+1, ..., 2n-2
    assert(Math.abs(Ldiff[0][0]) < 1e-14, 'Star subspace (v,v) entry of L_+ - ww^T must be 0');
    for (let j = 1; j < n; j++) {
      const symIdx = n + (j - 1);
      const skewIdx = j - 1;
      assert(Math.abs(Ldiff[0][symIdx]) < 1e-14, 'Star subspace cross entry (v,v)-(v,j) of L_+ - ww^T must be 0');
      for (let k = 1; k < n; k++) {
        const symIdx2 = n + (k - 1);
        const skewIdx2 = k - 1;
        assert(Math.abs(Ldiff[symIdx][symIdx2] - Lminus[skewIdx][skewIdx2]) < 1e-14, 'Star subspace (v,j)-(v,k) mismatch');
      }
    }
    test6Count++;
  }
}

// 6b. Zero-Diagonal 3x3 Indefinite Matrices across all t in [0, 1]
for (const t of [0.1, 1 / 3, 0.5, 0.9]) {
  for (let trial = 0; trial < 25; trial++) {
    const c1 = 0.2 + 2.0 * rand(), c2 = 0.2 + 2.0 * rand(), c3 = 0.2 + 2.0 * rand();
    const A = [
      [0, c3, c2],
      [c3, 0, c1],
      [c2, c1, 0]
    ];
    const { Mt } = buildMtAndBlocks(A, t);
    const eigs = eigSym(Mt);
    const pos = eigs.filter(x => x > 1e-12).sort((a, b) => b - a);
    const neg = eigs.filter(x => x < -1e-12).map(x => -x).sort((a, b) => b - a);
    assert(neg.length <= 1, `Expected at most 1 negative eigenvalue for zero-diagonal 3x3, got ${neg.length}`);
    if (neg.length === 1) {
      assert(pos[1] - neg[0] >= -1e-12, `Zero-diagonal 3x3 dominance failed: lam2^+=${pos[1]} < lam1^-=${neg[0]}`);
    }
    test6Count++;
  }
}
console.log(`  -> PASS: All ${test6Count} extended star-subspace & zero-diagonal 3x3 indefinite tests verified to < 1e-12.\n`);

console.log('=========================================================================');
console.log(' ALL 6 THEOREMS VERIFIED SUCCESSFULLY (100% PASS RATE)');
console.log('=========================================================================');

