// Exact test of Rossman's (**) and tail_m on 3x3 matrices G with zero/small entries
function symEigenvalues(M) {
  const n = M.length;
  const A = M.map(row => Float64Array.from(row));
  for (let iter = 0; iter < 200 * n * n; iter++) {
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
  }
  return A.map((r, i) => r[i]).sort((a, b) => b - a);
}

function buildGtilde(G) {
  const n = G.length;
  const M = Array.from({ length: n * n }, () => new Float64Array(n * n));
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    for (let k = 0; k < n; k++) for (let l = 0; l < n; l++) {
      M[i + j * n][k + l * n] = G[i][l] * G[k][j] * Math.sqrt(G[i][j] * G[k][l]);
    }
  }
  return M;
}

// Test G = [[a, b, c], [b, d, 0], [c, 0, 0]]
for (const [a, b, c, d] of [
  [10, 1, 2, 1],
  [1, 1, 1, 1],
  [5, 1, 3, 2],
  [1, 2, 3, 0.1],
  [0.1, 1, 2, 3],
  [2, 5, 1, 0.01]
]) {
  const G = [
    [a, b, c],
    [b, d, 0],
    [c, 0, 0]
  ];
  const M = buildGtilde(G);
  const lam = symEigenvalues(M);
  console.log(`G=(${a},${b},${c},${d}): lam =`, lam.map(x => Number(x.toFixed(6))));
  console.log(`  lam_2 + lam_9 = ${(lam[1] + lam[8]).toExponential(4)}, sum_{k=2}^9 lam_k^3 = ${lam.slice(1).reduce((s, x) => s + x ** 3, 0).toExponential(4)}, sum_{k=2}^9 lam_k^5 = ${lam.slice(1).reduce((s, x) => s + x ** 5, 0).toExponential(4)}`);
}
