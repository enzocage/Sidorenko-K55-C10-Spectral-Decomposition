// Test:
// 1. Exact symbolic/numerical behavior of 3x3 for t in (0, 1)
// 2. Can Conjecture 4.2 ever be violated?
// 3. Can we prove Conjecture 3.2 and (**) for n=2, n=3, PSD G, rank-2 G, and general G?

function eigSym(M) {
  const n = M.length;
  const A = M.map(row => Float64Array.from(row));
  for (let iter = 0; iter < 300 * n * n; iter++) {
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

function analyzeLimit3x3(a, b, c, d, t) {
  const r = Math.pow(a * d, t) * Math.pow(b, 2 * (1 - t));
  const s = Math.pow(b, 2 * t) * Math.pow(a * d, 1 - t);
  const sq2 = Math.SQRT2;
  const Lplus4 = [
    [a * a, r, sq2 * a * b, sq2 * a * c],
    [r, d * d, sq2 * b * d, 0],
    [sq2 * a * b, sq2 * b * d, s + b * b, b * c],
    [sq2 * a * c, 0, b * c, c * c]
  ];
  const negLminus2 = [
    [b * b - s, b * c],
    [b * c, c * c]
  ];
  const ep = eigSym(Lplus4);
  const em = eigSym(negLminus2);
  const lam = [...ep, ...em, 0, 0, 0].sort((x, y) => y - x);
  return { ep, em, lam };
}

// Check the exact matrix from deep_probe_sidorenko:
// a = 0.95746, b = 0.08472, c = 0.16486, d = 0.12064
for (const t of [1 / 3, 0.4, 0.45, 0.5, 0.6, 0.8, 0.95]) {
  const { ep, em, lam } = analyzeLimit3x3(0.95746, 0.08472, 0.16486, 0.12064, t);
  const l29 = lam[1] + lam[8];
  const tail3 = lam.slice(1).reduce((s, x) => s + x ** 3, 0);
  const tail5 = lam.slice(1).reduce((s, x) => s + x ** 5, 0);
  // Check derivative of f(p) for large p:
  // Note: for large p, f(p) = (lam_1^p + sum_{k>=2} sign(lam_k) |lam_k|^p)^{1/p}
  // Wait! Look at the asymptotic expansion of f(p) as p -> infinity!!
  // Let lam_2* = max_{k>=2} |lam_k|!
  // If |lam_{n^2}| > lam_2, then for large p, the dominant secondary term in sum_{k=1}^{n^2} sign(lam_k) |lam_k|^p
  // is NEGATIVE: - |lam_{n^2}|^p !!
  // WAIT A SECOND! If sum_{k>=2} sign(lam_k) |lam_k|^p < 0 for large p, then
  // f(p) = (lam_1^p - |lam_{n^2}|^p (1 + o(1)))^{1/p} < lam_1 = f(\infty)!!
  // Which means f(p) MUST INCREASE to lam_1 as p -> infinity, VIOLATING Conjecture 4.2!!
  const signedSumP = (p) => lam.slice(1).reduce((s, x) => s + Math.sign(x) * Math.pow(Math.abs(x), p), 0);
  console.log(`t=${t.toFixed(4)}: lam2=${lam[1].toFixed(6)}, lam9=${lam[8].toFixed(6)}, lam2+lam9=${l29.toExponential(3)}, signedSum(p=20)=${signedSumP(20).toExponential(3)}`);
}
