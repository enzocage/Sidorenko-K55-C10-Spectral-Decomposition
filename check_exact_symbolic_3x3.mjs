// Analyze exact 4x4 + 2x2 block eigenvalues for 3x3 matrix A = [[a, b, c], [b, d, 0], [c, 0, 0]]
// as a function of t in (0, 1)

function analyzeLimit3x3(a, b, c, d, t) {
  // On Sym_3, active 4x4 block on basis (0,0), (1,1), (0,1), (0,2):
  // Let s = b^{2t} (a d)^{1-t} = (a d)^{1-t} b^{2t}
  // Note: (a d)^t B_{01}^2 = (a d)^t b^{2(1-t)} =: r
  const r = Math.pow(a * d, t) * Math.pow(b, 2 * (1 - t));
  const s = Math.pow(b, 2 * t) * Math.pow(a * d, 1 - t);
  const sq2 = Math.SQRT2;

  const Lplus4 = [
    [a * a, r, sq2 * a * b, sq2 * a * c],
    [r, d * d, sq2 * b * d, 0],
    [sq2 * a * b, sq2 * b * d, s + b * b, b * c],
    [sq2 * a * c, 0, b * c, c * c]
  ];

  // On Skew_3, active 2x2 block on basis (0,1), (0,2):
  // -Lminus2 has entries:
  const negLminus2 = [
    [b * b - s, b * c],
    [b * c, c * c]
  ];

  return { Lplus4, negLminus2, r, s };
}

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

for (const t of [1 / 3, 0.5, 0.6, 0.8]) {
  // Let's test various (a, b, c, d)
  let minLam2PlusLam9 = Infinity;
  let minTail3 = Infinity;
  for (const [a, b, c, d] of [
    [1, 0.1, 0.2, 0.1],
    [1, 0.01, 0.1, 0.5],
    [1, 0.1, 0.01, 0.5],
    [1, 0.2, 0.5, 0.05],
    [1, 0.05, 0.5, 0.2]
  ]) {
    const { Lplus4, negLminus2 } = analyzeLimit3x3(a, b, c, d, t);
    const ep = eigSym(Lplus4);
    const em = eigSym(negLminus2);
    const lam = [...ep, ...em, 0, 0, 0].sort((x, y) => y - x);
    const l29 = lam[1] + lam[8];
    const tail3 = lam.slice(1).reduce((acc, x) => acc + x ** 3, 0);
    if (l29 < minLam2PlusLam9) minLam2PlusLam9 = l29;
    if (tail3 < minTail3) minTail3 = tail3;
  }
  console.log(`t=${t.toFixed(4)}: min(lam2+lam9)=${minLam2PlusLam9.toExponential(4)}, minTail3=${minTail3.toExponential(4)}`);
}
