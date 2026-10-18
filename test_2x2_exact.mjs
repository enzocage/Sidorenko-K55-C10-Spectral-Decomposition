// Exact analysis of n = 2: A = [[a, b], [b, d]] for all t in [0, 1]
function eigSym3(M) {
  const n = 3;
  const A = M.map(row => Float64Array.from(row));
  for (let iter = 0; iter < 500; iter++) {
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

for (const t of [0.1, 0.2, 1 / 3, 0.5, 0.6, 0.8, 0.9]) {
  let minLam2PlusLam4 = Infinity;
  let minTail3 = Infinity;
  for (let trial = 0; trial < 2000; trial++) {
    const a = Math.exp(6 * (Math.random() - 0.5));
    const b = Math.exp(6 * (Math.random() - 0.5));
    const d = Math.exp(6 * (Math.random() - 0.5));
    const norm = Math.sqrt(a * a + 2 * b * b + d * d);
    const A0 = a / norm, B0 = b / norm, D0 = d / norm;
    const r = Math.pow(A0 * D0, t) * Math.pow(B0, 2 * (1 - t));
    const s = Math.pow(B0, 2 * t) * Math.pow(A0 * D0, 1 - t);
    const sq2 = Math.SQRT2;
    const Lplus = [
      [A0 * A0, r, sq2 * A0 * B0],
      [r, D0 * D0, sq2 * B0 * D0],
      [sq2 * A0 * B0, sq2 * B0 * D0, B0 * B0 + s]
    ];
    const ep = eigSym3(Lplus);
    const lSkew = B0 * B0 - s;
    const lam = [...ep, lSkew].sort((x, y) => y - x);
    const l24 = lam[1] + lam[3];
    const t3 = lam[1] ** 3 + lam[2] ** 3 + lam[3] ** 3;
    if (l24 < minLam2PlusLam4) minLam2PlusLam4 = l24;
    if (t3 < minTail3) minTail3 = t3;
  }
  console.log(`n=2, t=${t.toFixed(4)}: min(lam2+lam4)=${minLam2PlusLam4.toExponential(4)}, minTail3=${minTail3.toExponential(4)}`);
}
