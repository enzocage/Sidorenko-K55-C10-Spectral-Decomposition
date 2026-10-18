// Test whether EVERY t in (1/2, 1) has a 3x3 counterexample to Rossman's Conjecture 4.2!
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
  return { ep, em, lam, r, s };
}

// Look at the limit where a = 1, d = eps, b = eps^alpha, c = eps * k!
for (const t of [0.51, 0.55, 0.6, 0.7, 0.8, 0.9]) {
  // Choose a = 1, d = 0.01, b = d^1.5 = 0.001, and set c so that em[0] is slightly smaller than |ep[3]|!
  // Wait: what is |ep[3]| when a = 1 and d, b, c << 1?
  // In Lplus4, row 0 has a^2 = 1. Schur complement of a^2 = 1 on (1,1), (0,1), (0,2):
  // In position (1,1), the Schur complement entry is d^2 - r^2 !!
  // WAIT A SECOND!! READ THAT AGAIN!!
  // THE (1,1) ENTRY OF THE SCHUR COMPLEMENT OF a^2 = 1 IN Lplus4 IS:
  //   d^2 - r^2 / a^2 = d^2 - a^{2t-2} d^{2t} b^{4(1-t)} !!
  const a = 1.0;
  const d = 1e-3;
  const b = Math.pow(d, 1.2); // so b^2 = d^2.4, and r = d^{t + 2.4(1-t)} = d^{2.4 - 1.4 t}
  // Wait: we want r >> d, which means (a d)^t b^{2(1-t)} >> d  <=>  d^t b^{2(1-t)} >> d  <=>  b^2 >> d^{(1-t)/(1-t)} = d !!
  // YES!! Whenever d < b^2 << d^t ... wait: choose d << b << 1!
  // Let b = 0.05, d = 0.01, c = 0.08!
  const { ep, em, lam } = analyzeLimit3x3(1.0, 0.05, 0.08, 0.01, t);
  console.log(`t=${t.toFixed(2)}: lam2=${lam[1].toExponential(4)}, lam9=${lam[8].toExponential(4)}, lam2+lam9=${(lam[1] + lam[8]).toExponential(4)}`);
}
