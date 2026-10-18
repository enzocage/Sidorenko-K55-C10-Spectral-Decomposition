// Exact symbolic/asymptotic analysis of 3x3 matrix A = [[a, b, c], [b, d, 0], [c, 0, 0]]
// and search across t in [0, 1]

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

// Look at the eigenvalues of Lplus4 and negLminus2!
// Wait: in negLminus2 = [[b^2 - s, b c], [b c, c^2]],
// its trace is b^2 + c^2 - s, and its determinant is (b^2 - s)c^2 - b^2 c^2 = -s c^2 < 0!
// So the two eigenvalues of negLminus2 are:
// xi_+ = ((b^2 + c^2 - s) + sqrt((b^2 + c^2 - s)^2 + 4 s c^2)) / 2 > 0
// xi_- = ((b^2 + c^2 - s) - sqrt((b^2 + c^2 - s)^2 + 4 s c^2)) / 2 < 0
// Therefore, |xi_-| = ( (s - b^2 - c^2) + sqrt((s - b^2 - c^2)^2 + 4 s c^2) ) / 2 !!
// Wait: what if we compare |xi_-| with the eigenvalues of Lplus4?!
// Let's print the 4 eigenvalues of Lplus4 and the 2 eigenvalues of negLminus2!
for (const t of [1 / 3, 0.5, 0.55, 0.6, 0.7, 0.8]) {
  const { ep, em, r, s } = analyzeLimit3x3(1.0, 0.08, 0.16, 0.12, t);
  console.log(`t=${t.toFixed(4)} (r=${r.toFixed(5)}, s=${s.toFixed(5)}):`);
  console.log(`  ep (L_+):     [${ep.map(x => x.toFixed(6)).join(', ')}]`);
  console.log(`  em (-L_-):    [${em.map(x => x.toFixed(6)).join(', ')}]`);
  console.log(`  ep[1] + em[1] = ${(ep[1] + em[1]).toExponential(4)}`);
}
