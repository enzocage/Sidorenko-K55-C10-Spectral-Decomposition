// Test rank-2 nonnegative symmetric matrices G of size n x n (both PSD and indefinite!)
function eigSym(M) {
  const n = M.length;
  if (n === 0) return [];
  const A = M.map(row => Float64Array.from(row));
  for (let iter = 0; iter < 250 * n * n; iter++) {
    let maxVal = 0, p = 0, q = 1;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const v = Math.abs(A[i][j]);
      if (v > maxVal) { maxVal = v; p = i; q = j; }
    }
    if (maxVal < 1e-14) break;
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

function buildBlocksG(G) {
  const n = G.length;
  const symPairs = [];
  for (let i = 0; i < n; i++) symPairs.push([i, i, 1.0]);
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) symPairs.push([i, j, Math.SQRT1_2]);
  const dSym = symPairs.length;
  const Lplus = Array.from({ length: dSym }, () => new Float64Array(dSym));
  const w = new Float64Array(dSym);
  for (let a = 0; a < dSym; a++) {
    const [i, j, wa] = symPairs[a];
    w[a] = (i === j ? 1.0 : Math.SQRT2) * Math.pow(G[i][j], 1.5);
    for (let b = a; b < dSym; b++) {
      const [k, l, wb] = symPairs[b];
      const pA = (i === j) ? [[i, i]] : [[i, j], [j, i]];
      const pB = (k === l) ? [[k, l]] : [[k, l], [l, k]];
      let val = 0;
      for (const [i1, j1] of pA) for (const [k1, l1] of pB) {
        val += Math.sqrt(G[i1][j1] * G[k1][l1]) * G[i1][k1] * G[j1][l1];
      }
      val *= wa * wb;
      Lplus[a][b] = Lplus[b][a] = val;
    }
  }

  const LplusMinusWW = Array.from({ length: dSym }, (_, a) =>
    Float64Array.from({ length: dSym }, (_, b) => Lplus[a][b] - w[a] * w[b])
  );

  const skewPairs = [];
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) skewPairs.push([i, j]);
  const dSkew = skewPairs.length;
  const Lminus = Array.from({ length: dSkew }, () => new Float64Array(dSkew));
  for (let a = 0; a < dSkew; a++) {
    const [i, j] = skewPairs[a];
    for (let b = a; b < dSkew; b++) {
      const [k, l] = skewPairs[b];
      const s = Math.sqrt(G[i][j] * G[k][l]);
      Lminus[a][b] = Lminus[b][a] = s * (G[i][k] * G[j][l] - G[i][l] * G[j][k]);
    }
  }
  return { Lplus, LplusMinusWW, Lminus };
}

for (const sign2 of [+1, -1]) {
  let minLam2PlusLamN2 = Infinity;
  for (let trial = 0; trial < 500; trial++) {
    const n = 4;
    const u = Array.from({ length: n }, () => Math.exp(3 * (Math.random() - 0.5)));
    const v = Array.from({ length: n }, () => (sign2 === 1 ? Math.exp(3 * (Math.random() - 0.5)) : (Math.random() - 0.5) * u[0]));
    const G = Array.from({ length: n }, (_, i) =>
      Array.from({ length: n }, (_, j) => u[i] * u[j] + sign2 * v[i] * v[j])
    );
    let ok = true;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (G[i][j] <= 1e-6) ok = false;
    if (!ok) continue;

    const { Lplus, Lminus } = buildBlocksG(G);
    const ep = eigSym(Lplus);
    const em = eigSym(Lminus);
    const lam = [...ep, ...em.map(x => -x)].sort((a, b) => b - a);
    const d = lam[1] + lam[lam.length - 1];
    if (d < minLam2PlusLamN2) minLam2PlusLamN2 = d;
  }
  console.log(`Rank-2 (n=4, sign2=${sign2}): min(lam_2 + lam_{n^2}) = ${minLam2PlusLamN2.toExponential(4)}`);
}
