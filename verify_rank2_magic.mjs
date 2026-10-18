// Check whether for ALL rank-2 matrices G, L_+ - w w^T has nonzero spectrum {+alpha, tau_1, -alpha}!!
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
  let tau1 = 0;
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    tau1 += G[i][j] * (G[i][i] * G[j][j] - G[i][j] ** 2);
  }
  return { Lplus, LplusMinusWW, tau1 };
}

for (const n of [3, 4, 5]) {
  for (const sign2 of [+1, -1]) {
    const u = Array.from({ length: n }, () => Math.random() + 0.5);
    const v = Array.from({ length: n }, () => (Math.random() - 0.5) * 0.4);
    const G = Array.from({ length: n }, (_, i) =>
      Array.from({ length: n }, (_, j) => u[i] * u[j] + sign2 * v[i] * v[j])
    );
    const { LplusMinusWW, tau1 } = buildBlocksG(G);
    const e0 = eigSym(LplusMinusWW).filter(x => Math.abs(x) > 1e-10);
    console.log(`n=${n}, sign2=${sign2}: tau1 = ${tau1.toFixed(6)}, eig(L_+ - w w^T) = [${e0.map(x => x.toFixed(6)).join(', ')}]`);
  }
}
