// Adversarial optimization on PSD nonnegative matrices G = X X^T to see if ep[j+1] >= em[j] ALWAYS holds!
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
  for (let a = 0; a < dSym; a++) {
    const [i, j, wa] = symPairs[a];
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
  return { Lplus, Lminus };
}

for (const n of [3, 4]) {
  let minPt = Infinity, minMaj = Infinity;
  for (let restart = 0; restart < 50; restart++) {
    let X = Array.from({ length: n }, () => Array.from({ length: n }, () => Math.random() - 0.2));
    let curPt = Infinity;
    for (let step = 0; step < 300; step++) {
      const cand = X.map(r => r.slice());
      const i = Math.floor(Math.random() * n), j = Math.floor(Math.random() * n);
      cand[i][j] += 0.3 * (Math.random() - 0.5);
      const G = Array.from({ length: n }, (_, r) =>
        Array.from({ length: n }, (_, c) => {
          let s = 0;
          for (let k = 0; k < n; k++) s += cand[r][k] * cand[c][k];
          return s;
        })
      );
      let ok = true, sumG = 0;
      for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) {
        if (G[r][c] <= 1e-9) ok = false;
        sumG += G[r][c];
      }
      if (!ok) continue;
      for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) G[r][c] *= (n * n) / sumG;

      const { Lplus, Lminus } = buildBlocksG(G);
      const ep = eigSym(Lplus);
      const em = eigSym(Lminus);
      let wPt = Infinity, wMaj = Infinity, sp = 0, sm = 0;
      for (let k = 0; k < em.length; k++) {
        if (ep[k + 1] - em[k] < wPt) wPt = ep[k + 1] - em[k];
        sp += ep[k + 1]; sm += em[k];
        if (sp - sm < wMaj) wMaj = sp - sm;
      }
      if (wPt < curPt) {
        curPt = wPt; X = cand;
        if (wPt < minPt) minPt = wPt;
      }
      if (wMaj < minMaj) minMaj = wMaj;
    }
  }
  console.log(`PSD adversarial n=${n}: minPt=${minPt.toExponential(4)}, minMaj=${minMaj.toExponential(4)}`);
}
