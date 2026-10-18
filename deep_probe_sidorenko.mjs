// Deep probe of Rossman's Conjecture 3.2, Conjecture 4.2, and (**)
// plus exact structure of L_+ and L_-

function symEigenvalues(M) {
  const n = M.length;
  if (n === 0) return [];
  const A = M.map(row => Float64Array.from(row));
  const maxIter = 120 * n * n;
  for (let iter = 0; iter < maxIter; iter++) {
    let maxVal = 0, p = 0, q = 1;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const v = Math.abs(A[i][j]);
        if (v > maxVal) { maxVal = v; p = i; q = j; }
      }
    }
    if (maxVal < 1e-14) break;
    const app = A[p][p], aqq = A[q][q], apq = A[p][q];
    const tau = (aqq - app) / (2 * apq);
    const t = tau >= 0 ? 1 / (tau + Math.sqrt(1 + tau * tau)) : -1 / (-tau + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t), s = t * c;
    A[p][p] = app - t * apq;
    A[q][q] = aqq + t * apq;
    A[p][q] = 0; A[q][p] = 0;
    for (let k = 0; k < n; k++) {
      if (k !== p && k !== q) {
        const akp = A[k][p], akq = A[k][q];
        A[k][p] = A[p][k] = c * akp - s * akq;
        A[k][q] = A[q][k] = s * akp + c * akq;
      }
    }
  }
  const eig = [];
  for (let i = 0; i < n; i++) eig.push(A[i][i]);
  eig.sort((a, b) => b - a);
  return eig;
}

function buildBlocksMt(A, t) {
  const n = A.length;
  const B = A.map(row => row.map(x => Math.pow(x, 1 - t)));
  const At = A.map(row => row.map(x => Math.pow(x, t)));

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
        val += At[i1][j1] * At[k1][l1] * B[i1][k1] * B[j1][l1];
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
      const s = At[i][j] * At[k][l];
      Lminus[a][b] = Lminus[b][a] = s * (B[i][k] * B[j][l] - B[i][l] * B[j][k]);
    }
  }
  return { Lplus, Lminus };
}

// Check what matrix A at n=3, t=0.80 gave minMaj(**) < 0!
for (const tVal of [0.8, 0.5, 1 / 3, 0.2]) {
  let bestA = null, minMaj = Infinity;
  const n = 3;
  for (let restart = 0; restart < 100; restart++) {
    let A = Array.from({ length: n }, () => Array(n).fill(0));
    for (let i = 0; i < n; i++) for (let j = i; j < n; j++) A[i][j] = A[j][i] = Math.exp(8 * (Math.random() - 0.5));
    let cur = Infinity;
    for (let step = 0; step < 300; step++) {
      const cand = A.map(r => r.slice());
      const i = Math.floor(Math.random() * n), j = Math.floor(Math.random() * n);
      cand[i][j] = cand[j][i] = Math.max(1e-8, Math.min(1e4, cand[i][j] * Math.exp(0.5 * (Math.random() - 0.5))));
      let s2 = 0;
      for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) s2 += cand[r][c] ** 2;
      for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) cand[r][c] /= Math.sqrt(s2);

      const { Lplus, Lminus } = buildBlocksMt(cand, tVal);
      const ep = symEigenvalues(Lplus);
      const em = symEigenvalues(Lminus);
      const lam = [...ep, ...em.map(x => -x)].sort((a, b) => b - a);
      const N2 = n * n;
      let w = Infinity;
      for (let k = 2; k <= (n * (n - 1)) / 2 + 1; k++) {
        let s = 0;
        for (let idx = 1; idx < k; idx++) s += lam[idx] + lam[N2 - idx];
        if (s < w) w = s;
      }
      if (w < cur) {
        cur = w; A = cand;
        if (cur < minMaj) { minMaj = cur; bestA = cand; }
      }
    }
  }
  console.log(`n=3, t=${tVal.toFixed(4)}: minMaj(**) = ${minMaj.toExponential(4)}`);
  if (minMaj < -1e-7) {
    console.log("  Matrix A:", bestA.map(r => r.map(x => Number(x.toFixed(5)))));
    const { Lplus, Lminus } = buildBlocksMt(bestA, tVal);
    const ep = symEigenvalues(Lplus);
    const em = symEigenvalues(Lminus);
    const lam = [...ep, ...em.map(x => -x)].sort((a, b) => b - a);
    console.log("  lam:", lam.map(x => Number(x.toFixed(6))));
    // Also check if Conjecture 4.2 (pseudo-positivity) is violated for this A!
    const f = (p) => {
      let s = 0;
      for (const x of lam) s += Math.sign(x) * Math.pow(Math.abs(x), p);
      return Math.pow(s, 1 / p);
    };
    console.log("  f(1), f(1.5), f(2), f(3), f(5), f(10):", [1, 1.5, 2, 3, 5, 10].map(p => Number(f(p).toFixed(6))));
  }
}
