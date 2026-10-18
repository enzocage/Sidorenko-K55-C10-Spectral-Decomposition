// Test Rossman's conjectures and PSD vs non-PSD behavior under adversarial search
function symEigenvalues(M) {
  const n = M.length;
  if (n === 0) return [];
  const A = M.map(row => Float64Array.from(row));
  const maxIter = 100 * n * n;
  for (let iter = 0; iter < maxIter; iter++) {
    let maxVal = 0, p = 0, q = 1;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const v = Math.abs(A[i][j]);
        if (v > maxVal) { maxVal = v; p = i; q = j; }
      }
    }
    if (maxVal < 1e-13) break;
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

// 1. Test PSD matrices G = X X^T with X >= 0
console.log("=== 1. Testing PSD nonnegative symmetric matrices G ===");
for (let n = 2; n <= 5; n++) {
  let majViol = 0, ptViol = 0;
  for (let trial = 0; trial < 500; trial++) {
    const X = Array.from({ length: n }, () => Array.from({ length: n }, () => Math.exp(4 * (Math.random() - 0.5))));
    const G = Array.from({ length: n }, (_, i) =>
      Array.from({ length: n }, (_, j) => {
        let s = 0;
        for (let k = 0; k < n; k++) s += X[i][k] * X[j][k];
        return s;
      })
    );
    const A = G.map(r => r.map(x => Math.pow(x, 1.5)));
    const { Lplus, Lminus } = buildBlocksMt(A, 1 / 3);
    const ep = symEigenvalues(Lplus);
    const em = symEigenvalues(Lminus);
    let sp = 0, sm = 0;
    for (let j = 0; j < em.length; j++) {
      if (ep[j + 1] + 1e-9 < em[j]) ptViol++;
      sp += ep[j + 1];
      sm += em[j];
      if (sp + 1e-9 < sm) majViol++;
    }
  }
  console.log(`PSD n=${n}: ptViol=${ptViol}, majViol=${majViol}`);
}

// 2. Adversarial evolutionary search on general nonnegative symmetric A for Rossman's (**) and Conjecture 4.2
console.log("\n=== 2. Adversarial Search on Rossman's (**) and Tail_m ===");
for (const n of [3, 4, 5]) {
  for (const tVal of [1 / 3, 0.5, 0.8]) {
    let bestA = Array.from({ length: n }, () => Array(n).fill(1));
    let minObj = Infinity;
    let minTail3 = Infinity;
    let minTail5 = Infinity;

    for (let restart = 0; restart < 30; restart++) {
      let A = Array.from({ length: n }, () => Array(n).fill(0));
      for (let i = 0; i < n; i++) {
        for (let j = i; j < n; j++) {
          A[i][j] = A[j][i] = Math.exp(6 * (Math.random() - 0.5));
        }
      }
      let curObj = Infinity;
      for (let step = 0; step < 200; step++) {
        const cand = A.map(r => r.slice());
        const i = Math.floor(Math.random() * n);
        const j = Math.floor(Math.random() * n);
        const factor = Math.exp(0.5 * (Math.random() - 0.5));
        cand[i][j] = cand[j][i] = Math.max(1e-7, Math.min(1e4, cand[i][j] * factor));

        // Normalize Frobenius norm = 1
        let norm2 = 0;
        for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) norm2 += cand[r][c] * cand[r][c];
        const sc = 1 / Math.sqrt(norm2);
        for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) cand[r][c] *= sc;

        const { Lplus, Lminus } = buildBlocksMt(cand, tVal);
        const ep = symEigenvalues(Lplus);
        const em = symEigenvalues(Lminus);
        const lam = [...ep, ...em.map(x => -x)].sort((a, b) => b - a);
        const N2 = n * n;

        // Compute minimum of (lam_2 + ... + lam_k) + (lam_{N2-k+2} + ... + lam_{N2})
        let worstMaj = Infinity;
        for (let k = 2; k <= (n * (n - 1)) / 2 + 1; k++) {
          let s = 0;
          for (let idx = 1; idx < k; idx++) s += lam[idx] + lam[N2 - idx];
          if (s < worstMaj) worstMaj = s;
        }
        let tail3 = 0, tail5 = 0;
        for (let idx = 1; idx < N2; idx++) {
          tail3 += Math.pow(lam[idx], 3);
          tail5 += Math.pow(lam[idx], 5);
        }
        if (tail3 < minTail3) minTail3 = tail3;
        if (tail5 < minTail5) minTail5 = tail5;

        if (worstMaj < curObj) {
          curObj = worstMaj;
          A = cand;
          if (curObj < minObj) {
            minObj = curObj;
            bestA = cand;
          }
        }
      }
    }
    console.log(`n=${n}, t=${tVal.toFixed(2)}: minMaj(**)=${minObj.toExponential(3)}, minTail3=${minTail3.toExponential(3)}, minTail5=${minTail5.toExponential(3)}`);
  }
}
