// Compare eigenvalues and power sums of L_+, L_+^{off}, and L_-
import fs from 'fs';

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

function buildBlocks(G) {
  const n = G.length;
  // Gtilde_ij,kl = sqrt(G_ij G_kl) G_il G_kj
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
  const LplusOff = Array.from({ length: dSkew }, () => new Float64Array(dSkew));
  for (let a = 0; a < dSkew; a++) {
    const [i, j] = skewPairs[a];
    for (let b = a; b < dSkew; b++) {
      const [k, l] = skewPairs[b];
      const s = Math.sqrt(G[i][j] * G[k][l]);
      Lminus[a][b] = Lminus[b][a] = s * (G[i][k] * G[j][l] - G[i][l] * G[j][k]);
      LplusOff[a][b] = LplusOff[b][a] = s * (G[i][k] * G[j][l] + G[i][l] * G[j][k]);
    }
  }
  return { Lplus, LplusOff, Lminus };
}

for (let n = 2; n <= 5; n++) {
  let minDiff2 = Infinity, minDiff3 = Infinity, minDiff5 = Infinity;
  let minTail3 = Infinity, minTail5 = Infinity;
  for (let t = 0; t < 500; t++) {
    const G = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = i; j < n; j++) {
        G[i][j] = G[j][i] = Math.exp(6 * (Math.random() - 0.5));
      }
    }
    const { Lplus, LplusOff, Lminus } = buildBlocks(G);
    const ep = symEigenvalues(Lplus);
    const epo = symEigenvalues(LplusOff);
    const em = symEigenvalues(Lminus);

    const sumPow = (arr, m) => arr.reduce((acc, x) => acc + Math.pow(x, m), 0);
    // Note: eigenvalues of Gtilde are ep and -em
    // So Tr(Gtilde^m) = sumPow(ep, m) - sumPow(em, m) for odd m!
    const tail3 = sumPow(ep.slice(1), 3) - sumPow(em, 3);
    const tail5 = sumPow(ep.slice(1), 5) - sumPow(em, 5);
    if (tail3 < minTail3) minTail3 = tail3;
    if (tail5 < minTail5) minTail5 = tail5;

    // Compare Tr((LplusOff)^m) vs Tr((Lminus)^m)
    const d3 = sumPow(epo, 3) - sumPow(em, 3);
    const d5 = sumPow(epo, 5) - sumPow(em, 5);
    if (d3 < minDiff3) minDiff3 = d3;
    if (d5 < minDiff5) minDiff5 = d5;
  }
  console.log(`n=${n}: minTail3=${minTail3.toExponential(3)}, minTail5=${minTail5.toExponential(3)}, minDiff3(Off-Minus)=${minDiff3.toExponential(3)}, minDiff5(Off-Minus)=${minDiff5.toExponential(3)}`);
}
