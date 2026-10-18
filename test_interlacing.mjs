// Test elementwise comparison and majorization between eig(L_+) and eig(L_-)
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

for (let n = 2; n <= 5; n++) {
  let pointwiseViolations = 0;
  let majorizationViolations = 0;
  let absMajorizationViolations = 0;
  for (let t = 0; t < 1000; t++) {
    const G = Array.from({ length: n }, () => new Float64Array(n));
    for (let i = 0; i < n; i++) {
      for (let j = i; j < n; j++) {
        // Test extreme distributions, 0-1 matrices, bipartite-like matrices, etc.
        let v;
        if (t % 5 === 0) v = Math.random() < 0.5 ? 1e-4 : 1;
        else if (t % 5 === 1) v = Math.exp(8 * (Math.random() - 0.5));
        else if (t % 5 === 2) v = (i + j) % 2 === 0 ? 1e-3 : 1 + Math.random();
        else if (t % 5 === 3) v = i === j ? 10 * Math.random() : Math.random();
        else v = i === j ? 1e-5 : Math.random();
        G[i][j] = G[j][i] = v;
      }
    }
    const { Lplus, Lminus } = buildBlocks(G);
    const ep = symEigenvalues(Lplus); // length n(n+1)/2
    const em = symEigenvalues(Lminus); // length n(n-1)/2

    // Check if ep[j+1] >= em[j] for all j
    for (let j = 0; j < em.length; j++) {
      if (ep[j + 1] + 1e-9 < em[j]) pointwiseViolations++;
    }

    // Check majorization of ep[1..] vs em[0..]
    let sPlus = 0, sMinus = 0;
    for (let j = 0; j < em.length; j++) {
      sPlus += ep[j + 1];
      sMinus += em[j];
      if (sPlus + 1e-9 < sMinus) majorizationViolations++;
    }
  }
  console.log(`n=${n}: pointwiseViolations=${pointwiseViolations}, majorizationViolations=${majorizationViolations}`);
}
