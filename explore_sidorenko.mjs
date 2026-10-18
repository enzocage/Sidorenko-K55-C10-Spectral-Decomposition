// Exploration of Sidorenko's Conjecture for K_{5,5} \ C_{10} (ML_{10})
// and Rossman's Spectral Conjectures (May 2025)

// Jacobi eigenvalue solver for real symmetric matrices
function symEigenvalues(M) {
  const n = M.length;
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

// Build Rossman's L_+ (on Sym_n) and L_- (on Skew_n) for M(t)
// Recall M(t) = L_+ \oplus (-L_-)
function buildSymSkewBlocks(A, t) {
  const n = A.length;
  const B = A.map(row => row.map(x => Math.pow(x, 1 - t)));
  const At = A.map(row => row.map(x => Math.pow(x, t)));

  // Basis of Sym_n: first (i,i) for 0<=i<n, then (i,j) for 0<=i<j<n
  const symPairs = [];
  for (let i = 0; i < n; i++) symPairs.push([i, i, 1.0]);
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) symPairs.push([i, j, Math.SQRT1_2]);
  }
  const dSym = symPairs.length;
  const Lplus = Array.from({ length: dSym }, () => new Float64Array(dSym));
  for (let a = 0; a < dSym; a++) {
    const [i, j, wa] = symPairs[a];
    for (let b = a; b < dSym; b++) {
      const [k, l, wb] = symPairs[b];
      // sum over permutations
      let val = 0;
      const pairsA = (i === j) ? [[i, i]] : [[i, j], [j, i]];
      const pairsB = (k === l) ? [[k, l]] : [[k, l], [l, k]];
      for (const [i1, j1] of pairsA) {
        for (const [k1, l1] of pairsB) {
          val += At[i1][j1] * At[k1][l1] * B[i1][k1] * B[j1][l1];
        }
      }
      val *= wa * wb;
      Lplus[a][b] = Lplus[b][a] = val;
    }
  }

  // Basis of Skew_n: (i,j) for 0<=i<j<n
  const skewPairs = [];
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) skewPairs.push([i, j]);
  }
  const dSkew = skewPairs.length;
  const Lminus = Array.from({ length: dSkew }, () => new Float64Array(dSkew));
  for (let a = 0; a < dSkew; a++) {
    const [i, j] = skewPairs[a];
    for (let b = a; b < dSkew; b++) {
      const [k, l] = skewPairs[b];
      const val = At[i][j] * At[k][l] * (B[i][k] * B[j][l] - B[i][l] * B[j][k]);
      Lminus[a][b] = Lminus[b][a] = val;
    }
  }

  return { Lplus, Lminus };
}

function spectrumMt(A, t) {
  const { Lplus, Lminus } = buildSymSkewBlocks(A, t);
  const eigPlus = symEigenvalues(Lplus);
  const eigMinus = symEigenvalues(Lminus);
  // Eigenvalues of M(t) are eigPlus U (-eigMinus)
  const all = [...eigPlus, ...eigMinus.map(x => -x)];
  all.sort((a, b) => b - a);
  return { all, eigPlus, eigMinus };
}

// Test Rossman's conjectures on random and extremal symmetric nonnegative matrices
function testSpectra() {
  let minSum5From2 = Infinity;
  let minMajorization = Infinity;
  let minSidorenkoRatio = Infinity;

  for (let n = 2; n <= 6; n++) {
    for (let trial = 0; trial < 200; trial++) {
      // Generate various types of nonnegative symmetric matrices G
      const G = Array.from({ length: n }, () => new Float64Array(n));
      const mode = trial % 4;
      for (let i = 0; i < n; i++) {
        for (let j = i; j < n; j++) {
          let v = 0;
          if (mode === 0) v = Math.random();
          else if (mode === 1) v = Math.exp(4 * (Math.random() - 0.5));
          else if (mode === 2) v = Math.random() < 0.4 ? 1e-6 : Math.random();
          else v = (i === j) ? 1e-5 : 1 + 0.5 * Math.sin(i + j + trial);
          G[i][j] = G[j][i] = Math.max(v, 1e-9);
        }
      }
      // Normalize sum G_ij = n^2
      let sumG = 0;
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) sumG += G[i][j];
      const scale = (n * n) / sumG;
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) G[i][j] *= scale;

      // Build A = G^{\circ 3/2}
      const A = G.map(row => row.map(x => Math.pow(x, 1.5)));
      const { all: lam, eigPlus, eigMinus } = spectrumMt(A, 1 / 3);

      // Check Tr(Gtilde^5) >= n^10
      let tr5 = 0, sum5From2 = 0;
      for (let k = 0; k < lam.length; k++) {
        const p5 = Math.pow(lam[k], 5);
        tr5 += p5;
        if (k >= 1) sum5From2 += p5;
      }
      const ratio = tr5 / Math.pow(n, 10);
      if (ratio < minSidorenkoRatio) minSidorenkoRatio = ratio;
      if (sum5From2 < minSum5From2) minSum5From2 = sum5From2;

      // Check Rossman's majorization (**) on page 9:
      // (lam_2 + ... + lam_k) + (lam_{n^2 - k + 2} + ... + lam_{n^2}) >= 0
      const N2 = n * n;
      for (let k = 2; k <= (n * (n - 1)) / 2; k++) {
        let s = 0;
        for (let idx = 1; idx < k; idx++) {
          s += lam[idx] + lam[N2 - idx];
        }
        if (s < minMajorization) {
          minMajorization = s;
          if (s < -1e-9) {
            console.log(`Counterexample to (**) at n=${n}, k=${k}: s=${s}`);
          }
        }
      }
    }
  }
  console.log({ minSidorenkoRatio, minSum5From2, minMajorization });
}

testSpectra();
