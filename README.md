# Canonical Symmetric–Exterior Spectral Decomposition, Cubic Moment Reduction, and Partial Resolution of Rossman's Conjectures on Sidorenko's Conjecture for Bipartite Möbius Ladders ($K_{5,5} \setminus C_{10}$)

**Author:** Felix Schmidt (`mail@felixschmidt.org`)  
**Paper (PDF, 14 pages):** [`sidorenko_mobius_ladders.pdf`](./sidorenko_mobius_ladders.pdf)  
**LaTeX Source:** [`sidorenko_mobius_ladders.tex`](./sidorenko_mobius_ladders.tex)  
**Lean 4 Formalization:** [`SidorenkoMobiusTheorem.lean`](./SidorenkoMobiusTheorem.lean)  
**Master Verification Suite:** [`verify_sidorenko_mobius.mjs`](./verify_sidorenko_mobius.mjs)

---

## Overview

The $10$-vertex $3$-regular graph $K_{5,5} \setminus C_{10}$ (isomorphic to the $5$-rung bipartite Möbius ladder $ML_{10}$) has stood since Sidorenko (1991) as the smallest graph for which **Sidorenko's Conjecture** remains open.

Recently, **Benjamin Rossman (2025)** proved that for every $m$-rung bipartite ladder $BL_{2m}$,
$$\operatorname{hom}(BL_{2m}, G) \;=\; \operatorname{Tr}\big(\widetilde{G}^m\big), \qquad \widetilde{G}_{ij,kl} \;=\; G_{il}G_{kj}\sqrt{G_{ij}G_{kl}} \;=\; \big(D(G \otimes G)PD\big)_{ij,kl},$$
and embedded $\widetilde{G} = M(1/3)$ ($A = G^{\circ 3/2}$) into the continuous one-parameter family
$$M(t)_{ij,kl} \;=\; (A_{ij}A_{kl})^t (A_{il}A_{kj})^{1-t}, \qquad t \in [0, 1].$$
Rossman formulated three central conjectures:
- **Conjecture 3.2:** $\widetilde{G} = M(1/3)$ has a *pseudo-positive spectrum* (i.e., $f(p) = (\sum_k \operatorname{sign}(\widetilde{\lambda}_k)|\widetilde{\lambda}_k|^p)^{1/p}$ is nonnegative and nonincreasing over $p \in [1, \infty)$, which implies Sidorenko's Conjecture for $K_{5,5} \setminus C_{10}$ and all $ML_{2m}$).
- **Conjecture 4.2:** For every positive symmetric $n \times n$ matrix $A$ and **all** $t \in [0, 1]$, $M(t)$ has a pseudo-positive spectrum.
- **Majorization Conjecture $(**)$:** $(\widetilde{\lambda}_2 + \dots + \widetilde{\lambda}_k) + (\widetilde{\lambda}_{n^2-k+2} + \dots + \widetilde{\lambda}_{n^2}) \ge 0$ for all $k = 2, \dots, n^2$.

---

## Main Theorems

1. **Theorem 2.1 (Canonical $\operatorname{Sym}_n(\mathbb{R}) \oplus \operatorname{Skew}_n(\mathbb{R})$ Decomposition & Universal Trace Identity):**
   For every symmetric $n \times n$ matrix $A$ and every $t \in [0, 1]$, $M(t)$ commutes with the transpose involution $P$ and decomposes orthogonally on $\mathbb{R}^{n \times n} = \operatorname{Sym}_n(\mathbb{R}) \oplus^{\perp} \operatorname{Skew}_n(\mathbb{R})$ as
   $$M(t) \;=\; \mathcal{L}_+(t) \;\oplus\; \big(-\mathcal{L}_-(t)\big),$$
   with off-diagonal entrywise dominance $|(\mathcal{L}_-(t))_{\alpha,\beta}| \le (\mathcal{L}_+^{\mathrm{off}}(t))_{\alpha,\beta}$. Subtracting the rank-$1$ matrix $M(1) = w w^T = \operatorname{vec}(A)\operatorname{vec}(A)^T \succeq 0$ from $\mathcal{L}_+(t)$ expresses all entries of $\mathcal{L}_+(t) - w w^T$ via $2 \times 2$ minors of $B = A^{\circ(1-t)}$ and yields the universal trace identity
   $$\operatorname{Tr}\big(\mathcal{L}_+(t) - w w^T\big) \;=\; \operatorname{Tr}\big(\mathcal{L}_-(t)\big) \;=\; \sum_{1 \le i < j \le n} A_{ij}^{2t}\big(B_{ii}B_{jj} - B_{ij}^2\big).$$

2. **Theorem 3.1 (Square-Root-Free Cubic Moment Tensor Reduction):**
   By cyclic similarity $\operatorname{Spec}(\widetilde{G}) = \operatorname{Spec}(D^2(G \otimes G)P)$, all fractional powers vanish from the characteristic polynomial of $\widetilde{G}$. For any symmetric matrix $G = \sum_{e=1}^r \varepsilon_e x^{(e)}(x^{(e)})^T$ of rank $r$ and arbitrary dimension $n \times n$, the nonzero spectrum of $\widetilde{G}$ equals that of the $r^2 \times r^2$ cubic moment operator
   $$\mathcal{M}_r \;=\; (J \otimes J)P_r \sum_{e=1}^r \varepsilon_e (S_e \otimes S_e) \;=\; \mathcal{M}_r^+ \;\oplus\; \big(-\mathcal{N}_r^-\big), \qquad (S_e)_{ab} \;=\; \sum_{i=1}^n x_i^{(e)} x_i^{(a)} x_i^{(b)}.$$

3. **Theorem 4.3 (Unconditional Resolution for All Rank-$\le 2$ Matrices and Graphons):**
   Using the universal $\operatorname{SL}_2(\mathbb{R})$ deficit identity $\operatorname{Sym}^2(S) - \operatorname{vec}(S)\operatorname{vec}(S)^T = \det(S)K_0$ and the **Lorentzian Reverse Cauchy–Schwarz Inequality** in signature $(+,+,-)$, we prove that $\mathcal{L}_+ - w w^T$ has exact nonzero eigenvalues $\{+\alpha, \tau_1, -\alpha\}$ with $\alpha^2 - \tau_1^2 = \varepsilon(p_{12}^2 - p_{11}p_{22})$ and $p_{12}^2 - p_{11}p_{22} \ge 0$. By Weyl's Monotonicity Theorem, $\widetilde{\lambda}_2 + \widetilde{\lambda}_{n^2} \ge 0$ holds unconditionally for all positive semidefinite and indefinite rank-$\le 2$ matrices of arbitrary size $n \times n$, resolving Rossman's Conjecture 3.2, Conjecture $(**)$, and Sidorenko's Conjecture for $K_{5,5} \setminus C_{10}$ and all $ML_{2m}$ in rank $\le 2$ (as well as Conjecture 4.2 for $n = 2$ across all $t \in [0, 1]$).

4. **Theorem 5.1 (Disproof of Rossman's General Conjecture 4.2 for $n \ge 3$ and $t \in (2/3, 1)$):**
   Using the exact determinant identity $\det(L_{124}(t) + c^2 I_3) = 2c^2(c^2(d^2 + c^2) - r^2)$, we prove that for every $t \in (2/3, 1)$ there exist strictly positive $3 \times 3$ symmetric matrices $A$ such that $|\lambda_9(M(t))| > \lambda_2(M(t))$ and $f_t(p)$ is strictly increasing for large $p$ (and already at $p = 5$ for $t = 0.8$), disproving Conjecture 4.2 in general while explaining why the geometric progression $r^2 = s b^2$ at $t = 1/3$ protects $\widetilde{G}$.

---

## Reproducing the Verification Suite

Run the self-contained master verification script with Node.js:

```bash
node verify_sidorenko_mobius.mjs
```
