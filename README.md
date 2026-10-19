# Canonical Symmetricâ€“Exterior Spectral Decomposition, Cubic Moment Reduction, and Partial Resolution of Rossman's Conjectures on Sidorenko's Conjecture for Bipartite MÃ¶bius Ladders ($K_{5,5} \setminus C_{10}$)

**Author:** Felix Schmidt (`mail@felixschmidt.org`)  
**Paper (PDF, 17 pages):** [`sidorenko_mobius_ladders.pdf`](./sidorenko_mobius_ladders.pdf)  
**LaTeX Source:** [`sidorenko_mobius_ladders.tex`](./sidorenko_mobius_ladders.tex)  
**Lean 4 Formalization:** [`SidorenkoMobiusTheorem.lean`](./SidorenkoMobiusTheorem.lean)  
**Master Verification Suite:** [`verify_sidorenko_mobius.mjs`](./verify_sidorenko_mobius.mjs)

---

## Overview

The $10$-vertex $3$-regular graph $K_{5,5} \setminus C_{10}$ (isomorphic to the $5$-rung bipartite MÃ¶bius ladder $ML_{10}$) has stood since Sidorenko (1991) as the smallest graph for which **Sidorenko's inequality** remains open.

Recently, **Benjamin Rossman (2025)** proved that for every $m$-rung bipartite ladder $BL_{2m}$,
$$\mathrm{hom}(BL_{2m}, G) \;=\; \mathrm{Tr}\big(\widetilde{G}^m\big), \qquad \widetilde{G}_{ij,kl} \;=\; G_{il}G_{kj}\sqrt{G_{ij}G_{kl}} \;=\; \big(D(G \otimes G)PD\big)_{ij,kl},$$
and embedded $\widetilde{G} = M(1/3)$ ($A = G^{\circ 3/2}$) into the continuous one-parameter family
$$M(t)_{ij,kl} \;=\; (A_{ij}A_{kl})^t (A_{il}A_{kj})^{1-t}, \qquad t \in [0, 1].$$
Rossman formulated three central conjectures:
- **Conjecture 3.2:** $\widetilde{G} = M(1/3)$ has a *pseudo-positive spectrum* (i.e., $f(p) = (\sum_k \mathrm{sign}(\widetilde{\lambda}_k)|\widetilde{\lambda}_k|^p)^{1/p}$ is nonnegative and nonincreasing over $p \in [1, \infty)$, which implies Sidorenko's inequality for $K_{5,5} \setminus C_{10}$ and all $ML_{2m}$).
- **Conjecture 4.2:** For every positive symmetric $n \times n$ matrix $A$ and **all** $t \in [0, 1]$, $M(t)$ has a pseudo-positive spectrum.
- **Majorization Conjecture $(**)$:** $(\widetilde{\lambda}_2 + \dots + \widetilde{\lambda}_k) + (\widetilde{\lambda}_{n^2-k+2} + \dots + \widetilde{\lambda}_{n^2}) \ge 0$ for all $k = 2, \dots, n^2$.

---

## Main Theorems

1. **Theorems 2.1 & 2.3 (Canonical $\mathrm{Sym}_n(\mathbb{R}) \oplus \mathrm{Skew}_n(\mathbb{R})$ Decomposition, Universal Exterior-Trace Identity, & Extended Star-Subspace Decomposition):**
   For every symmetric $n \times n$ matrix $A$ and every $t \in [0, 1]$, $M(t)$ commutes with the transpose involution $P$ and decomposes orthogonally on $\mathbb{R}^{n \times n} = \mathrm{Sym}_n(\mathbb{R}) \oplus^{\perp} \mathrm{Skew}_n(\mathbb{R})$ as
   $$M(t) \;=\; \mathcal{L}_+(t) \;\oplus\; \big(-\mathcal{L}_-(t)\big),$$
   with off-diagonal entrywise dominance $|(\mathcal{L}_-(t))_{\alpha,\beta}| \le (\mathcal{L}_+^{\mathrm{off}}(t))_{\alpha,\beta}$ and universal trace identity
   $$\mathrm{Tr}\big(\mathcal{L}_+(t) - w w^T\big) \;=\; \mathrm{Tr}\big(\mathcal{L}_-(t)\big) \;=\; \sum_{1 \le i < j \le n} A_{ij}^{2t}\big(B_{ii}B_{jj} - B_{ij}^2\big), \qquad B = A^{\circ(1-t)}.$$
   Moreover, $\langle V, (\mathrm{Sym}^2 B - \mathrm{vec}(B)\mathrm{vec}(B)^T)V \rangle = -2\mathrm{Tr}((\wedge^2 V)(\wedge^2 B))$ for all $V \in \mathrm{Sym}_n(\mathbb{R})$, and on the $n$-dimensional extended star subspace $\widehat{\mathcal{S}}_v^+ = \mathbb{R}E_{vv} \oplus \mathrm{span}\{E_{vi}^+ : i \ne v\}$ of any vertex $v \in \{1,\dots,n\}$,
   $$\big(\mathcal{L}_+(t) - w w^T\big)\Big|_{\widehat{\mathcal{S}}_v^+} \;=\; \begin{pmatrix} 0 & 0 \\ 0 & \mathcal{L}_-(t)\big|_{\mathcal{S}_v^-} \end{pmatrix}, \qquad \mathcal{L}_+(t)\big|_{\widehat{\mathcal{S}}_v^+} \;=\; \begin{pmatrix} 0 & 0 \\ 0 & \mathcal{L}_-(t)\big|_{\mathcal{S}_v^-} \end{pmatrix} + \widehat{w}_v \widehat{w}_v^T.$$

2. **Theorem 3.1 (Square-Root-Free Cubic Moment Tensor Reduction):**
   By cyclic similarity $\mathrm{Spec}(\widetilde{G}) = \mathrm{Spec}(D^2(G \otimes G)P)$, all fractional powers vanish from the characteristic polynomial of $\widetilde{G}$. For any symmetric matrix $G = \sum_{e=1}^r \varepsilon_e x^{(e)}(x^{(e)})^T$ of rank $r$ and arbitrary dimension $n \times n$, the nonzero spectrum of $\widetilde{G}$ equals that of the $r^2 \times r^2$ cubic moment operator
   $$\mathcal{M}_r \;=\; (J \otimes J)P_r \sum_{e=1}^r \varepsilon_e (S_e \otimes S_e) \;=\; \mathcal{M}_r^+ \;\oplus\; \big(-\mathcal{N}_r^-\big), \qquad (S_e)_{ab} \;=\; \sum_{i=1}^n x_i^{(e)} x_i^{(a)} x_i^{(b)}.$$

3. **Theorem 4.3 (Unconditional Resolution for All Rank-$\le 2$ Matrices and Graphons):**
   Using the universal $\mathrm{SL}_2(\mathbb{R})$ deficit identity $\mathrm{Sym}^2(S) - \mathrm{vec}(S)\mathrm{vec}(S)^T = \det(S)K_0$ and the **Lorentzian Reverse Cauchyâ€“Schwarz Inequality** in signature $(+,+,-)$, we prove that $\mathcal{L}_+ - w w^T$ has exact nonzero eigenvalues $\{+\alpha, \tau_1, -\alpha\}$ with $\alpha^2 - \tau_1^2 = \varepsilon(p_{12}^2 - p_{11}p_{22})$ and $p_{12}^2 - p_{11}p_{22} \ge 0$. By Weyl's Monotonicity Theorem, $\widetilde{\lambda}_2 + \widetilde{\lambda}_{n^2} \ge 0$ holds unconditionally for all positive semidefinite and indefinite rank-$\le 2$ matrices of arbitrary size $n \times n$, resolving Rossman's Conjecture 3.2, Conjecture $(**)$, and Sidorenko's inequality for $K_{5,5} \setminus C_{10}$ and all $ML_{2m}$ in rank $\le 2$ (as well as Conjecture 4.2 for $n = 2$ across all $t \in [0, 1]$).

4. **Theorem 5.2 (Pointwise Eigenvalue Dominance for All Rank-$\le 3$ Positive Semidefinite Host Matrices of Arbitrary Size $n \times n$):**
   Using the $\mathrm{SO}(3)$-equivariance of the Hodge star $\star : \wedge^2(\mathbb{R}^3) \xrightarrow{\sim} \mathbb{R}^3$, we prove that in the eigenbasis $\{u_1, u_2, u_3\}$ of $\mathcal{M}_3^- = \sum_{e=1}^m \wedge^2(S_e) = \mathrm{diag}(\tau_3, \tau_2, \tau_1)$ ($\tau_1 \ge \tau_2 \ge \tau_3$), the $4 \times 4$ compression of $\mathcal{M}_3^+ = \sum_{e=1}^m \mathrm{Sym}^2(S_e)$ to the traceless subspace $U_4 = \{V \in \mathrm{Sym}_3(\mathbb{R}) : \mathrm{Tr}(V) = 0, \, u_1^T V u_1 = 0\}$ satisfies the exact identity
   $$\mathcal{M}_3^+\big|_{U_4} \;=\; \mathrm{diag}(\tau_1, \, \tau_1, \, \tau_2, \, \tau_3) \;+\; \sum_{e=1}^m \mathbf{z}_e \mathbf{z}_e^T \;\succeq\; \mathrm{diag}(\tau_1, \, \tau_1, \, \tau_2, \, \tau_3).$$
   By Cauchy interlacing and Weyl monotonicity, this establishes **pointwise eigenvalue dominance** $\lambda_{k+1}^+(\widetilde{G}) \ge \lambda_k^-(\widetilde{G})$ ($k = 1, 2, 3$), Rossman's Majorization Conjecture $(**)$, Conjecture 3.2, and Sidorenko's inequality for $K_{5,5} \setminus C_{10}$ and all $ML_{2m}$ for **all** nonnegative symmetric positive semidefinite matrices $G \succeq 0$ of rank $\le 3$ and arbitrary dimension $n \times n$.

5. **Theorem 5.3 (Unconditional Eigenvalue Dominance for Zero-Diagonal $3 \times 3$ Indefinite Matrices Across All $t \in [0, 1]$):**
   For every zero-diagonal $3 \times 3$ nonnegative symmetric matrix $A$ (rank $3$, indefinite signature $(1,2)$) and every $t \in [0, 1]$, we prove $-\mathcal{L}_-(t) = 2\mathrm{diag}(x_1, x_2, x_3) - u u^T$ and $\lambda_2(M(t)) + \lambda_9(M(t)) \ge (x_1 - x_2) + x_3 \ge 0$, establishing Conjectures 3.2, 4.2, and $(**)$.

6. **Theorem 6.1 (Analytic Disproof of Rossman's General Conjecture 4.2 for $n \ge 3$ and $t \in (2/3, 1)$):**
   Using the exact determinant identity $\det(L_{124}(t) + c^2 I_3) = 2c^2(c^2(d^2 + c^2) - r^2)$, we give an explicit analytic proof that for every $t \in (2/3, 1)$ there exist strictly positive $3 \times 3$ symmetric matrices $A$ such that $|\lambda_9(M(t))| > \lambda_2(M(t))$ and $f_t(p)$ is strictly increasing for large $p$ (and already at $p = 5$ for $t = 0.8$), while explaining why the geometric progression $r^2 = s b^2$ at $t = 1/3$ protects $\widetilde{G}$.

---

## Reproducing the Verification Suite

Run the self-contained master verification script (523+ test cases across all 6 theorems) with Node.js:

```bash
node verify_sidorenko_mobius.mjs
```

