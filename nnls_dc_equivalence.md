# Exactness of Divide-and-Conquer NNLS with Iterative Refinement

> **Status.** This is the working note that preceded the manuscript in
> `paper/`, kept for its extended remarks. Its numbering differs from
> the manuscript's, and where the two differ the manuscript is
> authoritative. The manuscript adds, among other things, the exact
> halting round (its Theorem 1(c)), a tolerance bound that also covers
> inexact complementarity (its Proposition 2), and an observed failure
> of the support test alone under non-uniqueness.

**Subject.** E. H. Brookes, R. V. Boppana, B. Demeler, *Computing Large Sparse
Multivariate Optimization Problems with an Application in Biophysics*, SC'06
(doi 10.1145/1188455.1188541), presents a divide-and-conquer (D&C) method for
large NNLS problems: partition the parameter set, apply the fitting function
`f` to each block, union the returned parameter sets, and apply `f` again
(Text 1); §3.2 adds an *iterative variant* in which the final result set is
unioned back into every block and the procedure repeats "until the results no
longer vary." The paper observes that the basic scheme and the full
computation "usually differ," while the iterative variant "is in exact
correspondence" empirically. No proof was given. This note supplies one.

**Results proved here.**

1. *(Theorem 1)* The iterative variant terminates after finitely many rounds,
   and at termination its solution is a global minimizer of the **full**
   NNLS problem. The implemented stopping test — one round that leaves the
   result unchanged — is a *sound certificate* of global optimality.
2. *(Theorem 2)* At termination the objective value, the fitted vector
   $Ax$, and the residual are **identical** to those of the full-grid
   solution — unconditionally. The amplitude vector itself is identical
   whenever the full problem's minimizer is unique (generic case); a
   sufficient condition is given.
3. *(§6)* The **single pass** (Text 1 without refinement) is *not*
   equivalent in general: an explicit 4-column counterexample is given in
   which it returns SSR $=1/12$ while the full solution has SSR $=0$. The
   refinement loop is therefore not cosmetic; it is what makes the method
   exact.
4. *(§7)* A finite-tolerance version: if iteration stops at an exactly
   solved iterate whose pricing violations are all $\le\delta$, the
   objective suboptimality is at most $\delta\lVert x^*\rVert_1$.

The proof is a Lyapunov-descent argument — the direction of the
"contraction" idea — closed by two structural facts: a *distributed pricing*
lemma (a KKT violation anywhere forces a strict objective decrease in the
next round) and *finiteness of the attainable value set* (each iterate is an
exact minimizer over one of finitely many column subsets). §8.1 discusses
why this route succeeds where a metric contraction argument cannot.

---

## 1. Setup and notation

Data $b\in\mathbb{R}^m$; basis matrix $A\in\mathbb{R}^{m\times n}$ with
columns $a_j$, $j\in S:=\{1,\dots,n\}$ (one column per parameter; $n=|S|$
from $10^3$ to $10^6$ in the paper's analysis, $1.5\times10^6$ in its
largest run). For a subset $C\subseteq S$, the restricted NNLS
problem is

$$
\mathrm{P}(C):\qquad \min_{x\ge 0,\ \operatorname{supp}(x)\subseteq C}
\ F(x):=\tfrac12\lVert Ax-b\rVert_2^2 ,
$$

with optimal value $\mathrm{Val}(C)$. The full problem is $\mathrm{P}(S)$,
$v^*:=\mathrm{Val}(S)$. The paper's set function is
$f(C):=\operatorname{supp}(x_C)$ for a minimizer $x_C$ of $\mathrm{P}(C)$
("the subset of parameters that contribute to the best fit"). When
$\mathrm{P}(C)$ has several minimizers, $f$ may return any of them; every
statement below holds for an arbitrary selection. Write
$r(x):=b-Ax$ for the residual.

**Lemma 0 (existence; well-posedness of values and fits).**
$\mathrm{P}(C)$ attains its minimum, and the fitted vector $Ax_C$ is the
same for every minimizer.
*Proof.* $K_C:=\{A x:\ x\ge0,\ \operatorname{supp}(x)\subseteq C\}$ is a
finitely generated convex cone, hence closed (Minkowski–Weyl). The
projection $p_C$ of $b$ onto the closed convex set $K_C$ exists and is
unique; any preimage $x\ge0$ of $p_C$ supported in $C$ is a minimizer, and
every minimizer maps to $p_C$. $\square$

## 2. Optimality conditions and the pricing lemma

**Lemma 1 (KKT).** Let $x$ be feasible for $\mathrm{P}(C)$ and $r=r(x)$.
Then $x$ solves $\mathrm{P}(C)$ **iff**

$$
a_j^{\mathsf T} r \le 0\ \ \forall j\in C,
\qquad\text{and}\qquad
a_j^{\mathsf T} r = 0\ \ \forall j\in \operatorname{supp}(x). \tag{KKT}
$$

*Proof.* $F$ is convex and differentiable with $\nabla F(x)=-A^{\mathsf T}r$,
and the feasible set is convex, so $x$ is optimal iff
$\nabla F(x)^{\mathsf T}(y-x)\ge 0$ for all feasible $y$, i.e.
$(A^{\mathsf T}r)^{\mathsf T}(y-x)\le 0$.
Taking $y=x+e_j$ ($j\in C$) gives $a_j^{\mathsf T}r\le0$; taking
$y=x-x_je_j$ for $x_j>0$ gives $a_j^{\mathsf T}r\ge0$, hence $=0$ on the
support. Conversely, under (KKT), for any feasible $y$,
$(A^{\mathsf T}r)^{\mathsf T}(y-x)
=\sum_{j\in C}(a_j^{\mathsf T}r)\,y_j-\sum_j (a_j^{\mathsf T}r)\,x_j
=\sum_{j\in C}(a_j^{\mathsf T}r)\,y_j\le 0$,
and convexity gives $F(y)\ge F(x)$. $\square$

**Lemma 2 (pricing: local solutions certify globally).** If $x$ solves
$\mathrm{P}(C)$ and $a_j^{\mathsf T} r(x)\le 0$ for all $j\notin C$, then
$x$ solves $\mathrm{P}(S)$.
*Proof.* The conditions (KKT) for $C=S$ hold. $\square$

The quantity $a_j^{\mathsf T}r$ is the (negative) reduced gradient of column
$j$; testing its sign is the *pricing* step of column-generation methods.
Lemma 2 says the full grid never needs to be *solved* — only *priced*.

**Lemma 3 (restriction).** (i) $C\subseteq C'$ implies
$\mathrm{Val}(C')\le \mathrm{Val}(C)$.
(ii) If $x_C$ solves $\mathrm{P}(C)$ and
$\operatorname{supp}(x_C)\subseteq D\subseteq C$, then $x_C$ solves
$\mathrm{P}(D)$ and $\mathrm{Val}(D)=\mathrm{Val}(C)$.
*Proof.* (i): feasibility nests. (ii): the conditions (KKT) for $D$ are a
subset of those for $C$. $\square$

Lemma 3(ii) is why discarding zero-amplitude parameters ("keeping only the
contributors") loses nothing *about the current solution*; the danger — and
the reason a proof is needed — is that a discarded parameter may be needed
by a *better* solution not yet visible inside the block.

## 3. The algorithm, formalized

Round $k=0,1,2,\dots$ maps a current result set $R_k\subseteq S$ (with
$R_0=\varnothing$) to $R_{k+1}$:

* **Leaves.** Partition $S$ into blocks $S^{(k)}_1,\dots,S^{(k)}_{p_k}$
  (the partition may differ between rounds; the moving-grid partitioning of
  §5 of the paper is allowed). For each $i$ solve
  $\mathrm{P}\big(S^{(k)}_i\cup R_k\big)$, obtaining a minimizer
  $y_i$ and its support $U_i=f\big(S^{(k)}_i\cup R_k\big)$.
* **Merge tree.** Combine the returned sets pairwise or in larger groups,
  possibly in several stages (the recursion of §4.1): each internal node
  $\nu$ has candidate set $C_\nu=\bigcup_{\mu\ \mathrm{child}} U_\mu$,
  solves $\mathrm{P}(C_\nu)$ for $z_\nu$, and passes
  $U_\nu=\operatorname{supp}(z_\nu)$ upward.
* **Root.** The root's minimizer is the round's iterate
  $x_{k+1}:=z_{\mathrm{root}}$, with candidate set
  $C_{k+1}:=C_{\mathrm{root}}$, value $v_{k+1}:=F(x_{k+1})$, and
  $R_{k+1}:=\operatorname{supp}(x_{k+1})$.

Round $0$ is exactly the basic scheme of Text 1. The iterative variant of
§3.2 is the sequence of rounds, stopped when the result no longer varies.

**Hypotheses.**

* **(H1)** Each application of $f$ solves its restricted problem exactly.
  (Active-set NNLS solvers — Lawson–Hanson and its descendants — terminate
  finitely at an exact KKT point in exact arithmetic.)
* **(H2)** In every round the blocks cover $S$, and every leaf includes the
  current result set $R_k$ (§3.2: "all parameters in $R_D$ are unioned back
  into each $S_i$").
* **(H3)** Every merge node's candidate set contains the **whole** returned
  set of each of its children (merges union returned sets; they do not split
  or truncate them).

(H3) is automatic for the two-level scheme of Text 1 (one final union) and
for any multistage merge that packs *whole* result sets into groups. §8.4
discusses the one implementation detail that can violate it.

## 4. Descent lemmas

**Lemma 4 (tree descent).** Under (H1), (H3), for every internal node $\nu$
with children $\mu$: $F(z_\nu)\le \min_\mu F(z_\mu)$. Consequently
$v_{k+1}\le \min_i F(y_i)$.
*Proof.* $\operatorname{supp}(z_\mu)=U_\mu\subseteq C_\nu$, so $z_\mu$ is
feasible for $\mathrm{P}(C_\nu)$, of which $z_\nu$ is a minimizer. Induct
along the path from each leaf to the root. $\square$

**Lemma 5 (monotone rounds).** Under (H1)–(H3), for $k\ge1$:
$v_{k+1}\le v_k$.
*Proof.* $\operatorname{supp}(x_k)=R_k\subseteq S^{(k)}_i\cup R_k$, so the
incumbent $x_k$ is feasible for every leaf problem; hence
$F(y_i)\le F(x_k)=v_k$ for all $i$, and Lemma 4 finishes. $\square$

**Lemma 6 (strict descent off the optimum — distributed pricing).**
Under (H1)–(H3), if $x_k$ ($k\ge1$) does **not** solve $\mathrm{P}(S)$,
then $v_{k+1}<v_k$.
*Proof.* By construction $x_k$ solves $\mathrm{P}(C_k)$, so (KKT) holds on
$C_k$; in particular complementarity holds on
$\operatorname{supp}(x_k)\subseteq C_k$. Since $x_k$ is not optimal for
$\mathrm{P}(S)$, Lemma 1 (with $C=S$) fails, which forces some
$j_0\notin C_k$ with

$$
a_{j_0}^{\mathsf T} r(x_k) > 0 .
$$

By (H2), $j_0\in S^{(k)}_{i_0}$ for some block $i_0$, and the leaf problem
$\mathrm{P}\big(S^{(k)}_{i_0}\cup R_k\big)$ contains both $j_0$ and
$\operatorname{supp}(x_k)$. Along the feasible ray
$x_k+t\,e_{j_0}$, $t\ge0$,

$$
\tfrac{d}{dt}F(x_k+te_{j_0})\Big|_{t=0}
= -\,a_{j_0}^{\mathsf T} r(x_k) < 0,
$$

so the leaf optimum satisfies $F(y_{i_0})<v_k$, and by Lemma 4,
$v_{k+1}\le F(y_{i_0})<v_k$. $\square$

Lemma 6 is the heart of the matter: *the refinement round re-prices every
column of the full grid against the current global residual*. A column that
was discarded inside its block (because the block's local residual pointed
away from it) is re-offered in every later round against the merged
residual; if it could improve the fit, the objective must strictly drop.

## 5. Main results

**Theorem 1 (finite, exact termination; sound certificate).**
Assume (H1)–(H3). Then:

1. There is a finite $K$ such that $x_K$ is a global minimizer of the full
   problem $\mathrm{P}(S)$, and every subsequent iterate is one as well,
   with $v_k=v^*$ for all $k\ge K$.
2. If any round leaves the value unchanged, $v_{k+1}=v_k$ ($k\ge1$), then
   $x_k$ and $x_{k+1}$ are already global minimizers. In particular the
   implemented test "the results no longer vary" (same set, same
   amplitudes) is a sound global-optimality certificate.

*Proof.* Each iterate is an exact minimizer over its root candidate set, so
$v_k=\mathrm{Val}(C_k)$ belongs to the finite set
$V:=\{\mathrm{Val}(C): C\subseteq S\}$, $|V|\le 2^n$. By Lemma 5 the
sequence $(v_k)_{k\ge1}$ is nonincreasing, and by Lemma 6 it is *strictly*
decreasing as long as the iterate is not globally optimal. A strictly
decreasing sequence taking values in a finite set has finite length, so
after at most $|V|$ rounds some $x_K$ is globally optimal. For $k\ge K$,
$v^*\le v_k\le v_K=v^*$, and any feasible point of $\mathrm{P}(S)$ with
value $v^*$ is a global minimizer. Part 2 is the contrapositive of
Lemma 6, plus the same sandwich for $x_{k+1}$. $\square$

**Theorem 2 (what "equivalence" means).** Let $x_\infty$ be the terminal
iterate and let $x^*$ be **any** minimizer of the full problem. Then,
unconditionally,

$$
F(x_\infty)=v^*,\qquad A x_\infty = A x^*,\qquad r(x_\infty)=r(x^*),
$$

i.e. the optimal objective (hence RMSD) and the fitted model are *identical*
to the full-grid computation's — these quantities are unique by Lemma 0.
Moreover $x_\infty$ is itself a global minimizer. If the full problem's
minimizer is unique, then $x_\infty=x^*$ exactly, and the returned parameter
set equals $R=f(S)$.
A sufficient condition for uniqueness: with $r^*$ the (unique) optimal
residual and $Z:=\{j: a_j^{\mathsf T}r^*=0\}$ the zero-reduced-cost columns,
the solution set of $\mathrm{P}(S)$ is
$\{x\ge0:\ \operatorname{supp}(x)\subseteq Z,\ A_Z x_Z = A x^*\}$; if the
columns $\{a_j\}_{j\in Z}$ are linearly independent, this set is a single
point. $\square$

Non-uniqueness is not exotic on fine grids (near-duplicate basis functions),
so the unconditional part — value, fit, residual — is the scientifically
robust statement; amplitude-level equivalence is guaranteed under the
(generic) uniqueness condition, and can be *enforced* by strictly convex
regularization (§8.5).

**Remark (stopping rule).** Under non-uniqueness, iterates can wander
among distinct optimal supports with $v_k\equiv v^*$, and the
set-stability test then need not fire at all even though every iterate
is already optimal (the manuscript's duplicated-column probe exhibits a
period-3 cycle). Stopping on "no decrease of the residual" (which the
paper already uses for the noise-removal case) is robust: by Theorem 1.2 a
stalled value certifies optimality.

## 6. The single pass is not exact: a counterexample

Take $m=3$, $n=4$:

$$
a_1=\tfrac1{\sqrt2}\begin{pmatrix}1\\0\\1\end{pmatrix},\quad
a_2=\begin{pmatrix}1\\0\\0\end{pmatrix},\quad
a_3=\tfrac1{\sqrt2}\begin{pmatrix}0\\1\\1\end{pmatrix},\quad
a_4=\begin{pmatrix}0\\1\\0\end{pmatrix},\qquad
b=\begin{pmatrix}1\\1\\3/2\end{pmatrix},
$$

with blocks $S_1=\{1,2\}$, $S_2=\{3,4\}$.

* **Leaf 1.** $\mathrm{P}(S_1)$: the unconstrained solution has $x_2<0$,
  so the constrained optimum is $x_1=\tfrac{5}{2\sqrt2}$, $x_2=0$, residual
  $r=(-\tfrac14,\,1,\,\tfrac14)^{\mathsf T}$ with
  $a_2^{\mathsf T}r=-\tfrac14<0$ (strict, so the discard is robust):
  $f(S_1)=\{1\}$.
* **Leaf 2.** Symmetrically $f(S_2)=\{3\}$.
* **Merge.** $\mathrm{P}(\{1,3\})$: Gram matrix
  $\bigl(\begin{smallmatrix}1&1/2\\1/2&1\end{smallmatrix}\bigr)$ gives
  $x_1=x_3=\tfrac{5\sqrt2}{6}$, fitted vector
  $(\tfrac56,\tfrac56,\tfrac53)^{\mathsf T}$, residual
  $r=(\tfrac16,\tfrac16,-\tfrac16)^{\mathsf T}$, and
  $$\mathrm{SSR}_{\mathrm{D\&C}}=\tfrac1{12}.$$
* **Truth.** $b$ is exactly representable:
  $x^*=(\tfrac{3\sqrt2}{4},\,\tfrac14,\,\tfrac{3\sqrt2}{4},\,\tfrac14)$
  gives $Ax^*=b$, so $\mathrm{SSR}^*=0<\tfrac1{12}$, and
  $R=f(S)\supseteq\{2,4\}\neq R_D=\{1,3\}$.

The mechanism is a *suppressor effect*: inside $S_1$, $a_1$ alone fits the
$(x,z)$-components of $b$ so well that the local residual points away from
$a_2$, which is therefore discarded — correctly, *locally* (Lemma 1 holds
for the block). But once $a_3$ enters and absorbs the $y$-component, the
joint residual rotates: at the merged solution
$a_2^{\mathsf T}r=a_4^{\mathsf T}r=\tfrac16>0$, a pricing violation. The
single pass never re-offers $a_2,a_4$ and locks in the loss. The first
refinement round solves $\mathrm{P}(\{1,2,3\})$ and $\mathrm{P}(\{1,3,4\})$
— both already fit exactly — and terminates at $\mathrm{SSR}=0=v^*$.

This makes precise the paper's own observation ("in practice, they usually
differ") and shows the gap can be a *constant factor of the entire signal*,
not merely roundoff. Why, then, was the *iterative* variant always observed
exact, typically within 3–7 rounds? Theorem 1 guarantees exactness at the
fixed point; speed is favored by the application's structure — on fine
grids each block contains near-substitutes for the globally needed columns,
so the first pass already lands near the optimal face and few pricing
rounds remain. (Worst-case round counts are another matter; §8.2.)

## 7. Finite-tolerance version

Exact zero tests are an idealization; here is the graceful degradation.
Suppose the procedure stops at an iterate $x$ that exactly solves
$\mathrm{P}(C)$ for its final candidate set (so complementarity
$a_j^{\mathsf T}r=0$ holds on $\operatorname{supp}(x)$), and the pricing
violations satisfy $\max_j a_j^{\mathsf T} r(x)\le\delta$ for some
$\delta\ge0$. Then for every minimizer $x^*$ of $\mathrm{P}(S)$:

$$
F(x)-v^*\ \le\ \delta\,\lVert x^*\rVert_1,
\qquad
\lVert Ax - Ax^*\rVert_2^2\ \le\ 2\,\delta\,\lVert x^*\rVert_1 .
$$

*Proof.* Convexity: $v^*=F(x^*)\ge F(x)+\nabla F(x)^{\mathsf T}(x^*-x)$
with $\nabla F(x)=-A^{\mathsf T}r$. Complementarity gives
$\nabla F(x)^{\mathsf T}x=0$, and
$\nabla F(x)^{\mathsf T}x^*=-\sum_j (a_j^{\mathsf T}r)\,x^*_j
\ge-\delta\lVert x^*\rVert_1$ since $x^*\ge0$. Hence
$v^*\ge F(x)-\delta\lVert x^*\rVert_1$. For the second bound, project onto
the closed convex cone $K_S$: for any $p\in K_S$,
$\lVert p-b\rVert^2\ge\lVert p^*-b\rVert^2+\lVert p-p^*\rVert^2$ with
$p^*=Ax^*$ the projection of $b$; take $p=Ax$. $\square$

So a $\delta$-tolerant pricing test yields an explicit suboptimality bound;
$\delta=0$ recovers Theorem 2.

## 8. Remarks

### 8.1 On the contraction approach

The natural fixed-point framing — show the round map is a contraction, then
invoke Banach — runs into two structural obstructions:

* **Fixed points need not be unique.** The fixed points of the round map
  are exactly the global minimizers (Theorem 1.2 in one direction, Lemma 3
  in the other), and with non-unique minimizers (e.g. duplicated or
  linearly dependent grid columns) they form a continuum. A strict
  contraction on a complete metric space has a *unique* fixed point, so no
  metric can make the round map one in general.
* **No instance-independent modulus.** Even with a unique minimizer, a
  single round's progress can be made arbitrarily small relative to the
  distance from the optimum by ill-conditioning (nearly parallel columns),
  so no uniform contraction factor exists across instances.

What *is* true — and is the rigorous content of the contraction intuition —
is that $\Lambda(x):=F(x)-v^*$ is a **Lyapunov function** for the round
map: nonincreasing always (Lemma 5), strictly decreasing off the fixed-point
set (Lemma 6). Lyapunov descent alone gives only asymptotic statements in
continuous optimization (values can decrease forever without reaching the
infimum); the second ingredient, special to this algorithm, is that every
iterate is an *exact* minimizer over one of the $2^n$ column subsets, so
the value sequence lives in a **finite set**. Strict descent through a
finite set terminates — yielding exact arrival in finitely many rounds,
which is stronger than the geometric convergence a contraction argument
would have delivered.

### 8.2 Worst-case round counts

Theorem 1's bound ($\le|V|\le 2^n$ rounds) is combinatorial, in the same
spirit as finite-termination results for active-set methods and the
simplex method, and we make no polynomial claim. The empirical record —
3–7 rounds in the paper, 2–13 across the 200 randomized instances in
the companion script (interlaced-subgrid partitions take the longest)
— reflects the benign structure of smooth-kernel design matrices, not
the worst case.

### 8.3 Why the pieces stay small (memory)

Active-set solvers return minimizers whose positive columns are linearly
independent, so every returned set has $|f(C)|\le\operatorname{rank}(A)\le
m$ regardless of $|C|$. Merge candidates are therefore bounded by (fan-in)
$\times\operatorname{rank}(A)$ plus $|R_k|$ — the theoretical face of the
paper's empirical observation that $f$ returns a small fraction $x<1$ of
its input (Table 1), and the reason the multistage recursion of §4.1
terminates quickly.

### 8.4 The one implementation detail that matters: (H3)

§4.1 describes re-partitioning the unioned stage results into chunks of
size $m$. If such a chunking **splits** a returned support across chunks,
(H3) fails: a merge node need no longer contain any child's full solution,
Lemma 4's feasibility argument collapses, and a round can in principle
*lose* ground — with it goes the soundness proof of the "results no longer
vary" certificate. Two safe implementations: pack **whole** returned sets
into stage groups (their sizes are $\le\operatorname{rank}(A)$ by §8.3, so
this costs nothing), or union $R_k$ into every internal candidate set as
well (restores Lemma 5, though the clean strict-descent proof still wants
atomic merges). In the companion experiments the atomic variant is used.

### 8.5 Extensions

* **Tikhonov / regularized NNLS.** Replacing $F$ by
  $F(x)+\tfrac\lambda2\lVert Lx\rVert^2$ (as in regularized 2DSA-type
  analyses) is again an NNLS on an augmented system, so Theorems 1–2 apply
  verbatim; if $\lambda>0$ and $L$ has trivial kernel the objective is
  strictly convex, minimizers are unique, and equivalence holds at the level
  of the amplitude vector itself, unconditionally.
* **General smooth convex losses.** Lemmas 1–6 use only convexity and
  differentiability of $F$ plus exact subproblem solves, so the theorem
  holds for any such loss (e.g. weighted least squares).
* **Free-sign auxiliary parameters (systematic noise).** Time-invariant
  noise offsets are sign-free. If those degrees of freedom are carried in
  *every* leaf and merge candidate and solved *jointly* (their KKT
  condition is plain stationarity, and pricing of the constrained columns
  is unchanged), the theorem survives. By contrast, interleaving noise
  removal as a separate processing step *between* solves changes the
  objective from round to round; the Lyapunov argument no longer applies —
  consistent with §3.2's report that the iterative variant "may not
  converge to a fixed parameter set" in that mode and needs a
  goodness-of-fit stopping rule.

### 8.6 Relation to known frameworks

The refinement loop is a *distributed column generation* scheme: the merged
problem is a restricted master, the leaves perform pricing over a partition
of the full column set, and Lemma 6 is the classical "a negative reduced
cost column improves the master" argument, parallelized. The same
descent-plus-finiteness pattern underlies finite-termination proofs for
working-set decomposition methods (e.g. Osuna-style SVM chunking) and for
active-set NNLS itself (Lawson–Hanson), of which the present algorithm can
be seen as a coarse-grained, parallel relative.

## 9. Numerical verification

`verify.py` (same directory; NumPy/SciPy) implements §3 exactly (atomic
merges, configurable block counts and fan-in) and checks, in every trial,
the parent–child tree-descent inequality at every merge node (Lemma 4),
round monotonicity (Lemma 5), terminal value equality against full-grid
NNLS, and BOTH KKT residuals of the tolerance analysis — the pricing
residual $\delta=\max(0,\max_j a_j^{\mathsf T}r)$ and the
complementarity residual
$\varepsilon=\max(0,-(A^{\mathsf T}r)^{\mathsf T}x)$ (pricing alone is
not sufficient for optimality). Single-pass suboptimality uses the
manuscript's criterion $v_{\mathrm{sp}}-v^*>10^{-9}(1+v^*)$. Results
(seeds 20260807/20260808):

| experiment | trials | rounds (min/med/max) | worst value gap | worst δ | worst ε | single pass suboptimal |
|---|---|---|---|---|---|---|
| AUC-like smooth correlated kernels | 60 | 4 / 6 / 9 | 2.2e-16 | 2.5e-16 | 1.1e-13 | 60/60 (median +18% SSR) |
| 2-D lattice, interlaced subgrids | 40 | 7 / 10 / 13 | 4.4e-16 | 2.7e-16 | 1.3e-13 | 40/40 (median 8.4× excess) |
| iid Gaussian designs | 60 | 2 / 3 / 3 | 3.1e-28 | 8.8e-16 | 6.0e-14 | 33/60 |
| exact duplicate columns (non-unique optima) | 40 | 2 / 4 / 9 | 9.5e-17 | 8.5e-16 | 7.4e-14 | 39/40 |

The 4-column counterexample of §6 is reproduced exactly
($\mathrm{SSR}=1/12$, i.e. $F=1/24$; violation $1/6$), and one
refinement round restores $\mathrm{SSR}=0$. A scaling probe extends the
smooth-kernel generator to $n=15360$ (64×) with rounds staying at 6–9
and roundoff-level agreement, and a support-rule-only probe on the
duplicated-column generator exhibits non-termination (a period-3 cycle
among optimal supports), confirming that the value rule is what
guarantees halting; see `experiments.py`.

## References

1. E. H. Brookes, R. V. Boppana, B. Demeler. *Computing Large Sparse
   Multivariate Optimization Problems with an Application in Biophysics.*
   SC'06. doi:10.1145/1188455.1188541.
2. C. L. Lawson, R. J. Hanson. *Solving Least Squares Problems.*
   Prentice-Hall, 1974 (SIAM Classics 1995), Ch. 23.
3. R. Bro, S. De Jong. *A fast non-negativity-constrained least squares
   algorithm.* J. Chemometrics 11 (1997) 393–401.
4. M. Frank, P. Wolfe. *An algorithm for quadratic programming.* Naval
   Res. Logist. Q. 3 (1956) 95–110. (Attainment of quadratic minima on
   polyhedra.)
5. P. C. Gilmore, R. E. Gomory. *A linear programming approach to the
   cutting-stock problem.* Oper. Res. 9 (1961) 849–859. (Column
   generation / pricing.)
6. E. Osuna, R. Freund, F. Girosi. *An improved training algorithm for
   support vector machines.* NNSP 1997. (Working-set decomposition with
   strict-improvement convergence argument.)
