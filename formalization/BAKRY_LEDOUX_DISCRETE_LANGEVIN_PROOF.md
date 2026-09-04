# Archival design note: Bakry--Ledoux from Gaussian OU and finite Euler limits

> **Reader note.** This file records the proof design while the
> Gaussian/Bakry--Ledoux modules were being built. Its opening status and some
> forward-looking sentences are historical. The construction is now complete:
> finite Gaussian isoperimetry is proved by explicit OU/Bobkov interpolation,
> the target is identified by a fully discrete diagonal Euler--RWM limit, and
> `DiscreteTime.target_bakryLedoux` is unconditional relative to
> `FirstOrderPotential`. For the current account and reusable API, read
> `PAPER_READER_GUIDE.md`, `REUSABLE_RESULTS.md`, and
> `PROOF_STRATEGY_LEDGER.md`.

This note is retained because it contains detailed mathematical derivations
and explains why the formalization avoided a general SDE dependency. The
stage labels G1--G5 below are local labels for normal-profile calculus,
Mehler calculus, the OU residual, functional closure, and enlargement.

## 1. Statement and conventions

Let

```text
pi(dx) = Z^(-1) exp(-U(x)) dx,       x in R^d,
```

where `U` is `C^2` and

```text
m I <= Hess U(x) <= L I,             0 < m <= L.
```

Write `Phi` for the standard normal CDF and `PhiInv` for its inverse on
`(0,1)`.  For `r > 0`, use the open enlargement

```text
A^r = {x : dist(x,A) < r}.
```

The desired assertion is

```text
pi(A^r) >= Phi(PhiInv(pi(A)) + sqrt(m) r)                 (BL)
```

for every measurable `A`.  The cases `pi(A)=0` and `pi(A)=1` are interpreted
by monotone limits from `(0,1)` and are immediate.  The strict condition
`r > 0` is intentional: Mathlib's `Metric.thickening 0 A` is empty.  A version
using a closed enlargement may instead include `r=0`.

The proof has four modules:

1. sharp Gaussian enlargement, proved with the explicit Gaussian
   Ornstein--Uhlenbeck semigroup;
2. a finite deterministic Lipschitz estimate for Euler--Langevin endpoints;
3. stability of enlargement inequalities under weak convergence;
4. identification and long-time convergence of the finite Euler limit.

The original plan expected Module 4 to use target-side stochastic analysis.
The completed Lean development instead proves target identification with a
finite Euler--RWM comparison, contraction, and a diagonal weak limit. No SDE
theorem remains in the checked dependency chain.

## 2. Gaussian OU module

### G1. Normal profile calculus

For `s in (0,1)`, define

```text
I(s) = phi(PhiInv(s)),
phi(x) = (2 pi)^(-1/2) exp(-x^2/2).
```

Since `Phi' = phi` and `phi' = -x phi`, the inverse-function rule gives

```text
I'(s)  = -PhiInv(s),
I''(s) = -1 / I(s),
I(s) I''(s) = -1.                                      (G1)
```

Also, `I` is positive and concave on `(0,1)`, symmetric about `1/2`, and
extends continuously to `[0,1]` with `I(0)=I(1)=0`.

These are scalar real-analysis lemmas.  For Lean it is preferable to prove
them first on every compact interval `[epsilon,1-epsilon]`; endpoint facts
then follow by monotone limits.

### G2. Explicit Ornstein--Uhlenbeck semigroup

For the standard Gaussian measure `gamma_d`, set

```text
P_t f(x) = integral f(exp(-t)x + sqrt(1-exp(-2t)) z) gamma_d(dz).
```

The following facts follow directly from this Mehler formula:

```text
P_0 f = f,
P_(s+t) = P_s P_t,
integral P_t f dgamma_d = integral f dgamma_d,
grad P_t f = exp(-t) P_t(grad f),
P_t f -> integral f dgamma_d as t -> infinity.
```

Initially take `f` smooth, bounded, and with values in
`[epsilon,1-epsilon]`.  This avoids every endpoint singularity of `I''`.

### G3. The local Bobkov inequality

Let `L = Delta - <x,grad>` be the OU generator.  For fixed `t`, put

```text
u_s = P_(t-s) f,
c_s = 1-exp(-2s),
Q_s = sqrt(I(u_s)^2 + c_s |grad u_s|^2),
F(s) = P_s Q_s,                          0 <= s <= t.
```

Then `partial_s u_s = -L u_s`.  We claim `F'(s) >= 0`.

Here is the complete pointwise calculation.  Write `v=grad u_s`, `H=Hess
u_s`, and

```text
A = I(u_s)^2 + c_s |v|^2.
```

Using `(partial_s+L)u_s=0`, `I I''=-1`, `c_s'=2(1-c_s)`, and the explicit OU
Bochner identity

```text
(partial_s+L)|grad u_s|^2 = 2(|Hess u_s|_HS^2 + |grad u_s|^2),
```

one obtains

```text
(partial_s+L)A = 2 I'(u_s)^2 |v|^2 + 2 c_s |H|_HS^2.     (G2)
```

Moreover,

```text
grad A = 2 I(u_s) I'(u_s) v + 2 c_s H v.
```

Finite-dimensional Cauchy--Schwarz, applied componentwise to the two block
vectors `(I,sqrt(c_s)v)` and `(I' v_j,sqrt(c_s) H_j*)`, gives

```text
|grad A|^2
  <= 4 (I^2+c_s|v|^2)(I'^2|v|^2+c_s|H|_HS^2)
   = 2 A (partial_s+L)A.                                  (G3)
```

The diffusion chain rule now yields

```text
(partial_s+L)sqrt(A)
 = ((partial_s+L)A)/(2 sqrt(A)) - |grad A|^2/(4 A^(3/2))
 >= 0.
```

Differentiating `P_s Q_s` therefore proves `F'(s)>=0`.  Comparing `s=0` and
`s=t` gives the local inequality

```text
I(P_t f) <= P_t sqrt(I(f)^2 + (1-exp(-2t)) |grad f|^2).   (G4)
```

This calculation is the only Bochner-style step in the proof, and it is for
the explicit Gaussian OU semigroup, not for the target diffusion.

### G4. Functional Gaussian isoperimetry

Let `t -> infinity` in (G4).  OU invariance and convergence to the mean,
followed by dominated convergence, give Bobkov's functional inequality

```text
I(integral f dgamma_d)
  <= integral sqrt(I(f)^2 + |grad f|^2) dgamma_d.          (G5)
```

Truncation first removes the restriction that the values stay away from
`0,1`; smooth approximation then extends (G5) to locally Lipschitz
`f : R^d -> [0,1]`.

### G5. From the functional inequality to enlargement

For a Borel set `A`, apply (G5) to the standard Lipschitz ramps

```text
f_h(x) = max(0, 1-dist(x,A)/h).
```

Letting `h downarrow 0` gives the Gaussian perimeter inequality

```text
gamma_d^+(A) >= I(gamma_d(A)),                            (G6)
```

first for closed `A`, then for arbitrary Borel `A` by inner regularity.  In
this limit `I(f_h)` is supported on the vanishing strip, while
`|grad f_h| <= 1/h`; the resulting liminf is exactly the outer Minkowski
content.  No smooth boundary is assumed.

Put `a(r)=gamma_d(A^r)`.  The semigroup property of thickenings and (G6)
imply for every `r>0`

```text
D^+ a(r) >= I(a(r)).                                      (G7)
```

On intervals where `0<a(r)<1`, set `b(r)=PhiInv(a(r))`.
Because `(PhiInv)'=1/I`, the lower-Dini chain rule gives `D^+b(r)>=1`.
The elementary Dini comparison lemma then yields

```text
b(r) >= b(0+) + r >= PhiInv(gamma_d(A)) + r.
```

Applying `Phi` proves sharp finite-dimensional Gaussian enlargement:

```text
gamma_d(A^r)
  >= Phi(PhiInv(gamma_d(A)) + r).                         (GI)
```

For formalization, G5 should be split into: ramps for closed sets, perimeter
liminf, Dini derivative of enlargements, scalar comparison, and Radon
approximation.  This is more code than the differential calculation G3, but
it uses only metric thickenings and one-variable analysis.

## 3. Finite Euler--Langevin module

Fix `T>0` and `N>=1`; write `delta=T/N`.  For a deterministic `x`, let

```text
X_0 = x,
X_(k+1) = X_k - delta grad U(X_k) + sqrt(2 delta) Z_(k+1),
```

where `(Z_1,...,Z_N)` is a standard Gaussian vector in `R^(Nd)`.

### E1. Strong monotonicity and one-step contraction

The Hessian lower bound, or equivalently the two lower Taylor inequalities,
gives

```text
<grad U(x)-grad U(y), x-y> >= m |x-y|^2.                 (E1)
```

The upper Hessian bound gives `|grad U(x)-grad U(y)|<=L|x-y|`.  Hence, for
`delta>=0`,

```text
|(x-delta grad U(x))-(y-delta grad U(y))|^2
  <= rho_delta^2 |x-y|^2,
rho_delta^2 = 1-2m delta+L^2 delta^2.                    (E2)
```

The polynomial `rho_delta^2` is nonnegative for every `delta`: using
`0<m<=L`,

```text
rho_delta^2
 = 1-(m/L)^2 + (L delta-m/L)^2 >= 0.
```

### E2. Dependence on all innovations

Drive two paths by innovation tuples `z,w` and start them at the same point.
Writing `D_k=|X_k(z)-X_k(w)|` and `b_k=|z_k-w_k|`, (E2) gives

```text
D_(k+1) <= rho_delta D_k + sqrt(2delta) b_k,
D_0=0.
```

Finite induction gives

```text
D_k <= sqrt(2delta) sum_(j<k) rho_delta^(k-1-j) b_j.
```

Cauchy--Schwarz gives the squared Euclidean product-norm estimate

```text
D_k^2
 <= [2delta sum_(j<k) rho_delta^(2(k-1-j))]
      [sum_(j<k) b_j^2].                                  (E3)
```

This is exactly the assertion that the endpoint map from `R^(Nd)` to `R^d`
is Lipschitz with squared constant equal to the first bracket.

### E3. Finite geometric coefficient

Assume `L^2 delta < 2m`, so `rho_delta^2<1`.  Reversing a finite sum and using
the finite identity

```text
(sum_(j<k) q^j)(1-q) = 1-q^k
```

gives

```text
2delta sum_(j<k) rho_delta^(2j)
 = 2(1-rho_delta^(2k))/(2m-L^2 delta)
 <= 2/(2m-L^2 delta).                                    (E4)
```

The checked Lean proof deliberately uses the product identity itself, not an
infinite geometric series.

### E4. Transfer of Gaussian enlargement

Let `F : R^(Nd) -> R^d` be the endpoint map and let `C` be its Lipschitz
constant.  For every set `A`,

```text
(F^(-1) A)^(r/C) subset F^(-1)(A^r).                     (E5)
```

Apply (GI) in dimension `Nd` to `F^(-1)A` and use (E5).  For the endpoint
law `mu_(N,T,x)` this gives

```text
mu_(N,T,x)(A^r)
 >= Phi(PhiInv(mu_(N,T,x)(A)) + r/C_(N,T)),              (E6)
```

with

```text
C_(N,T)^2 <= 2/(2m-L^2 T/N).                             (E7)
```

For fixed `T`, the right side of (E7) tends to `1/m`.  This coarser bound is
preferable for Lean to the sharper finite-time expression
`(1-rho^(2N))/(m-L^2 delta/2)`: it avoids proving
`rho_N^(2N)->exp(-2mT)` and loses nothing in the final theorem.

## 4. Weak-limit stability module

The following lemma is needed twice and is worth formalizing independently.

### W1. Stability theorem

Let `mu_n` and `mu` be probability measures on `R^d`, with `mu_n` converging
weakly to `mu`.  Let `c_n>0`, `c_n->c>0`, and suppose every `mu_n` satisfies

```text
mu_n(B^s) >= Phi(PhiInv(mu_n(B)) + s/c_n)                (W1)
```

for every Borel `B` and every `s>0`.  Then `mu` satisfies the same inequality
with `c`.

### W2. Proof without illegal Portmanteau reversal

Fix Borel `A`, `r>0`, and first suppose `mu(A)>0`.  Choose compact `K subset
A` with `mu(K)>=mu(A)-eta`.  Choose `epsilon,s>0` with
`epsilon+s<r`, and set

```text
B = K^epsilon,
F = {x : dist(x,K) <= epsilon+s}.
```

Then `B` is open, `F` is closed, and

```text
B^s subset F subset A^r.                                 (W2)
```

Portmanteau gives

```text
liminf mu_n(B) >= mu(B) >= mu(K),
limsup mu_n(F) <= mu(F).                                 (W3)
```

Since `mu_n(F)>=mu_n(B^s)`, (W1), monotonicity and continuity of the normal
profile imply

```text
mu(A^r) >= mu(F)
 >= Phi(PhiInv(mu(K)) + s/c).                            (W4)
```

Now let `eta downarrow 0`, `epsilon downarrow 0`, and `s upward r` while
maintaining `epsilon+s<r`.  This proves the claim.  If `mu(A)=0`, the desired
lower bound is zero by the endpoint convention.  If `mu(A)=1`, use compact
inner approximations of masses tending to one.

The closed set `F` is essential.  Applying Portmanteau directly to the open
output thickening would give the inequality in the wrong direction.

### W3. Varying upper bounds for the Lipschitz constants

In (E6) one may only know `C_(N,T)^2 <= a_N` with `a_N->1/m`.  Apply (E6)
with `c_N=sqrt(a_N)`: because `C_(N,T)<=c_N`, using the smaller source radius
`r/c_N` remains valid.  Then W1 applies and yields the sharp constant
`c=1/sqrt(m)`.

## 5. Target Langevin limit module

This is the point at which a genuine stochastic theorem is needed.

### L1. Explicit theorem to be formalized

Under the stated `C^2`, `m`-strong convexity and `L`-smoothness assumptions:

1. For every `x`, the integral equation

   ```text
   X_t^x = x - integral_0^t grad U(X_s^x) ds + sqrt(2) B_t             (L1)
   ```

   has a unique continuous strong solution.

2. Coupled Euler endpoints with mesh `T/N` and Brownian increments converge
   to `X_T^x` in `L^2`, hence weakly.

3. The probability measure `pi(dx)=Z^(-1)exp(-U(x))dx` is invariant for the
   transition semigroup `P_T(x,.)=Law(X_T^x)`.

4. With synchronous noise,

   ```text
   |X_t^x-X_t^y| <= exp(-mt)|x-y|.                         (L2)
   ```

These statements are standard for overdamped Langevin diffusions with a
globally Lipschitz drift.  Items 1 and 2 can be proved directly by Picard
iteration, moment estimates, Brownian increments, and discrete Gronwall.
Item 3 uses weighted integration by parts plus uniqueness of the associated
Markov/Fokker--Planck evolution.  That last implication is the part most
likely to require significant new Mathlib infrastructure.

### L2. Direct proof skeleton for Euler convergence

Define the continuous Euler interpolation

```text
Xbar_t = x - integral_0^t grad U(Xbar_(floor(s/delta)delta)) ds
           + sqrt(2) B_t.
```

Global Lipschitzness and linear growth give, uniformly for `t<=T`,

```text
E sup_(s<=t)|X_s|^2 + E sup_(s<=t)|Xbar_s|^2 <= C_(T,x),
E|Xbar_s-Xbar_(floor(s/delta)delta)|^2 <= C_(T,x) delta.
```

Consequently,

```text
E sup_(s<=T)|X_s-Xbar_s|^2
 <= C L^2 integral_0^T E sup_(u<=s)|X_u-Xbar_u|^2 ds
      + C_(T,x) delta.
```

Gronwall proves an `O(delta)` mean-square error.  The grid endpoint of
`Xbar` is exactly the finite recursion in Section 3.

### L3. Invariance and the honest analytic boundary

For `f in C_c^2`, integration by parts gives

```text
integral [Delta f - <grad U,grad f>] dpi
 = Z^(-1) integral div(exp(-U) grad f) dx
 = 0.                                                     (L3)
```

To conclude `pi P_t=pi`, one uses uniqueness for the Fokker--Planck equation
or, equivalently, uniqueness of the martingale problem for the globally
Lipschitz uniformly elliptic SDE.  Equation (L3) alone does not logically
imply invariance without this uniqueness/core theorem.  A formal development
must expose one of the following interfaces:

```text
infinitesimalInvariant_implies_invariant
```

for this concrete Langevin generator, or

```text
fokkerPlanck_unique_globallyLipschitz
```

for probability solutions with finite second moment.

A completely discrete alternative constructs invariant laws of the ULA
chains and passes their discrete generator identities to a weak limit.  It
still needs the theorem that the stationary distributional equation
`L*mu=0` has unique probability solution `pi`; this is elliptic PDE or
martingale-problem infrastructure in another form.  Thus the discrete route
does not make the identification theorem disappear.

### L4. Long-time convergence

Let `Y_0` have law `pi`, independent of the Brownian motion, and drive
`X^x,Y` synchronously.  Invariance gives `Law(Y_T)=pi`.  Since the noise
cancels in the difference, strong monotonicity gives

```text
d/dt |X_t^x-Y_t|^2 <= -2m |X_t^x-Y_t|^2,
```

and hence (L2).  Strong convexity already supplies a finite second moment of
`pi`, so

```text
W_2(P_T(x,.),pi)
 <= exp(-mT) (integral |x-y|^2 pi(dy))^(1/2) -> 0.         (L4)
```

In particular `P_T(x,.)` converges weakly to `pi`.

## 6. Assembly

Fix `T>0`.  By L2, the Euler endpoint laws converge weakly to `P_T(x,.)`.
E4, E7, the coefficient limit, and W1 therefore give

```text
P_T(x,A^r)
 >= Phi(PhiInv(P_T(x,A)) + sqrt(m) r)                    (A1)
```

for every Borel `A` and `r>0`.  The constant is independent of `T`.

Now let `T->infinity`.  By L4, `P_T(x,.)` converges weakly to `pi`.  Applying
W1 once more to (A1) proves (BL).

This proves the desired Bakry--Ledoux enlargement theorem.  The proof does
not use a target `Gamma_2` interpolation, Ethier--Kurtz convergence, or the
Lovasz--Simonovits localization lemma.  It does use the concrete Langevin
SDE theorem L1--L3.  Calling the entire proof “purely discrete” would
therefore be inaccurate until the stationary generator-uniqueness step has
itself been formalized.

## 7. Lean decomposition and current status

| ID | Lean-sized declaration | Status |
|---|---|---|
| E1 | strong monotonicity of `gradU` | checked |
| E2 | one-step squared and norm contraction | checked |
| E2a | nonnegativity and square-root identity for `rho` | checked |
| E3a | exact affine-recursion solution | checked |
| E3b | finite Cauchy--Schwarz endpoint estimate | checked |
| E4a | reverse finite powers equal ordinary geometric sum | checked |
| E4b | coefficient `<=2/(2m-L^2 delta)` | checked |
| E4c | final squared innovation sensitivity | checked |
| E7a | coefficient tends to `1/m` as `delta->0` | checked |
| E7b | fixed-time mesh coefficient limit | checked |
| E7c | eventual fixed-time small-step condition | checked |
| E5a | flatten/unflatten `R^(Nd)` innovation blocks | checked |
| E5b | product Euclidean norm-square identity | checked |
| E5c | endpoint `LipschitzWith` theorem | checked |
| G1 | normal-profile derivative identities | checked on `(0,1)`; quantile/profile endpoint limits and the continuous closed extension are checked |
| G2 | Mehler semigroup and invariance | checked for bounded continuous tests, including long-time convergence; Fréchet-derivative commutation checked for bounded `C¹` data |
| G3 | local Bobkov interpolation | **checked completely**, including higher fields, backward PDE, residual identity/sign, path domination, and the full smooth interpolation certificate |
| G4 | functional Bobkov closure | checked from smooth interpolation certificates: local inequality, long-time varying-integral limit, continuous closed profile, and endpoint truncation |
| G5 | locally-Lipschitz approximation and enlargement | checked without external approximation/continuity inputs: normalized bump mollification, canonical ramps, strip support, perimeter liminf, intrinsic right-continuity, thickening Dini slope, Gaussian-quantile comparison, closed-set enlargement, and Radon approximation |
| W1--W3 | weak-limit stability | checked abstractly and directly for the endpoint-corrected Gaussian shift |
| E8 | finite endpoint enlargement and limit transfer | **checked unconditionally**, including finite-index Gaussian reindexing and diagonal target convergence |
| L1--L4 | SDE construction/invariance route | not needed; replaced by the checked elementary discrete-time endpoint argument |

The checked declarations are in
`UniformRandomMALA/Concrete/BakryLedouxReduction.lean` and
`UniformRandomMALA/Concrete/FiniteEulerGaussianImage.lean`, with G1--G4 in
`GaussianNormalProfile.lean`, `GaussianOU.lean`, `GaussianBobkov.lean`,
`GaussianBobkovFunctional.lean`, `GaussianOUGenerator.lean`, and
`GaussianOUCanonicalFields.lean`, `GaussianOUCanonicalResidual.lean`, and
`GaussianOUCanonicalInterpolation.lean`; concrete G5 and the final transfer
are in `GaussianRampCanonicalInterpolation.lean`.

## 8. References and provenance

No argument above is claimed as new.  The normal-profile semigroup method is
the Bakry--Ledoux method specialized to the explicit Gaussian OU semigroup;
the target transfer is the standard contractive-iterated-random-functions
plus Langevin approximation argument.

* D. Bakry and M. Ledoux, *Levy--Gromov's isoperimetric inequality for an
  infinite dimensional diffusion generator*, Invent. Math. 123 (1996),
  259--281. <https://doi.org/10.1007/s002220050026>
* S. G. Bobkov, *An isoperimetric problem on the line*, Studia Math. 123
  (1997), 3--44. <https://eudml.org/doc/216334>
* D. Bakry, I. Gentil, and M. Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Springer, 2014. The Gaussian functional
  isoperimetric and semigroup calculus are treated there.
  <https://doi.org/10.1007/978-3-319-00227-9>
* P. E. Kloeden and E. Platen, *Numerical Solution of Stochastic Differential
  Equations*, Springer, 1992. The globally-Lipschitz Euler strong-convergence
  theorem used in L2 is standard material in this reference.
  <https://doi.org/10.1007/978-3-662-12616-5>
* S. Ohta, *A semigroup approach to Finsler geometry: Bakry--Ledoux's
  isoperimetric inequality*. This gives a clear modern presentation of the
  normal-profile interpolation. <https://arxiv.org/abs/1602.00390>
