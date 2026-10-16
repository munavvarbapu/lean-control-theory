# Mathematical notes

These notes explain the statements proved in the Lean files. All vector
spaces below are over a field $\mathbb K$. The state space is $V$, the input
space is $U$, and the output space is $Y$.

## 1. Reachability without coordinates

Let $A:V\to V$ and $B:U\to V$ be linear. Define

$$\mathcal R(A,B)=\sum_{j\ge0}\operatorname{im}(A^jB).$$

The sum is a sum of subspaces, not a union. A vector in it is a finite
linear combination of input directions and their iterates. In Lean,
`⨆` expresses the supremum in the lattice of submodules, so closure under
addition and scalar multiplication is built into the definition.

First, $Bu\in\mathcal R(A,B)$ by taking $j=0$. Next,
$A(A^jBu)=A^{j+1}Bu$, so $\mathcal R(A,B)$ is $A$-invariant. Finally, if
$S$ contains $\operatorname{im}B$ and is $A$-invariant, induction gives
$A^jBu\in S$ for every $j,u$. Hence $\mathcal R(A,B)\subseteq S$.

This is the argument behind `reachable_invariant` and `reachable_minimal`.
It does not assume finite dimension.

## 2. Why feedback does not change the reachable space

Our feedback convention is $u=Kx+v$. The state map becomes $A+BK$, while
the new free input still acts through $B$.

If $x\in\mathcal R(A,B)$, then

$$(A+BK)x=Ax+B(Kx)\in\mathcal R(A,B).$$

Thus $\mathcal R(A,B)$ contains the input image and is invariant under
$A+BK$. Minimality gives
$\mathcal R(A+BK,B)\subseteq\mathcal R(A,B)$. Apply the same argument to
the pair $(A+BK,B)$ with feedback $-K$ to obtain the reverse inclusion.

This proves equality of reachable spaces. It does not say that every
feedback is stabilizing.

## 3. Coordinate changes

Suppose $F:V\to W$ satisfies $FA=A'F$ and $FB=B'$. Then $F$ sends
reachable states for $(A,B)$ into reachable states for $(A',B')$.

For an invertible state change $z=ex$, choose

$$A'=eAe^{-1},\qquad B'=eB.$$

Apply the intertwining result to $e$ and $e^{-1}$ to get

$$\mathcal R(A',B')=e\mathcal R(A,B).$$

The orientation follows from `z = e x`. Choosing `x = e z` would reverse
the order of the conjugation.

## 4. The finite Kalman criterion

Now assume $n=\dim V<\infty$. For any power $X^j$, divide by the monic
characteristic polynomial $\chi_A$:

$$X^j=q(X)\chi_A(X)+r(X),\qquad\deg r<n.$$

Cayley--Hamilton gives $\chi_A(A)=0$. Therefore

$$A^j=r(A)=\sum_{i=0}^{n-1}r_iA^i.$$

Apply the equality to $Bu$. Each $A^jBu$ lies in the span of the first
$n$ input blocks. The opposite inclusion is immediate, so

$$\mathcal R(A,B)=\sum_{i=0}^{n-1}\operatorname{im}(A^iB).$$

The formal proof handles the zero-dimensional case separately. This
matters because the natural degree of the zero polynomial is zero in
Lean, and a strict bound `natDegree < 0` would be false.

The linear Kalman map is

$$\mathcal K_n(u_0,\ldots,u_{n-1})=\sum_{i=0}^{n-1}A^iBu_i.$$

Its image is exactly that finite span. Thus algebraic controllability is
equivalent to surjectivity of $\mathcal K_n$.

## 5. Observability and duality

For $C:V\to Y$, define

$$\mathcal N(A,C)=\bigcap_{j\ge0}\ker(CA^j).$$

This is the largest $A$-invariant subspace inside $\ker C$. Observability
means $\mathcal N(A,C)=\{0\}$.

Let $V^*$ be the algebraic dual. The transpose sends $\ell$ to
$A^*\ell=\ell\circ A$. A covector annihilates the reachable space exactly
when

$$\ell(A^jBu)=0\qquad\text{for every }j,u.$$

That is precisely
$B^*(A^*)^j\ell=0$. Consequently,

$$\mathcal R(A,B)^\circ=\mathcal N(A^*,B^*).$$

Algebraic duals separate vectors and subspaces over a field. Hence the
left side is zero exactly when the reachable space is all of $V$.
This proves controllability/observability duality. No inner product is
used, and no conjugate transpose is hidden in the notation.

## 6. The PBH eigenvector criterion

Assume $\mathbb K$ is algebraically closed and $V$ is finite dimensional.
An eigenvector satisfying $Ax=cx$ and $Cx=0$ belongs to
$\mathcal N(A,C)$ because $CA^jx=c^jCx=0$.

Conversely, if $\mathcal N(A,C)$ is nonzero, restrict $A$ to that invariant
subspace. Over an algebraically closed field, the restriction has a
nonzero eigenvector. This eigenvector is invisible to $C$, contradicting
the eigenvector test. Thus

$$\mathcal N(A,C)=\{0\}
\iff \bigl(Ax=cx,\ Cx=0\bigr)\Longrightarrow x=0.$$

Applying duality gives the PBH test

$$\mathcal R(A,B)=V
\iff \bigl(\ell\circ A=c\ell,\ \ell\circ B=0\bigr)
\Longrightarrow\ell=0.$$

All values of $c$ in the algebraically closed field are considered. A
test involving only real eigenvalues of a real system can miss complex
modes. The present theorem does not formalize complexification of an
arbitrary real system.

## 7. The explicit stabilization example

For the double integrator, $A(x,y)=(y,0)$ and $Bu=(0,u)$. The directions
$Bu=(0,u)$ and $ABu=(u,0)$ already span the state space.

The feedback $u=-2x-3y$ gives

$$x'=y,\qquad y'=-2x-3y.$$

For $E(x,y)=5x^2+2xy+y^2$, direct differentiation gives

$$E'=-4(x^2+y^2)\le-\frac23E.$$

The last inequality uses $E\le6(x^2+y^2)$. The weighted energy
$e^{2t/3}E(x(t),y(t))$ has nonpositive derivative and is therefore
nonincreasing. Dividing by the positive exponential gives the decay
estimate in the README. The lower and upper bounds on $E$ then give the
explicit squared-state estimate.

The theorem assumes a differentiable trajectory satisfying the equations.
It contains no numerical simulation or floating-point approximation.
