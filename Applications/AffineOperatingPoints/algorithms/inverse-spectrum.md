# Prescribing the spectrum with two gains

Every finite union of closed rational intervals and rays is the exact
spectrum of a weakly connected floorless max-affine network with gains
$2$ and $3$ and nonnegative rational offsets. This includes singletons,
the empty set, and all of $\mathbb R$. Every real level is feasible for
the same network's relaxed inequalities.

Here the spectrum consists of levels $\lambda$ such that
$F(x)=x+\lambda\mathbf 1$ for some real vector $x$. The forward
[policy theorem](../../../Maths/Multitubes/MaxAffine/PolicySpectrum.lean#L201-L221)
represents the spectrum as a finite union of policy-level sets. Each
[policy-level set](../../../Maths/Multitubes/MaxAffine/PolicySpectrum.lean#L140-L151)
is closed and convex. The construction below gives an inverse in the
two-gain subclass. The definitions of
[eigenvalues and relaxation levels](../../../Maths/Multitubes/MaxAffine/Spectrum.lean#L165-L183)
fix the convention for $\lambda$.

## Constructing and solving the network

Sort the input intervals and merge overlaps and touching endpoints.
Use one sink coordinate $y$. For each bounded open gap, and for each
finite outer bound, add one coordinate $x_i$ with self-loops and one
arc to the sink. The sink has a gain-$3$ loop and the common rule

$$
F_y(x,y)=\max\bigl(3y,\max_i(2x_i+d_i)\bigr).
$$

All source equations have a unique solution at a fixed level. Once
these values are fixed, the sink equation requires $y\le\lambda/2$
and $2x_i+d_i\le y+\lambda$ for all $i$. It is solvable exactly when
$2x_i+d_i\le 3\lambda/2$ for all $i$, in which case $y=\lambda/2$
works.

| Restriction | Source rule $F_i(x_i)$ | Arc offset $d_i$ | Forced $x_i$ |
| --- | --- | --- | --- |
| Exclude $(c-r,c+r)$ | $\max(2x_i+c,3x_i+c)$ | $(3c+r)/2$ | $\min(\lambda-c,(\lambda-c)/2)$ |
| Require $\lambda\ge a$ | $3x_i$ | $a/2$ | $\lambda/2$ |
| Require $\lambda\le b$ | $2x_i$ | $-b/2$ | $\lambda$ |

In the gap row, put $t=\lambda-c$. The difference
$2x_i+d_i-3\lambda/2=(r-|t|)/2$ gives the exclusion and retains both
endpoints. For the other rows the differences are $(a-\lambda)/2$
and $(\lambda-b)/2$. Together the rows cut out exactly the prescribed
union. For the empty set use $a=1$ and $b=0$. For the whole line use a
gap row with $c=r=0$, imposing no restriction while retaining both gains.
Every outer source is adjacent to the common sink in the underlying
undirected graph.

For each branch $z\mapsto sz+d$, replace $d$ by $d+(s-1)T$ using
$T=\max(0,\max_{\text{branches}} -d/(s-1))$. This conjugates the
operator by the change of coordinates $x\mapsto x-T\mathbf 1$,
preserves every level, and makes all offsets nonnegative. For an
admitted level use the forced source values and $y=\lambda/2$, then
subtract $T$ from every coordinate. To witness relaxation at **any**
level, first lower each unshifted source value to at most
$(3\lambda/2-d_i)/2$. Every source inequality survives lowering its
coordinate because its self-loop gains exceed one. Keep $y=\lambda/2$
and apply the same shift. The implementation computes these ceilings
directly in the shifted coordinates.

For example,
$F(x,y)=(\max(2x,3x),\max(3y,2x+1/2))$ excludes precisely $(-1,1)$.
The vector $(\min(\lambda,\lambda/2),\lambda/2)$ witnesses every level
outside that open gap.

Adding the return branch $2y$ at the first coordinate makes the graph
strongly connected. Every real level then has an eigenvector. In
particular $(-1/3,-1/6)$ is a fixed point at level zero.
[Strong connectivity and the full-spectrum classification](strongly-connected.md)

## Why two gains suffice and one cannot do this in general

For a common gain $s\ne1$, every coordinate is a nonempty maximum
of branches and $F(x+t\mathbf 1)=F(x)+st\mathbf 1$. Translating any
existing eigenvector moves its level by $(s-1)t$, so a nonempty spectrum
is the whole line. The corresponding
[Lean result](../../../Maths/Multitubes/MaxAffine/Spectrum.lean#L327-L351)
assumes strong connectivity to obtain an initial eigenvector.
For common gain $1$, the map is monotone and additively homogeneous,
hence nonexpansive in the sup norm. If $x,y$ have levels
$\lambda,\mu$, compare $F(x)$ to $F(y+C\mathbf 1)$ with
$C=\max_i(x_i-y_i)$ and use a coordinate attaining $C$ to get
$\lambda\le\mu$. Reversing the two vectors gives equality. Thus a
single gain cannot realize a proper spectrum with two or more levels.

Sergeev's Theorem 3.1 realizes finite systems of bounded intervals
and points for the two-sided max-plus pencil
$A\otimes x=\lambda\otimes B\otimes x$. Here the operator has one
affine maximum per coordinate, fixed gains $2,3$, and one shared sink.
[Sergeev, *Every System of Intervals Is a Spectrum*](https://www.kybernetika.cz/content/2011/5/715/paper.pdf)

## Run the compiler

Use JSON pairs with `null` for infinity and strings for exact rational
endpoints. Sorting costs $O(k\log k)$ comparisons for $k$ input pairs.
The scan, network construction, and individual witness construction
use $O(k)$ rational operations. The output uses the adjacent
fixed-level solver's `vertices`, `branches`, and `level` fields.

```sh
printf '%s\n' '[[null,-1],[1,null]]' > gap.json
python3 inverse_spectrum.py gap.json --level 0 > network.json
python3 affine_spectrum.py --input network.json
python3 inverse_spectrum.py gap.json --witness 1
```

Use `--relaxation-witness` for inequality witnesses. The stdlib
compiler and the independent checker are linked below. The checker
uses Z3 to eliminate all vector coordinates and compare the resulting
formula against the raw interval input over **all real levels**, for
both equations and inequalities.

[Compiler](inverse_spectrum.py) · [Z3 checker](inverse_spectrum_check.py)

The separate sources above give a short formula for each forbidden gap. A second
construction realizes the same sets with exactly two strongly connected components,
even when the target consists of many disjoint intervals. [Two-component theorem and compiler](two-components.md)
