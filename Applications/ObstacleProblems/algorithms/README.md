# Exact PV sizing with a fixed battery and a specified dispatch rule

Given hourly load and a solar-generation profile per unit of PV rating, compute all PV ratings at which a fixed battery changes from empty, to charging or discharging within its operating band, to full. Compute grid imports and spill as exact functions of PV rating, and invert the import curve to find the smallest rating meeting a prescribed energy budget. For a periodically repeated trace with standing losses, compute the steady-state cycle directly. A single setting needs one scalar replay for an assigned initial charge or two for a steady-state cycle. The complete response needs a linear-size sweep and one sort.

The [two-sided transfer summary](../../../Maths/Recursion/TwoSidedReflection.lean) gives exact forward composition, and the [clamped fixed-point theorem](../../../Maths/Recursion/ClampedAffineFixedPoint.lean) gives the initial charge of the periodic solution. These are formalized in Lean. The parameter sweep and its operation bounds below are derived from these facts and tested in Python.

## Run the solver on another trace

The CSV interface takes two columns named `load_kwh` and `yield_kwh_per_kw`. Each row is one interval. Values such as `0.125` or `1/8` are read as exact rationals. The finite default starts with a full battery. `--initial` sets other initial charge in kWh. Use `--periodic` with a per-interval `--retention` below one for the steady-state cycle.

```bash
python3 storage_csv.py storage_fixture.csv --capacity 1
python3 storage_csv.py storage_fixture.csv --capacity 1 --budget 1
python3 storage_csv.py storage_fixture.csv --capacity 1 --periodic --retention 9/10 --rating 2
```

The first command emits JSON with all knots and affine coefficient pairs `[slope, offset]`, followed by every interval's empty and full thresholds in chronological order. The two tails and each open knot interval use the corresponding affine pair, and values agree at shared knots. The second command returns the least nonnegative rating satisfying the import budget and the import and spill there. An unattainable budget returns a null rating. The last command evaluates the selected rating in the steady-state replay. JSON strings preserve the exact rationals and represent unbounded contact thresholds as `+inf` or `-inf`.

For a full, lossless battery, one threshold per generating interval describes the entire import curve. On a 96-hour household trace with 4 kWh of storage, the smallest multiplier of measured PV generation that holds imports to 10 kWh is exactly $3926/2377$. The metered example includes the input, attribution and an independent cut-based solver. [Threshold formula and metered example](metered-pv-hinges.md)

## Model and scope

For an intervention that changes supply at only one time, a separate index computes how much
shortage and spill change by a specified deadline. [Single-intervention algorithm](pulse-response.md)

For phase $i$, define
$$
 r_i(\theta)=a_i x_{i-1}(\theta)+b_i+w_i\theta,
 \qquad x_i(\theta)=\min(u_i,\max(l_i,r_i(\theta))).
$$
The gains $a_i$ and forcing coefficients $w_i$ are nonnegative, and $l_i\le u_i$. In the PV application $\theta\ge0$ is rated power in kW, $x_i$ is battery energy in kWh, $b_i$ is negative demand over the interval, $w_i$ is kWh generated per kW of rating in that interval, and $a_i$ is the retained fraction of the previous charge. With $l_i=0$, grid import or unserved demand is $(l_i-r_i)_+$ and spill or grid export is $(r_i-u_i)_+$. This is a PV-first greedy dispatch with standing losses, ideal charging and discharging, no power caps, and any fixed or preassigned time-varying energy bands. The example uses one constant band. Observation weights can apply import or export tariffs to the corresponding energy sum. The dispatch controls themselves are given by the recurrence.

The finite case allows an affine seed of nonnegative slope, including any fixed initial charge. The steady-state case solves $x_n=x_0$ when $\prod_i a_i<1$. Coefficients are rational in the prototype and can be real numbers in the arithmetic-operation bounds.

## Sweep

For $a_i>0$, write $x_i=A_i h_i+B_i\theta+C_i$ with
$$
 A_0=1,\quad B_0=C_0=0,\qquad
 (A_i,B_i,C_i)=(a_i A_{i-1},a_i B_{i-1}+w_i,a_i C_{i-1}+b_i).
$$
Before clipping, the physical value is $A_i h_{i-1}+B_i\theta+C_i$. Keep the unchanged affine pieces of $h_{i-1}$ in parameter order in a deque, so the new affine transformation takes constant work. A zero gain instead empties the deque and starts the frame at $(A_i,B_i,C_i)=(1,w_i,b_i)$ with the single input line $h=0$.

Inductively $x_i$ and $r_i$ are continuous nondecreasing functions of $\theta$. For a noncollapsed band, $r_i\le l_i$ is a closed left tail and $r_i\ge u_i$ is a closed right tail. Either tail can be empty or the whole line. For the left tail, pop pieces from the left while their right endpoints have $r_i\le l_i$. The first retained piece either excludes the tail altogether or gives its endpoint by a single affine solve. Replace the popped and truncated region by the normalized affine line for $l_i$. Mirror the operation for the right tail. Checking the weak inequalities when popping yields the last parameter of an equality plateau at the lower obstacle and the first one at the upper obstacle. When $l_i=u_i$, the output is in contact with both obstacles for every parameter. The two successive clamps still give the correct positive losses.

There are at most four new pieces per positive-gain phase, including copies of the two partly trimmed pieces. Each pop charges a previous creation, and each phase visits at most two pieces that it decides to keep during its endpoint searches. This gives $O(n)$ arithmetic operations and space for all contact thresholds and the terminal response. The explicit lists of affine pieces for all $x_i$ can have quadratic total size. For example, take $x_0=0$, $a_i=w_i=1$, $b_i=i$, and band $[0,n^2+1]$. At stage $i$ a new lower breakpoint appears at $-i$, and all lower breakpoints $-i+1,\ldots,-1$ survive. The upper clipping occurs strictly after $-1$. An implementation that rescans each full representation visits $(n^2+3n-2)/2$ pieces.

### Exact import, spill, and weighted storage curves

Every piece or part of a piece removed by the lower trim contributes the affine function $l_i-r_i$ on its deleted parameter interval. The upper trim contributes $r_i-u_i$ on its removed intervals. Using the lower-clipped value $\max(l_i,r_i)$ for the upper trim gives the same positive upper excess because $l_i\le u_i$. Fully eliminated pieces each contribute once. Partly eliminated pieces contribute once per endpoint trim. Thus across all phases there are $O(n)$ affine contributions supported on intervals to each loss sum. Phase-dependent observation weights just scale these contributions. Accumulate coefficient changes at their parameter endpoints, sort, and take one prefix sum to get each exact continuous piecewise-affine curve in $O(n\log n)$ arithmetic operations and $O(n)$ memory.

For a weighted storage sum $\sum_i c_i x_i$, the $B_i\theta+C_i$ contributions accumulate directly, and a surviving normalized piece contributes its same line throughout a contiguous range of phases. On deletion, scale the line by the sum of $c_i A_i$ over these phases via a prefix sum. Its birth and death each cost constant work, including when a trimmed piece is replaced with a shorter copy. This gives the same bound for weighted storage. One can evaluate any resulting curve or its left and right derivatives in $O(\log n)$ operations. Nonnegative observation weights give a nonincreasing import curve and a nondecreasing spill or storage curve. An inverse budget query binary-searches the values at knots and then solves one affine equation, taking $O(\log n)$ operations.

The comparison-sorting bound for emitting all ordered knots is sharp in general: zero-capacity steps with unit forcing produce $\sum_i (d_i-\theta)_+$, whose ordered knots sort arbitrary distinct loads $d_i$. If only one inverse query is required, sorting can be avoided in principle. Write the continuous monotone curve as one affine function plus a hinge at each coefficient-change event. Evaluate at a median active hinge location, discard the half on the far side of the desired root, and absorb every discarded hinge on the left into the affine function. Keep equality in the left search so the output is the first crossing even on a plateau. Linear-time median selection and geometric shrinkage give $O(n)$ arithmetic operations after fragment generation. The prototype implements the sorted curves and inverse binary search.

### Periodic replay

For each fixed $\theta$, composition of the clamped-affine steps gives
$$
 F_\theta(x)=\operatorname{clip}_{[L(\theta),U(\theta)]}
  (A x+B\theta+C),\qquad A=\prod_i a_i.
$$
Here $B,C$ are the ordinary slope and shift acquired in a single composition of the unclamped parts. Composition uses the identity
$$
 \operatorname{clip}_{I}(\operatorname{clip}_{[L,U]}(x))
  =\operatorname{clip}_{[\operatorname{clip}_{I}(L),\operatorname{clip}_{I}(U)]}(x)
$$
and the fact that a nonnegative affine map pushes the inner clip endpoints forward. This is the composition algebra in the Multitubes `ClampedAffineSummary`. Its fixed-point formula gives $x_0^*=\operatorname{clip}_{[L,U]}(z)$ for $z=(B\theta+C)/(1-A)$ and $0\le A<1$. Indeed, if $z<L$ then $A L+B\theta+C\le L$, and if $z>U$ then $A U+B\theta+C\ge U$. In the interior, the unconstrained fixed point is unchanged. Thus $F_\theta(z)=x_0^*$, already the exact seed. Start the deque from the affine line $z$, sweep the phases once to compute this seed for every parameter, then sweep them again with the observations enabled. For all parameter values, including at a contact tie, the second pass is exactly the cyclic orbit. The preprocessing bounds do not depend on how close $A$ is to 1, as arithmetic-operation counts.

There is also a lossless cyclic extension. When $A=1$, put $d(\theta)=B\theta+C$. The fixed set is $\{L\}$ for $d<0$, $\{U\}$ for $d>0$, and $[L,U]$ for $d=0$. Obtain $L$ and $U$ with forward sweeps starting from the first phase's lower and upper obstacles respectively, then make a second pass for each endpoint. Select the resulting loss curves on the two half-lines separated by the zero of $d$, or one branch if $d$ has constant sign or vanishes identically. At $d=0$, if $L<U$, no fixed orbit has a strictly clipped phase. Strict clipping makes the entire composition locally constant in its seed, while the composition is the identity on $[L,U]$. This holds at the endpoints too, by the one-sided intersection with the interval. All choices therefore give the same losses at zero drift, even if the chosen state jumps. This extension is a mathematical result here. The executable periodic mode takes $A<1$.

## Prior work and the added result

Brett J. Donnellan's 2022 thesis derives a critical-capacity formula at fixed PV rating and uses a decomposition to estimate the opposite axis, grid-sourced energy as a function of PV rating. Sections 1.6 and 2.1 use a full initial battery, perfect efficiency and no power limits, and equations (2.2)–(2.5) give the finite recurrence above. Section 2.6.3 explicitly identifies the exact fixed-storage PV-rating relation as the missing counterpart to the storage-capacity expression. An exact finite piecewise-affine curve answers that question for the stated dispatch assumptions. The thesis's separate smooth approximation may still be useful for differentiable economic modeling. [Donnellan, *Household Energy System Sizing Technique*, §§1.6, 2.1 and 2.6.3](https://digital.library.adelaide.edu.au/items/8ab09436-24ec-4147-ad5b-d0e6bb189001).

The open-chain add-affine-and-clip deque is the same algorithmic kernel that Johnson and Kolmogorov, Pock and Rolínek use for quadratic-unary total variation denoising. Dividing each $x_i$ and its band by $A_i$ gives their derivative recurrence, where the phase update adds $(b_i+w_i\theta)/A_i$ before clipping. KPR §4.1 already obtains all clipping thresholds using a lazy slope representation and amortized end deletion. Two-sided Skorokhod maps also give explicit min-max forward formulas for a fixed driving path; the moving-band formula includes the gain-one case. [Johnson, dynamic programming for the fused lasso](https://doi.org/10.1080/10618600.2012.681238), [Kolmogorov, Pock and Rolínek, Figure 3 and §4.1](https://arxiv.org/pdf/1502.07770), [Burdzy, Kang and Ramanan, Theorem 2.6](https://arxiv.org/abs/0712.2863).

Classical parametric max flow is another exact alternative for the ideal lossless case. A time path has affine supply arcs of capacity $\theta w_i$, fixed load arcs, and carry arcs of battery capacity. A full initial battery is extra constant supply into the first phase. Maximum served load agrees with greedy discharge-first operation. To see this, if cumulative served energy is $S$ and storage is $x$, greedy preserves domination of both $S$ and $S+x$ over any feasible dispatch. After supply $g$ and demand $D$, the new served amount is $\min(S+D,S+x+g)$, and the new served-plus-stored amount is $\min(S'+u,S+x+g)$. This proves optimality by induction. In the cut formulation, nested cuts can also be written as one quadratic chain-TV problem. Related storage-sizing approaches use energy decomposition and reliability models across capacities; modeled storage tools such as PyPSA expose standing loss and cyclic state of charge. The demonstrated additions are the all-phase import and spill fragment sums and their exact steady-state extension under standing losses, using one pass to compute the seed and one pass to observe its orbit. [Gallo, Grigoriadis and Tarjan, *A Fast Parametric Maximum Flow Algorithm and Applications*](https://www.cs.princeton.edu/techreports/1987/105.pdf), [Yuan, Wei and Yang, reliability-oriented storage sizing](https://www.sciencedirect.com/science/article/pii/S0960148126006233), [PyPSA storage model](https://docs.pypsa.org/v1.0.5/user-guide/optimization/storage/).

Run the [exact checks](check_obstacle_sweep.py) with `python3 check_obstacle_sweep.py` from this directory. They compare the [solver](obstacle_sweep.py) with scalar replay and independently constructed piecewise-affine curves. The CSV entry point and the checks use the Python standard library. The complexity estimates count rational arithmetic operations. Numerator and denominator lengths can grow with the trace.
