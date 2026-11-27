# Exact import hinges for a fixed, ideal battery

For hour $i$, let $d_i\ge0$ be demand and $g_i\ge0$ generation per unit of the PV multiplier $\theta\ge0$. Start with a full battery of usable capacity $E\ge0$. The horizon is finite, with free terminal charge. Storage is lossless and has unrestricted charge and discharge power. Set
$$
s_0=E,\qquad r_i(\theta)=s_{i-1}(\theta)+\theta g_i-d_i,\qquad
s_i(\theta)=\min(E,\max(0,r_i(\theta))).
$$
Grid import is $I(\theta)=\sum_i(-r_i(\theta))_+$. There is a threshold $\tau_i\ge0$ for each generating hour such that
$$
I(\theta)=I_\infty+\sum_{i:g_i>0} g_i(\tau_i-\theta)_+ .
$$
Thus each positive knot removes some of the marginal benefit of additional PV, and there are at most as many knots as hours with $g_i>0$. All threshold weights are the measured or modeled hourly generation values.

## Time-path cut and threshold proof

Give time vertex $i$ incoming source capacity $\theta g_i$, outgoing sink capacity $d_i$, and carry capacity $E$ on each arc $i\to i+1$. Give vertex 1 an additional incoming source capacity $E$. For source-side indicators $z_i$, the cut cost is
$$
C_\theta(z)=\sum_i [\theta g_i(1-z_i)+d_i z_i]+E(1-z_1)+
 E\sum_{i=1}^{n-1}(z_i-z_{i+1})_+.
$$
Write $p_i(0),p_i(1)$ for the two prefix cut minima with the final side specified. For $i>1$ they obey
$$
p_i(0)=\theta g_i+\min(p_{i-1}(0),p_{i-1}(1)+E),\qquad
p_i(1)=d_i+\min(p_{i-1}(0),p_{i-1}(1)).
$$
Their difference $\delta_i=p_i(0)-p_i(1)$ starts at $\theta g_1-d_1+E$, then obeys $\delta_i=\theta g_i-d_i+\min(E,\max(0,\delta_{i-1}))$. In particular, $\delta_i=r_i$. If $m_i=\min(p_i(0),p_i(1))$, then $m_i=m_{i-1}+d_i+\min(0,\delta_i)$, also at $i=1$ with $m_0=0$. Consequently $\min_z C_\theta(z)=\sum_i d_i-I(\theta)$.

Each $\delta_i(\theta)$ is continuous and nondecreasing. A minimizing cut is recovered by choosing $z_n=1$ exactly when $\delta_n>0$, and, working backward, $z_i=1$ exactly when $\delta_i>E(1-z_{i+1})$. At equality this chooses the smaller state, yielding the inclusion-minimal optimal source side by backward induction. The source sides grow with $\theta$, since the test for each $z_i$ is increasing in $\theta$ and in $z_{i+1}$. Thus $z_i=1$ for almost every $\theta>\tau_i$, and $z_i=0$ for almost every $\theta<\tau_i$.

If some hour generates, use $\Theta=\max_{g_i>0}(d_i+E)/g_i$. For $\theta>\Theta$ every $g_i>0$ has $\delta_i>E$, so these hours have entered the source side. For $\theta\ge\Theta$ each generating hour also ends with a full battery. With the initially full battery this gives the constant
$$
I_\infty=\sum_R\left(\sum_{i\in R}d_i-E\right)_+ ,
$$
where $R$ runs over maximal zero-generation intervals, including any initial and final ones. With no generation take $\Theta=0$. The whole horizon is one zero-generation interval and $I$ is constant. Away from the finitely many crossings of distinct affine cut costs, the derivative of the minimum cut value is $\sum_i g_i(1-z_i)$. Integrating the negative of this derivative from $I_\infty$ proves the formula, including ties by continuity. Thresholds at zero contribute no positive knots. With $E=0$ one can immediately take $\tau_i=d_i/g_i$ for every $g_i>0$.

## Convex characterization and extraction

For $\Theta>0$, choose any minimizer over $[0,\Theta]^n$ of
$$
\sum_i\left(\frac{g_i x_i^2}{2}-d_i x_i\right)+E x_1+
 E\sum_{i=1}^{n-1}(x_{i+1}-x_i)_+ .
$$
Set $z_i(t)=\mathbf1_{t>x_i}$. The objective is the integral from 0 to $\Theta$ of $C_t(z(t))-C_t(\mathbf1)$. For the directed pair term this follows by integrating $\mathbf1_{x_i<t\le x_{i+1}}$; the unary terms follow by integrating $tg_i-d_i$ on $[0,x_i)$. The nested optimal cuts attain the integral of the pointwise minima, so any minimizer has optimizing levels almost everywhere. All minimizers agree on every coordinate with $g_i>0$ by strict convexity in those coordinates. If $\Theta=0$, the boxed problem fixes all thresholds at zero.

The clipping sweep also computes the thresholds directly. For $E>0$, let $a_i$ be the right endpoint of $\{\delta_i\le0\}$ and $b_i$ the left endpoint of $\{\delta_i\ge E\}$, using extended-real endpoints for empty or unbounded tails before clipping to $[0,\Theta]$. Then $a_i\le b_i$. Starting with $\tau_n=a_n$, use $\tau_i=\min(b_i,\max(a_i,\tau_{i+1}))$ in reverse order. Indeed, for successor 1 choose state 1 above $a_i$ and choose state 0 on a zero plateau. For successor 0 choose state 1 above $b_i$, including any $E$-equality plateau above that endpoint. These are minimizing choices even on the plateaus, and the two tests combine into the stated clamp. Isolated endpoint choices have no effect on the integral. With the clipping deque, this gives the unsorted hinges in $O(n)$ arithmetic operations and space. Sorting the distinct positive thresholds gives ordered knots and an upper-budget inverse by binary search and one affine solve.

The time-path construction is an application of monotone parametric max flow. The quadratic problem uses the submodular coarea extension, and its edge term is ordinary chain total variation plus a linear endpoint term since $u_+=(|u|+u)/2$. KPR’s quadratic-chain clipping and backward pass give the relevant algorithmic kernel. The exact hinge representation answers the fixed-storage, variable-PV relation posed in Donnellan §2.6.3 for the ideal dispatch in §§1.6 and 2.1. His decomposition was intended to supply a differentiable approximation for investment modeling, whereas the exact relation is generally piecewise affine. [Gallo, Grigoriadis and Tarjan (1989)](https://doi.org/10.1137/0218003), [Chambolle and Darbon (2009), Remark 3.2](https://escholarship.org/uc/item/5sd211v1), [Kolmogorov, Pock and Rolínek (2016), Figure 3 and §4.1](https://arxiv.org/pdf/1502.07770), [Donnellan (2022)](https://hdl.handle.net/2440/136631).

## Metered household example

The [96-hour excerpt](opsd_residential3_may2017.csv) uses the CoSSMic household `DE_KN_residential3` in the Open Power System Data 2020-04-15 release. For each of the three cumulative counters `DE_KN_residential3_pv`, `DE_KN_residential3_grid_import`, and `DE_KN_residential3_grid_export`, difference the 97 consecutive readings from May 1, 2017 00:00 UTC through May 5, 2017 00:00 UTC. Each output row corresponds to the hour starting at its earlier reading. None of the three fields is marked interpolated at the selected endpoints. The output uses measured PV increments and inferred load $\Delta\text{import}+\Delta\text{PV}-\Delta\text{export}$. Every increment and inferred load is nonnegative. The sums are 63.131 kWh PV and 52.885 kWh load. Attribution follows the package’s requested author-date form. Open Power System Data. 2020. *Data Package Household Data*. Version 2020-04-15. The primary source for this excerpt is CoSSMic. The adaptation differences the cumulative counters and combines three feeds into inferred hourly load. The data are licensed under CC BY 4.0. [OPSD household data and provenance](https://data.open-power-system-data.org/household_data/2020-04-15/), [Dataset metadata](https://data.open-power-system-data.org/household_data/2020-04-15/datapackage.json), [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

With a full 4 kWh battery, modeled grid import is 48.885 kWh at $\theta=0$, 13.867 kWh at $\theta=1$, and 9.172 kWh at $\theta=2$. There are 22 positive knots and the floor is 3.081 kWh, reached at $698/9$. For the illustrative 10 kWh import budget, the relevant segment is $I(\theta)=13.926-2.377\theta$ on $(224/163,743/347)$. The smallest feasible multiplier is $3926/2377$, about **1.65166 times the recorded PV generation profile**, with import exactly 10 kWh by independent replay. The multiplier is dimensionless and the example applies to the measured four days under the specified dispatch.

Run `python3 pv_cut_check.py` to reproduce the exact figures from the excerpt. The [checker](pv_cut_check.py) compares the hinge formula, the two-state cut minimum and scalar replay on the metered trace at 71 rational parameters. On 2,577 tiny traces it also explicitly enumerates all cuts, with 24,460 exact parameter comparisons. To regenerate the excerpt, download the [source CSV](https://data.open-power-system-data.org/household_data/2020-04-15/household_data_60min_singleindex.csv) and run `python3 pv_cut_check.py --source SOURCE.csv`.

| File | SHA-256 |
|---|---|
| Upstream `household_data_60min_singleindex.csv` | `15956440b27465686eae2abf5895cbc3dab80f934a891bcb2f4f944428e97d60` |
| Excerpt `opsd_residential3_may2017.csv` | `252c41228c717b1b2f7162998a67bbe623d0da19ef35127c8ee34253a1cb41ee` |

The [production sweep cross-check](pv_sweep_crosscheck.py) maps the measured `pv_kwh` field to forcing per unit of the dimensionless multiplier. Run `python3 pv_sweep_crosscheck.py` to verify all 22 positive knots, the entire nonnegative import curve, and the exact 10 kWh inverse against the production sweep.
