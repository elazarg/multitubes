# Exact edge-deletion sensitivity for linear quivers

For a rooted linear quiver with $n$ vertices, $m$ edges, and stalk dimensions at most $d$, computing the dimensions of the compatible-section spaces after **every** individual edge deletion takes $O((n+m)d^3\log(2n))$ arithmetic operations over an ordered field. A separate index works over any field and supports sets of $k$ deletions in time polynomial in $k,d,\log(2n),\log(2+m)$ after near-linear preprocessing for fixed $d$. Both methods allow singular maps, heterogeneous stalks, and failures that break reachability from the original root.

Sumray, Harrington and Nanda’s *Quiver Laplacians and Feature Selection*, §§2–4 and Appendix A, identifies globally compatible features with sections of a linear quiver and studies the effect of removing edges. Proposition A.1(a) uses spectral interlacing. The index here represents the exact post-deletion zero eigenspace when the rooted hypothesis holds. The single-deletion batch computes its dimension. The paper's feature quivers can have several source components, so the bound with one small root need not apply to a particular instance. [Quiver Laplacians and Feature Selection](https://people.maths.ox.ac.uk/nanda/source/HarmSel.pdf)

The [rooted section theorem](../../../Maths/Multitubes/Exact.lean) determines each vertex value by forward transport along a chosen root path. The algorithms below use that identity and ordinary linear algebra. Python computes the deletion profiles and checks them against independent rank calculations. The complexity bounds are proved in this note.

## Tree coordinates

Let $X_v$ be the stalk at $v$, with $d_v=\dim X_v$ and $d=\max(1,\max_v d_v)$. Each edge $e:u\to v$ has a linear map $A_e:X_u\to X_v$ and asserts $x_v=A_e x_u$. Some vertex $r$ reaches every vertex. Choose any spanning out-arborescence $T$ rooted at $r$ and write $P_{a,v}:X_a\to X_v$ for the tree composition from an ancestor $a$ to $v$, including $P_{v,v}=I_v$. Parallel edges have separate IDs and a loop uses both incidences at the same vertex. The bounds count field arithmetic with ordinary small-matrix multiplication and Gaussian elimination.

For an assignment $x=(x_v)$, set
$$
z_r=x_r,\qquad z_v=x_v-A_{p(v)\to v}x_{p(v)}\quad(v\ne r),
$$
using the selected tree edge into $v$. This triangular change of coordinates is invertible even for rectangular or singular maps. Recursion down the tree gives $x_v=\sum_{a\preceq v} P_{a,v}z_a$, where $a\preceq v$ denotes ancestry including equality. For a set $F$ of deleted edges, let $S$ consist of $r$ and the target of each deleted tree edge. The coordinates in $S$ are the only free variables before checking the surviving non-tree edges.

For a non-tree edge $e:u\to v$, let $D_{e,-}=-A_e$ and $D_{e,+}=I_v$ denote its source and target incidence maps. Both incidences are present when $u=v$. Its residual in the coordinate $z_a$ is
$$
B_{e,a}=\mathbf 1_{a\preceq u}D_{e,-}P_{a,u}
       +\mathbf 1_{a\preceq v}D_{e,+}P_{a,v}.
$$
An inactive term is the appropriately shaped zero. The surviving section space is isomorphic to the kernel of the stack of $[B_{e,a}]_{a\in S}$ over $e\in E\setminus(T\cup F)$. The width is at most $(|F|+1)d$. A tree sweep recovers a full section from a kernel vector in $O(nd^2)$ operations.

When $F=\varnothing$, the root value determines the section. Seigal, Harrington and Nanda establish the arborescence section isomorphism in Proposition 1.6 and compute sections of arbitrary quivers in Theorem 5.1 by tree reduction. Here the coordinate system is fixed before failures. Each failed tree edge releases one new coordinate and preserves the root-only columns, which allows computations across failures to share work. The root-value argument is the linear instance of Multitubes’ `Transport.IsRootedSection.walkMap_eq` in `Maths/Multitubes/Exact.lean`. [Principal Components along Quiver Representations](https://arxiv.org/pdf/2104.10666)

## All single deletions over an ordered field

Let $C_e=B_{e,r}$ for each non-tree edge, let $C$ stack those blocks, and set $G=C^\top C$. For a single non-tree deletion $e$, the dimension is $d_r-\operatorname{rank}(G-C_e^\top C_e)$. For a single tree-edge deletion into $s$, stack $B_{e,s}$ over all non-tree edges to obtain $B_s$. The dimension is
$$
d_r+d_s-\operatorname{rank}
\begin{pmatrix}G&M_s\\M_s^\top&H_s\end{pmatrix},
\qquad M_s=C^\top B_s,\qquad H_s=B_s^\top B_s .
$$
Over an ordered field, $\ker R=\ker R^\top R$ since $\sum_i(Ry)_i^2=0$ implies every $(Ry)_i=0$. The same identity uses conjugate transpose over $\mathbb C$. Over $\mathbb F_2$, two copies of the row $[1]$ instead give Gram matrix zero and rank one for the original stack.

Initialize all accumulators to zero. For each non-tree edge $e:u\to v$, add $C_e^\top C_e$ to $G$. For each incidence $i\in\{-,+\}$ with endpoint $b$, add $C_e^\top D_{e,i}$ to $M_b$ and $D_{e,i}^\top D_{e,i}$ to $H_b$. At $a=\operatorname{LCA}(u,v)$, add $L^\top R+R^\top L$ to $H_a$, where $L=D_{e,-}P_{a,u}$ and $R=D_{e,+}P_{a,v}$.

In reverse tree order, for every child $b$ of $a$, add $M_bP_{a,b}$ to $M_a$ and $P_{a,b}^\top H_bP_{a,b}$ to $H_a$. An endpoint incidence contributes to precisely the ancestors of its endpoint, and its local term is pulled to those ancestors by composition. A cross term contributes to precisely the common ancestors, reached by depositing it at the least common ancestor. Expanding $B_{e,s}^\top B_{e,s}$ gives these two endpoint squares and their cross term. The sweep therefore produces all of the required blocks.

Binary lifting supplies tree products and least common ancestors in $O(\log(2n))$ operations on maps or indexes per edge. The sweep and ranks take $O((m+n)d^3)$ further field operations, and the input, tables and accumulators take $O((m+n\log(2n))d^2)$ field elements. With integer entries of absolute value at most $2^b$ and tree height $h$, Gram entries have $O((h+1)(b+\log(2d))+\log(2+2m))$ bits before rank computation. The arithmetic bounds allow rational coefficients of varying bit length. Computing the Gram matrix in ordinary floating point can lose numerical rank information.

## A multiple-deletion index over any field

Give vertices a depth-first preorder number. Each subtree is an interval, and a balanced segment tree provides canonical intervals. For an interval $I$ in this segment tree, let $a_I$ be the LCA of the vertices in $I$. A parent interval's anchor is an ancestor of each child anchor.

For each non-tree edge $e:u\to v$ and each pair of canonical intervals $I\ni u,\ J\ni v$, store the edge ID and the row space of
$$
R_{e,I,J}=[D_{e,-}P_{a_I,u}\ \ D_{e,+}P_{a_J,v}]
$$
in bucket $(I,J)$. Each block has at most $d$ rows and $2d$ columns. Process edges by ID. Build a balanced tree on the ordered entries of each nonempty bucket, storing at every node a basis for the sum of row spaces underneath. For preprocessing, compute a coefficient for each canonical interval covering an endpoint by starting at its leaf and composing once per step toward the interval-tree root. The anchor-to-child-anchor maps are precomputed with binary lifting.

Given $F$, split preorder at the endpoints of the subtrees rooted in $S$ and split those pieces into disjoint canonical intervals $\mathcal I$. On each $I\in\mathcal I$, the set of active ancestors from $S$ is the same across all vertices. It is exactly the set of $a\in S$ ancestral to $a_I$, since an ancestor of every vertex is an ancestor of their LCA and an ancestor of the LCA is an ancestor of every vertex. Form
$$
U_I:(z_a)_{a\in S}\longmapsto\sum_{\substack{a\in S\\a\preceq a_I}} P_{a,a_I}z_a.
$$
Every vertex $v\in I$ receives $P_{a_I,v}U_I(z)$ by composition. Every edge with endpoints in the selected intervals $I,J$ therefore contributes the rows of $R_{e,I,J}\binom{U_I}{U_J}$. Right multiplication by the common stacked map commutes with taking row spans, so compressed bucket bases suffice. Each edge belongs to exactly one selected bucket.

A bucket containing failed non-tree edges is queried through its internal tree. Locate the failed IDs by binary search and decompose the surviving ID intervals into canonical nodes. Use the bases of those nodes. A bucket with no failed IDs uses its root basis. Incremental elimination of the pulled-back rows returns a basis in the free coordinates. Its kernel represents exactly all post-deletion sections.

```text
preprocess:
    choose a rooted out-tree and build ancestor products
    build the preorder segment tree, LCA anchors, and anchor-to-child-anchor products
    for each non-tree edge in edge-ID order:
        compose each endpoint incidence up its canonical interval chain
        append the pulled-back block to each pair of endpoint intervals
    build an edge-ID segment tree of row-space bases within each nonempty bucket

query(F):
    free = root and targets of failed tree edges
    selected = canonical cover after splitting preorder at free subtree boundaries
    construct the coordinate map to each selected anchor
    assign each failed non-tree edge to its unique pair of selected intervals
    for each ordered pair of selected intervals with a bucket:
        get its basis blocks excluding failed IDs
        pull the blocks to the free coordinates and insert into one row basis
    return the free coordinate labels and their row basis
```

Let $\ell_n=1+\lceil\log_2 n\rceil$, $\ell_m=1+\lceil\log_2(1+m)\rceil$, $p=|S|\le k+1$ and $q=|F\setminus T|$. There are $O(m\ell_n^2)$ bucket entries and $O(n\ell_n)$ anchor and ancestor-product operations on maps or indexes. Building the bases costs $O((m+n)d^3\ell_n^2)$ arithmetic and uses $O((m+n)d^2\ell_n^2)$ field elements. A query selects $O(p\ell_n)$ intervals and retrieves $O(p^2\ell_n^2+q\ell_m)$ basis blocks of at most $2d$ rows each. Multiplying each block by its common map and applying incremental elimination costs $O(p^2d^3)$, giving
$$
O\bigl(d^3p^2(p^2\ell_n^2+q\ell_m)\bigr)
$$
field operations, including the anchor maps. The prototype uses a hash table for bucket lookup. Sorting bucket keys and using binary search gives deterministic lookups, with up to one extra logarithm in ordinary index comparisons per lookup. A one-vertex graph and zero-dimensional stalks use the same formulas with empty blocks.

Over an ordered field, a second multiple-deletion index stores transported Gram sums. Use the four ordered pairs of the two incidences of each check edge, including the two self-pairs. The $(a,b)$ block of the queried Gram matrix is the rectangle sum over the subtrees of $a,b$. Pull each canonical rectangle sum back by the two anchor maps and subtract the individual Gram terms of the failed non-tree edges. The same preprocessing bound applies, with $O(d^3(p^2\ell_n^2+qp(\ell_n+p)+p^3))$ field operations per query. This variant is implemented in the same checker.

## Baselines and scope

**Repeated rooted solve.** For each deletion, build the reduced residual stack in the same tree coordinates. The comparator stops each scan when it reaches full rank. Its worst-case bound for all single deletions is $O(m^2d^3\log(2n))$ with binary lifting.

**One global elimination.** Let $A$ be the original coboundary matrix, with row blocks indexed by edges, and let $K$ have columns forming a basis for $\ker A^\top$. If $D$ is the set of deleted row indices and $K_D$ its coordinate restriction, then
$$
\dim\ker A_{\overline D}=\dim\ker A+|D|-\operatorname{rank}K_D .
$$
The rank lost equals the dimension of the intersection of $\operatorname{im} A$ with the vectors supported on $D$. In those coordinates, that intersection is the kernel of $K_D^\top$. One elimination followed by small block ranks thus handles the batch regardless of rootability. The prototype builds fundamental dependencies by sparse elimination and inserts their restrictions into the individual edge bases as it finds them, avoiding a dense dual-basis allocation. The benchmark uses child-before-parent column order to limit fill in the tree equations. Sparse elimination with little fill can be fast. With a precomputed real row-space projector, use $(I-A(A^\top A)^\dagger A^\top)_{DD}=K_DK_D^\top$ for an orthonormal $K$. Hansen and Ghrist §6 uses a related pseudoinverse expression for effective resistance and spectral sparsification of cellular sheaves. [Toward a Spectral Theory of Cellular Sheaves](https://arxiv.org/abs/1808.01513)

**Sparse rank algorithms.** Casacuberta and Kyng’s §4 and §5.1 give expected $\widetilde O(N^{2.2131})$ arithmetic for general sparse finite-field rank and nullspace at matrix dimension $N$, including homology applications. Both coboundary dimensions here can grow linearly with the number of vertices of a bounded-stalk sparse quiver. Generic explicit nullspace matrices can have quadratic storage dimensions. Fomin et al. give $O(w^3N)$ determinant and rank with a width-$w$ decomposition of the matrix graph. Rootability allows large treewidth. These are bounds for the cited algorithms in their stated regimes. They give no lower bound on a generic sensitivity algorithm. [Sparse finite-field rank and nullspace](https://arxiv.org/abs/2106.09830) · [Low-treewidth graph and matrix algorithms](https://arxiv.org/abs/1511.01379)

The tree equations alone have rank $\sum_{v\ne r}d_v$, because in the defect coordinates they project to all non-root stalks. This is linear in the vertex count when all stalk dimensions are positive. A sparse rank routine with a rank-dependent term, such as Cheung, Kwok and Lau’s $\widetilde O(\operatorname{nnz}(A)+\operatorname{rank}(A)^\omega)$ column-basis algorithm, can therefore still have a superlinear term here. If the diagram has few non-tree checks, direct rooted scans can also be appropriate. [Fast Matrix Rank Algorithms and Applications](https://arxiv.org/abs/1203.6705)

A graph sheaf can have arbitrary paired restrictions $X_u\to Y_e\leftarrow X_v$. Its incidence quiver, as defined in Multitubes' `Applications/CellularSheaves/CellularSheaves/GraphSheaf.lean`, can lack a root that reaches all vertices. When the target restrictions on selected tree edges are isomorphisms, solve them for forward transport. The remaining two-term restrictions can take the place of the non-tree residual incidences, with their dimensions included in $d$. For several source components, an artificial root carrying a direct sum of selected source stalks and projection edges gives the same section space with a potentially larger $d$. Failures in the original diagram can be queried with this root fixed.

## Prototype

Run `python3 quiver_faults.py` with NumPy available for exact seeded comparisons. The prototype accepts integer matrices and computes rational ranks using arbitrary-precision integers and fractions. The span index also supports reduction to a prime field. The tests include loops, parallel edges, zero-dimensional stalks, singular rectangular maps, and nested tree cuts. `python3 quiver_faults.py --benchmark` compares the batch, sparse dual and repeated rooted algorithms on synthetic workloads. [Checker and benchmark](quiver_faults.py)

For example, the first edge below is the tree edge. The second maps back to the root. Deleting either leaves one section parameter.

```python
from quiver_faults import Edge, SpanFaultOracle, Tree, gram_single_faults

edges = [Edge(0, 1, [[0]]), Edge(1, 0, [[2**32]])]
tree = Tree([1, 1], edges, [None, 0])
assert gram_single_faults(tree) == (0, {0: 1, 1: 1})
assert SpanFaultOracle(tree).dimension({0, 1}) == 2
```

Each edge matrix has shape `(target dimension, source dimension)`. The tree's parent array contains exactly one `None` at the root and the selected incoming edge ID at each other vertex. Edge IDs are zero-based indexes in the supplied list. For prime-field queries, pass the prime as `modulus` to `Tree` and use `SpanFaultOracle`.
