# Operating points of max-affine networks

Each channel reports the largest of several affine responses to other channels. An
operating point at offset $\lambda$ is a vector of real readings for which the difference
between the reported value and the input reading equals $\lambda$ at every channel. The inputs and
offsets can have either sign. The positive and zero gains describe monotone responses.

- Given the network and an offset, decide whether an operating point exists. The solver
  returns the readings or a certificate that they cannot exist. A feasible set of upper
  bounds on the responses can still leave some channel strictly below its required value.
  [Decision algorithm and certificate verifier](algorithms/affine-spectrum.md)
- Given the desired set of offsets, construct a network that has an operating point
  at exactly those offsets. Any finite union of closed rational intervals, including
  isolated points and unbounded rays, is realizable using only gains 2 and 3.
  Even two strongly connected components suffice, independent of the number of intervals.
  [Single-sink construction](algorithms/inverse-spectrum.md) · [Two-component compiler and eigenvector counts](algorithms/two-components.md)
- When every channel can reach every other, compute the whole spectrum in one linear
  program. It is a singleton, a closed upper ray, or the whole real line.
  [Strong connectivity and the full-spectrum algorithm](algorithms/strongly-connected.md)
- If every cycle has positive gains whose product exceeds one, the operating points at
  each level of a strongly connected network have a finite description. A partial order
  records which tight cycles must be selected together. A selection determines every real
  reading. The index can also find the greatest operating point compatible with specified
  measurement ranges. [Representation and counting complexity](algorithms/counting-operating-points.md) ·
  [Measurement-box solver](algorithms/measurement-boxes.md)
- With both a contracting cycle and an expansive cycle in a strongly connected positive-gain
  network, decide whether a feasible level has finitely many operating points or a continuum.
  In the latter case the solver identifies a channel that can vary continuously and its full
  interval of attainable readings. [Finite or continuous operating points](algorithms/mixed-cycle-fibres.md)
- Given a missing operating level and a choice of new connections, compute every intercept
  that repairs the level for each proposed connection. The query index assumes gains above
  one and at least one incoming and outgoing branch at each vertex.
  [One-connection repair algorithm](algorithms/connection-retuning.md)

One return connection can fill a whole gap. Take two channels with responses
$F_1=\max(2x,3x)$ and $F_2=\max(3y,2x+1/2)$. The admissible offsets are exactly
$(-\infty,-1]\cup[1,\infty)$. Feed $2y$ back as a third input to the first channel
and every real offset becomes admissible. At the previously excluded offset zero,
the readings $(-1/3,-1/6)$ reproduce themselves at both channels.

The first question uses the library's propagation of lower bounds and of tight coordinates.
The second gives a converse to its finite union of policy intervals. [Reachable lower
bounds](../../Maths/Multitubes/MaxAffine/ReachableLowerBounds.lean) ·
[Policy intervals](../../Maths/Multitubes/MaxAffine/PolicySpectrum.lean)
