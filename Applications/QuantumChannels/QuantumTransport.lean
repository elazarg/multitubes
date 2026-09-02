/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import QuantumTransport.Discard

/-!
# Quantum transport

This is the umbrella module for transport by finite-dimensional Kraus maps and
for the discard-channel obstruction to residual reversal.

## Main definitions

* `QuantumTransport.krausMap` - a heterogeneous finite Kraus map.
* `QuantumTransport.ofKrausFamily` - transport by edgewise Kraus maps.
* `QuantumTransport.discard` - the two-to-one-dimensional discard channel on
  positive cones.

## Main results

* `QuantumTransport.walkMap_le_of_lax_or_exact` - propagation of lower bounds.
* `QuantumTransport.le_walkMap_of_oplax_or_exact` - propagation of upper bounds.
* `QuantumTransport.not_exists_discardResidual` - the discard edge cannot be
  reversed by an order residual.

## Tags

quantum channel, Kraus map, transport, Löwner order, residual
-/
