# TLA+ Specification of DynaStore Protocol

This directory contains the complete TLA+ specification of the **DynaStore** protocol, as proposed in the seminal paper:

> **"Dynamic Atomic Storage without Consensus"**  
> Marcos K. Aguilera, Idit Keidar, Dahlia Malkhi, and Alexander Shraer  
> *Journal of the ACM (JACM)*, Vol. 58, No. 2, Article 7, April 2011

## Overview

DynaStore is the first algorithm to solve the atomic read/write storage problem in a **dynamic setting without consensus** or stronger primitives. It operates in a completely asynchronous model where fault-tolerant consensus is impossible, proving that dynamic atomic storage is strictly weaker than consensus.

### Key Contributions of DynaStore

1. **No Consensus Required**: Unlike previous dynamic storage systems (RAMBO, etc.), DynaStore doesn't require agreement on the sequence of configuration changes.

2. **Weak Snapshots**: Introduces a novel weak snapshot abstraction that provides enough coordination for correctness without requiring full consensus.

3. **Dynamic Reconfiguration**: Supports adding and removing processes from the system while maintaining atomicity of read/write operations.

4. **Asynchronous Model**: Works in completely asynchronous systems with process crashes.

## Module Structure

### Core Specifications

| Module | Description |
|--------|-------------|
| `WeakSnapshot.tla` | Algorithm 1: Weak Snapshot abstraction implementation |
| `DynaStore.tla` | Algorithms 2 & 3: Main DynaStore protocol |
| `DynaStoreProperties.tla` | Safety and liveness properties (Definition 3.1, 3.2) |
| `DynaStoreTheorems.tla` | Lemmas and theorems from Section 5.5 |

### Model Checking Configurations

| Module | Description |
|--------|-------------|
| `WeakSnapshotMC.tla` | Model checking helpers for WeakSnapshot |
| `DynaStoreMC.tla` | Model checking helpers for DynaStore |
| `WeakSnapshot.cfg` | TLC configuration for WeakSnapshot |
| `DynaStore.cfg` | TLC configuration for DynaStore |

## Weak Snapshot (Algorithm 1)

The Weak Snapshot object provides two operations:
- `update_i(c)`: Writes value `c` to the snapshot
- `scan_i()`: Returns a set of values written to the snapshot

### Properties (PR1-PR5)

1. **PR1 (Integrity)**: Values returned by scan were written by update
2. **PR2 (Validity)**: Scans after completed updates return non-empty sets
3. **PR3 (Monotonicity)**: Later scans return supersets of earlier scans
4. **PR4 (Non-empty Intersection)**: All non-empty scans share a common element
5. **PR5 (Termination)**: Operations by majority processes complete

### Key Insight

The weak snapshot ensures that the "first" update is seen by all scans that see any updates, enabling a simpler implementation than atomic snapshot objects.

## DynaStore Protocol (Algorithms 2 & 3)

### Data Structures

```
State per process p_i:
  v_i           : Value received in WRITE message (initially ⊥)
  ts_i          : Timestamp for v_i (initially (0, ⊥))
  v_i^max       : Latest value observed in Traverse (initially ⊥)
  ts_i^max      : Timestamp for v_i^max (initially (0, ⊥))
  pickNewTS_i   : Should Traverse pick new timestamp? (initially FALSE)
  M_i           : Set of received messages (initially ∅)
  msgNum_i      : Message sequence number (initially 0)
  curView_i     : Current view (initially Init)
```

### Operations

#### Read Operation (Lines 12-16)
```
operation read_i():
  pickNewTS_i ← FALSE
  newView ← Traverse(∅, ⊥)
  NotifyQ(newView)
  return v_i^max
```

#### Write Operation (Lines 17-21)
```
operation write_i(v):
  pickNewTS_i ← TRUE
  newView ← Traverse(∅, v)
  NotifyQ(newView)
  return OK
```

#### Reconfig Operation (Lines 22-26)
```
operation reconfig_i(cng):
  pickNewTS_i ← FALSE
  newView ← Traverse(cng, ⊥)
  NotifyQ(newView)
  return OK
```

### Traverse Procedure

The Traverse procedure is the heart of DynaStore. It:
1. Traverses a DAG of views starting from `curView`
2. Discovers proposed configuration changes via weak snapshots
3. Transfers register state from view to view
4. Returns when reaching a stable view

### Message Handlers

- **REQ/REPLY**: Used for quorum-based read/write in views
- **NOTIFY**: Propagates completed view changes to other processes

## Safety Properties

### Linearizability (Definition 3.1)

A history σ is linearizable if:
1. It can be extended to a complete history σ'
2. There exists a sequential permutation π preserving real-time order
3. Operations in π satisfy the sequential specification

### Key Invariants

- Timestamps are monotonically increasing
- Views always contain the initial configuration
- Desired view is always a superset of current view

## Liveness Properties

### Dynamic Service Liveness (Definition 3.2)

If at every time t:
- Fewer than majority of view members have crashed or been removed
- Number of proposed changes is finite

Then:
1. Enable operations event occurs at every active process
2. Every operation at an active process eventually completes

## Correctness Theorems

### Theorem 5.18 (Atomicity)
DynaStore preserves linearizability (Definition 3.1).

**Proof Sketch:**
1. Order operations by associated timestamps
2. Lemma 5.17 ensures real-time order preservation
3. Lemma 5.16 ensures sequential specification satisfaction

### Theorem 5.28 (Liveness)
DynaStore preserves Dynamic Service Liveness (Definition 3.2).

**Proof Sketch:**
1. Lemma 5.26: NOTIFY reaches all active processes
2. Lemma 5.27: Traverse terminates under stable conditions
3. Under assumptions A1, A2, all operations complete

## Model Checking with TLC

### Prerequisites

- TLA+ Toolbox or command-line TLC
- Java Runtime Environment

### Running Model Checking

#### Weak Snapshot
```bash
# Using TLC command line
java -jar tla2tools.jar -config WeakSnapshot.cfg WeakSnapshot.tla
```

#### DynaStore
```bash
# Using TLC command line
java -jar tla2tools.jar -config DynaStore.cfg DynaStore.tla
```

### Suggested Experiments

1. **Small Model (Quick Validation)**
   - 2 processes, 1 value, 2 max changes
   - Check basic invariants and deadlock freedom

2. **Medium Model (Thorough Checking)**
   - 3 processes, 2 values, 4 max changes
   - Check linearizability and liveness

3. **Specific Scenarios**
   - Single writer scenario
   - Sequential operations
   - View change focus

See `EXPERIMENTS.md` for detailed experiment configurations.

## File Descriptions

| File | Lines | Description |
|------|-------|-------------|
| `WeakSnapshot.tla` | ~250 | Weak Snapshot implementation (Algorithm 1) |
| `DynaStore.tla` | ~500 | Main DynaStore protocol (Algorithms 2 & 3) |
| `DynaStoreProperties.tla` | ~250 | Safety/liveness properties |
| `DynaStoreTheorems.tla` | ~400 | Correctness lemmas/theorems |
| `DynaStoreMC.tla` | ~200 | Model checking configurations |
| `WeakSnapshotMC.tla` | ~100 | WeakSnapshot MC configurations |

## References

1. Aguilera, M.K., Keidar, I., Malkhi, D., and Shraer, A. (2011). Dynamic Atomic Storage without Consensus. *Journal of the ACM*, 58(2), Article 7.

2. Lamport, L. (1994). The TLA+ Specification Language. *DEC SRC Technical Note*.

3. Herlihy, M.P. and Wing, J.M. (1990). Linearizability: A Correctness Condition for Concurrent Objects. *ACM TOPLAS*, 12(3), 463-492.

## Author

TLA+ Specification created based on the JACM 2011 paper by Aguilera et al.

## License

This specification is provided for educational and research purposes