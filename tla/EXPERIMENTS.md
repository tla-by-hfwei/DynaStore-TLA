# TLC Model Checking Experiments for DynaStore

This guide provides comprehensive instructions for running TLC model checking experiments on the DynaStore TLA+ specification.

## Prerequisites

1. **TLA+ Tools**: Download from https://github.com/tlaplus/tlaplus/releases
2. **Java**: JRE 11 or later
3. **Memory**: Minimum 4GB RAM recommended, 8GB+ for larger models

## Quick Start

### Running from Command Line

```bash
# Navigate to the tla directory
cd tla/

# Run basic WeakSnapshot check
java -jar tla2tools.jar -config WeakSnapshot.cfg WeakSnapshot.tla

# Run basic DynaStore check  
java -jar tla2tools.jar -config DynaStore.cfg DynaStore.tla
```

### Running from TLA+ Toolbox

1. Open TLA+ Toolbox
2. Create a new spec from `DynaStore.tla` or `WeakSnapshot.tla`
3. Create a new model with the configurations below
4. Run TLC model checker

---

## Experiment 1: Weak Snapshot Basic Properties

**Goal**: Verify PR1-PR4 properties of Weak Snapshot (Algorithm 1)

### Configuration

```
CONSTANTS:
    P = {p1, p2, p3}
    Values = {v1, v2}

INVARIANTS:
    TypeOK
    Integrity          \* PR1
    ValidityInvariant  \* PR2

CONSTRAINT:
    Len(ops) <= 6

SPECIFICATION: Spec
```

### Expected Results
- States: ~10,000-50,000
- Time: < 1 minute
- Violations: None expected

### Variations to Try

1. **2 Processes**: Reduce P to {p1, p2} for faster checking
2. **3 Values**: Add v3 to Values for more state coverage
3. **Longer History**: Increase constraint to Len(ops) <= 8

---

## Experiment 2: Weak Snapshot Monotonicity

**Goal**: Verify PR3 (monotonicity of scans)

### Configuration

```
CONSTANTS:
    P = {p1, p2}
    Values = {v1}

INVARIANTS:
    TypeOK

PROPERTIES:
    []MonotonicityCheck(ops)

CONSTRAINT:
    Len(ops) <= 8

SPECIFICATION: Spec
```

### Key Check
Verify that if scan σ1 returns C1 and scan σ2 (invoked after σ1 completes) returns C2, then C1 ⊆ C2.

---

## Experiment 3: Weak Snapshot Non-Empty Intersection

**Goal**: Verify PR4 (common element in all non-empty scans)

### Configuration

```
CONSTANTS:
    P = {p1, p2, p3}
    Values = {v1, v2, v3}

INVARIANTS:
    TypeOK

PROPERTIES:
    []NonEmptyIntersectionCheck(ops)

CONSTRAINT:
    Len(ops) <= 6

SPECIFICATION: Spec
```

### Key Check
All non-empty scan results share at least one common value.

---

## Experiment 4: DynaStore Type Safety

**Goal**: Basic type checking and deadlock freedom

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 2

INVARIANTS:
    TypeOK
    ViewContainsInit
    TimestampMonotonicity

CONSTRAINT:
    /\ Len(history) <= 6
    /\ Cardinality(msgs) <= 10

CHECK_DEADLOCK: TRUE
SPECIFICATION: Init_State /\ [][Next]_vars
```

### Expected Results
- States: ~50,000-200,000
- Time: 1-5 minutes
- No deadlocks (unless process not in view halts)

---

## Experiment 5: DynaStore Read/Write Operations

**Goal**: Verify basic read/write behavior without reconfiguration

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1, v2}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 2

INVARIANTS:
    TypeOK
    LinearizabilityInvariant
    ViewContainsInit

ACTION CONSTRAINT:
    \* Disable reconfig operations
    \A i \in Procs : opType'[i] /= "reconfig"

CONSTRAINT:
    Len(history) <= 8

SPECIFICATION: Init_State /\ [][Next]_vars
```

### Key Check
Reads return either ⊥ or a previously written value.

---

## Experiment 6: DynaStore with Reconfigurations

**Goal**: Verify safety with dynamic reconfiguration

### Configuration

```
CONSTANTS:
    Procs = {p1, p2, p3}
    Values = {v1}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 3

INVARIANTS:
    TypeOK
    ViewContainsInit
    DesiredViewContainsCurrent
    Lemma5_3_FrontSubsetDesired
    Lemma5_4_FrontContainsCurView

CONSTRAINT:
    /\ Len(history) <= 6
    /\ Cardinality(msgs) <= 15

SPECIFICATION: Init_State /\ [][Next]_vars
```

### Expected Results
- States: ~100,000-500,000
- Time: 5-15 minutes
- Verify that view invariants are maintained

---

## Experiment 7: Lemma Verification

**Goal**: Check key lemmas from Section 5.5

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 3

INVARIANTS:
    TypeOK
    Lemma5_3_FrontSubsetDesired
    Lemma5_4_FrontContainsCurView
    Lemma5_7_ReconfigIncluded
    Lemma5_16a_AtsWellDefined

CONSTRAINT:
    Len(history) <= 8

SPECIFICATION: Init_State /\ [][Next]_vars
```

### Key Lemmas Checked
- Lemma 5.3: Front ⊆ desiredView
- Lemma 5.4: curView ⊆ Front
- Lemma 5.7: reconfig changes included in result
- Lemma 5.16a: timestamps well-defined

---

## Experiment 8: Liveness Under Fairness

**Goal**: Verify termination properties

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 2

PROPERTIES:
    \* All operations eventually complete (under fairness)
    \A i \in Procs : (pc[i] /= "idle") ~> (pc[i] = "idle")

CONSTRAINT:
    Len(history) <= 6

SPECIFICATION: FairSpec  \* Spec with fairness
```

### Important Note
Liveness checking requires fairness constraints and may take longer.

---

## Experiment 9: Sequential Operations Scenario

**Goal**: Verify correctness with no concurrency

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1, v2}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 2

INVARIANTS:
    TypeOK
    LinearizabilityInvariant

ACTION CONSTRAINT:
    \* At most one operation at a time
    Cardinality({i \in Procs : pc'[i] /= "idle"}) <= 1

CONSTRAINT:
    Len(history) <= 10

SPECIFICATION: Init_State /\ [][Next]_vars
```

### Expected Results
- Much smaller state space
- Useful for debugging basic operation flow

---

## Experiment 10: Stress Test with Maximum Concurrency

**Goal**: Find corner cases with high concurrency

### Configuration

```
CONSTANTS:
    Procs = {p1, p2, p3}
    Values = {v1, v2}
    Init = {[type |-> "Add", proc |-> p1], 
            [type |-> "Add", proc |-> p2],
            [type |-> "Add", proc |-> p3]}
    MaxChanges = 4

INVARIANTS:
    TypeOK
    ViewContainsInit

CONSTRAINT:
    /\ Len(history) <= 10
    /\ Cardinality(msgs) <= 30

SPECIFICATION: Init_State /\ [][Next]_vars
```

### Performance Tips
- Use symmetry reduction for Procs and Values
- Consider running overnight for thorough coverage
- Use multiple worker threads: `-workers 4`

---

## Advanced Experiment: Linearizability Check

**Goal**: Full linearizability verification

### Approach
1. Run TLC to generate traces
2. Use external linearizability checker on history
3. Or verify simplified linearizability invariant in TLC

### Configuration

```
CONSTANTS:
    Procs = {p1, p2}
    Values = {v1}
    Init = {[type |-> "Add", proc |-> p1], [type |-> "Add", proc |-> p2]}
    MaxChanges = 2

INVARIANTS:
    TypeOK
    LinearizabilityInvariant
    AtomicitySimplified

CONSTRAINT:
    Len(history) <= 8

SPECIFICATION: Init_State /\ [][Next]_vars
```

---

## Command Line Options

### Basic Run
```bash
java -jar tla2tools.jar -config DynaStore.cfg DynaStore.tla
```

### With Multiple Workers
```bash
java -jar tla2tools.jar -workers 4 -config DynaStore.cfg DynaStore.tla
```

### With More Memory
```bash
java -Xmx8g -jar tla2tools.jar -config DynaStore.cfg DynaStore.tla
```

### Simulation Mode (Random Traces)
```bash
java -jar tla2tools.jar -simulate -depth 100 DynaStore.tla
```

### Generate Counterexample Graph
```bash
java -jar tla2tools.jar -dump dot states.dot DynaStore.tla
```

---

## Interpreting Results

### Success Output
```
Model checking completed. No error has been found.
  Estimated reachable states: XXXXXX
  Distinct states found: XXXXXX
```

### Invariant Violation
```
Error: Invariant TypeOK is violated.
Error: The behavior up to this point is:
  STATE 1: <Initial State>
  STATE 2: ...
```

### Deadlock
```
Error: Deadlock reached.
```
For DynaStore, deadlock may be expected when a process is not in the current view (it halts).

---

## Troubleshooting

### Out of Memory
- Reduce model size (fewer processes, values, smaller constraints)
- Increase Java heap: `-Xmx16g`
- Use disk-based state storage

### Very Long Runtime
- Add tighter state constraints
- Use symmetry reduction
- Consider simulation mode for initial exploration

### Unexpected Violations
- Check if violation is due to simplifications in the spec
- Verify constants match intended semantics
- Review the trace to understand the scenario

---

## Summary Table

| Experiment | Focus | Procs | Values | States | Time |
|------------|-------|-------|--------|--------|------|
| 1 | WS Properties | 3 | 2 | ~10K | <1min |
| 2 | WS Monotonicity | 2 | 1 | ~5K | <1min |
| 3 | WS Intersection | 3 | 3 | ~50K | 1-2min |
| 4 | DS Type Safety | 2 | 1 | ~50K | 1-5min |
| 5 | DS R/W Only | 2 | 2 | ~100K | 2-5min |
| 6 | DS Reconfig | 3 | 1 | ~200K | 5-15min |
| 7 | DS Lemmas | 2 | 1 | ~100K | 3-10min |
| 8 | DS Liveness | 2 | 1 | ~50K | 5-20min |
| 9 | DS Sequential | 2 | 2 | ~20K | <1min |
| 10 | DS Stress | 3 | 2 | ~500K | 15-60min |

WS = WeakSnapshot, DS = DynaStore

---

## References

- TLA+ Hyperbook: https://lamport.azurewebsites.net/tla/hyperbook.html
- TLC Model Checker: https://lamport.azurewebsites.net/tla/tlc.html
- DynaStore Paper: JACM 2011
