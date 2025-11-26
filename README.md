# DynaStore-TLA

TLA+ Specification of the **DynaStore** Protocol proposed by Aguilera et al. in the JACM 2011 paper: *"Dynamic Atomic Storage without Consensus"*.

## Overview

DynaStore is a groundbreaking distributed storage protocol that implements **atomic read/write registers** in a **dynamic environment** — supporting process additions and removals (reconfigurations) — **without requiring consensus**. This is significant because:

1. It proves that dynamic atomic storage is strictly weaker than consensus
2. It works in completely asynchronous systems with crash failures
3. It refutes the common belief that consensus is necessary for dynamic storage

## Paper Reference

> **"Dynamic Atomic Storage without Consensus"**  
> Marcos K. Aguilera, Idit Keidar, Dahlia Malkhi, and Alexander Shraer  
> *Journal of the ACM (JACM)*, Volume 58, Number 2, Article 7, April 2011

The original paper is available in the `refs/` directory.

## Repository Structure

```
DynaStore-TLA/
├── README.md                    # This file
├── refs/
│   └── JACM2011 Dynamic Atomic Storage without Consensus.pdf
└── tla/
    ├── README.md                # Detailed TLA+ specification documentation
    ├── EXPERIMENTS.md           # Model checking experiments guide
    ├── WeakSnapshot.tla         # Algorithm 1: Weak Snapshot
    ├── WeakSnapshot.cfg         # TLC config for WeakSnapshot
    ├── WeakSnapshotMC.tla       # WeakSnapshot model checking helpers
    ├── DynaStore.tla            # Algorithms 2 & 3: Main DynaStore protocol
    ├── DynaStore.cfg            # TLC config for DynaStore
    ├── DynaStoreMC.tla          # DynaStore model checking helpers
    ├── DynaStoreProperties.tla  # Safety & liveness properties
    └── DynaStoreTheorems.tla    # Correctness lemmas & theorems
```

## Key Concepts

### Weak Snapshot (Algorithm 1)

A novel abstraction weaker than atomic snapshots but sufficient for DynaStore:
- `update(c)`: Write a value to the snapshot
- `scan()`: Read all values written so far

Key property: All non-empty scans contain the "first" update value.

### DynaStore Protocol (Algorithms 2 & 3)

Three main operations:
- `read()`: Atomically read the register value
- `write(v)`: Atomically write value v to the register
- `reconfig(cng)`: Propose configuration changes (add/remove processes)

The protocol uses a **DAG of views** where each view represents a configuration state.

### Safety: Linearizability (Atomicity)

Every execution can be linearized — there exists a sequential ordering of operations that:
1. Preserves real-time order
2. Each read returns the most recently written value

### Liveness: Dynamic Service Liveness

Under proper failure conditions (majority of each view alive, finite reconfigurations):
1. All operations at active processes eventually complete
2. Enable events occur at newly added processes

## Quick Start

### Prerequisites
- TLA+ Toolbox or TLC command-line tools
- Java Runtime Environment (JRE 11+)

### Running Model Checking

```bash
cd tla/

# Check Weak Snapshot
java -jar tla2tools.jar -config WeakSnapshot.cfg WeakSnapshot.tla

# Check DynaStore
java -jar tla2tools.jar -config DynaStore.cfg DynaStore.tla
```

### Using TLA+ Toolbox
1. Open the TLA+ Toolbox
2. Create a new specification from `tla/DynaStore.tla`
3. Create a model with appropriate constants
4. Run the model checker

See `tla/EXPERIMENTS.md` for detailed experiment configurations.

## TLA+ Modules Overview

| Module | Description |
|--------|-------------|
| `WeakSnapshot.tla` | Implements the weak snapshot abstraction (PR1-PR5 properties) |
| `DynaStore.tla` | Main protocol with Traverse, ReadInView, WriteInView, ContactQ |
| `DynaStoreProperties.tla` | Linearizability (Def 3.1) and Dynamic Service Liveness (Def 3.2) |
| `DynaStoreTheorems.tla` | Lemmas 5.2-5.28 and Theorems 5.18, 5.28 from Section 5.5 |

## Correctness Results

### Theorem 5.18 (Atomicity)
DynaStore preserves linearizability.

### Theorem 5.28 (Liveness)
Under the liveness condition (Definition 3.2), all operations at active processes complete.

## Contributing

Contributions to improve the specification are welcome:
- Bug fixes in the TLA+ modules
- Additional invariants and properties
- Model checking optimizations
- Documentation improvements

## License

This TLA+ specification is provided for educational and research purposes.

## Authors

TLA+ Specification created based on the JACM 2011 paper by:
- Marcos K. Aguilera
- Idit Keidar
- Dahlia Malkhi
- Alexander Shraer

## See Also

- [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
- [TLA+ Toolbox](https://github.com/tlaplus/tlaplus)
- [Practical TLA+ Book](https://www.apress.com/gp/book/9781484238288)
