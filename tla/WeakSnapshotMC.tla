--------------------------- MODULE WeakSnapshotMC ---------------------------
(***************************************************************************
 * TLA+ Model Checking Configuration for Weak Snapshot
 * 
 * This module provides configurations for model checking the Weak Snapshot
 * specification (Algorithm 1) using TLC.
 *
 * Author: TLA+ Specification based on JACM2011 paper
 ***************************************************************************)

EXTENDS WeakSnapshot, TLC

-----------------------------------------------------------------------------
(***************************************************************************
 * Model Configuration Constants
 ***************************************************************************)

\* For model checking, we define constraints assuming the WeakSnapshot module
\* has P and Values set appropriately in the TLC model.

-----------------------------------------------------------------------------
(***************************************************************************
 * State Constraints
 ***************************************************************************)

\* Limit the length of operation history
HistoryConstraint == Len(ops) <= 8

\* Combined constraint
StateConstraint == HistoryConstraint

-----------------------------------------------------------------------------
(***************************************************************************
 * Invariants to Check
 ***************************************************************************)

\* Type invariant
InvTypeOK == TypeOK

\* Integrity (PR1): Values returned by scan come from updates
InvIntegrity == Integrity

\* Check that at most one write occurs per process
InvAtMostOneWrite ==
    \A i \in P : 
        LET updatesByI == SelectSeq(ops, LAMBDA op : 
                            op.type = "update" /\ op.proc = i)
        IN Len(updatesByI) <= 1

-----------------------------------------------------------------------------
(***************************************************************************
 * Properties to Check
 ***************************************************************************)

\* Monotonicity of scans
PropMonotonicity == MonotonicityCheck(ops)

\* Non-empty intersection of non-empty scans
PropNonEmptyIntersection == NonEmptyIntersectionCheck(ops)

\* Eventually some operation completes (liveness under fairness)
PropProgress ==
    \E i \in P : pc[i] = "idle" ~> \E j \in P : pc[j] /= "idle"

-----------------------------------------------------------------------------
(***************************************************************************
 * Test Scenarios
 ***************************************************************************)

\* Scenario: Only updates, no scans
UpdateOnlyScenario ==
    \A i \in 1..Len(ops) : ops[i].type = "update"

\* Scenario: Only scans, no updates
ScanOnlyScenario ==
    \A i \in 1..Len(ops) : ops[i].type = "scan"

\* Scenario: Alternating updates and scans
AlternatingScenario ==
    \A i \in 1..Len(ops)-1 :
        ops[i].type /= ops[i+1].type

=============================================================================
\* Modification History
\* TLA+ Model Checking Configuration for Weak Snapshot
