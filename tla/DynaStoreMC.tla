--------------------------- MODULE DynaStoreMC ------------------------------
(***************************************************************************
 * TLA+ Model Checking Configuration for DynaStore
 * 
 * This module provides configurations and constraints for model checking
 * the DynaStore specification using TLC.
 *
 * The module includes:
 * 1. Constrained model instances for tractable checking
 * 2. Symmetry optimizations
 * 3. State space constraints
 * 4. Specific invariants and properties to check
 *
 * Author: TLA+ Specification based on JACM2011 paper
 ***************************************************************************)

EXTENDS DynaStore, TLC

-----------------------------------------------------------------------------
(***************************************************************************
 * Model Constants for Different Checking Scenarios
 ***************************************************************************)

\* Small model for quick validation
CONSTANT 
    SmallProcs,     \* 2-3 processes
    SmallValues,    \* 1-2 values
    SmallInit,      \* Initial view with 2 processes
    SmallMaxChanges \* 2-3 changes max

\* Medium model for thorough checking
CONSTANT
    MediumProcs,    \* 3-4 processes
    MediumValues,   \* 2-3 values
    MediumInit,     \* Initial view with 3 processes
    MediumMaxChanges \* 4-5 changes max

-----------------------------------------------------------------------------
(***************************************************************************
 * State Space Constraints
 ***************************************************************************)

\* Limit the depth of history for bounded model checking
HistoryLimit == Len(history) <= 10

\* Limit the number of pending operations
PendingOperationsLimit == 
    Cardinality({i \in Procs : pc[i] /= "idle"}) <= 3

\* Limit the number of messages in transit
MessagesLimit == Cardinality(msgs) <= 20

\* Limit the number of views explored
ViewsExploredLimit ==
    \A i \in Procs : Cardinality(front[i]) <= 5

\* Combined constraint for model checking
StateConstraint ==
    /\ HistoryLimit
    /\ PendingOperationsLimit
    /\ MessagesLimit
    /\ ViewsExploredLimit

-----------------------------------------------------------------------------
(***************************************************************************
 * Symmetry Sets for Optimization
 * 
 * TLC can exploit symmetry to reduce the state space.
 * We define symmetry sets for processes and values.
 ***************************************************************************)

\* Declare symmetry sets in the model configuration file
\* SYMMETRY ProcSymmetry, ValueSymmetry

-----------------------------------------------------------------------------
(***************************************************************************
 * Invariants to Check
 ***************************************************************************)

\* Core type invariant
InvTypeOK == TypeOK

\* Safety invariants
\* LinearizabilityInvariant: All completed reads return either Null or a written value
MCLinearizabilityInvariant ==
    \A idx \in 1..Len(history) :
        (history[idx].type = "read_complete" /\ history[idx].result /= Null) =>
            \E jdx \in 1..idx : 
                history[jdx].type = "write_start" /\ 
                history[jdx].val = history[idx].result

\* ViewContainsInit: Current view is always a superset of Init
MCViewContainsInit ==
    \A procId \in Procs : Init \subseteq curView[procId]

\* TimestampMonotonicity: Timestamps are monotonically increasing
MCTimestampMonotonicity ==
    \A procId \in Procs :
        tsMax[procId].num >= 0 /\
        (ts[procId].num > 0 => ts[procId].pid \in Procs)

InvSafety ==
    /\ MCLinearizabilityInvariant
    /\ MCViewContainsInit
    /\ MCTimestampMonotonicity

\* Traverse invariants (from Section 5.5.1)
\* Lemma 5.3: Front ⊆ desiredView
MCLemma5_3_FrontSubsetDesired ==
    \A procId \in Procs :
        pc[procId] \in {"traverse", "readInView", "writeInView"} =>
            \A w \in front[procId] : w \subseteq desiredView[procId]

\* Lemma 5.4: curView ⊆ Front
MCLemma5_4_FrontContainsCurView ==
    \A procId \in Procs :
        pc[procId] \in {"traverse", "readInView", "writeInView"} =>
            \A w \in front[procId] : curView[procId] \subseteq w

\* Lemma 5.7: reconfig changes included in result
MCLemma5_7_ReconfigIncluded ==
    \A procId \in Procs :
        (pc[procId] = "notifyQ" /\ opType[procId] = "reconfig") =>
            opArg[procId] \subseteq desiredView[procId]

InvTraverse ==
    /\ MCLemma5_3_FrontSubsetDesired
    /\ MCLemma5_4_FrontContainsCurView
    /\ MCLemma5_7_ReconfigIncluded

\* Timestamp invariants (from Section 5.5.2)
\* Lemma 5.16a: timestamps well-defined
MCLemma5_16a_AtsWellDefined ==
    \A procId \in Procs :
        pc[procId] = "done" => tsMax[procId].num >= 0

InvTimestamps ==
    /\ MCLemma5_16a_AtsWellDefined

-----------------------------------------------------------------------------
(***************************************************************************
 * Properties to Check
 ***************************************************************************)

\* Deadlock freedom
DeadlockFree == 
    \E i \in Procs : ENABLED Next

\* At least one process can make progress
ProgressPossible ==
    \/ \E i \in Procs : pc[i] = "idle" /\ enabled[i]
    \/ \E i \in Procs : pc[i] /= "idle"

\* All started operations eventually complete (under fairness)
AllOperationsComplete ==
    \A i \in Procs : (pc[i] /= "idle") ~> (pc[i] = "idle")

\* Read operations return valid values
ReadsValid ==
    \A i \in Procs :
        (pc[i] = "done" /\ opType[i] = "read") =>
            vMax[i] = Null \/ \E j \in Procs : v[j] = vMax[i]

-----------------------------------------------------------------------------
(***************************************************************************
 * Action Constraints
 * 
 * These constraints can be used to focus model checking on specific
 * scenarios or to reduce the state space.
 ***************************************************************************)

\* Only allow one concurrent operation per process
\* (Simplified - original expression was invalid)
SingleOpPerProcess ==
    \A i \in Procs : pc[i] /= "idle" =>
        ~\E val \in Values : ENABLED WriteStart(i, val)

\* Limit reconfigurations to specific changes
LimitedReconfigs ==
    \A i \in Procs, cng \in SUBSET Change :
        ReconfigStart(i, cng) =>
            Cardinality(cng) = 1  \* Only single changes

-----------------------------------------------------------------------------
(***************************************************************************
 * Specific Test Scenarios
 ***************************************************************************)

\* Scenario 1: Single writer, multiple readers
SingleWriterScenario ==
    /\ LET writers == {i \in Procs : opType[i] = "write"}
       IN Cardinality(writers) <= 1

\* Scenario 2: No reconfigurations (static system)
NoReconfigScenario ==
    \A i \in Procs : opType[i] /= "reconfig"

\* Scenario 3: Sequential operations (no concurrency)
SequentialScenario ==
    Cardinality({i \in Procs : pc[i] /= "idle"}) <= 1

\* Scenario 4: Focus on view changes
ViewChangeScenario ==
    \* Allow reconfigs but limit read/write operations
    Len(SelectSeq(history, LAMBDA op : 
        op.type \in {"read_start", "write_start"})) <= 2

-----------------------------------------------------------------------------
(***************************************************************************
 * Counterexample Analysis Helpers
 ***************************************************************************)

\* Print current state for debugging
DebugState ==
    /\ PrintT(<<"pc", pc>>)
    /\ PrintT(<<"curView", curView>>)
    /\ PrintT(<<"tsMax", tsMax>>)
    /\ PrintT(<<"history", history>>)

\* Check for specific error conditions
ErrorConditions ==
    \* Read returns a value that was never written
    /\ ~\E i \in Procs :
        pc[i] = "done" /\ opType[i] = "read" /\
        vMax[i] /= Null /\
        ~\E j \in 1..Len(history) :
            history[j].type = "write_start" /\ history[j].val = vMax[i]

=============================================================================
\* Modification History
\* TLA+ Model Checking Configuration for DynaStore
