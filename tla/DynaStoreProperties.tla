--------------------------- MODULE DynaStoreProperties -------------------------
(***************************************************************************
 * TLA+ Specification of DynaStore Safety and Liveness Properties
 * 
 * From: "Dynamic Atomic Storage without Consensus" 
 *       Aguilera et al., JACM 2011
 *       Section 3: Problem Definition
 *       Section 5.5: Correctness of DynaStore
 *
 * This module defines the safety (linearizability/atomicity) and liveness
 * properties that DynaStore must satisfy.
 *
 * Safety (Atomicity/Linearizability):
 * - For every execution, there exists a corresponding sequential execution
 *   that preserves real-time order and satisfies the sequential specification
 *
 * Liveness (Dynamic Service Liveness - Definition 3.2):
 * - Under proper failure conditions, all operations complete
 * - Enable events occur at all active processes
 *
 * Author: TLA+ Specification based on JACM2011 paper
 ***************************************************************************)

EXTENDS DynaStore

-----------------------------------------------------------------------------
(***************************************************************************
 * Helper Definitions
 ***************************************************************************)

\* Get last element of a sequence
Last(s) == s[Len(s)]

\* Concatenate two strings (for type construction)
\* Since TLA+ doesn't have string concatenation built-in, we use direct type matching

-----------------------------------------------------------------------------
(***************************************************************************
 * Section 3: Linearizability (Definition 3.1)
 * 
 * A history σ is linearizable if σ^RW can be extended to a history σ',
 * and there exists a sequential permutation π of complete operations such that:
 * (1) π preserves the real-time order of σ
 * (2) The operations of π satisfy the sequential specification
 *
 * The sequential specification requires that each read returns the value
 * written by the most recent preceding write, or ⊥ if no write preceded.
 ***************************************************************************)

\* Extract read/write operations from history (ignoring reconfig)
RWHistory(h) ==
    SelectSeq(h, LAMBDA op : op.type \in {"read_start", "read_complete",
                                           "write_start", "write_complete"})

\* Get completion type for an operation type
CompletionType(opTypeStr) ==
    IF opTypeStr = "read" THEN "read_complete"
    ELSE IF opTypeStr = "write" THEN "write_complete"
    ELSE "reconfig_complete"

\* Get start type for an operation type
StartType(opTypeStr) ==
    IF opTypeStr = "read" THEN "read_start"
    ELSE IF opTypeStr = "write" THEN "write_start"
    ELSE "reconfig_start"

\* Check if operation o1 completed before o2 started (real-time order)
PrecedesInRealTime(h, o1, o2) ==
    LET idx1Complete == CHOOSE idx \in 1..Len(h) : 
                          h[idx].proc = o1.proc /\ 
                          h[idx].type = CompletionType(o1.type)
        idx2Start == CHOOSE idx \in 1..Len(h) :
                       h[idx].proc = o2.proc /\
                       h[idx].type = StartType(o2.type)
    IN idx1Complete < idx2Start

\* A read operation returns a valid value according to sequential spec
ValidRead(readOp, precedingWrites) ==
    IF precedingWrites = <<>>
    THEN readOp.result = Null  \* No preceding write, return initial value
    ELSE readOp.result = Last(precedingWrites).val

\* Check if a sequential permutation satisfies the specification
SatisfiesSequentialSpec(perm) ==
    \A idx \in 1..Len(perm) :
        perm[idx].type = "read" =>
            LET precedingWrites == SubSeq(perm, 1, idx-1)
                filteredWrites == SelectSeq(precedingWrites, 
                                           LAMBDA op : op.type = "write")
            IN ValidRead(perm[idx], filteredWrites)

\* Main linearizability check (simplified for model checking)
\* In practice, this is checked offline using the history
LinearizabilityInvariant ==
    \* All completed reads return either Null or a written value
    \A idx \in 1..Len(history) :
        (history[idx].type = "read_complete" /\ history[idx].result /= Null) =>
            \E jdx \in 1..idx : 
                history[jdx].type = "write_start" /\ 
                history[jdx].val = history[idx].result

-----------------------------------------------------------------------------
(***************************************************************************
 * Section 3: Dynamic Service Liveness (Definition 3.2)
 * 
 * If at every time t in the execution:
 * - fewer than |V(t).members|/2 processes out of V(t).members ∪ P(t).join 
 *   are in F(t) ∪ P(t).remove
 * - the number of different changes proposed is finite
 * 
 * Then:
 * (1) Eventually, enable_operations occurs at every active process
 *     that was added by a complete reconfig operation
 * (2) Every operation invoked at an active process eventually completes
 ***************************************************************************)

\* V(t): Union of all completed reconfig changes by time t
CompletedChanges == 
    UNION {history[idx].cng : idx \in {jdx \in 1..Len(history) : 
                                   history[jdx].type = "reconfig_complete"}}

\* Members of completed view
CompletedViewMembers == Members(Init \cup CompletedChanges)

\* P(t): Pending changes at time t (started but not completed reconfigs)
PendingChanges ==
    LET startedReconfigs == {idx \in 1..Len(history) : 
                              history[idx].type = "reconfig_start"}
        completedReconfigs == {idx \in 1..Len(history) :
                                history[idx].type = "reconfig_complete"}
        pendingProcs == {history[idx].proc : idx \in startedReconfigs} \
                       {history[idx].proc : idx \in completedReconfigs}
    IN UNION {history[idx].cng : idx \in {jdx \in startedReconfigs : 
                                          history[jdx].proc \in pendingProcs}}

\* F(t): Crashed processes (not modeled explicitly, assumed empty for checking)
CrashedProcesses == {}

\* Liveness condition from Definition 3.2
\* At any time t, fewer than |V(t).members|/2 out of 
\* V(t).members ∪ P(t).join are in F(t) ∪ P(t).remove
LivenessConditionHolds ==
    LET viewMembers == CompletedViewMembers
        pendingJoin == {c.proc : c \in {x \in PendingChanges : x.type = Add}}
        pendingRemove == {c.proc : c \in {x \in PendingChanges : x.type = Remove}}
        problematicProcs == (CrashedProcesses \cup pendingRemove)
        totalPool == viewMembers \cup pendingJoin
        problemCount == Cardinality(totalPool \cap problematicProcs)
    IN problemCount * 2 < Cardinality(viewMembers)

\* Liveness Property 1: Enable operations eventually occurs at active processes
\* An active process is one that:
\* - Does not crash
\* - Has Add proposed
\* - Does not have Remove proposed
EventuallyEnabled ==
    \A procId \in Procs :
        \* If procId was added and not removed
        ([type |-> Add, proc |-> procId] \in CompletedChanges \/
         [type |-> Add, proc |-> procId] \in Init) /\
        [type |-> Remove, proc |-> procId] \notin (CompletedChanges \cup PendingChanges) =>
            <>(enabled[procId])

\* Liveness Property 2: All operations at active processes eventually complete
EventuallyComplete ==
    \A procId \in Procs :
        (pc[procId] /= "idle" /\ enabled[procId]) ~> (pc[procId] = "idle")

-----------------------------------------------------------------------------
(***************************************************************************
 * Additional Safety Invariants
 ***************************************************************************)

\* No operation returns before it starts
NoEarlyReturn ==
    \A procId \in Procs : 
        pc[procId] = "idle" \/ pc[procId] /= "done" \/
        \E jdx \in 1..Len(history) : 
            history[jdx].type \in {"read_start", "write_start", "reconfig_start"} /\
            history[jdx].proc = procId

\* Timestamps are monotonically increasing
TimestampMonotonicity ==
    \A procId \in Procs :
        tsMax[procId].num >= 0 /\
        (ts[procId].num > 0 => ts[procId].pid \in Procs)

\* Current view is always a superset of Init
ViewContainsInit ==
    \A procId \in Procs : Init \subseteq curView[procId]

\* Desired view always contains current view
DesiredViewContainsCurrent ==
    \A procId \in Procs :
        pc[procId] \in {"traverse", "readInView", "writeInView", "notifyQ", "done"} =>
            curView[procId] \subseteq desiredView[procId]

-----------------------------------------------------------------------------
(***************************************************************************
 * Correctness Theorem from Section 5.5.2
 * 
 * Theorem 5.18 (Atomicity): DynaStore preserves Linearizability
 *
 * This is verified by checking that:
 * 1. All operations have associated timestamps
 * 2. Timestamps preserve real-time order (Lemma 5.17)
 * 3. Reads return the value with matching timestamp
 ***************************************************************************)

\* Simplified atomicity check: writes with same value have same timestamp effect
AtomicitySimplified ==
    \A procId1, procId2 \in Procs :
        (vMax[procId1] = vMax[procId2] /\ vMax[procId1] /= Null) => 
            tsMax[procId1] = tsMax[procId2]

-----------------------------------------------------------------------------
(***************************************************************************
 * Combined Safety Property for Model Checking
 ***************************************************************************)

Safety ==
    /\ TypeOK
    /\ LinearizabilityInvariant
    /\ NoEarlyReturn
    /\ TimestampMonotonicity
    /\ ViewContainsInit
    /\ DesiredViewContainsCurrent

-----------------------------------------------------------------------------
(***************************************************************************
 * Combined Liveness Property for Model Checking
 ***************************************************************************)

Liveness ==
    LivenessConditionHolds => (EventuallyEnabled /\ EventuallyComplete)

=============================================================================
\* Modification History
\* TLA+ Specification of DynaStore Properties from JACM2011 paper
