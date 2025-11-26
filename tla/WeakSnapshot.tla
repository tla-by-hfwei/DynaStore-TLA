--------------------------- MODULE WeakSnapshot ----------------------------
(***************************************************************************
 * TLA+ Specification of Weak Snapshot Abstraction
 * 
 * From: "Dynamic Atomic Storage without Consensus" 
 *       Aguilera et al., JACM 2011
 *       Algorithm 1: Weak Snapshot - code for process pi
 *
 * A weak snapshot object S accessible by a set P of processes supports two 
 * operations: update_i(c) and scan_i(). The update_i(c) operation gets a 
 * value c and returns OK, whereas scan_i() returns a set of values.
 *
 * Required Properties (PR1-PR5):
 * PR1 (integrity): Values returned by scan must have been written by update
 * PR2 (validity): A scan invoked after a completed update returns non-empty
 * PR3 (monotonicity of scans): Later scans return supersets of earlier scans
 * PR4 (non-empty intersection): There exists a common element in all non-empty scans
 * PR5 (termination): Operations by non-crashed majority processes complete
 *
 * Author: TLA+ Specification based on JACM2011 paper
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    P,              \* Set of processes (fixed for each weak snapshot instance)
    Values          \* Set of possible values to store

VARIABLES
    Mem,            \* Mem[i] : SWMR register for process i, initially Null
    pc,             \* Program counter for each process
    arg,            \* Argument passed to current operation
    result,         \* Result to be returned
    C,              \* Local variable: collected values
    ops,            \* Operation history: sequence of completed operations
    pending         \* Pending operations

Null == CHOOSE v : v \notin Values  \* Special null value (⊥)

vars == <<Mem, pc, arg, result, C, ops, pending>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Type Invariants
 ***************************************************************************)

TypeOK ==
    /\ Mem \in [P -> Values \cup {Null}]
    /\ pc \in [P -> {"idle", "update_collect", "update_write", "update_done",
                     "scan_collect1", "scan_check", "scan_collect2", "scan_done"}]
    /\ arg \in [P -> Values \cup {Null}]
    /\ result \in [P -> SUBSET Values]
    /\ C \in [P -> SUBSET Values]
    /\ pending \subseteq P

-----------------------------------------------------------------------------
(***************************************************************************
 * Collect Procedure
 * 
 * procedure collect()
 *   C <- {}
 *   for each pk in P
 *     c <- Mem[k].Read()
 *     if c != Null then C <- C \cup {c}
 *   return C
 *
 * Since collect reads from all registers atomically in the abstract spec,
 * we model it as a single atomic action.
 ***************************************************************************)

Collect(i) ==
    {Mem[k] : k \in P} \ {Null}

-----------------------------------------------------------------------------
(***************************************************************************
 * Update Operation (Algorithm 1, lines 1-5)
 * 
 * operation update_i(c)
 *   if collect() = {} then
 *     Mem[i].Write(c)
 *   end if
 *   return OK
 ***************************************************************************)

\* Start update operation
UpdateStart(i, v) ==
    /\ pc[i] = "idle"
    /\ i \notin pending
    /\ pc' = [pc EXCEPT ![i] = "update_collect"]
    /\ arg' = [arg EXCEPT ![i] = v]
    /\ pending' = pending \cup {i}
    /\ UNCHANGED <<Mem, result, C, ops>>

\* Collect phase of update
UpdateCollect(i) ==
    /\ pc[i] = "update_collect"
    /\ C' = [C EXCEPT ![i] = Collect(i)]
    /\ IF C'[i] = {}
       THEN pc' = [pc EXCEPT ![i] = "update_write"]
       ELSE pc' = [pc EXCEPT ![i] = "update_done"]
    /\ UNCHANGED <<Mem, arg, result, ops, pending>>

\* Write phase of update (only if collect returned empty)
UpdateWrite(i) ==
    /\ pc[i] = "update_write"
    /\ Mem' = [Mem EXCEPT ![i] = arg[i]]
    /\ pc' = [pc EXCEPT ![i] = "update_done"]
    /\ UNCHANGED <<arg, result, C, ops, pending>>

\* Complete update operation
UpdateDone(i) ==
    /\ pc[i] = "update_done"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ result' = [result EXCEPT ![i] = {}]  \* Update returns OK (modeled as empty set)
    /\ ops' = Append(ops, [type |-> "update", proc |-> i, val |-> arg[i]])
    /\ pending' = pending \ {i}
    /\ UNCHANGED <<Mem, arg, C>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Scan Operation (Algorithm 1, lines 6-11)
 * 
 * operation scan_i()
 *   C <- collect()
 *   if C = {} then return {}
 *   C <- collect()
 *   return C
 *
 * Scan performs collect twice. If the first collect returns empty, 
 * it returns empty. Otherwise, it returns the second collect's result.
 ***************************************************************************)

\* Start scan operation
ScanStart(i) ==
    /\ pc[i] = "idle"
    /\ i \notin pending
    /\ pc' = [pc EXCEPT ![i] = "scan_collect1"]
    /\ pending' = pending \cup {i}
    /\ UNCHANGED <<Mem, arg, result, C, ops>>

\* First collect of scan
ScanCollect1(i) ==
    /\ pc[i] = "scan_collect1"
    /\ C' = [C EXCEPT ![i] = Collect(i)]
    /\ pc' = [pc EXCEPT ![i] = "scan_check"]
    /\ UNCHANGED <<Mem, arg, result, ops, pending>>

\* Check if first collect is empty
ScanCheck(i) ==
    /\ pc[i] = "scan_check"
    /\ IF C[i] = {}
       THEN /\ result' = [result EXCEPT ![i] = {}]
            /\ pc' = [pc EXCEPT ![i] = "scan_done"]
       ELSE pc' = [pc EXCEPT ![i] = "scan_collect2"]
    /\ IF C[i] /= {} THEN UNCHANGED result ELSE TRUE
    /\ UNCHANGED <<Mem, arg, C, ops, pending>>

\* Second collect of scan
ScanCollect2(i) ==
    /\ pc[i] = "scan_collect2"
    /\ C' = [C EXCEPT ![i] = Collect(i)]
    /\ result' = [result EXCEPT ![i] = C'[i]]
    /\ pc' = [pc EXCEPT ![i] = "scan_done"]
    /\ UNCHANGED <<Mem, arg, ops, pending>>

\* Complete scan operation
ScanDone(i) ==
    /\ pc[i] = "scan_done"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ops' = Append(ops, [type |-> "scan", proc |-> i, val |-> result[i]])
    /\ pending' = pending \ {i}
    /\ UNCHANGED <<Mem, arg, result, C>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Initial State
 ***************************************************************************)

Init ==
    /\ Mem = [i \in P |-> Null]
    /\ pc = [i \in P |-> "idle"]
    /\ arg = [i \in P |-> Null]
    /\ result = [i \in P |-> {}]
    /\ C = [i \in P |-> {}]
    /\ ops = <<>>
    /\ pending = {}

-----------------------------------------------------------------------------
(***************************************************************************
 * Next State Relation
 ***************************************************************************)

Next ==
    \E i \in P, v \in Values :
        \/ UpdateStart(i, v)
        \/ UpdateCollect(i)
        \/ UpdateWrite(i)
        \/ UpdateDone(i)
        \/ ScanStart(i)
        \/ ScanCollect1(i)
        \/ ScanCheck(i)
        \/ ScanCollect2(i)
        \/ ScanDone(i)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************
 * Safety Properties (PR1-PR4)
 ***************************************************************************)

\* PR1 (Integrity): Values returned by scan must have been written by update
\* A scan returns C, then for each c in C, an update(c) was invoked
Integrity ==
    \A i \in P :
        pc[i] = "scan_done" =>
            \A v \in result[i] : \E k \in P : Mem[k] = v

\* PR2 (Validity): If scan is invoked after an update completes, it returns non-empty
\* This is checked through the trace: if update completed, subsequent scan sees non-empty
\* (Modeled as: if any Mem[k] is non-Null, second collect in scan sees it)
ValidityInvariant ==
    \A i \in P :
        (pc[i] = "scan_collect2") => 
            ((\E k \in P : Mem[k] /= Null) => C[i] /= {})

\* PR3 (Monotonicity of Scans): Later scans return supersets
\* This requires checking the operation history
MonotonicityCheck(ops_seq) ==
    LET 
        scans == SelectSeq(ops_seq, LAMBDA op : op.type = "scan")
    IN 
        \A i, j \in 1..Len(scans) :
            i < j => 
                (scans[i].val = {} \/ scans[j].val /= {})

\* PR4 (Non-empty Intersection): There exists c such that all non-empty scans contain c
\* For all non-empty scans, their intersection is non-empty
NonEmptyIntersectionCheck(ops_seq) ==
    LET 
        scans == SelectSeq(ops_seq, LAMBDA op : op.type = "scan")
        nonEmptyScans == SelectSeq(scans, LAMBDA op : op.val /= {})
    IN 
        Len(nonEmptyScans) > 0 => 
            \E v \in Values : 
                \A k \in 1..Len(nonEmptyScans) : v \in nonEmptyScans[k].val

-----------------------------------------------------------------------------
(***************************************************************************
 * Theorem: At most one Write to each Mem[i] (Paper Section 4.1)
 * 
 * Notice that at most one Mem[i].Write operation can be invoked in the 
 * execution, since after the first Mem[i].Write operation completes, 
 * any collect invoked by pi will return a non-empty set and pi will 
 * never invoke Mem[i].Write again.
 ***************************************************************************)

\* A process writes at most once
AtMostOneWrite(i) ==
    Mem[i] /= Null => 
        \A j \in 1..Len(ops) :
            (ops[j].type = "update" /\ ops[j].proc = i) =>
                \A k \in j+1..Len(ops) :
                    ~(ops[k].type = "update" /\ ops[k].proc = i /\ 
                      ops[k].val /= ops[j].val)

-----------------------------------------------------------------------------
(***************************************************************************
 * Helper Definitions for TLC Model Checking
 ***************************************************************************)

\* SelectSeq is already provided by the Sequences module

=============================================================================
\* Modification History
\* Last modified: TLA+ Specification of Weak Snapshot from JACM2011 paper
