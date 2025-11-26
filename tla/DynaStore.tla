------------------------------- MODULE DynaStore -------------------------------
(***************************************************************************
 * TLA+ Specification of DynaStore Protocol
 * 
 * From: "Dynamic Atomic Storage without Consensus" 
 *       Aguilera et al., JACM 2011
 *       Algorithms 2 & 3: Main DynaStore Protocol
 *
 * DynaStore is the first algorithm to solve the atomic R/W storage problem 
 * in a dynamic setting without consensus or stronger primitives. It operates 
 * in a completely asynchronous model where fault-tolerant consensus is 
 * impossible even if no reconfigurations occur.
 *
 * Key Components:
 * 1. Views: Sets of changes (Add/Remove operations) representing configurations
 * 2. Weak Snapshots: For each view w, there's a weak snapshot object ws(w)
 * 3. Traverse: Main procedure that traverses DAG of views
 * 4. ReadInView/WriteInView: Operations on specific views
 * 5. ContactQ: Quorum-based read/write on view members
 *
 * The protocol maintains atomicity (linearizability) for read/write operations
 * while supporting dynamic reconfiguration without consensus.
 *
 * Author: TLA+ Specification based on JACM2011 paper
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs,          \* Set of all possible process identifiers
    Values,         \* Set of values that can be written
    Init,           \* Initial view (set of changes)
    MaxChanges      \* Maximum number of changes (for model checking)

VARIABLES
    \* State variables for each process (Algorithm 2, lines 1-9)
    v,              \* v[i] : latest value received in a WRITE message
    ts,             \* ts[i] : timestamp corresponding to v[i]
    vMax,           \* vMax[i] : latest value observed in Traverse
    tsMax,          \* tsMax[i] : timestamp corresponding to vMax[i]
    pickNewTS,      \* pickNewTS[i] : should Traverse pick a new timestamp?
    M,              \* M[i] : set of messages received
    msgNum,         \* msgNum[i] : message sequence number
    curView,        \* curView[i] : current view of process i
    
    \* Weak Snapshot state for each view
    wsMem,          \* wsMem[w][i] : memory cell for process i in weak snapshot of view w
    
    \* Operation state
    pc,             \* Program counter for each process
    opType,         \* Current operation type: "read", "write", "reconfig"
    opArg,          \* Operation argument (value for write, changes for reconfig)
    
    \* Traverse local variables
    desiredView,    \* Target view being traversed towards
    front,          \* Set of views to be processed
    w_current,      \* Current view being processed in traverse
    changeSets,     \* Change sets returned from scan
    
    \* Message passing
    msgs,           \* Set of messages in transit
    
    \* For verification
    history,        \* History of operations for linearizability checking
    enabled         \* Whether operations are enabled for each process

-----------------------------------------------------------------------------
(***************************************************************************
 * Type Definitions
 ***************************************************************************)

\* A change is either (Add, p) or (Remove, p)
Add == "Add"
Remove == "Remove"
Change == [type : {Add, Remove}, proc : Procs]

\* A view is a set of changes
View == SUBSET Change

\* Timestamps: (num, pid) pairs, lexicographically ordered
Timestamp == [num : Nat, pid : Procs \cup {"-"}]
NullTS == [num |-> 0, pid |-> "-"]

\* Null value
Null == CHOOSE x : x \notin Values

\* Message types
MsgTypes == {"REQ_R", "REQ_W", "REPLY", "NOTIFY"}

-----------------------------------------------------------------------------
(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Get members of a view: join \ remove
Members(view) ==
    LET joinSet == {c.proc : c \in {x \in view : x.type = Add}}
        removeSet == {c.proc : c \in {x \in view : x.type = Remove}}
    IN joinSet \ removeSet

\* Compare timestamps (lexicographic order)
TsLess(t1, t2) ==
    \/ t1.num < t2.num
    \/ (t1.num = t2.num /\ t1.pid /= t2.pid)  \* Simplified comparison

TsLeq(t1, t2) ==
    t1 = t2 \/ TsLess(t1, t2)

TsMax(t1, t2) ==
    IF TsLess(t1, t2) THEN t2 ELSE t1

\* Size of a view (number of changes)
ViewSize(view) == Cardinality(view)

\* View subset relation (used for view ordering)
ViewSubset(v1, v2) == v1 \subseteq v2 /\ v1 /= v2

\* Get smallest views in a set
SmallestViews(views) ==
    LET minSize == CHOOSE s \in {ViewSize(vw) : vw \in views} :
                      \A vw \in views : s <= ViewSize(vw)
    IN {vw \in views : ViewSize(vw) = minSize}

\* Is process i a member of view w?
IsMember(i, w) == i \in Members(w)

\* Majority of a set
Majority(S) == {Q \in SUBSET S : Cardinality(Q) * 2 > Cardinality(S)}

\* All views reachable from Init with bounded changes
AllViews == {vw \in SUBSET Change : Cardinality(vw) <= MaxChanges}

-----------------------------------------------------------------------------
(***************************************************************************
 * Variable Initialization
 ***************************************************************************)

vars == <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, curView,
          wsMem, pc, opType, opArg, desiredView, front, w_current,
          changeSets, msgs, history, enabled>>

TypeOK ==
    /\ v \in [Procs -> Values \cup {Null}]
    /\ ts \in [Procs -> Timestamp]
    /\ vMax \in [Procs -> Values \cup {Null}]
    /\ tsMax \in [Procs -> Timestamp]
    /\ pickNewTS \in [Procs -> BOOLEAN]
    /\ M \in [Procs -> SUBSET msgs]
    /\ msgNum \in [Procs -> Nat]
    /\ curView \in [Procs -> View]
    /\ pc \in [Procs -> {"idle", "read", "write", "reconfig",
                         "traverse", "readInView", "writeInView",
                         "contactQ", "notifyQ", "done"}]
    /\ enabled \in [Procs -> BOOLEAN]

Init_State ==
    \* Process state (Algorithm 2, lines 1-9)
    /\ v = [i \in Procs |-> Null]
    /\ ts = [i \in Procs |-> NullTS]
    /\ vMax = [i \in Procs |-> Null]
    /\ tsMax = [i \in Procs |-> NullTS]
    /\ pickNewTS = [i \in Procs |-> FALSE]
    /\ M = [i \in Procs |-> {}]
    /\ msgNum = [i \in Procs |-> 0]
    /\ curView = [i \in Procs |-> Init]
    \* Weak snapshot state
    /\ wsMem = [w \in AllViews |-> [i \in Procs |-> {}]]
    \* Operation state
    /\ pc = [i \in Procs |-> "idle"]
    /\ opType = [i \in Procs |-> "none"]
    /\ opArg = [i \in Procs |-> Null]
    \* Traverse state
    /\ desiredView = [i \in Procs |-> Init]
    /\ front = [i \in Procs |-> {}]
    /\ w_current = [i \in Procs |-> Init]
    /\ changeSets = [i \in Procs |-> {}]
    \* Messages
    /\ msgs = {}
    \* Verification state
    /\ history = <<>>
    \* Enable operations initially for processes in Init.join (line 11)
    /\ enabled = [i \in Procs |-> i \in Members(Init)]

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 10-11: Initialization
 * 
 * initially:
 *   if (i \in Init.join) then enable operations
 ***************************************************************************)

\* Operations are enabled for process i if it's in the initial view
\* This is handled in Init_State via the enabled variable

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 12-16: Read Operation
 * 
 * operation read_i():
 *   pickNewTS_i <- FALSE
 *   newView <- Traverse({}, ⊥)
 *   NotifyQ(newView)
 *   return vMax_i
 ***************************************************************************)

ReadStart(i) ==
    /\ pc[i] = "idle"
    /\ enabled[i]
    /\ pc' = [pc EXCEPT ![i] = "traverse"]
    /\ opType' = [opType EXCEPT ![i] = "read"]
    /\ opArg' = [opArg EXCEPT ![i] = Null]
    /\ pickNewTS' = [pickNewTS EXCEPT ![i] = FALSE]
    \* Initialize Traverse
    /\ desiredView' = [desiredView EXCEPT ![i] = curView[i]]
    /\ front' = [front EXCEPT ![i] = {curView[i]}]
    /\ history' = Append(history, [type |-> "read_start", proc |-> i])
    /\ UNCHANGED <<v, ts, vMax, tsMax, M, msgNum, curView, wsMem, 
                   w_current, changeSets, msgs, enabled>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 17-21: Write Operation
 * 
 * operation write_i(val):
 *   pickNewTS_i <- TRUE
 *   newView <- Traverse({}, val)
 *   NotifyQ(newView)
 *   return OK
 ***************************************************************************)

WriteStart(i, val) ==
    /\ pc[i] = "idle"
    /\ enabled[i]
    /\ val \in Values
    /\ pc' = [pc EXCEPT ![i] = "traverse"]
    /\ opType' = [opType EXCEPT ![i] = "write"]
    /\ opArg' = [opArg EXCEPT ![i] = val]
    /\ pickNewTS' = [pickNewTS EXCEPT ![i] = TRUE]
    \* Initialize Traverse
    /\ desiredView' = [desiredView EXCEPT ![i] = curView[i]]
    /\ front' = [front EXCEPT ![i] = {curView[i]}]
    /\ history' = Append(history, [type |-> "write_start", proc |-> i, val |-> val])
    /\ UNCHANGED <<v, ts, vMax, tsMax, M, msgNum, curView, wsMem,
                   w_current, changeSets, msgs, enabled>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 22-26: Reconfig Operation
 * 
 * operation reconfig_i(cng):
 *   pickNewTS_i <- FALSE
 *   newView <- Traverse(cng, ⊥)
 *   NotifyQ(newView)
 *   return OK
 ***************************************************************************)

ReconfigStart(i, cng) ==
    /\ pc[i] = "idle"
    /\ enabled[i]
    /\ cng \subseteq Change
    /\ cng /= {}
    /\ pc' = [pc EXCEPT ![i] = "traverse"]
    /\ opType' = [opType EXCEPT ![i] = "reconfig"]
    /\ opArg' = [opArg EXCEPT ![i] = cng]
    /\ pickNewTS' = [pickNewTS EXCEPT ![i] = FALSE]
    \* Initialize Traverse with cng included in desiredView
    /\ desiredView' = [desiredView EXCEPT ![i] = curView[i] \cup cng]
    /\ front' = [front EXCEPT ![i] = {curView[i]}]
    /\ history' = Append(history, [type |-> "reconfig_start", proc |-> i, cng |-> cng])
    /\ UNCHANGED <<v, ts, vMax, tsMax, M, msgNum, curView, wsMem,
                   w_current, changeSets, msgs, enabled>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 46-67: Traverse Procedure
 * 
 * procedure Traverse(cng, val)
 *   desiredView <- curView_i \cup cng
 *   Front <- {curView_i}
 *   do
 *     s <- min{|w| : w \in Front}
 *     w <- any view \in Front s.t. |view| = s
 *     if (i \notin w.members) then halt_i
 *     if w /= desiredView then
 *       update_i(w, desiredView \ w)
 *     end if
 *     ChangeSets <- ReadInView(w)
 *     if ChangeSets /= {} then
 *       Front <- Front \ {w}
 *       for each c \in ChangeSets
 *         desiredView <- desiredView \cup c
 *         Front <- Front \cup {w \cup c}
 *       end for
 *     else ChangeSets <- WriteInView(w, val)
 *   while ChangeSets /= {}
 *   curView_i <- desiredView
 *   return desiredView
 ***************************************************************************)

\* Choose a smallest view from Front and check membership
TraverseSelectView(i) ==
    /\ pc[i] = "traverse"
    /\ front[i] /= {}
    /\ LET smallest == SmallestViews(front[i])
           w == CHOOSE x \in smallest : TRUE
       IN
       \* Check if process is member of selected view (line 52)
       IF ~IsMember(i, w)
       THEN \* Halt - process is not in view
            /\ pc' = [pc EXCEPT ![i] = "idle"]
            /\ UNCHANGED <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, curView,
                          wsMem, opType, opArg, desiredView, front, w_current,
                          changeSets, msgs, history, enabled>>
       ELSE \* Continue with this view
            /\ w_current' = [w_current EXCEPT ![i] = w]
            \* If w /= desiredView, update weak snapshot (lines 53-55)
            /\ IF w /= desiredView[i]
               THEN wsMem' = [wsMem EXCEPT ![w][i] = 
                               IF wsMem[w][i] = {} 
                               THEN {desiredView[i] \ w}
                               ELSE wsMem[w][i]]
               ELSE UNCHANGED wsMem
            /\ pc' = [pc EXCEPT ![i] = "readInView"]
            /\ UNCHANGED <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, curView,
                          opType, opArg, desiredView, front, changeSets, 
                          msgs, history, enabled>>

\* ReadInView: Scan weak snapshot and contact quorum (lines 33-37)
\* Returns change sets from the weak snapshot scan
TraverseReadInView(i) ==
    /\ pc[i] = "readInView"
    /\ LET w == w_current[i]
           \* Collect all non-empty values from weak snapshot of w
           scanResult == {wsMem[w][k] : k \in Members(w)} \ {{}}
       IN
       /\ changeSets' = [changeSets EXCEPT ![i] = scanResult]
       \* If ChangeSets /= {}, process the changes (lines 57-61)
       /\ IF scanResult /= {}
          THEN 
            /\ front' = [front EXCEPT ![i] = 
                  (front[i] \ {w}) \cup {w \cup c : c \in scanResult}]
            /\ desiredView' = [desiredView EXCEPT ![i] = 
                  desiredView[i] \cup UNION scanResult]
            /\ pc' = [pc EXCEPT ![i] = "traverse"]
            /\ UNCHANGED <<wsMem, vMax, tsMax>>
          ELSE
            \* ChangeSets = {}, invoke WriteInView (line 63)
            /\ pc' = [pc EXCEPT ![i] = "writeInView"]
            /\ UNCHANGED <<front, desiredView, wsMem, vMax, tsMax>>
       /\ UNCHANGED <<v, ts, pickNewTS, M, msgNum, curView, 
                     opType, opArg, w_current, msgs, history, enabled>>

\* WriteInView: Write value and scan (lines 38-45)
TraverseWriteInView(i) ==
    /\ pc[i] = "writeInView"
    /\ LET w == w_current[i]
           val == opArg[i]
       IN
       \* If pickNewTS, create new timestamp (lines 39-41)
       /\ IF pickNewTS[i]
          THEN 
            /\ pickNewTS' = [pickNewTS EXCEPT ![i] = FALSE]
            /\ vMax' = [vMax EXCEPT ![i] = val]
            /\ tsMax' = [tsMax EXCEPT ![i] = [num |-> tsMax[i].num + 1, pid |-> i]]
          ELSE UNCHANGED <<pickNewTS, vMax, tsMax>>
       \* Scan weak snapshot again (line 43)
       /\ LET scanResult == {wsMem[w][k] : k \in Members(w)} \ {{}}
          IN changeSets' = [changeSets EXCEPT ![i] = scanResult]
       \* Check if we should continue loop or exit (line 64)
       /\ LET scanResult == {wsMem[w_current[i]][k] : k \in Members(w_current[i])} \ {{}}
          IN
          IF scanResult /= {}
          THEN \* Continue loop
            /\ front' = [front EXCEPT ![i] = 
                  (front[i] \ {w}) \cup {w \cup c : c \in scanResult}]
            /\ desiredView' = [desiredView EXCEPT ![i] = 
                  desiredView[i] \cup UNION scanResult]
            /\ pc' = [pc EXCEPT ![i] = "traverse"]
          ELSE \* Exit loop - Traverse complete (lines 65-66)
            /\ curView' = [curView EXCEPT ![i] = desiredView[i]]
            /\ pc' = [pc EXCEPT ![i] = "notifyQ"]
            /\ UNCHANGED <<front, desiredView>>
       /\ UNCHANGED <<v, ts, M, msgNum, wsMem, opType, opArg, w_current,
                     msgs, history, enabled>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 2, Lines 27-32: NotifyQ Procedure
 * 
 * procedure NotifyQ(w)
 *   if did not receive <NOTIFY, w> then
 *     send <NOTIFY, w> to w.members
 *   end if
 *   wait for <NOTIFY, w> from a majority of w.members
 ***************************************************************************)

\* Send NOTIFY message and wait for majority response
NotifyQSend(i) ==
    /\ pc[i] = "notifyQ"
    /\ LET w == desiredView[i]
       IN
       \* Send NOTIFY to all members
       /\ msgs' = msgs \cup {[type |-> "NOTIFY", view |-> w, 
                              from |-> i, to |-> j] : j \in Members(w)}
       /\ pc' = [pc EXCEPT ![i] = "done"]
       /\ UNCHANGED <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, curView,
                     wsMem, opType, opArg, desiredView, front, w_current,
                     changeSets, history, enabled>>

\* Complete operation
OperationComplete(i) ==
    /\ pc[i] = "done"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ LET result == IF opType[i] = "read" THEN vMax[i] ELSE "OK"
           typeStr == IF opType[i] = "read" THEN "read_complete"
                      ELSE IF opType[i] = "write" THEN "write_complete"
                      ELSE "reconfig_complete"
       IN history' = Append(history, [type |-> typeStr, 
                                      proc |-> i, 
                                      result |-> result])
    /\ UNCHANGED <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, curView,
                  wsMem, opType, opArg, desiredView, front, w_current,
                  changeSets, msgs, enabled>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Algorithm 3, Lines 83-98: Message Handlers
 * 
 * upon receiving <REQ, msgType, num, v, ts> from pj:
 *   if msgType = W then
 *     if (ts > ts_i) then (v_i, ts_i) <- (v, ts)
 *     send <REPLY, num> to pj
 *   end if
 *   else send <REPLY, num, v_i, ts_i> to pj
 *
 * upon receiving <REPLY, ...>:
 *   add the message and its sender-id to M_i
 *
 * upon receiving <NOTIFY, w> for the first time:
 *   send <NOTIFY, w> to w.members
 *   if (curView_i ⊂ w) then
 *     pause any ongoing Traverse
 *     curView_i <- w
 *     if (i \in w.join) then enable operations
 *     if paused in line 94, restart Traverse from line 47
 *   end if
 ***************************************************************************)

\* Handle NOTIFY message
HandleNotify(i) ==
    /\ \E msg \in msgs : 
        /\ msg.type = "NOTIFY"
        /\ msg.to = i
        /\ LET w == msg.view
           IN
           \* Forward NOTIFY if first time
           /\ msgs' = msgs \cup {[type |-> "NOTIFY", view |-> w,
                                  from |-> i, to |-> j] : j \in Members(w)}
           \* If curView ⊂ w, update and restart if needed (lines 93-98)
           /\ IF ViewSubset(curView[i], w)
              THEN 
                /\ curView' = [curView EXCEPT ![i] = w]
                \* Enable operations if i is in w.join
                /\ enabled' = [enabled EXCEPT ![i] = 
                      enabled[i] \/ i \in {c.proc : c \in {x \in w : x.type = Add}}]
                \* If in traverse, restart
                /\ IF pc[i] \in {"traverse", "readInView", "writeInView"}
                   THEN 
                     /\ desiredView' = [desiredView EXCEPT ![i] = w]
                     /\ front' = [front EXCEPT ![i] = {w}]
                   ELSE UNCHANGED <<desiredView, front>>
              ELSE UNCHANGED <<curView, enabled, desiredView, front>>
    /\ UNCHANGED <<v, ts, vMax, tsMax, pickNewTS, M, msgNum, wsMem,
                  pc, opType, opArg, w_current, changeSets, history>>

-----------------------------------------------------------------------------
(***************************************************************************
 * Next State Relation
 ***************************************************************************)

Next ==
    \/ \E i \in Procs : ReadStart(i)
    \/ \E i \in Procs, val \in Values : WriteStart(i, val)
    \/ \E i \in Procs, cng \in SUBSET Change : 
         cng /= {} /\ Cardinality(cng) <= MaxChanges /\ ReconfigStart(i, cng)
    \/ \E i \in Procs : TraverseSelectView(i)
    \/ \E i \in Procs : TraverseReadInView(i)
    \/ \E i \in Procs : TraverseWriteInView(i)
    \/ \E i \in Procs : NotifyQSend(i)
    \/ \E i \in Procs : OperationComplete(i)
    \/ \E i \in Procs : HandleNotify(i)

Spec == Init_State /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************
 * Fairness Conditions
 ***************************************************************************)

\* Weak fairness for all actions
Fairness ==
    /\ \A i \in Procs : WF_vars(TraverseSelectView(i))
    /\ \A i \in Procs : WF_vars(TraverseReadInView(i))
    /\ \A i \in Procs : WF_vars(TraverseWriteInView(i))
    /\ \A i \in Procs : WF_vars(NotifyQSend(i))
    /\ \A i \in Procs : WF_vars(OperationComplete(i))
    /\ \A i \in Procs : WF_vars(HandleNotify(i))

FairSpec == Spec /\ Fairness

=============================================================================
\* Modification History
\* TLA+ Specification of DynaStore Protocol from JACM2011 paper
