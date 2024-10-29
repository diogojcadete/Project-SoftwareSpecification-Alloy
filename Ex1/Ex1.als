sig Node {
    outbox: set Msg  
}


sig Member in Node {
    nxt: one Member,           
    qnxt: Node -> lone Node,    
}


one sig Leader in Member {
   lnxt: Member -> lone Member 
}


abstract sig Msg {
    sndr: Node,            
    rcvrs: set Node       
}


sig SentMsg, SendingMsg, PendingMsg extends Msg {}

// Function to return every member in a queue starting from member `m`.
fun queuers [m: Member] : set Node {
    m.^(~(m.qnxt))             // Uses transitive closure to gather all nodes connected by `qnxt`.
}

// Function to return the last node in the queue starting from `m`.
fun lastQ [m: Member] : set Node {
    {n: Node | n in queuers[m] and no n.(~(m.qnxt))} // Node with no outgoing connection is the last.
}

// Function to return the first node in the queue starting from `m`.
fun firstQ [m: Member] : set Node {
    {n: Node | some n.(m.qnxt) and n.(m.qnxt) = m} // Node with an incoming connection is the first.
}

// Function to return all members in the leader's queue starting from leader `l`.
fun queuersLeader [l: Leader] : set Member {
    l.^(~(l.lnxt))             // Uses transitive closure to gather all members connected by `lnxt`.
}

// Function to return the first member in the leader's queue.
fun firstQLeader [l: Leader] : set Member {
    {m: Member | some m.(l.lnxt) and m.(l.lnxt) = l} // Member with an incoming connection from the leader.
}

// Function to return the last member in the leader's queue.
fun lastQLeader [l: Leader] : set Member {
    {m: Member | m in queuersLeader[l] and no m.(~(l.lnxt))} // Member with no outgoing `lnxt` connection.
}

// Visualizer function to show `qnxt` links between nodes in a set.
fun visualizeQnxt[]: Node -> lone Node {
    Node.qnxt
}

// Visualizer function to show `lnxt` links between nodes in a set.
fun visualizeLnxt[]: Node -> lone Node {
    Node.lnxt
}

// Fact defining properties of Topology 1: each member has a chain of `nxt` links connecting all members.
fact {
    all m: Member | m.(^nxt) = Member // `nxt` forms a full sequence over all members.
}

// Fact defining properties of Topology 2 for queue structure and connections.
fact {
    // Members cannot belong to the queue of any other member.
    (all m: Member | no (queuers[m] & Member))
    
    // Internal members of the queue must have both predecessor and successor nodes.
    (all m: Member, n: Node | (n in queuers[m] && n !in firstQ[m] && n !in lastQ[m]) implies 
        (one n.(~(m.qnxt)) && one n.(m.qnxt)))

    // All nodes with a `qnxt` successor must belong to the queue.
    (all m: Member, n: Node | (some n.(m.qnxt)) implies n in queuers[m])
    
    // Each member's queue must have exactly one unique first and last node.
    (all m: Member | lone firstQ[m])
    (all m: Member | lone lastQ[m])

    // Members cannot connect to themselves in `qnxt`.
    (all m: Member | no m.(m.qnxt))
}

// Fact defining properties of Topology 3: leader-based queue structure.
fact {
    // Leader queues can only contain `Member` nodes, not other leaders.
    all l: Leader | no (queuersLeader[l] & Leader)

    // Internal members of the leader queue must have both predecessor and successor links in `lnxt`.
    all m: Member, l: Leader | 
        (m in queuersLeader[l] && m !in firstQLeader[l] && m !in lastQLeader[l]) 
        implies (one m.(~(l.lnxt)) && one m.(l.lnxt))
    
    // All members with a successor in `lnxt` must belong to the leader's queue.
    all m: Member, l: Leader | (some m.(l.lnxt)) implies m in queuersLeader[l]

    // Leader should not connect to itself in `lnxt`.
    all l: Leader | no l.(l.lnxt)
    
    // Each leader queue must have a unique first and last member.
    all l: Leader | lone firstQLeader[l] and lone lastQLeader[l]
}

// Fact defining properties of Topology 4: nodes should belong to only one member's queue.
fact {
    all n: Node, m1, m2: Member | (m1 != m2 && n in queuers[m1]) implies n !in queuers[m2]
}

// Fact defining rules for message consistency.
fact MessageConsistency {
    // 1. Outbox can only contain pending or sending messages and should match sender rules.
    all n: Node | n.outbox in PendingMsg + SendingMsg
    all n: Node, m: Msg | (m in n.outbox) implies 
        ((m in PendingMsg and m.sndr = n) or (m in SendingMsg and m.sndr = Leader))

    // 2. Nodes with a message from the leader in their outbox must be a member and a receiver.
    all n: Node, m: SendingMsg | (m in n.outbox and m.sndr = Leader) implies (
        n in Member and n in m.rcvrs
    )

    // 3. Nodes cannot receive their own messages.
    all m: Msg | m.sndr !in m.rcvrs

    // 4. Sending messages must have receivers, be in a member's outbox, and receivers must be members.
    all m: SendingMsg | some m.rcvrs && m.rcvrs in Member && some mem: Member | m in mem.outbox

    // 5. Pending messages must have no receivers and only appear in their sender's outbox.
    all m: PendingMsg | no m.rcvrs && m in m.sndr.outbox

    // 6. Sent messages must have receivers and should not appear in any outbox.
    all m: SentMsg | some m.rcvrs && no n: Node | m in n.outbox
}


//RUN COMMAND REPRESENTED IN Ex1.2.1.png//
run {
    // Ensure at least five nodes in the network
    #Node >= 5
    &&
    #Member >2
    // Ensure a non-empty leader queue
    #lnxt> 1
    &&
    // Ensure at least two non-empty member queues
    #qnxt>3
    && // At least two different members each with a non-empty queue
    
    (some m1: Member, m2: Member | m1 != m2 && #queuers[m1] > 0 && #queuers[m2] > 0)

    // Ensure at least one message of each type (PendingMsg, SendingMsg, SentMsg)
   #PendingMsg > 0 && #SendingMsg > 0 && #SentMsg > 0
} for 10 Node, 5 Msg



//RUN COMMAND REPRESENTED IN Ex1.2.2.png//
run {
    // Ensure at least five nodes in the network
    #Node >= 4
    &&
    #Member >2
    // Ensure a non-empty leader queue
    #lnxt> 2
    &&
    // Ensure at least two non-empty member queues
    #qnxt>2
    && // At least two different members each with a non-empty queue
    
    (some m1: Member, m2: Member | m1 != m2 && #queuers[m1] > 0 && #queuers[m2] > 0)

    // Ensure at least one message of each type (PendingMsg, SendingMsg, SentMsg)
   #PendingMsg > 0 && #SendingMsg > 0 && #SentMsg > 0
} for 10 Node, 5 Msg


