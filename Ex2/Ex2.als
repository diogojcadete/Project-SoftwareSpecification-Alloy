
sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
 var nxt: one Node, 
 var qnxt : Node -> lone Node 
}

var one sig Leader in Member {
var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}



fun visualizeQnxt[]: Node -> lone Node{
	Node.qnxt
}
fun visualizeLnxt[]: Node -> lone Node{
	Node.lnxt
}




/**-----STATE TRANSFORMERS 1--------**/

// This predicate handles the application of a new member.
pred MemberApplication[m: Member, n: Node] {
    // Checks if the application can be processed through either case 1 or case 2.
    MemberApplicationCase1[m, n] or (some lastNode: Node | MemberApplicationCase2[m, n, lastNode])
}

// Case 1 for member application when the queue is empty.
pred MemberApplicationCase1[m: Member, n: Node] {
    // Precondition: The queue is empty, containing only the member 'm'.
    no m.~(m.qnxt)                // Ensures 'm' has no connections in 'qnxt'.
    n !in Member                   // 'n' should not be in the Member set.
    no n.(Member.qnxt)            // 'n' should not have any connections to other Members.

    // Postcondition: Add 'n' to the queue after 'm'.
    m.qnxt' = (n -> m)            // Sets 'm' to point to 'n' in the queue.

    // Frame condition: Ensures all other members' connections remain unchanged.
    all m1 : Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                  // Ensures message states remain unchanged.
    stutterMemberRing[]           // Ensures the member ring remains unchanged.
    stutterLeader[]               // Ensures leader state remains unchanged.
}

// Case 2 for member application when the queue already has members.
pred MemberApplicationCase2[m: Member, n: Node, lastNode: Node] {
    // Precondition: 'n' is not in the queue and is a new member.
    some m.~(m.qnxt)              // There are other nodes in the queue.
    no n.(Member.qnxt)            // 'n' should not have connections to other Members.
    n !in Member                   // 'n' should not be a member already.
    lastNode in m.(^(~(m.qnxt)))  // 'lastNode' should be part of 'm's connections.
    no lastNode.(~(m.qnxt))       // 'lastNode' should not have outgoing connections in 'qnxt'.

    // Postcondition: Add 'n' into the queue after 'lastNode'.
    m.qnxt' = m.qnxt + (n -> lastNode)  // Connects 'n' after 'lastNode'.

    // Frame condition: Ensures all other members' connections remain unchanged.
    all m1 : Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                  // Ensures message states remain unchanged.
    stutterMemberRing[]           // Ensures the member ring remains unchanged.
    stutterLeader[]               // Ensures leader state remains unchanged.
}

// Handles promotion of a member in the queue.
pred MemberPromotionCase1[n: Node, m: Member] {
    // Precondition: 'n' must be the first element of the queue.
    n.(m.qnxt) = m                 // 'n' is linked to 'm'.
    no n.~(m.qnxt)                 // 'n' has no outgoing links in 'qnxt'.

    // Postcondition: Update the queue to promote 'n'.
    no m.qnxt'                     // 'm' should not have connections in the new state.
    nxt' = nxt - (m -> m.nxt) + (m -> n) + (n -> m.nxt) // Update next pointers.
    Member' = Member + n           // Add 'n' to the member list.

    // Frame condition: Ensures all other members' connections remain unchanged.
    all m1 : Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                  // Ensures message states remain unchanged.
    stutterLeader[]               // Ensures leader state remains unchanged.
}

// Handles promotion of a member when there are more nodes after it.
pred MemberPromotionCase2[n: Node, m: Member] {
    // Precondition: 'n' must be the first in the queue with successors.
    n.(m.qnxt) = m                 // 'n' is linked to 'm'.
    some n.~(m.qnxt)               // 'n' has additional nodes following it.

    // Postcondition: Update the queue to reflect 'n's promotion.
    m.qnxt' = m.qnxt - (n -> m) + (n.(~(m.qnxt)) -> m) // Update links accordingly.
    nxt' = nxt - (m -> m.nxt) + (m -> n) + (n -> m.nxt) // Adjust next pointers.
    Member' = Member + n           // Add 'n' to the member list.

    // Frame condition: Ensures all other members' connections remain unchanged.
    all m1 : Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                  // Ensures message states remain unchanged.
    stutterLeader[]               // Ensures leader state remains unchanged.
}

// Handles member exit from the ring.
pred MemberExit[m: Member] {
    // Precondition: 'm' cannot be the leader and must not have outgoing messages or connections.
    m !in Leader                    // Ensures 'm' is not the leader.
    no (m.outbox)                  // Ensures 'm' has no messages to send.
    no (m.qnxt)                    // Ensures 'm' has no next member in the queue.
    
    // Postcondition: Adjust the queue to remove 'm'.
    nxt' = nxt - (m -> m.nxt) - (m.(~nxt) -> m) + (m.(~nxt) -> m.nxt) // Update connections.
    Member' = Member - m           // Remove 'm' from the member list.

    // Frame condition: Ensures all other members' connections remain unchanged.
    all m1 : Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                  // Ensures message states remain unchanged.
    stutterLeader[]               // Ensures leader state remains unchanged.
}

// Handles the application of a new leader.
pred LeaderApplicationCase1[m: Member] {
    // Precondition: The leader's queue must be empty and 'm' must not already be a leader.
    no Leader.~(Leader.qnxt)        // Leader's queue has no members.
    m !in Leader                     // 'm' must not be the leader.
    no m.(Leader.lnxt)              // 'm' has no outgoing links.

    // Postcondition: Set 'm' as the new leader.
    Leader.lnxt' = (m -> Leader)     // Connects 'm' to the leader.

    // Frame condition: All other states remain unchanged.
    Leader = Leader'                 // Leader state remains unchanged.
    stutterMsg[]                    // Ensures message states remain unchanged.
    stutterMemberQueue[]            // Ensures member queue state remains unchanged.
    stutterMemberRing[]             // Ensures member ring remains unchanged.
}

// Handles case 2 for leader application when there are members in the queue.
pred LeaderApplicationCase2[m: Member] {
    // Use auxiliary predicate to manage leader application with connections.
    some lastNode: Node | LeaderApplicationAux[m, Leader, lastNode]
}

// Auxiliary predicate for processing leader application.
pred LeaderApplicationAux[m: Member, l: Leader, lastNode: Node] {
    // Precondition: The member must not already be in the leader's queue.
    some l.~(l.lnxt)                // Ensure there are nodes in the leader's queue.
    no m.(l.lnxt)                   // 'm' must not be connected to the leader's queue.
    m !in Leader  // 'm' must not already be a leader 
    lastNode in l.(^(~(l.lnxt)))    // 'lastNode' must be part of the leader's connections.
    no lastNode.(~(l.lnxt))         // 'lastNode' should not have outgoing links.

    // Postcondition: Connect 'm' into the leader's queue after 'lastNode'.
    l.lnxt' = l.lnxt + (m -> lastNode) // Update leader's next links.

    // Frame condition: All other states remain unchanged.
    Leader = Leader'                 // Leader state remains unchanged.
    stutterMsg[]                    // Ensures message states remain unchanged.
    stutterMemberQueue[]            // Ensures member queue state remains unchanged.
    stutterMemberRing[]             // Ensures member ring remains unchanged.
}

// Handles the promotion of a member to leader case 1.
pred LeaderPromotionCase1[m: Member] {
    // Precondition: 'm' must be the first in the leader's queue and has sent messages.
    m.(Leader.lnxt) = Leader         // Ensure 'm' is linked to the current leader.
    no m.~(Leader.lnxt)              // 'm' must not have outgoing links in the leader's queue.
    no (Leader.outbox)               // Leader should have no outgoing messages.
    all msg: Msg | (msg.sndr = Leader) implies (msg in SentMsg) // All messages sent by leader.

    // Postcondition: Promote 'm' to leader.
    no Leader.lnxt'                  // Leader's next pointer must not exist in the new state.
    Leader' = m                      // Update the leader to 'm'.
    no m.lnxt'                       // Ensure 'm' has no outgoing links.

    // Frame condition: All other states remain unchanged.
    stutterMemberRing[]              // Ensure member ring state remains unchanged.
    stutterMsg[]                     // Ensure message states remain unchanged.
    stutterMemberQueue[]             // Ensure member queue state remains unchanged.
}

// Handles the promotion of a member to leader case 2.
pred LeaderPromotionCase2[m: Member] {
    // Precondition: Similar to case 1 but 'm' has successors.
    m.(Leader.lnxt) = Leader         // Ensure 'm' is linked to the current leader.
    some m.~(Leader.lnxt)            // Ensure 'm' has additional nodes following.
    no (Leader.outbox)               // Leader should have no outgoing messages.
    all msg: Msg | (msg.sndr = Leader) implies (msg in SentMsg) // All messages sent by leader.

    // Postcondition: Promote 'm' to leader.
    no Leader.lnxt'                  // Leader's next pointer must not exist in the new state.
    Leader' = m                      // Update the leader to 'm'.
    m.lnxt' = Leader.lnxt - (m -> Leader) // Update links for the new leader.

    // Frame condition: All other states remain unchanged.
    stutterMemberQueue[]             // Ensure member queue state remains unchanged.
    stutterMemberRing[]              // Ensure member ring state remains unchanged.
    stutterMsg[]                     // Ensure message states remain unchanged.
}

// Handles the exit of a non-member (node) from the member's queue.
pred nonMemberExitCase1[m: Member, n: Node] {
    // Find a node 'n1' for exit operations.
    some n1: Node | nonMemberExitAux1[m, n, n1]
}

// Auxiliary predicate for the first non-member exit case.
pred nonMemberExitAux1[m: Member, n: Node, n1: Node] {
    // Precondition: 'n' is connected to 'n1' in 'm's queue.
    (n -> n1) in m.qnxt             // Connection must exist in 'm's queue.
    n !in Member                     // Ensure 'n' is not in the Member set.
    no (n.~(m.qnxt))                // Ensure 'n' has no outgoing connections in 'm's queue.

    // Postcondition: Update the queue to remove 'n'.
    m.qnxt' = m.qnxt - (n -> n1)    // Remove the connection from 'm's queue.

    // Frame condition: All other states remain unchanged.
    all m1: Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                    // Ensures message states remain unchanged.
    stutterMemberRing[]             // Ensures member ring remains unchanged.
    stutterLeader[]                 // Ensures leader state remains unchanged.
}

// Handles the exit of a non-member (node) case 2.
pred nonMemberExitCase2[m: Member, n: Node] {
    // Find a node 'n1' for exit operations.
    some n1: Node | nonMemberExitAux2[m, n, n1]
}

// Auxiliary predicate for the second non-member exit case.
pred nonMemberExitAux2[m: Member, n: Node, n1: Node] {
    // Precondition: 'n' must have connections in 'm's queue.
    some (n.~(m.qnxt))              // Ensure 'n' has connections following it.
    (n -> n1) in m.qnxt             // Ensure connection must exist in 'm's queue.
    n !in Member                     // Ensure 'n' is not in the Member set.

    // Postcondition: Update the queue to remove 'n' and adjust links.
    m.qnxt' = m.qnxt - (n.(~(m.qnxt)) -> n) - (n -> n1) + (n.(~(m.qnxt)) -> n1) // Adjust connections.

    // Frame condition: All other states remain unchanged.
    all m1: Member' - m | m1.qnxt' = m1.qnxt
    stutterMsg[]                    // Ensures message states remain unchanged.
    stutterMemberRing[]             // Ensures member ring remains unchanged.
    stutterLeader[]                 // Ensures leader state remains unchanged.
}

// Handles the initialization of a broadcast message.
pred BroadcastInitialisation[msg: Msg] {
    // Precondition: The message must be in the leader's outbox and not in sending state.
    // The leader must have a next member in the queue.
    msg in Leader.outbox             // Message should be in leader's outbox.
    msg in PendingMsg                 // Message must be pending.
    no SendingMsg                     // No messages should be currently sending.
    msg.sndr = Leader                 // Set the sender to the leader.
    Leader.nxt != Leader             // Leader must point to a different member.

    // Postcondition: Update outbox of the next member and clean leader's outbox.
    (Leader.nxt).outbox' = (Leader.nxt).outbox + msg // Add message to next member's outbox.
    Leader.outbox' = Leader.outbox - msg // Remove message from leader's outbox.
    msg.rcvrs' = msg.rcvrs + Leader.nxt // Update receivers to include the next member.
    PendingMsg' = PendingMsg - msg    // Remove message from pending messages.
    SendingMsg' = SendingMsg + msg     // Add message to sending messages.

    // Frame condition: All other states remain unchanged.
    all msg1: Msg' - msg | msg1' = msg1
    SentMsg' = SentMsg                 // Sent messages remain unchanged.
    stutterMemberQueue[]               // Ensure member queue state remains unchanged.
    stutterMemberRing[]                // Ensure member ring state remains unchanged.
    stutterLeader[]                    // Ensure leader state remains unchanged.
}

// Handles message redirection from the member's outbox.
pred MessageRedirect[m: Member, msg: Msg] {
    // Precondition: There must be a message in the outbox that is currently being sent.
    msg in m.outbox                   // Message must be in the member's outbox.
    msg in SendingMsg                 // Message must be in the sending state.
    msg.sndr = Leader                 // Ensure the sender is the leader.
    m.nxt !in Leader                  // The next member cannot be the leader.

    // Postcondition: Redirect the message to the next member's outbox.
    (m.nxt).outbox' = (m.nxt).outbox + msg // Add message to the next member's outbox.
    m.outbox' = m.outbox - msg       // Remove message from the current member's outbox.
    msg.rcvrs' = msg.rcvrs + m.nxt   // Update receivers to include the next member.

    // Frame condition: All other states remain unchanged.
    all msg1: Msg' - msg | msg1' = msg1
    PendingMsg' = PendingMsg           // Pending messages remain unchanged.
    SendingMsg' = SendingMsg           // Sending messages remain unchanged.
    SentMsg' = SentMsg                 // Sent messages remain unchanged.
    stutterMemberQueue[]               // Ensure member queue state remains unchanged.
    stutterMemberRing[]                // Ensure member ring state remains unchanged.
    stutterLeader[]                    // Ensure leader state remains unchanged.
}

// Handles the termination of a broadcast message.
pred BroadcastTermination[m: Member, msg: Msg] {
    // Precondition: The message must not be in the leader's outbox.
    msg !in Leader.outbox              // Ensure the message is not with the leader.
    (m.nxt) in Leader                  // The next member must be a leader.
    msg.rcvrs = Member - Leader        // Ensure all members received the message except the leader.
    msg in SendingMsg && msg in m.outbox // Message must be sending and in the current member's outbox.
    msg.sndr = Leader                  // Ensure the sender is the leader.

    // Postcondition: Update message status as received by leader.
    m.outbox' = m.outbox - msg        // Remove the message from the current member's outbox.
    SendingMsg' = SendingMsg - msg     // Remove the message from sending messages.
    SentMsg' = SentMsg + msg           // Add the message to sent messages.

    // Frame condition: All other states remain unchanged.
    all msg1: Msg' - msg | msg1' = msg1
    PendingMsg' = PendingMsg           // Pending messages remain unchanged.
    rcvrs' = rcvrs                     // Ensure receivers state remains unchanged.
    stutterMemberQueue[]               // Ensure member queue state remains unchanged.
    stutterMemberRing[]                // Ensure member ring state remains unchanged.
    stutterLeader[]                    // Ensure leader state remains unchanged.
}


//-------------------------------/--/-------------------------------
pred init {
    // There is exactly one leader at the beginning
    one Leader
   // Initialize the next pointer to point the leader to itself, creating a self-loop.
    nxt = Leader -> Leader
   // There are no connections in the queue and leader links initially.
    no qnxt
    no lnxt
    some Node - Leader // Ensures there are nodes present other than the leader.
    no (Member -Leader) //Ensures that the only Member is the leader

 
    // For each message in the pending messages, it must be in the sender's outbox,
    // and it should not have any recipients yet.
   all n: Node | lone n.outbox
   all msg: Msg | msg in PendingMsg implies (msg.sndr.outbox = msg and no(msg.rcvrs)  and lone n: Node | msg in n.outbox)
   
   
    no Msg-PendingMsg
    no SendingMsg
    no SentMsg
}



pred stutterMemberRing[]{
	nxt' = nxt
	Member' = Member
}


pred stutterMemberQueue[]{
	qnxt' = qnxt
}

pred stutterLeader[]{
	lnxt' = lnxt
	Leader' = Leader
}

pred stutterMsg[]{
	rcvrs' = rcvrs
	outbox' = outbox
	PendingMsg' = PendingMsg
	SendingMsg' = SendingMsg
	SentMsg' = SentMsg
}



pred stutter[]{
	stutterMemberRing[]
	stutterLeader[]
	stutterMsg[]
	stutterMemberQueue[]
}

pred trans[]{
	stutter[] 
       or 
       (some m: Member, n: Node, msg: Msg | 
          MemberApplication[m, n]
	   or MemberPromotionCase1[n, m]
	or MemberPromotionCase2[n, m]
	or MemberExit[m]
	or LeaderApplicationCase1[m] 
	or LeaderApplicationCase2[m] 
	or LeaderPromotionCase1[m]
	or LeaderPromotionCase2[m]
	or nonMemberExitCase1[m,n]
	or nonMemberExitCase2[m,n]
	or BroadcastInitialisation[msg]
	or MessageRedirect[m,msg]
	or BroadcastTermination[m,msg]

)
}
 
pred system[]{
    init[] && always trans[]
}

pred TraceMemberApplication[]{
    eventually some m1: Member, n1, n2: Node |
        MemberApplication[m1, n1] and MemberApplication[m1, n2]
}


pred TraceMemberPromotion1[]{
	eventually some m: Member, n: Node |
		MemberPromotionCase1[n, m]
}

pred TraceMemberPromotion2[]{
	eventually some m: Member, n: Node |
		MemberPromotionCase2[n, m]
}


pred TraceMemberExit[]{
	eventually some m: Member |
		MemberExit[m]
}


pred TraceNonMemberExit1[]{
	eventually some n: Node, m: Member |
		nonMemberExitCase1[m,n]
}

pred TraceNonMemberExit2[]{
	eventually some n: Node, m: Member |
		nonMemberExitCase2[m,n]
}

pred TraceLeaderPromotion[]{
	(eventually some m : Member | LeaderPromotionCase1[m])
	or (eventually some m: Member | LeaderPromotionCase2[m])
}

pred TraceLeaderApplication[]{
	(eventually some m : Member | LeaderApplicationCase1[m])
	or 	(eventually some m : Member | LeaderApplicationCase2[m])
}

pred TraceBroadcastInitialisation{
	eventually some m: Msg |
		BroadcastInitialisation[m]
}



pred TraceMessageRedirect{
	eventually some msg: Msg, m: Member |
		MessageRedirect[m,msg]
}


pred TraceBroadcastTermination{
	eventually some msg: Msg, m: Member |
		BroadcastTermination[m,msg]
}


fact{system[]}




//---------------------------------**RUN**------------------//

//RUN COMMAND FOR THE FIRST TRACE IN THE Ex2.2pdf
run{#Node = 5 and TraceNonMemberExit1[] and eventually #Member > 2 and TraceMessageRedirect[] and eventually #SentMsg>0 and TraceLeaderPromotion[] and TraceMemberExit[]} for 5 Node,1 Msg, 13 steps 


//RUN COMMAND FOR THE FIRST TRACE IN THE Ex2.2pdf
run{#Node = 5 and eventually #SentMsg>0   and TraceLeaderPromotion[]   and TraceMemberExit[] and TraceNonMemberExit1[] } for 5 Node,1 Msg, 15 steps 



