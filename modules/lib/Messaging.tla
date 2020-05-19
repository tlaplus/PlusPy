------------------------ MODULE Messaging ------------------------
\* This module specifies a reliable FIFO point-to-point messaging
\* interface between a set of processes

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
CONSTANT Processes, Message
VARIABLE mi

\*++:SPEC

\* mi contains the state of the messaging interface.
\* It is a map of processes to queues of undelivered messages
LOCAL TypeInvariant == mi \in [Processes -> Seq(Message)]

LOCAL InitialState(procs) == [ p \in procs |-> <<>> ]

\* Initially no messages are undelivered
Init == mi = InitialState(Processes)

\* Function takes intf, the state of the messaging interface, and msgs, a
\* set of << destination, message >> pairs, and updates the state by adding
\* the message to the right (destination) queue of undelivered messages.
LOCAL doSend[intf \in [Processes -> Seq(Message)],
             msgs \in SUBSET 
                 {<<proc, msg>> : proc \in Processes, msg \in Message}] ==
    IF msgs = {} THEN intf
    ELSE
        LET m == CHOOSE m \in msgs : TRUE
        IN doSend[[intf EXCEPT ![m[1]] = Append(@, m[2])], msgs \ {m}]

\* Helper operator for Send()
LOCAL SendAll(intf, msgs) == doSend[intf, msgs]

\* msgs is a set of << destination, payload >> pairs.  The intention
\* is to deliver each payload to the given destination process.
Send(msgs) == mi' = SendAll(mi, msgs)

\* Helper operators for Receive()
LOCAL WaitForMessage(intf, p)   == intf[p] /= <<>>
LOCAL NextMessage(intf, p)      == Head(intf[p])
LOCAL DeliveredMessage(intf, p) == [ intf EXCEPT ![p] = Tail(@) ]

\* Process p is trying to receive a message.  If its queue of undelivered
\* messages is non-empty, invoke Deliver(p, m) with m being the first
\* message on its queue.  Deliver should return TRUE if successful.
\* If so, remove the message from the queue.
Receive(p, Deliver(_, _)) ==
    /\ WaitForMessage(mi, p)
    /\ Deliver(p, NextMessage(mi, p))
    /\ mi' = DeliveredMessage(mi, p)

=========================================================================

\*++:PlusPy

LOCAL INSTANCE IOUtils

\* Initially no messages are undelivered
Init == mi = TRUE

\* msgs is a set of << destination, payload >> pairs.  The intention
\* is to deliver each payload to the given destination process.
Send(msgs) == mi' = \A x \in msgs: IOPut("tcp", x[1], x[2])

\* Process p is trying to receive a message.  If its queue of undelivered
\* messages is non-empty, invoke Deliver(p, m) with m being the first
\* message on its queue.  Deliver should return TRUE if successful.
\* If so, remove the message from the queue.
Receive(p, Deliver(_, _)) ==
    /\ IOWait("tcp", p)
    /\ Deliver(p, IOGet("tcp", p))
    /\ UNCHANGED mi

=========================================================================
