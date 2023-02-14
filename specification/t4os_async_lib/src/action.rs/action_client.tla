---- MODULE action_client ----
VARIABLE state

Trans(a, b) ==
  /\ state = a
  /\ state' = b

Init == state = "ClientSendGoal"

Next ==
  \/ Trans("ClientSendGoal", "ClientRecvFeedback")
  \/ Trans("ClientSendGoal", "ClientSendGoal")
  \/ Trans("ClientRecvFeedback", "ClientRecvFeedback")
  \/ Trans("ClientRecvFeedback", "ClientSendGoal")

Spec == Init /\ [][Next]_state
====
