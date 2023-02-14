---- MODULE action_server ----
VARIABLE state

Trans(a, b) ==
  /\ state = a
  /\ state' = b

Init == state = "ServerRecvGoal"

Next ==
  \/ Trans("ServerRecvGoal", "ServerRecvGoal")
  \/ Trans("ServerRecvGoal", "ServerSendFeedback")
  \/ Trans("ServerSendFeedback", "ServerSendFeedback")
  \/ Trans("ServerSendFeedback", "ServerRecvGoal")

Spec == Init /\ [][Next]_state
====
