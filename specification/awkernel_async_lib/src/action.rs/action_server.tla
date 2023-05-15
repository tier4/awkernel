---- MODULE action_server ----
VARIABLE state

Trans(a, b) ==
  /\ state = a
  /\ state' = b

Init == state = "ServerRecvGoal"

Next ==
  \/ Trans("ServerRecvGoal", "ServerSendGoalResult")
  \/ Trans("ServerSendGoalResult", "ServerRecvGoal")
  \/ Trans("ServerSendGoalResult", "ServerSendFeedback")
  \/ Trans("ServerSendFeedback", "ServerSendFeedback")
  \/ Trans("ServerSendFeedback", "ServerSendCancel")
  \/ Trans("ServerSendFeedback", "ServerRecvGoal")
  \/ Trans("ServerSendCancel", "ServerRecvGoal")

Spec == Init /\ [][Next]_state
====
