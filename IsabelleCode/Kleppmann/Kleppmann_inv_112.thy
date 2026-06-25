theory Kleppmann_inv_112
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant112_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv112 msgs states UNIV"
  shows "inv112 msgs' states' UNIV"
  using assms
proof(induction rule: coordinator_induct)
  case (Init_Start t a r)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Collect_Yes_Done t a y r sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Collect_Yes_Wait t a y r sender)
  then show ?case 
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Collect_No t a y r sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Collect_Timeout_Zero t a y)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Collect_Timeout_Suc t a y r_prev)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Commit_Ack_Done a ack' sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Commit_Ack_Wait a ack' sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Commit_Timeout a ack')
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Commit_Restart a ack')
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Abort_Ack_Done a ack' sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) fun_upd_apply sorry
next
  case (Abort_Ack_Wait a ack' sender)
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Abort_Timeout a ack')
  then show ?case
    using inv1_def UnCI assms(2,3,5) sorry
next
  case (Abort_Restart a ack')
  then show ?case
using inv1_def UnCI assms(2,3,5) sorry
qed

end