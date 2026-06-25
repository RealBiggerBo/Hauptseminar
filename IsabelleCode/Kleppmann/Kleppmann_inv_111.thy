theory Kleppmann_inv_111
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant111_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv111 msgs states"
  shows "inv111 msgs' states'"
  using assms
proof(induction rule: coordinator_induct)
  case (Init_Start t a r)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Collect_Yes_Done t a y r sender)
  then show ?case
    using assms inv111_def by (metis fun_upd_same)
next
  case (Collect_Yes_Wait t a y r sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Collect_No t a y r sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Collect_Timeout_Zero t a y)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Collect_Timeout_Suc t a y r_prev)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Commit_Ack_Done a ack' sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Commit_Ack_Wait a ack' sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Commit_Timeout a ack')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Commit_Restart a ack')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Abort_Ack_Done a ack' sender)
  then show ?case
    using assms inv111_def by (metis fun_upd_def)
next
  case (Abort_Ack_Wait a ack' sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Abort_Timeout a ack')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
next
  case (Abort_Restart a ack')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3) by auto
  then show ?case
    using assms(5) by simp
qed

lemma invariant111_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv111 msgs states"
  shows "inv111 msgs' states'"
  using assms
proof (induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Init_Prep_No t a r sender t')
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Init_Timeout t a r)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Prep_Commit sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(2,3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Prep_Abort sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Committed_Commit all ack sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
next
  case (Aborted_Abort all ack sender)
  then have "inv111 msgs states \<longleftrightarrow> inv111 msgs' states'"
    unfolding inv111_def using assms(3,4) by auto
  then show ?case
    using assms(6) by simp
qed

lemma invariant111:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv111 msgs' states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have statesInit:"\<forall>p. states' p = Initial (init_val p) UNIV r"
    using execute_init assms by fast
  moreover have msgsEmpty:"msgs' = {}"
    using execute_init Nil by fast
  ultimately show ?case
    using inv111_def by auto
next
  case (snoc x events)
  obtain proc event where "x = (proc, event)"
    by fastforce
  hence exec: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV
               (events @ [(proc, event)]) msgs' states'"
    using snoc.prems assms by fast
  from this obtain msgs states sent new_state
    where step_rel1: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states"
      and step_rel2: "tupac_step proc (states proc) event = (new_state, sent)"
      and step_rel3: "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
      and step_rel4: "states' = states (proc := new_state)"
    by auto
  show ?case
  proof (cases "proc = 0")
    case True
    then have "coordinator_step proc (states 0) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv111 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant111_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv111 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant111_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end