theory Kleppmann_inv_3
  imports Kleppmann_inv_15
begin

lemma invariant3_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv3 msgs states \<and> inv15 msgs states \<and> inv110 msgs states"
  shows "inv3 msgs' states'"
  using assms
proof(induction rule: coordinator_induct2)
  case (Init_Start t a r)
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)"
    using assms(5) inv15_def by fastforce
  moreover have "(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using Init_Start by simp
  ultimately show ?case
    using inv3_def by (smt (verit, ccfv_threshold) Un_iff assms(2) image_iff prod.inject)
next
  case (Collect_Yes_Done t a y r sender)
  have "inv15 msgs' states'"
    using invariant15 assms(4) by metis
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs')"
    using inv15_def Collect_Yes_Done(4) assms(3) by (metis fun_upd_same)
  then show ?case
    using inv3_def by fast
next
  case (Collect_Yes_Wait t a y r sender)
 then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)"
    using assms(5) inv15_def by fastforce
  moreover have "(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using Collect_Yes_Wait by simp
  ultimately show ?case
    using inv3_def by (smt (verit, ccfv_threshold) Un_iff assms(2) image_iff prod.inject)
next
  case (Collect_No t a y r sender)
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs)"
    using inv110_def assms(5) by fast
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs')"
    using Collect_No(4) assms(2) by blast
  then show ?case
    using inv3_def by metis
next
  case (Collect_Timeout_Zero t a y)
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs)"
    using inv110_def assms(5) by fast
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs')"
    using Collect_Timeout_Zero(4) assms(2) by blast
  then show ?case
    using inv3_def by metis
next
  case (Collect_Timeout_Suc t a y r_prev)
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs)"
    using inv110_def assms(5) by fast
  then have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs')"
    using Collect_Timeout_Suc(4) assms(2) by blast
  then show ?case
    using inv3_def by metis
next
  case (Commit_Ack_Done a ack' sender)
  then have "(\<forall>rcpt. (Send rcpt Commit) \<notin> sent) \<and>(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    by simp
  moreover have "(\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs')"
    using calculation assms by fast
  moreover have "(\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs')"
    using calculation assms by fast
  ultimately show ?case
    using inv3_def assms(3,5) by (smt (verit) Un_iff assms(2) image_iff prod.inject)
next
  case (Commit_Ack_Wait a ack' sender)
  then have "(\<forall>rcpt. (Send rcpt Commit) \<notin> sent) \<and>(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    by simp
  moreover have "(\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs')"
    using calculation assms by fast
  moreover have "(\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs')"
    using calculation assms by fast
  ultimately show ?case
    using inv3_def assms(3,5) by (smt (verit) Un_iff assms(2) image_iff prod.inject)
next
  case (Commit_Timeout a ack')
  then have "\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs"
    using inv3_def assms(2,5) by (meson inv15_def)
  then have "\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'"
    using Commit_Timeout(4) assms(2) by auto
  then show ?case
    using inv3_def by metis
next
  case (Commit_Restart a ack')
  then have "\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs"
    using inv3_def assms(2,5) by (meson inv15_def)
  then have "\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'"
    using Commit_Restart(4) assms(2) by auto
  then show ?case
    using inv3_def by metis
next
  case (Abort_Ack_Done a ack' sender)
  then have "(\<forall>rcpt. (Send rcpt Commit) \<notin> sent) \<and>(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    by simp
  moreover have "(\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs')"
    using calculation assms by fast
  moreover have "(\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs')"
    using calculation assms by fast
  ultimately show ?case
    using inv3_def assms(3,5) by (smt (verit) Un_iff assms(2) image_iff prod.inject)
next
  case (Abort_Ack_Wait a ack' sender)
  then have "(\<forall>rcpt. (Send rcpt Commit) \<notin> sent) \<and>(\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    by simp
  moreover have "(\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs')"
    using calculation assms by fast
  moreover have "(\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Abort) \<notin> msgs')"
    using calculation assms by fast
  ultimately show ?case
    using inv3_def assms(3,5) by (smt (verit) Un_iff assms(2) image_iff prod.inject)
next
  case (Abort_Timeout a ack')
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(5) by presburger
next
  case (Abort_Restart a ack')
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(5) by presburger
qed

lemma invariant3_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv3 msgs states"
  shows "inv3 msgs' states'"
  using assms
proof (induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Init_Prep_No t a r sender t')
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Init_Timeout t a r)
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Prep_Commit sender)
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Prep_Abort sender)
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Committed_Commit all ack sender)
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
next
  case (Aborted_Abort all ack sender)
  then have "inv3 msgs states \<longleftrightarrow> inv3 msgs' states'"
    unfolding inv3_def using assms by (simp add: image_iff inv110_def)
  then show ?case
    using assms(6) by presburger
qed

lemma invariant3:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv3 msgs' states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have msgsEmpty:"msgs' = {}"
    using execute_init by fast
  then show ?case
    using inv3_def by fast
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
  moreover have invHelp:"inv15 msgs states \<and> inv110 msgs states"
    using invariant15 assms using step_rel1 by blast
  show ?case
  proof (cases "proc = 0")
    case True
    then have "coordinator_step proc (states 0) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv3 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant3_coordinator True step_rel3 step_rel4 exec invHelp by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv3 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant3_participant False step_rel3 step_rel4 exec invHelp by metis
  qed
qed

end