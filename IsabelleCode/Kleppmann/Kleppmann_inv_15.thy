theory Kleppmann_inv_15
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant15_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv15 msgs states \<and> inv110 msgs states"
  shows "inv15 msgs' states' \<and> inv110 msgs' states'"
  using assms
proof(induction rule: coordinator_induct)
  case (Init_Start t a r)
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using assms(5) inv15_def by fastforce
  moreover have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Commit) \<notin> sent)"
    using assms(5) inv110_def Init_Start by fastforce
  ultimately show ?case
    using inv15_def inv110_def assms by (smt (verit, best) Un_iff image_iff old.prod.inject)
next
  case (Collect_Yes_Done t a y r sender)
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using assms(5) inv15_def by fast
  moreover have "states' 0 = Committed a {0}"
    using assms(3) inv110_def by (simp add: Collect_Yes_Done(4))
  then have "inv110 msgs' states'"
    using inv110_def by fastforce
  ultimately show ?case
    using inv15_def assms by (smt (verit, best) Un_iff image_iff old.prod.inject)
next
  case (Collect_Yes_Wait t a y r sender)
  then have "msgs = msgs' \<and> (\<exists>t a y r. states 0 = Collecting t a y r) \<and> (\<exists>t a y r. states' 0 = Collecting t a y r)"
    using assms(2,3) by simp
  then show ?case
    using inv15_def inv110_def assms(2,5) by metis
next
  case (Collect_No t a y r sender)
  then have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs"
    using assms(5) inv110_def by fast
  then have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs'"
    using Collect_No assms(2) by auto
  then have "inv110 msgs' states'"
    using inv110_def by auto
  then show ?case
    using inv15_def assms(3) Collect_No by fastforce 
next
  case (Collect_Timeout_Zero t a y)
  then have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs"
    using assms(5) inv110_def by fast
  then have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs'"
    using Collect_Timeout_Zero assms(2) by auto
  then have "inv110 msgs' states'"
    using inv110_def by auto
  then show ?case
    using inv15_def assms(3) Collect_Timeout_Zero by fastforce 
next
  case (Collect_Timeout_Suc t a y r_prev)
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using assms(5) inv15_def by fast
  moreover have "(\<forall>sender recpt. (sender, Send recpt Commit) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Commit) \<notin> sent)"
    using assms(5) inv110_def Collect_Timeout_Suc by fastforce
  ultimately show ?case
    using inv15_def inv110_def assms by (smt (verit, best) Un_iff image_iff old.prod.inject)
next
  case (Commit_Ack_Done a ack' sender)
  then have "states' 0 = Forgotten"
    using assms(3) by simp
  then show ?case
    using inv15_def inv110_def by (metis (mono_tags, lifting) state.distinct(17,27,29,9))
next
  case (Commit_Ack_Wait a ack' sender)
  then have "msgs = msgs' \<and> (\<exists>a ack. states 0 = Committed a ack) \<and> (\<exists>a ack. states' 0 = Committed a ack)"
    using assms(2,3) by simp
  moreover from this have "inv110 msgs' states'"
    using inv110_def by fastforce
  ultimately show ?case
    using inv15_def assms(2,5) by (metis)
next
  case (Commit_Timeout a ack')
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using assms(5) inv15_def by fast
  then have "inv15 msgs' states'"
    using inv15_def assms(2) by (smt (verit, best) Un_iff image_iff old.prod.inject)
  moreover have "states' 0 = Committed a ack'"
    using Commit_Timeout(3) assms(3) by simp
  then have "inv110 msgs' states'"
    using inv110_def by fastforce
  ultimately show ?case
    by simp
next
  case (Commit_Restart a ack')
  then have "(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<and> (\<forall>rcpt. (Send rcpt Abort) \<notin> sent)"
    using assms(5) inv15_def by fast
  then have "inv15 msgs' states'"
    using inv15_def assms(2) by (smt (verit, best) Un_iff image_iff old.prod.inject)
  moreover have "states' 0 = Committed a ack'"
    using Commit_Restart(3) assms(3) by simp
  then have "inv110 msgs' states'"
    using inv110_def by fastforce
  ultimately show ?case
    by simp
next
  case (Abort_Ack_Done a ack' sender)
  then show ?case 
    using inv15_def inv110_def assms(3) by fastforce 
next
  case (Abort_Ack_Wait a ack' sender)
  then have "msgs = msgs' \<and> (\<exists>a ack. states 0 = Aborted a ack) \<and> (\<exists>a ack. states' 0 = Aborted a ack)"
    using assms(2,3) by simp
  moreover from this have "inv15 msgs' states'"
    using inv15_def by fastforce
  ultimately show ?case
    using inv110_def assms(2,5) by (metis)
next
  case (Abort_Timeout a ack')
  then have "states' 0 = Aborted a ack'"
    using assms by simp
  moreover have "(\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs) \<longleftrightarrow> (\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs')"
    using Abort_Timeout using assms(2) by blast
  ultimately show ?case
    using inv110_def inv15_def assms(5) by (metis (mono_tags, lifting) Abort_Timeout(1) state.distinct(15,25,7))
next
  case (Abort_Restart a ack')
  then have "states' 0 = Aborted a ack'"
    using assms by simp
  moreover have "(\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs) \<longleftrightarrow> (\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs')"
    using Abort_Restart using assms(2) by blast
  ultimately show ?case
    using inv110_def inv15_def assms(5) by (metis (mono_tags, lifting) Abort_Restart(1) state.distinct(15,25,7))
qed

lemma invariant15_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv15 msgs states \<and> inv110 msgs states"
  shows "inv15 msgs' states' \<and> inv110 msgs' states'"
  using assms
proof (induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Init_Prep_No t a r sender t')
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Init_Timeout t a r)
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Prep_Commit sender)
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Prep_Abort sender)
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Committed_Commit all ack sender)
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
next
  case (Aborted_Abort all ack sender)
  then have "states 0 = states' 0 \<and> (\<forall>rcpt.  (Send rcpt Abort) \<notin> sent) \<and> (\<forall>rcpt.  (Send rcpt Commit) \<notin> sent)"
    using assms(2,4) by simp
  then have "(inv15 msgs states \<longleftrightarrow> inv15 msgs' states') \<and> (inv110 msgs states \<longleftrightarrow> inv110 msgs' states')"
    unfolding inv15_def inv110_def using assms(3) by auto
  then show ?case
    using assms(6) by simp
qed

lemma invariant15:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv15 msgs' states' \<and> inv110 msgs' states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have statesInit:"\<forall>p. states' p = Initial (init_val p) UNIV r"
    using execute_init assms by fast
  moreover have msgsEmpty:"msgs' = {}"
    using execute_init Nil by fast
  ultimately show ?case
    using inv15_def inv110_def by blast
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
    moreover have"inv15 msgs states \<and> inv110 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant15_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv15 msgs states \<and> inv110 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant15_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end