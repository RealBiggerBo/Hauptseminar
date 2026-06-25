theory Kleppmann_inv_procs
  imports Kleppmann_inv_15
begin

lemma invariant1314_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "(inv11 msgs states UNIV \<and> inv13 msgs states UNIV \<and> inv14 msgs states UNIV \<and> inv17 msgs states \<and> inv18 msgs states \<and> inv19 msgs states) \<and> inv110 msgs states"
  shows "inv11 msgs' states' UNIV \<and> inv13 msgs' states' UNIV \<and> inv14 msgs' states' UNIV \<and> inv17 msgs' states' \<and> inv18 msgs' states' \<and> inv19 msgs' states'"
  using assms
proof(induction rule: coordinator_induct2)
  case (Init_Start t a r)
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Init_Start(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Init_Start(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Init_Start by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Init_Start by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Init_Start(1,2) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Init_Start(1,2) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def by (metis (no_types, lifting) calculation(10,11))
  moreover have "inv19 msgs' states'"
    using inv19_def calculation(1,8) assms(5) by (metis state.distinct(5))
  moreover have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs"
    using Init_Start(1) assms(5) inv110_def by fast
  then have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs'"
    using Init_Start(4) assms(2) by auto
  then have "inv11 msgs' states' UNIV"
    using inv11_def Init_Start assms(5) by (metis (lifting) calculation(8) state.distinct(5))
  ultimately show ?case
    using assms(5) by satx
next
  case (Collect_Yes_Done t a y r sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Collect_Yes_Done(4) assms(2) by fast
  moreover have "inv13 msgs' states' UNIV"
    using assms(3,5) Collect_Yes_Done(1,3,4) inv13_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Collect_Yes_Done by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states' 0 = Committed all ack)"
    using Collect_Yes_Done by (simp add: assms(3))
  moreover have "\<forall>p\<in>y. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)"
    using assms(5) Collect_Yes_Done(1) by (simp add: inv13_def)
  moreover have "\<exists>rcpt. (sender, Send rcpt Yes) \<in> msgs"
    using Collect_Yes_Done(2,5) assms(2,4) by fastforce
  moreover have "y \<union> {sender} = UNIV"
    using Collect_Yes_Done(1,3) inv13_def assms(5) by metis
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))"
    using calculation(6-8) by auto
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Collect_Yes_Done(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Collect_Yes_Done(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(11,12) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv18_def inv19_def assms(5) by (smt (verit))
next
  case (Collect_Yes_Wait t a y r sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Collect_Yes_Wait(4) assms(2) by fast
  moreover have "UNIV = a \<and> (\<forall>p\<in>y. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))"
    using Collect_Yes_Wait(1,5) assms(2,5) inv13_def by meson
  moreover have "(\<exists>rcpt. (sender, Send rcpt Yes) \<in> msgs)"
    using Collect_Yes_Wait(2,5) assms(2,4) by auto
  moreover have "UNIV = a \<and> (\<forall>p\<in>(y \<union> {sender}). p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using calculation(3,4) assms by auto
  moreover have "inv13 msgs' states' UNIV"
    using assms(3) calculation(5) inv13_def Collect_Yes_Wait(4) by (smt (verit, del_insts) fun_upd_same state.inject(2))
  moreover have "inv14 msgs' states' UNIV"
    using Collect_Yes_Wait by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Collect_Yes_Wait by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Collect_Yes_Wait(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Collect_Yes_Wait(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(10,11) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv18_def inv19_def assms(5) by (smt (verit))
next
  case (Collect_No t a y r sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Collect_No(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Collect_No(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Collect_No by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Collect_No by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "a \<noteq> {}"
    using Collect_No(1) assms(5) inv13_def by fastforce
  moreover have "\<exists>sender recpt. (sender, Send recpt Abort) \<in> msgs'"
    using calculation(7) Collect_No(4) using assms(2) by blast
  moreover have "inv17 msgs' states'"
    using inv17_def calculation(8) by fast
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv18_def inv19_def assms(5) by (smt (verit))
next
  case (Collect_Timeout_Zero t a y)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Collect_Timeout_Zero(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Collect_Timeout_Zero(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Collect_Timeout_Zero by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Collect_Timeout_Zero by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "a \<noteq> {}"
    using Collect_Timeout_Zero(1) assms(5) inv13_def by fastforce
  moreover have "\<exists>sender recpt. (sender, Send recpt Abort) \<in> msgs'"
    using calculation(7) Collect_Timeout_Zero(4) using assms(2) by blast
  moreover have "inv17 msgs' states'"
    using inv17_def calculation(8) by fast
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv18_def inv19_def assms(5) by (smt (verit))
next
  case (Collect_Timeout_Suc t a y r_prev)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Collect_Timeout_Suc(4) assms(2) by fast
  moreover have "UNIV = a \<and> (\<forall>p\<in>y. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(5) inv13_def by (metis Collect_Timeout_Suc.hyps(1) UnCI assms(2))
  moreover have "inv13 msgs' states' UNIV"
    using calculation(3) inv13_def by (metis (no_types, lifting) Collect_Timeout_Suc(3) assms(3) fun_upd_same state.inject(2))
  moreover have "inv14 msgs' states' UNIV"
    using Collect_Timeout_Suc by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Collect_Timeout_Suc by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Collect_Timeout_Suc(1,2) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Collect_Timeout_Suc(1,2) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(8,9) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv18_def inv19_def assms(5) by (smt (verit))
next
  case (Commit_Ack_Done a ack' sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Commit_Ack_Done(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Commit_Ack_Done(1,3,4) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Commit_Ack_Done by (simp add: assms(3) inv14_def)
  moreover have "(\<nexists>all ack. states' 0 = Committed all ack)"
    using Commit_Ack_Done by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Commit_Ack_Done(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Commit_Ack_Done(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv14_def inv19_def assms(5) by (smt (verit))
next
  case (Commit_Ack_Wait a ack' sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Commit_Ack_Wait(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Commit_Ack_Wait(1,3,4) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Commit_Ack_Wait by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Commit_Ack_Wait by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Commit_Ack_Wait(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Commit_Ack_Wait(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv14_def inv19_def assms(5) by (smt (verit))
next
  case (Commit_Timeout a ack')
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by (meson Un_iff inv19_def)
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Commit_Timeout(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Commit_Timeout(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Commit_Timeout by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Commit_Timeout by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Commit_Timeout(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Commit_Timeout(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv14_def inv19_def assms(5) by (smt (verit, del_insts) Commit_Timeout(1))
next
  case (Commit_Restart a ack')
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by (meson Un_iff inv19_def)
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Commit_Restart(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Commit_Restart(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Commit_Restart by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Commit_Restart by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Commit_Restart(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Commit_Restart(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv19_def assms(5) by (smt (verit, del_insts) Commit_Restart(1))
next
  case (Abort_Ack_Done a ack' sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Abort_Ack_Done(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Abort_Ack_Done(1,3,4) inv13_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Abort_Ack_Done by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Abort_Ack_Done by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Abort_Ack_Done(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Abort_Ack_Done(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv19_def assms(5) by (smt (verit))
next
  case (Abort_Ack_Wait a ack' sender)
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Abort_Ack_Wait(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Abort_Ack_Wait(1,3,4) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Abort_Ack_Wait by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Abort_Ack_Wait by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have "\<forall>p. (p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow>
            (p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs'))"
    using assms(1-3) Abort_Ack_Wait(1-3) by auto
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms(1-3) Abort_Ack_Wait(1-3) by auto
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    using inv17_def calculation(7,8) by (metis (no_types, lifting) assms(5))
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv19_def assms(5) by (smt (verit))
next
  case (Abort_Timeout a ack')
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Abort_Timeout(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Abort_Timeout(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Abort_Timeout by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Abort_Timeout by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have noYesSent:"\<forall>rcpt p. ((p, Send rcpt Yes) \<notin> msgs') \<longleftrightarrow> ((p, Send rcpt Yes) \<notin> msgs)"
    using Abort_Timeout(4) assms(2) by blast
  moreover have "(0 \<noteq> 0 \<and> (\<exists>all ack. states' 0 = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs')) \<longrightarrow> (\<forall>rcpt. (0, Send rcpt Yes) \<notin> msgs')"
    by simp
  moreover have "\<forall>p. p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    by (metis UnCI assms(2,3,5) fun_upd_apply inv17_def noYesSent)
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv17_def inv19_def assms(5) by (smt (verit))
next
  case (Abort_Restart a ack')
  then have "(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms by fast
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longleftrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using Abort_Restart(4) assms(2) by fast
  moreover have "inv13 msgs states UNIV \<longleftrightarrow> inv13 msgs' states' UNIV"
    using assms(3,5) Abort_Restart(1,3) inv13_def inv14_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using Abort_Restart by (simp add: assms(3) inv14_def)
  moreover have "(\<exists>all ack. states 0 = Committed all ack) \<longleftrightarrow> (\<exists>all ack. states' 0 = Committed all ack)"
    using Abort_Restart by (simp add: assms(3))
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Un_def assms(2,3) fun_upd_apply image_iff inv18_def mem_Collect_eq old.prod.inject)
  moreover have noYesSent:"\<forall>rcpt p. ((p, Send rcpt Yes) \<notin> msgs') \<longleftrightarrow> ((p, Send rcpt Yes) \<notin> msgs)"
    using Abort_Restart(4) assms(2) by blast
  moreover have "(0 \<noteq> 0 \<and> (\<exists>all ack. states' 0 = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs')) \<longrightarrow> (\<forall>rcpt. (0, Send rcpt Yes) \<notin> msgs')"
    by simp
  moreover have "\<forall>p. p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    by (metis UnCI assms(2,3,5) fun_upd_apply inv17_def noYesSent)
  ultimately show ?case
    using inv11_def inv13_def inv14_def inv17_def inv19_def assms(5) by (smt (verit))
qed

lemma invariant1314_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv11 msgs states UNIV \<and> inv13 msgs states UNIV \<and> inv14 msgs states UNIV \<and> inv17 msgs states \<and> inv18 msgs states \<and> inv19 msgs states"
  shows "inv11 msgs' states' UNIV \<and> inv13 msgs' states' UNIV \<and> inv14 msgs' states' UNIV \<and> inv17 msgs' states' \<and> inv18 msgs' states' \<and> inv19 msgs' states'"
  using assms
proof(induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, best) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Init_Prep_Yes(4,5) Pair_inject Un_insert_left assms(3,4,6) fun_upd_apply image_empty
        image_insert insert_iff inv18_def state.distinct(3) sup_bot_right sup_commute)
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    unfolding inv17_def using Init_Prep_Yes(4) assms(3,4,6) inv17_def[of msgs states] by auto
  ultimately show ?case
    by (simp add: assms(6) inv11)
next
  case (Init_Prep_No t a r sender t')
then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_SIG) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Init_Prep_No.hyps(4,5) Pair_inject Un_insert_left assms(3,4,6) fun_upd_apply image_insert
        image_is_empty insertE inv18_def state.distinct(7) sup_bot.right_neutral sup_commute)
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using Init_Prep_No assms by simp
  moreover have "\<forall>p \<noteq> proc. p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
                (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using inv17_def assms Init_Prep_No calculation(5) fun_upd_apply image_insert image_is_empty
        Un_empty_right Un_insert_right insert_iff by (smt (verit, del_insts))
  moreover have "(\<forall>rcpt. (proc, Send rcpt Yes) \<notin> msgs)"
    using Init_Prep_No(1) assms(2,6) inv18_def by metis
  moreover have "proc \<noteq> 0 \<and> (\<exists>all ack. states' proc = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
                (\<forall>rcpt. (proc, Send rcpt Yes) \<notin> msgs')"
    using calculation(5,7) by auto
  ultimately show ?case
    using assms(6) inv11 inv17_def by metis
next
  case (Init_Timeout t a r)
  then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_threshold) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, best) Init_Timeout(3,4) Pair_inject Un_insert_left assms(3,4,6) fun_upd_apply image_insert
        image_is_empty insertE inv18_def state.distinct(7) sup_bot.right_neutral sup_commute)
  moreover have "\<forall>p. (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs) \<longleftrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using Init_Timeout assms by simp
  moreover have "\<forall>p \<noteq> proc. p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
                (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using inv17_def assms Init_Timeout calculation(5) fun_upd_apply image_insert image_is_empty
        Un_empty_right Un_insert_right insert_iff by (smt (verit, del_insts))
  moreover have "(\<forall>rcpt. (proc, Send rcpt Yes) \<notin> msgs)"
    using Init_Timeout(1) assms(2,6) inv18_def by metis
  moreover have "proc \<noteq> 0 \<and> (\<exists>all ack. states' proc = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
                (\<forall>rcpt. (proc, Send rcpt Yes) \<notin> msgs')"
    using calculation(5,7) by auto
  ultimately show ?case
    using assms(6) inv11 inv17_def by metis
next
  case (Prep_Commit sender)
  then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_threshold) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    using Pair_inject Un_insert_left assms(3,4,6) fun_upd_apply image_insert
        image_is_empty insertE inv18_def sup_bot.right_neutral sup_commute
    by (smt (verit, best) Prep_Commit(3,4) state.distinct(5))
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    unfolding inv17_def using Prep_Commit(3) assms(3,4,6) inv17_def[of msgs states] by auto
  ultimately show ?case
    by (simp add: assms(6) inv11)
next
  case (Prep_Abort sender)
then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_threshold) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    using Pair_inject Un_insert_left assms(3,4,6) fun_upd_apply image_insert
        image_is_empty insertE inv18_def sup_bot.right_neutral sup_commute
    by (smt (verit, ccfv_threshold) Prep_Abort.hyps(3,4) state.distinct(7))
  moreover have "\<exists>sender recpt. (sender, Send recpt Abort) \<in> msgs'"
    using Prep_Abort assms by fastforce
  ultimately show ?case
    using assms(6) inv11 inv17_def by metis
next
  case (Committed_Commit all ack sender)
then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_threshold) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    by (smt (verit, ccfv_threshold) Committed_Commit(3,4) Pair_inject Un_insert_right assms(3,4,6) fun_upd_apply
        image_insert image_is_empty insert_iff inv18_def state.distinct(5) sup_bot.right_neutral)
  moreover have "inv17 msgs states \<longleftrightarrow> inv17 msgs' states'"
    unfolding inv17_def using Committed_Commit(3) assms(3,4,6) inv17_def[of msgs states] by auto
  ultimately show ?case
    by (simp add: assms(6) inv11)
next
  case (Aborted_Abort all ack sender)
then have commitEquiv:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
    using assms(1,3) by auto
  moreover have "(\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)) \<longrightarrow> (\<forall>p\<in>UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs'))"
    using assms(3) by auto
  ultimately have inv11:"inv11 msgs' states' UNIV"
    using inv11_def assms(6) by (smt (verit, ccfv_threshold) assms(2,4) fun_upd_apply)
  have "inv13 msgs' states' UNIV \<longleftrightarrow> inv13 msgs states UNIV"
    unfolding inv13_def using assms(2,3,4,6) inv13_def by fastforce
  then have "inv13 msgs' states' UNIV"
    using inv13_def assms(6) by simp
  moreover have "inv14 msgs' states' UNIV"
    by (metis assms(2,4,6) fun_upd_apply inv14_def)
  moreover have "inv19 msgs states \<longleftrightarrow> inv19 msgs' states'"
    unfolding inv19_def by (simp add: assms(2,4) commitEquiv)
  moreover have "inv18 msgs states \<longleftrightarrow> inv18 msgs' states'"
    unfolding inv18_def using Aborted_Abort(3) assms(3,4,6) inv18_def by force
  moreover have "proc \<noteq> 0 \<and> (\<exists>all ack. states' proc = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
          (\<forall>rcpt. (proc, Send rcpt Yes) \<notin> msgs')"
    using assms Aborted_Abort by fastforce
  moreover have "\<forall>p. p \<noteq> 0 \<and> (\<exists>all ack. states' p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs') \<longrightarrow>
          (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs')"
    using assms Aborted_Abort by fastforce
  ultimately show ?case
    by (simp add: assms(6) inv11 inv17_def)
qed

lemma invariants123:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv11 msgs' states' UNIV \<and> inv13 msgs' states' UNIV \<and> inv14 msgs' states' UNIV \<and> inv17 msgs' states' \<and> inv18 msgs' states' \<and> inv19 msgs' states'"
  using assms 
proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have statesInit:"\<forall>p. states' p = Initial (init_val p) UNIV r"
    using execute_init by fast
  then have "inv13 msgs' states' UNIV"
    using inv13_def by fastforce
  moreover have "inv14 msgs' states' UNIV"
    using inv14_def statesInit by fastforce
  moreover have msgsEmpty:"msgs' = {}"
    using execute_init Nil by fast
  then have "inv11 msgs' states' UNIV"
    using inv11_def msgsEmpty statesInit by fastforce
  moreover have "inv19 msgs' states'"
    using inv19_def statesInit by (metis state.distinct(5))
  moreover have "inv18 msgs' states'"
    using inv18_def statesInit msgsEmpty by blast
  moreover have "inv17 msgs' states'"
    using inv17_def statesInit msgsEmpty by blast
  ultimately show ?case
    by simp
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
  moreover have invHelp:"inv110 msgs states"
    using invariant15 step_rel1 by fastforce
  show ?case
  proof (cases "proc = 0")
    case True
    then have "coordinator_step proc (states 0) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv11 msgs states UNIV \<and> inv13 msgs states UNIV \<and> inv14 msgs states UNIV \<and> inv17 msgs states \<and> inv18 msgs states \<and> inv19 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant1314_coordinator True step_rel3 step_rel4 exec invHelp by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv11 msgs states UNIV \<and> inv13 msgs states UNIV \<and> inv14 msgs states UNIV \<and> inv17 msgs states \<and> inv18 msgs states \<and> inv19 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant1314_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end