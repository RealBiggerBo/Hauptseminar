theory Kleppmann_inv_212223
  imports Kleppmann_inv_24
begin

lemma invariant212223_coordinator:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and step: \<open>coordinator_step 0 (states 0) event = (new_state, sent)\<close>
  shows "inv21 0 (states 0) new_state"
    and "inv22 0 (states 0) new_state"
    and "inv23 0 (states 0) new_state"
proof -
  have "(\<exists>all ack. states 0 = Committed all ack) \<Longrightarrow> \<exists>all ack. new_state = Committed all ack \<or> (0 = 0 \<and> new_state = Forgotten)"
  proof -
    assume "\<exists>all ack. states 0 = Committed all ack"
    then show "\<exists>all ack. new_state = Committed all ack \<or> (0 = 0 \<and> new_state = Forgotten)"
      using step apply(cases "states 0"; cases event; auto)
      by (metis (no_types, lifting) coordinator_step.simps(15,16,17,18,19,5) msg.exhaust_sel prod.inject)
  qed
  then show "inv21 0 (states 0) new_state"
    using inv21_def by blast
next
  have "\<exists>all ack. states 0 = Aborted all ack \<Longrightarrow> \<exists>all ack. new_state = Aborted all ack \<or> (0 = 0 \<and> new_state = Forgotten)"
  proof -
    assume "\<exists>all ack. states 0 = Aborted all ack"
    then show "\<exists>all ack. new_state = Aborted all ack \<or> (0 = 0 \<and> new_state = Forgotten)"
      using step apply(cases "states 0"; cases event; auto)
      by (metis (no_types, lifting) coordinator_step.simps(8,21-25) msg.exhaust_sel prod.inject)
  qed
  then show "inv22 0 (states 0) new_state"
    using inv22_def by blast
next 
  have "states 0 = Forgotten \<Longrightarrow> new_state = Forgotten"
  proof -
    assume "states 0 = Forgotten"
    then show "new_state = Forgotten"
      using step by(cases "states 0"; cases event; auto)
  qed
  then show "inv23 0 (states 0) new_state"
    using inv23_def by blast
qed



lemma invariant212223_participant:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and step: \<open>participant_step (states proc) event = (new_state, sent)\<close>
    and "proc \<noteq> 0"
  shows "inv21 proc (states proc) new_state"
    and "inv22 proc (states proc) new_state"
    and "inv23 proc (states proc) new_state"
proof -
  have "(\<exists>all ack. states proc = Committed all ack) \<Longrightarrow> \<exists>all ack. new_state = Committed all ack"
  proof -
    assume "\<exists>all ack. states proc = Committed all ack"
    then show "\<exists>all ack. new_state = Committed all ack"
      using assms apply(cases "states proc"; cases event; auto)
      using participant_step.simps(4,11-15) msg.exhaust_sel prod.inject by (smt (verit, del_insts))
  qed
  then show "inv21 proc (states proc) new_state"
    using inv21_def by blast
next
  have "\<exists>all ack. states proc = Aborted all ack \<Longrightarrow> \<exists>all ack. new_state = Aborted all ack"
  proof -
    assume "\<exists>all ack. states proc = Aborted all ack"
    then show "\<exists>all ack. new_state = Aborted all ack"
      using assms apply(cases "states proc"; cases event; auto)
      using participant_step.simps(5,19-23) msg.exhaust_sel prod.inject by (smt (verit, del_insts))
  qed
  then show "inv22 proc (states proc) new_state"
    using inv22_def by blast
next 
  show "inv23 proc (states proc) new_state"
    using invariant24 assms(1,3) by (metis inv23_def inv24_def)
qed

lemma invariant212223:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and step: \<open>tupac_step proc (states proc) event = (new_state, sent)\<close>
  shows "inv21 proc (states proc) new_state 
        \<and> inv22 proc (states proc) new_state 
        \<and> inv23 proc (states proc) new_state"
proof(cases "proc = 0")
  case True
  then show ?thesis
    using invariant212223_coordinator assms by auto
next
  case False
  then show ?thesis
    using invariant212223_participant assms by auto
qed

end