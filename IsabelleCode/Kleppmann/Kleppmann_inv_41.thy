theory Kleppmann_inv_41
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant41_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv41 msgs states"
  shows "inv41 msgs' states'"
  using assms apply(induction rule: coordinator_induct)
  using inv41_def assms(3) apply(fastforce)+
  done

lemma invariant41_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv41 msgs states"
  shows "inv41 msgs' states'"
  using assms
proof (induction rule: participant_induct)
  case (Init_Prep_Yes t a r sender t')
  then show ?case
    using execute_receive by (smt (verit, ccfv_threshold) Un_commute assms(3,4,5,6) empty_iff fun_upd_apply 
        image_empty image_insert insert_iff insert_is_Un inv41_def msg.distinct(1) old.prod.inject send.inject)
next
  case (Init_Prep_No t a r sender t')
  then show ?case
    using execute_receive by (smt (verit, ccfv_threshold) Un_commute assms(3,4,5,6) fun_upd_apply imageE
        image_empty image_insert insert_is_Un inv41_def msg.distinct(3) old.prod.inject range_constant send.inject)
next
  case (Init_Timeout t a r)
  show ?case
    using inv41_def by (metis Init_Timeout.hyps(4) Un_empty assms(2,3,4,6) fun_upd_apply image_empty)
next
  case (Prep_Commit sender)
  then show ?case
    using execute_receive by (smt (verit, ccfv_threshold) Un_commute Un_empty_right assms(2,3,4,5,6) 
        fun_upd_apply imageE inv41_def msg.distinct(27) prod.inject range_constant send.inject)
next
  case (Prep_Abort sender)
  then show ?case
    using execute_receive by (smt (verit, ccfv_threshold) Un_commute assms(2,3,4,5,6) fun_upd_apply imageE 
        image_empty image_insert insert_is_Un inv41_def msg.distinct(29) old.prod.inject range_constant send.inject)
next
  case (Committed_Commit all ack sender)
  then show ?case
    using execute_receive by (smt (verit, best) Un_commute Un_empty_right assms(2,3,4,5,6) empty_def 
        fun_upd_other imageE image_empty inv41_def msg.distinct(27) prod.inject range_constant send.inject)
next
  case (Aborted_Abort all ack sender)
  then show ?case
    using execute_receive by (smt (verit, best) Un_commute Un_empty_right assms(2,3,4,5,6) empty_def 
        fun_upd_other imageE image_empty inv41_def msg.distinct(29) prod.inject range_constant send.inject)
qed

lemma invariant41:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv41 msgs' states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have statesInit:"\<forall>p. states' p = Initial (init_val p) UNIV r"
    using execute_init assms by fast
  moreover have msgsEmpty:"msgs' = {}"
    using execute_init Nil by fast
  ultimately show ?case
    using inv41_def by auto
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
    moreover have"inv41 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant41_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv41 msgs states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant41_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end