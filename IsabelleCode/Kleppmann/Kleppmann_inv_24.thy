theory Kleppmann_inv_24
  imports Kleppmann_inv_def Kleppmann_step_inducts
begin

lemma invariant24_coordinator:
  assumes "coordinator_step 0 (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv24 states"
  shows "inv24 states'"
  using assms apply (induction rule: coordinator_induct)
  using assms(3,5) apply (simp add: inv24_def)+
  done

lemma invariant24_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv24 states"
  shows "inv24 states'"
  using assms
  apply (induction rule: participant_induct)
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(24))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(29))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(29))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(28))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(29))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(28))
  using assms inv24_def apply (metis (no_types, lifting) fun_upd_apply state.distinct(29))
  done

lemma invariant24:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs' states'\<close>
  shows "inv24 states'"
  using assms proof(induction events arbitrary: msgs' states' r rule: List.rev_induct)
  case Nil
  then have "\<forall>p. states' p = Initial (init_val p) UNIV r"
    using execute_init assms by fast
  then show ?case
    using inv24_def by auto
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
    moreover have"inv24 states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant24_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv24 states"
      using snoc.IH step_rel1 by fast
    ultimately show ?thesis
      using invariant24_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end