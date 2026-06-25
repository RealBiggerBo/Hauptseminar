theory Kleppmann_ac
  imports Kleppmann_inv_1 
          Kleppmann_inv_3 
          Kleppmann_inv_procs 
          Kleppmann_inv_111 
          Kleppmann_inv_212223
          Kleppmann_inv_41
begin

theorem ac1_NoCoordinator:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and \<open>proc1 \<noteq> 0 \<and> proc2 \<noteq> 0\<close>
    and \<open>states proc1 = Committed a b \<or> states proc1 = Aborted a b\<close> 
    and \<open>states proc2 = Committed c d \<or> states proc2 = Aborted c d\<close>
  shows \<open>states proc1 = Committed a b \<longleftrightarrow> states proc2 = Committed c d\<close>
proof (rule ccontr)
  assume asm1:"\<not>(states proc1 = Committed a b \<longleftrightarrow> states proc2 = Committed c d)"
  have inv:"inv1 msgs states \<and> inv3 msgs states \<and> inv11 msgs states UNIV \<and> inv17 msgs states"
    using invariants123 invariant1 invariant3 assms(1) by blast
  then show "False"
  proof(cases "states proc1 = Committed a b")
    case True
    then have proc2Abort:"states proc2 = Aborted c d"
      using asm1 assms(4) by auto
    then have commitMsg:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs)"
      using True inv by (metis assms(2) inv1_def)
    then have noAbort:"(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)"
      using inv inv3_def by metis
    then have "(\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))"
      using inv inv11_def by (metis commitMsg)
    then have "\<exists>rcpt. (proc2, Send rcpt Yes) \<in> msgs"
      using assms(2) by auto
    moreover have "\<forall>rcpt. (proc2, Send rcpt Yes) \<notin> msgs"
      using proc2Abort assms(2) noAbort by (meson inv inv17_def)
    ultimately show ?thesis
      by simp
  next
    case False
    then have Aborted: "states proc1 = Aborted a b"
      using assms(3) by auto
    then have "states proc2 = Committed c d"
      using asm1 assms(4) by auto
    then have commitMsg:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs)"
      using inv by (metis assms(2) inv1_def)
    then have noAbort:"(\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)"
      using inv inv3_def by metis
    then have "(\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))"
      using inv inv11_def by (metis commitMsg)
    then have "(\<exists>rcpt. (proc1, Send rcpt Yes) \<in> msgs)"
      using assms(2) by simp
    moreover have "(\<forall>rcpt. (proc1, Send rcpt Yes) \<notin> msgs)"
      using Aborted assms(2) noAbort by (meson inv inv17_def)
    ultimately show ?thesis
      by simp
  qed
qed

theorem ac1_OneCoordinator:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and \<open>p \<noteq> 0\<close>
    and \<open>states 0 = Committed a b \<or> states 0 = Aborted a b\<close> 
    and \<open>states p = Committed c d \<or> states p = Aborted c d\<close>
  shows \<open>states 0 = Committed a b \<longleftrightarrow> states p = Committed c d\<close>
proof
  assume asmCommitted:"states 0 = Committed a b"
  have inv:"inv11 msgs states UNIV \<and> inv17 msgs states \<and> inv15 msgs states"
    using invariants123 invariant15 assms(1) by blast
  show "states p = Committed c d"
  proof(rule ccontr)
    assume asmAborted: "states p \<noteq> Committed c d"
    then have proc2Abort:"states p = Aborted c d"
      using assms(4) by auto
    then have "(\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))"
      using inv inv11_def by (metis asmCommitted)
    then have "\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs"
      using assms(2) by auto
    moreover have noAbort:"\<forall>sender rcpt. (sender, Send rcpt Abort) \<notin> msgs"
      using inv15_def asmCommitted inv by metis
    moreover have "\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs"
      using proc2Abort assms(2) noAbort by (meson inv inv17_def)
    ultimately show "False"
      by simp
    thm inv17_def
  qed
next
  assume asmCommitted:"states p = Committed c d"
  have inv:"inv1 msgs states \<and> inv111 msgs states"
    using invariants123 invariant1 invariant111 assms(1) invariant3 by blast
  have commitMsg:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs)"
    using inv asmCommitted inv1_def assms(2) by metis
  then have "\<exists>all ack. states 0 = Committed all ack \<or> states 0 = Forgotten"
    using inv inv111_def by metis
  then show "states 0 = Committed a b"
    using assms(3) by force
qed

(*all processes that decide must decide on the same value*)
theorem ac1:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and \<open>states proc1 = Committed a b \<or> states proc1 = Aborted a b\<close> 
    and \<open>states proc2 = Committed c d \<or> states proc2 = Aborted c d\<close>
  shows \<open>states proc1 = Committed a b \<longleftrightarrow> states proc2 = Committed c d\<close>
proof(cases "proc1 = proc2")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  then show ?thesis
  proof(cases "proc1 = 0 \<or> proc2 = 0")
    case True
    then show ?thesis
      using ac1_OneCoordinator by (metis assms(1-3) state.distinct(25))
  next
    case False
    then have "proc1 \<noteq> 0 \<and> proc2 \<noteq> 0"
      by satx
    then show ?thesis
      using ac1_NoCoordinator assms by blast
  qed
qed

(*once a process decides it cannot change its decision*)
theorem ac2:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and step: \<open>tupac_step proc (states proc) event = (new_state, sent)\<close>
  shows \<open>(\<exists>a b. states proc = Committed a b) \<longrightarrow> 
        (\<exists>c d. new_state = Committed c d) \<or> (proc = 0 \<and> new_state = Forgotten)\<close>
    and \<open>(\<exists>a b. states proc = Aborted a b) \<longrightarrow> 
        (\<exists>c d. new_state = Aborted c d) \<or> (proc = 0 \<and> new_state = Forgotten)\<close>
    and \<open>states proc = Forgotten \<longrightarrow> 
        (proc = 0 \<and> new_state = Forgotten)\<close>
  using invariant212223 assms inv21_def apply metis
  using invariant212223 assms inv22_def apply metis
  using invariant212223 assms inv23_def apply metis
  done

(*commit only if everyone voted yes*)
theorem ac3:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and \<open>states 0 = Committed a b\<close> 
  shows \<open>\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)\<close>
proof -
  have "inv11 msgs states UNIV"
    using assms invariants123 by blast
  then show ?thesis
    using assms inv11_def by metis
qed

lemma execute_prefix:
  assumes "execute step init procs events msgs states"
  and "events = a @ b"
  shows "\<exists>msgs' states'. execute step init procs a msgs' states'"
  using assms
proof (induction arbitrary: a b rule: execute.induct)
  case (1 step init procs)
  then show ?case 
    using execute.intros(1) by blast
next
  case (2 step init procs events msgs states proc event new_state sent events' msgs' states')
  show ?case
    apply(cases "b = []")
     apply (metis "2.hyps"(1,2,3,4,5) "2.prems" execute.intros(2) self_append_conv)
    by (metis "2.IH" "2.hyps"(5) "2.prems" butlast_append butlast_snoc)
qed

lemma execute_deterministic:
  assumes "execute step init procs events msgs1 states1"
      and "execute step init procs events msgs2 states2"
  shows "msgs1 = msgs2 \<and> states1 = states2"
  using assms
proof (induction arbitrary: msgs2 states2 rule: execute.induct)
  case (1 step init procs)
  then show ?case 
    by (auto elim: execute.cases)
next
  case (2 step init procs events msgs states proc event new_state sent events' msgs' states')
  then show ?case
    by force
qed

lemma execute_msgs_mono:
  assumes "execute step init procs events msgs states"
    and "events' = events @ [e]"
    and "execute step init procs events' msgs' states'"
  shows "msgs \<subseteq> msgs'"
proof -
  obtain p sent msgs_prev states_prev where
    "msgs' = msgs_prev \<union> ((\<lambda>msg. (p, msg)) ` sent)"
    "execute step init procs events msgs_prev states_prev"
    using assms(2,3) by (auto elim: execute.cases)
  then have"msgs = msgs_prev"
    using assms(1) execute_deterministic by metis
  then show ?thesis 
    using \<open>msgs' = msgs_prev \<union> ((\<lambda>msg. (p, msg)) ` sent)\<close> by simp
qed

lemma execute_msgs_subset:
  assumes "execute step init procs events msgs states"
    and "events = a @ b"
    and "execute step init procs a msgs' states'"
  shows "msgs' \<subseteq> msgs"
using assms proof(induction b arbitrary: msgs states msgs' states' events rule: List.rev_induct)
  case Nil
  then show ?case
    using execute_deterministic Nil(1,3) by fastforce
next
  case (snoc b bs)
  then obtain events' where "events' = a @ bs"
    by fastforce
  then obtain msgs_short states_short where "execute step init procs events' msgs_short states_short"
    using snoc(2,3) execute_prefix by (metis append_assoc)
  then have "msgs_short \<subseteq> msgs"
    using snoc by (simp add: \<open>events' = a @ bs\<close> execute_msgs_mono)
  moreover have "msgs' \<subseteq> msgs_short"
    using snoc \<open>execute step init procs events' msgs_short states_short\<close> \<open>events' = a @ bs\<close> by metis
  ultimately show ?case
    by order
qed

lemma execute_step_from_trace:
  assumes "execute step init procs events msgs' states'"
    and "events = a @ [(p,e)] @ b"
    and "execute step init procs a msgs states"
    and "step p (states p) e = (new_state, sent)"
  shows "execute step init procs (a@[(p,e)]) (msgs \<union> ((\<lambda>msg. (p, msg)) ` sent)) (states(p:=new_state))"
  proof -
  \<comment> \<open>1. Show that the prefix (a @ [(p,e)]) is executable\<close>
  obtain msgs_ae states_ae where 
    exec_ae: "execute step init procs (a @ [(p,e)]) msgs_ae states_ae"
    using execute_prefix assms(1-2) by (metis append_assoc)
  \<comment> \<open>2. Invert the execution of the prefix to get the properties of the last step\<close>    
  then obtain msgs_prev states_prev ns_prev sent_prev where
    exec_prev: "execute step init procs a msgs_prev states_prev" and
    p_in: "p \<in> procs" and
    valid: "valid_event e p msgs_prev" and
    step_prev: "step p (states_prev p) e = (ns_prev, sent_prev)" and
    msgs_ae_def: "msgs_ae = msgs_prev \<union> ((\<lambda>msg. (p, msg)) ` sent_prev)" and
    states_ae_def: "states_ae = states_prev(p := ns_prev)"
    by auto
  \<comment> \<open>3. Use determinism to show the state 'a' in the trace is exactly the 'a' we assumed\<close>
  then have "msgs = msgs_prev" "states = states_prev"
    using execute_deterministic by (metis assms(3))+
  \<comment> \<open>4. Substitute our known 'states' and 'msgs' into the transition properties\<close>
  moreover have "ns_prev = new_state" and "sent_prev = sent"
    using step_prev assms(4) calculation by auto
  \<comment> \<open>5. Reconstruct the execution step using the introduction rule\<close>
  ultimately show ?thesis
    using exec_ae msgs_ae_def states_ae_def by fastforce
qed

lemma noStart_init:
  assumes "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states"
    and "\<forall>p. (p, Timeout) \<notin> set events \<and> (p, Restart) \<notin> set events \<and> (0, Start) \<notin> set events"
  shows "\<forall>p. states p = Initial (init_val p) UNIV r"
using assms proof (induction events arbitrary: msgs states rule: List.rev_induct)
  case Nil
  then show ?case
    using execute_init by blast
next
  case (snoc x xs)
  obtain proc event where x_eq: "x = (proc, event)"
    by fastforce
  obtain msgs' states' where ex_xs: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV xs msgs' states'"
    using snoc.prems(1) execute_prefix by blast
  have IH: "\<forall>p. states' p = Initial (init_val p) UNIV r"
    using snoc.IH[OF ex_xs] snoc.prems(2) by simp
  obtain new_state sent where step: "tupac_step proc (states' proc) event = (new_state, sent)"
    by force
  have ex_snoc: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (xs @ [x]) (msgs' \<union> Pair proc ` sent) (states'(proc := new_state))"
    using ex_xs step x_eq execute_step by (smt (verit) execute.intros(2) execute_deterministic snoc.prems(1))
  have states_eq: "states = states'(proc := new_state)" 
   and msgs_eq: "msgs = msgs' \<union> Pair proc ` sent"
    using snoc.prems(1) ex_snoc execute_deterministic by metis+
  have coordinatorInit:"states 0 = Initial (init_val 0) UNIV r"
  proof (cases "proc = 0")
    case True
    with snoc.prems(2) x_eq have "event \<noteq> Timeout \<and> event \<noteq> Restart \<and> event \<noteq> Start"
      by fastforce
    then obtain sender msg where "event = Receive sender msg"
      by (meson event.exhaust)
    with True step IH states_eq show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using states_eq IH by simp
  qed
  moreover have "inv41 msgs states"
    using invariant41 snoc.prems(1) by blast
  ultimately have no_msgs: "msgs = {}"
    unfolding inv41_def by blast
  then have noToRsRc:"event \<noteq> Timeout \<and> event \<noteq> Restart \<and> (proc \<noteq> 0 \<longrightarrow> (\<forall>sender msg. event \<noteq> Receive sender msg))"
    using snoc.prems(2) x_eq ex_snoc msgs_eq by auto
  have "new_state = Initial (init_val proc) UNIV r"
  proof(cases "proc = 0")
    case True
    then show ?thesis
      using coordinatorInit states_eq by auto
  next
    case False
    then show ?thesis
      by (metis IH event.exhaust local.step participant_step.simps(27) prod.inject tupac_step.elims noToRsRc)
  qed
  then show ?case
    using states_eq IH coordinatorInit by auto
qed


lemma execute_receive_event:
  assumes "execute step init procs events msgs states"
    and "(rcpt, Receive sender msg) \<in> set events"
  shows "(sender, Send rcpt msg) \<in> msgs"
proof -
  obtain pevents fevents where split:"events = (pevents@[(rcpt, Receive sender msg)])@fevents"
    by (metis append.left_neutral append_Cons assms(2) in_set_conv_decomp_first append.assoc)
  then obtain msgs' states' where prefix_ex:"execute step init procs (pevents@[(rcpt, Receive sender msg)]) msgs' states'"
    using execute_prefix by (metis append.assoc assms(1))
  then have "(sender, Send rcpt msg) \<in> msgs'"
    using execute_receive by metis
  moreover have "msgs' \<subseteq> msgs"
    using assms(1) split prefix_ex execute_msgs_subset by meson
  ultimately show ?thesis
    by fast
qed

lemma
  assumes "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV beforeStart msgs states"
    and "\<forall>p. states p = Initial (init_val p) UNIV r"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs' states'"
    and "\<forall>p. (p, Timeout) \<notin> set beforePrepare \<and> (p, Restart) \<notin> set beforePrepare \<and> (p, Receive 0 (Prepare (init_val 0))) \<notin> set beforePrepare"
    and "p \<noteq> 0"
  shows "states' p = Initial (init_val p) UNIV r"
  using assms 
proof (induction beforePrepare arbitrary: msgs' states' rule: List.rev_induct)
  case Nil
    obtain msgs1 states1 where exNil:"execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]) msgs1 states1"
      using execute_prefix assms(3) by (metis append_assoc)
    moreover have "tupac_step 0 (states 0) Start = (Collecting (init_val 0) UNIV {0} r, {Send p (Prepare (init_val 0)) | p. p \<in> UNIV})"
      using assms(1,2) by auto
    moreover have "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) 
                                    UNIV 
                                    (beforeStart@[(0,Start)]) 
                                    (msgs \<union> ((\<lambda>msg. (0, msg)) ` {Send p (Prepare (init_val 0)) | p. p \<in> UNIV})) 
                                    (states(0:=Collecting (init_val 0) UNIV {0} r))"
      using calculation assms(1) by (simp add: execute_step_from_trace)
    ultimately have "states1 p = Initial (init_val p) UNIV r"
      by (metis (mono_tags, lifting) assms(2) fun_upd_apply assms(5) execute_deterministic)
    moreover have "states1 = states'"
      using Nil exNil assms execute_deterministic by (metis append.right_neutral)
    ultimately show ?case
      by simp
  next
    case (snoc x xs)
    then obtain proc event where "x = (proc, event)"
      by fastforce
    have invariants:"inv42 msgs' \<and> inv43 msgs' (init_val 0)"
      using snoc(4) sorry
    have noPrep:"\<forall>proc t. (p, Receive proc (Prepare t)) \<notin> set (xs @ [x])"
    proof(rule ccontr)
      assume "\<not>(\<forall>proc t. (p, Receive proc (Prepare t)) \<notin> set (xs @ [x]))"
      then have "\<exists>proc t. (p, Receive proc (Prepare t)) \<in> set (xs @ [x])"
        by blast
      then obtain proc t where ev_props:"(p, Receive proc (Prepare t)) \<in> set (xs @ [x])"
        by fastforce
      then have "(proc, Send p (Prepare t)) \<in> msgs'"
        using execute_receive_event snoc(4) execute_prefix by fastforce
      moreover from this have "(0, Send p (Prepare (init_val 0))) \<in> msgs'"
        using inv42_def inv43_def by (metis invariants)
      ultimately show "False"
        by (metis  inv42_def inv43_def invariants snoc(5) ev_props)
    qed
(*Thus such an Receive Prepare event cannot occur. 
  Furthermore there are no Timeouts nor restarts. 
  Thus the state of p does not change
  Since it was Initial ... before it is also now*)
    then show ?case
    proof(cases "proc = p")
      case True
      then have "(\<forall>proc t. event \<noteq> Receive proc (Prepare t)) \<and> event \<noteq> Timeout \<and> event \<noteq> Restart"
        using snoc(5) \<open>x = (proc, event)\<close> noPrep by fastforce
      then have "states' p = Initial (init_val p) UNIV r"
        sorry
      then show ?thesis
        by presburger
    next
      case False
      then have "states' p = states p"
        sorry
      then show ?thesis
        using snoc(3) by presburger
    qed
qed

(*if no failures and all processes vote yes then commit*)
theorem ac4:
  assumes valid_exec:\<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV events msgs states\<close>
    and initiated:\<open>(0,Start) \<in> set events\<close>
    and no_fail:\<open>\<forall>p. (p, Timeout) \<notin> set events \<and> (p, Restart) \<notin> set events\<close>
    and all_yes:\<open>\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)\<close>
    and participant_exists:\<open>\<exists>p. p \<in> UNIV \<and> p \<noteq> 0\<close>
    and delivery: \<open>\<forall>pevents fevents proc event. events = pevents@[(proc, event)]@fevents \<longrightarrow> 
      (\<exists>msgs states new_state sent. 
        tupac_step proc (states proc) event = (new_state, sent) \<and>
        execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV pevents msgs states \<and> 
        (\<forall>rcpt msg. 
        (Send rcpt msg) \<in> sent \<longrightarrow> 
        (rcpt, Receive proc msg) \<in> set fevents))\<close>
  shows "\<forall>sender rcpt. (sender, Send rcpt Abort) \<notin> msgs" (*What better to show here?*)
proof -
  obtain beforeStart afterStart where split:"events = beforeStart@[(0, Start)]@afterStart" 
                                  and noStart:"(0, Start) \<notin> set beforeStart"
    using assms(2) by (metis append_Cons append_Nil split_list_first)
  then have all_receives:"\<forall>p \<in> UNIV. p \<noteq> 0 \<longrightarrow> ((p, Receive 0 (Prepare (init_val 0))) \<in> set afterStart)"
  proof -
    obtain msgs_bs states_bs preparing prepareMsgs where val_ex_bs:"execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV beforeStart msgs_bs states_bs"
                                                      and step_start:"tupac_step 0 (states_bs 0) Start = (preparing, prepareMsgs)"
                                                      and deliver:"(\<forall>rcpt msg. (Send rcpt msg) \<in> prepareMsgs \<longrightarrow> 
                                                              (rcpt, Receive 0 msg) \<in> set afterStart)"
      using split delivery by metis
    moreover have \<open>\<forall>p. (p, Timeout) \<notin> set beforeStart \<and> (p, Restart) \<notin> set beforeStart\<close>
      using split no_fail by simp
    ultimately have "states_bs 0 = Initial (init_val 0) UNIV r"
      using noStart noStart_init by blast
    then have "tupac_step 0 (states_bs 0) Start = (Collecting (init_val 0) UNIV {0} r, {Send p (Prepare (init_val 0)) | p. p \<in> UNIV})"
      by simp
    then have "(\<forall>rcpt msg. (Send rcpt msg) \<in> {Send p (Prepare (init_val 0)) | p. p \<in> UNIV} \<longrightarrow> (rcpt, Receive 0 msg) \<in> set afterStart)"
      using deliver step_start by auto
    then show ?thesis
      by blast
  qed
  have all_send_yes: "\<forall>p. p \<in> UNIV \<and> p \<noteq> 0 \<longrightarrow> (0, Receive p Yes) \<in> set afterStart" (* Replace sent_by_p with your actual msg set logic *)
  proof
    fix p::'a
    show "p \<in> UNIV \<and> p \<noteq> 0 \<longrightarrow> (0, Receive p Yes) \<in> set afterStart"
    proof
      assume participant:"p \<in> UNIV \<and> p \<noteq> 0"
        (* Since this p must have received the Prepare message... *)
      then have "(p, Receive 0 (Prepare (init_val 0))) \<in> set afterStart"
        using all_receives by simp
      then obtain beforePrepare afterPrepare where splitPrep:"afterStart = beforePrepare@[(p, Receive 0 (Prepare (init_val 0)))]@afterPrepare" 
                                  and noPrepare:"(p, Receive 0 (Prepare (init_val 0))) \<notin> set beforePrepare"
        by (metis append.left_neutral append_Cons split_list_first)
      then have eventSplit:"events = beforeStart@[(0,Start)]@beforePrepare@[(p, Receive 0 (Prepare (init_val 0)))]@afterPrepare"
        using split by simp
      then have "(\<exists>msgs states new_state sent.
           tupac_step p (states p) (Receive 0 (Prepare (init_val 0))) = (new_state, sent) \<and>
           execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs states \<and>
           (\<forall>rcpt msg. Send rcpt msg \<in> sent \<longrightarrow> (rcpt, Receive p msg) \<in> set afterPrepare))"
        using delivery by auto
      then obtain msgs_bp states_bp prepared yesMsgs where val_ex_bs:"execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (beforeStart@[(0,Start)]@beforePrepare) msgs_bp states_bp"
                                                      and step_prepare:"tupac_step p (states_bp p) (Receive 0 (Prepare (init_val 0))) = (prepared, yesMsgs)"
                                                      and deliver:"(\<forall>rcpt msg. (Send rcpt msg) \<in> yesMsgs \<longrightarrow> 
                                                              (rcpt, Receive p msg) \<in> set afterStart)"
        using delivery participant splitPrep by auto

      then have "states_bp p = Initial (init_val 0) UNIV r"
        using noPrepare val_ex_bs sorry
      then have "tupac_step p (states_bp p) (Receive 0 (Prepare (init_val 0))) = (Prepared, {Send 0 Yes})"
        sorry
      then have "(\<forall>rcpt msg. (Send rcpt msg) \<in> {Send 0 Yes} \<longrightarrow> (rcpt, Receive p msg) \<in> set afterStart)"
        using deliver step_prepare sorry
      show "(0, Receive p Yes) \<in> set afterStart"
        using splitPrep deliver sorry
    qed
  qed
  then show ?thesis
    sorry
  (* 5. Now that everyone sent Yes, use the delivery assumption to show the Coordinator receives them - DONE*)
  (* ... Then split the trace again to find when the coordinator receives the LAST Yes ... *)
  (* Show that the coordinator is in Committed after processing every Yes event <-- ! ! !*)
qed

end