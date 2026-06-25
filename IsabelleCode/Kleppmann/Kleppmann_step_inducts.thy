theory Kleppmann_step_inducts
  imports Kleppmann_2PC
begin

lemma coordinator_induct2
  [consumes 5, case_names Init_Start 
                         Collect_Yes_Done Collect_Yes_Wait Collect_No 
                         Collect_Timeout_Zero Collect_Timeout_Suc 
                         Commit_Ack_Done Commit_Ack_Wait Commit_Timeout Commit_Restart 
                         Abort_Ack_Done Abort_Ack_Wait Abort_Timeout Abort_Restart]:
  assumes step_eq: "coordinator_step 0 (states 0) event = (new_state, sent)"
    and msgs_eq:   "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and states_eq: "states' = states (0 := new_state)"
    and exec:      "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and P_pre:     "P msgs states UNIV \<and> Q msgs states UNIV"
    and "\<And>t a r. \<lbrakk>states 0 = Initial t a r; event = Start; 
                  new_state = Collecting t a {0} r; sent = {Send p (Prepare t) | p. p \<in> a}\<rbrakk> 
                  \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>2. Collection: Receive Yes (All participants have answered)\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender Yes; 
                           y \<union> {sender} = a; new_state = Committed a {0}; 
                           sent = {Send p Commit | p. p \<in> a}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>3. Collection: Receive Yes (Still waiting for others)\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender Yes; 
                           y \<union> {sender} \<noteq> a; new_state = Collecting t a (y \<union> {sender}) r; 
                           sent = {}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>4. Collection: Receive No\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender No; 
                           new_state = Aborted a {0}; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                           \<Longrightarrow> P msgs' states' UNIV"
                           
    \<comment> \<open>5. Collection: Timeout with r = 0\<close>
    and "\<And>t a y. \<lbrakk>states 0 = Collecting t a y 0; event = Timeout; 
                  new_state = Aborted a {0}; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                  \<Longrightarrow> P msgs' states' UNIV"
                  
    \<comment> \<open>6. Collection: Timeout with r > 0\<close>
    and "\<And>t a y r_prev. \<lbrakk>states 0 = Collecting t a y (Suc r_prev); event = Timeout; 
                         new_state = Collecting t a y r_prev; sent = {Send p (Prepare t) | p. p \<in> (a - y)}\<rbrakk> 
                         \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>7. Committed: Receive Ack (All acks received)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Committed a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' = a; new_state = Forgotten; sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>8. Committed: Receive Ack (Still waiting for acks)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Committed a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' \<noteq> a; new_state = Committed a (ack' \<union> {sender}); sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>9. Committed: Timeout\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Committed a ack'; event = Timeout; 
                   new_state = Committed a ack'; sent = {Send p Commit | p. p \<in> (a - ack')}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>10. Committed: Restart\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Committed a ack'; event = Restart; 
                   new_state = Committed a ack'; sent = {Send p Commit | p. p \<in> a}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>11. Aborted: Receive Ack (All acks received)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Aborted a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' = a; new_state = Forgotten; sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>12. Aborted: Receive Ack (Still waiting for acks)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Aborted a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' \<noteq> a; new_state = Aborted a (ack' \<union> {sender}); sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>13. Aborted: Timeout\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Aborted a ack'; event = Timeout; 
                   new_state = Aborted a ack'; sent = {Send p Abort | p. p \<in> (a - ack')}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>14. Aborted: Restart\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Aborted a ack'; event = Restart; 
                   new_state = Aborted a ack'; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
  shows "P msgs' states' UNIV"
proof(cases event)
  case Start
  then show ?thesis
  proof(cases "\<exists>t a r. states 0 = Initial t a r")
    case True
    then show ?thesis
      using Start assms(6) step_eq by fastforce
  next
    case False
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Start by (metis coordinator_step.simps(11,13,14,20,26) state.exhaust)
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  qed
next
  case (Receive sender msg)
  then show ?thesis 
  proof(cases "states 0")
    case (Initial _ _ _)
    then show ?thesis
      using P_pre Receive msgs_eq states_eq step_eq by fastforce
  next
    case (Collecting t all yes r)
    then show ?thesis
    proof(cases "msg")
      case (Prepare x1)
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Collecting Receive by simp
      then show ?thesis
        using Collecting Receive assms step_eq by auto
    next
      case Yes
      then show ?thesis
      proof(cases "all = yes \<union> {sender}")
        case True
        then have "coordinator_step 0 (states 0) event = (Committed all {0}, {Send p Commit |p. p \<in> all})"
          using Collecting Receive \<open>msg = Yes\<close> by simp
        then show ?thesis
          using Collecting Receive \<open>msg = Yes\<close> assms(7) True step_eq by auto
      next
        case False
        then have "coordinator_step 0 (states 0) event = (Collecting t all (yes \<union> {sender}) r, {})"
          using Collecting Receive \<open>msg = Yes\<close> by simp
        then show ?thesis
          using Collecting Receive \<open>msg = Yes\<close> assms(8) False step_eq by auto
      qed
    next
      case No
      then have "coordinator_step 0 (states 0) event = (Aborted all {0}, {Send p Abort |p. p \<in> all})"
        using Collecting Receive by simp
      then show ?thesis
        using Collecting Receive assms(9) No step_eq by auto
    next
      case Commit
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Collecting Receive by simp
      then show ?thesis
        using Collecting Receive assms step_eq by auto
    next
      case Abort
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Collecting Receive by simp
      then show ?thesis
        using Collecting Receive assms step_eq by auto
    next
      case Ack
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Collecting Receive by simp
      then show ?thesis
        using Collecting Receive assms step_eq by auto
    qed
  next
    case Prepared
    then have "coordinator_step 0 (states 0) event = (Prepared, {})"
          using Prepared Receive by simp
    then show ?thesis
      by (metis P_pre Prepared Un_empty_right fun_upd_triv image_empty msgs_eq prod.inject states_eq step_eq)
  next
    case (Committed all ack)
    then show ?thesis
    proof(cases "msg = Ack")
      case True
      then show ?thesis
      proof(cases "{sender} \<union> ack = all")
        case True
        then have "coordinator_step 0 (states 0) event = (Forgotten, {})"
          using Committed Receive \<open>msg = Ack\<close> by simp
        then show ?thesis 
          using True Receive \<open>msg = Ack\<close> assms(12) msgs_eq states_eq step_eq by (simp add: Committed)
      next
        case False
        then have "coordinator_step 0 (states 0) event = (Committed all (ack \<union> {sender}), {})"
          using Committed Receive \<open>msg = Ack\<close> by simp
        then show ?thesis 
          using False Receive \<open>msg = Ack\<close> assms(13) msgs_eq states_eq step_eq Committed by auto
      qed
    next
      case False
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Committed Receive by (metis coordinator_step.simps(15,16,17,32,33) msg.exhaust)
      then have "msgs = msgs' \<and> states = states'"
        by (simp add: msgs_eq states_eq step_eq)
      then show ?thesis
        using P_pre by auto
    qed
  next
    case (Aborted all ack)
    then show ?thesis
    proof(cases "msg = Ack")
      case True
      then show ?thesis
      proof(cases "{sender} \<union> ack = all")
        case True
        then have "coordinator_step 0 (states 0) event = (Forgotten, {})"
          using Aborted Receive \<open>msg = Ack\<close> by simp
        then show ?thesis 
          using True Receive \<open>msg = Ack\<close> assms(16) msgs_eq states_eq step_eq by (simp add: Aborted)
      next
        case False
        then have "coordinator_step 0 (states 0) event = (Aborted all (ack \<union> {sender}), {})"
          using Aborted Receive \<open>msg = Ack\<close> by simp
        then show ?thesis 
          using False Receive \<open>msg = Ack\<close> assms(17) msgs_eq states_eq step_eq Aborted by auto
      qed
    next
      case False
      then have "coordinator_step 0 (states 0) event = (states 0, {})"
        using Aborted Receive msg.exhaust by (metis coordinator_step.simps(21,22,23,24,25))
      then have "msgs = msgs' \<and> states = states'"
        by (simp add: msgs_eq states_eq step_eq)
      then show ?thesis
        using P_pre by auto
    qed
  next
    case Forgotten
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Receive Forgotten by (metis coordinator_step.simps(26))
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  qed
next
  case Timeout
  then show ?thesis
  proof(cases "states 0")
    case (Initial _ _ _)
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Timeout Initial by simp
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  next
    case (Collecting t a y r)
    then show ?thesis
    proof(cases r)
      case 0
      then have "coordinator_step 0 (states 0) event = (Aborted a {0}, {Send p Abort | p. p \<in> a})"
        using Timeout Collecting by (simp)
      then have "new_state = Aborted a {0} \<and> sent = {Send p Abort | p. p \<in> a}"
        by (simp add: msgs_eq states_eq step_eq)
      then show ?thesis
        using Collecting Timeout 0 P_pre assms by auto
    next
      case (Suc r')
      then have "coordinator_step 0 (states 0) event = (Collecting t a y r', {Send p (Prepare t) | p. p \<in> (a-y)})"
        using Timeout Collecting by (simp)
      then have "new_state = Collecting t a y r' \<and> sent = {Send p (Prepare t) | p. p \<in> (a-y)}"
        by (simp add: msgs_eq states_eq step_eq)
      then show ?thesis
        using Collecting Timeout Suc P_pre assms by auto
    qed
  next
    case Prepared
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Timeout Prepared by simp
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  next
    case (Committed all ack)
    then have "coordinator_step 0 (states 0) event = (Committed all ack, {Send p Commit | p. p \<in> (all - ack)})"
      using Timeout Committed by (simp)
    then have "new_state = Committed all ack \<and> sent = {Send p Commit | p. p \<in> (all - ack)}"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using Committed Timeout P_pre assms(14) by auto
  next
    case (Aborted all ack)
    then have "coordinator_step 0 (states 0) event = (Aborted all ack, {Send p Abort | p. p \<in> (all - ack)})"
      using Timeout Aborted by (simp)
    then have "new_state = Aborted all ack \<and> sent = {Send p Abort | p. p \<in> (all - ack)}"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using Aborted Timeout P_pre assms(18) by auto
  next
    case Forgotten
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Timeout Forgotten by (metis coordinator_step.simps(26))
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  qed
next
  case Restart
  then show ?thesis
  proof(cases "states 0")
    case (Initial _ _ _)
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Restart Initial by simp
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  next
    case (Collecting t a y r)
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Restart Collecting by simp
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  next
    case Prepared
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Restart Prepared by simp
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  next
    case (Committed all ack)
    then have "coordinator_step 0 (states 0) event = (Committed all ack, {Send p Commit | p. p \<in> all})"
      using Restart Committed by (simp)
    then have "new_state = Committed all ack \<and> sent = {Send p Commit | p. p \<in> all}"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using Committed Restart P_pre assms by auto
  next
    case (Aborted all ack)
    then have "coordinator_step 0 (states 0) event = (Aborted all ack, {Send p Abort | p. p \<in> all})"
      using Restart Aborted by (simp)
    then have "new_state = Aborted all ack \<and> sent = {Send p Abort | p. p \<in> all}"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using Aborted Restart P_pre assms by auto
  next
    case Forgotten
    then have "coordinator_step 0 (states 0) event = (states 0, {})"
      using Restart Forgotten by (metis coordinator_step.simps(26))
    then have "msgs = msgs' \<and> states = states'"
      by (simp add: msgs_eq states_eq step_eq)
    then show ?thesis
      using P_pre by auto
  qed
qed

lemma participant_induct2
  [consumes 6, case_names Init_Prep_Yes Init_Prep_No Init_Timeout Prep_Commit Prep_Abort Committed_Commit Aborted_Abort]:
  assumes step_eq: "participant_step (states proc) event = (new_state, sent)"
    and not_zero:  "proc \<noteq> 0"
    and msgs_eq:   "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and states_eq: "states' = states (proc := new_state)"
    and exec:      "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "P msgs states UNIV \<and> Q msgs states UNIV"
    and "\<And>t a r sender t'. \<lbrakk>states proc = Initial t a r; event = Receive sender (Prepare t'); t = t'; new_state = Prepared; sent = {Send sender Yes}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>t a r sender t'. \<lbrakk>states proc = Initial t a r; event = Receive sender (Prepare t'); t \<noteq> t'; new_state = Aborted {} {}; sent = {Send sender No}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>t a r. \<lbrakk>states proc = Initial t a r; event = Timeout; new_state = Aborted {} {}; sent = {}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>sender. \<lbrakk>states proc = Prepared; event = Receive sender Commit; new_state = Committed {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>sender. \<lbrakk>states proc = Prepared; event = Receive sender Abort; new_state = Aborted {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>all ack sender. \<lbrakk>states proc = Committed all ack; event = Receive sender Commit; new_state = Committed {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>all ack sender. \<lbrakk>states proc = Aborted all ack; event = Receive sender Abort; new_state = Aborted {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
  shows "P msgs' states' UNIV"
proof(cases event)
  case Start
  then show ?thesis
    apply(cases "states proc")
    using assms(6) msgs_eq states_eq step_eq apply auto
    using assms(6) fun_upd_triv msgs_eq states_eq step_eq apply metis
    using assms(6) fun_upd_triv states_eq by metis
next
  case (Receive sender msg)
  then show ?thesis
    apply(cases "states proc")
         apply(cases msg)
              apply (metis (no_types, lifting) Pair_inject assms(7,8) participant_step.simps(1) step_eq)
    using assms(6) msgs_eq states_eq step_eq apply auto
    apply (smt (verit, ccfv_SIG) Un_empty_right assms(10,11) fun_upd_triv image_is_empty msg.case_eq_if
        old.prod.inject)
      apply(cases msg)
           apply auto[3]
    using assms(12) apply fastforce
       apply auto[2]
     apply(cases msg)
          apply auto[1]
         apply auto[3]
    using assms(13) apply fastforce
     apply auto[1]
    by (metis fun_upd_triv)
next
  case Timeout
  then show ?thesis
    apply(cases "states proc")
    using assms(6) msgs_eq states_eq step_eq apply auto
    using assms(6) fun_upd_triv msgs_eq states_eq step_eq assms(9) apply blast
     apply (metis fun_upd_triv)
    by (metis fun_upd_triv)
next
  case Restart
  then show ?thesis
    apply(cases "states proc")
    using assms(6) msgs_eq states_eq step_eq apply auto
    using assms(6) fun_upd_triv msgs_eq states_eq step_eq assms(9) apply metis
    by (metis fun_upd_triv)
qed

lemma coordinator_induct
[consumes 5, case_names Init_Start 
                         Collect_Yes_Done Collect_Yes_Wait Collect_No 
                         Collect_Timeout_Zero Collect_Timeout_Suc 
                         Commit_Ack_Done Commit_Ack_Wait Commit_Timeout Commit_Restart 
                         Abort_Ack_Done Abort_Ack_Wait Abort_Timeout Abort_Restart]:
  assumes step_eq: "coordinator_step 0 (states 0) event = (new_state, sent)"
    and msgs_eq:   "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and states_eq: "states' = states (0 := new_state)"
    and exec:      "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(0, event)]) msgs' states'"
    and P_pre:     "P msgs states UNIV"
    and "\<And>t a r. \<lbrakk>states 0 = Initial t a r; event = Start; 
                  new_state = Collecting t a {0} r; sent = {Send p (Prepare t) | p. p \<in> a}\<rbrakk> 
                  \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>2. Collection: Receive Yes (All participants have answered)\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender Yes; 
                           y \<union> {sender} = a; new_state = Committed a {0}; 
                           sent = {Send p Commit | p. p \<in> a}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>3. Collection: Receive Yes (Still waiting for others)\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender Yes; 
                           y \<union> {sender} \<noteq> a; new_state = Collecting t a (y \<union> {sender}) r; 
                           sent = {}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>4. Collection: Receive No\<close>
    and "\<And>t a y r sender. \<lbrakk>states 0 = Collecting t a y r; event = Receive sender No; 
                           new_state = Aborted a {0}; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                           \<Longrightarrow> P msgs' states' UNIV"
                           
    \<comment> \<open>5. Collection: Timeout with r = 0\<close>
    and "\<And>t a y. \<lbrakk>states 0 = Collecting t a y 0; event = Timeout; 
                  new_state = Aborted a {0}; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                  \<Longrightarrow> P msgs' states' UNIV"
                  
    \<comment> \<open>6. Collection: Timeout with r > 0\<close>
    and "\<And>t a y r_prev. \<lbrakk>states 0 = Collecting t a y (Suc r_prev); event = Timeout; 
                         new_state = Collecting t a y r_prev; sent = {Send p (Prepare t) | p. p \<in> (a - y)}\<rbrakk> 
                         \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>7. Committed: Receive Ack (All acks received)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Committed a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' = a; new_state = Forgotten; sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>8. Committed: Receive Ack (Still waiting for acks)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Committed a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' \<noteq> a; new_state = Committed a (ack' \<union> {sender}); sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>9. Committed: Timeout\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Committed a ack'; event = Timeout; 
                   new_state = Committed a ack'; sent = {Send p Commit | p. p \<in> (a - ack')}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>10. Committed: Restart\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Committed a ack'; event = Restart; 
                   new_state = Committed a ack'; sent = {Send p Commit | p. p \<in> a}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>11. Aborted: Receive Ack (All acks received)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Aborted a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' = a; new_state = Forgotten; sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>12. Aborted: Receive Ack (Still waiting for acks)\<close>
    and "\<And>a ack' sender. \<lbrakk>states 0 = Aborted a ack'; event = Receive sender Ack; 
                          {sender} \<union> ack' \<noteq> a; new_state = Aborted a (ack' \<union> {sender}); sent = {}\<rbrakk> 
                          \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>13. Aborted: Timeout\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Aborted a ack'; event = Timeout; 
                   new_state = Aborted a ack'; sent = {Send p Abort | p. p \<in> (a - ack')}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
    \<comment> \<open>14. Aborted: Restart\<close>
    and "\<And>a ack'. \<lbrakk>states 0 = Aborted a ack'; event = Restart; 
                   new_state = Aborted a ack'; sent = {Send p Abort | p. p \<in> a}\<rbrakk> 
                   \<Longrightarrow> P msgs' states' UNIV"
  shows "P msgs' states' UNIV"
    using coordinator_induct2[of states event new_state sent msgs' msgs states' init_val r events P "\<lambda>a b c. True"]
    using P_pre assms(10,11,12,13,14,15,16,17,18,19,6,7,8,9) exec msgs_eq states_eq step_eq by blast

lemma participant_induct
  [consumes 6, case_names Init_Prep_Yes Init_Prep_No Init_Timeout Prep_Commit Prep_Abort Committed_Commit Aborted_Abort]:
  assumes step_eq: "participant_step (states proc) event = (new_state, sent)"
    and not_zero:  "proc \<noteq> 0"
    and msgs_eq:   "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and states_eq: "states' = states (proc := new_state)"
    and exec:      "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV r) UNIV (events @ [(proc, event)]) msgs' states'"
    and "P msgs states UNIV"
    and "\<And>t a r sender t'. \<lbrakk>states proc = Initial t a r; event = Receive sender (Prepare t'); t = t'; new_state = Prepared; sent = {Send sender Yes}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>t a r sender t'. \<lbrakk>states proc = Initial t a r; event = Receive sender (Prepare t'); t \<noteq> t'; new_state = Aborted {} {}; sent = {Send sender No}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>t a r. \<lbrakk>states proc = Initial t a r; event = Timeout; new_state = Aborted {} {}; sent = {}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>sender. \<lbrakk>states proc = Prepared; event = Receive sender Commit; new_state = Committed {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>sender. \<lbrakk>states proc = Prepared; event = Receive sender Abort; new_state = Aborted {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>all ack sender. \<lbrakk>states proc = Committed all ack; event = Receive sender Commit; new_state = Committed {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
    and "\<And>all ack sender. \<lbrakk>states proc = Aborted all ack; event = Receive sender Abort; new_state = Aborted {} {}; sent = {Send sender Ack}\<rbrakk> \<Longrightarrow> P msgs' states' UNIV"
  shows "P msgs' states' UNIV"
  using participant_induct2[of states proc event new_state sent msgs' msgs states' init_val r events P "\<lambda>a b c. True"]
  using assms(10,11,12,13,6,7,8,9) exec msgs_eq not_zero states_eq step_eq by blast

end