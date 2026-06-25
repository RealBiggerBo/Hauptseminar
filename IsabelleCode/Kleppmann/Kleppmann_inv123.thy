theory Kleppmann_inv123
  imports Kleppmann_inv0
begin

lemma invariant_coordinator:
  assumes "coordinator_step (states 0) event = (new_state, sent)"
    and "msgs' = msgs \<union> ((\<lambda>msg. (0, msg)) ` sent)"
    and "states' = states (0 := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV) UNIV (events @ [(0, event)]) msgs' states'"
    and "inv0 msgs states \<and> inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs states"
  shows "inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs' states'"
proof (cases event)
  case (Start)
  then show ?thesis
  proof(cases "states 0")
    case (Initial t a)
    then have newState:"new_state = Collecting a {} {}"
      sorry
    then have 1:"inv1 msgs' states'"
      sorry
    from newState have 2:"inv2 msgs' states'"
      by (metis UnCI assms(2,3,5) fun_upd_apply inv2_def state.distinct(15))
    have "(\<forall>sender recpt. ((sender, Send recpt Abort) \<notin> msgs)) \<longleftrightarrow> (\<forall>sender recpt. ((sender, Send recpt Abort) \<notin> msgs'))"
      using Initial Start assms(1,2) by auto
    moreover have "(\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs')"
      using Initial Start assms(1,2) by auto
    ultimately have 3:"inv3 msgs' states'"
      by (metis Initial assms(5) inv0_def inv3_def)
    from 1 2 3 show ?thesis
      by simp
  next
    case (Collecting _ _ _)
    then show ?thesis 
      using Start assms(1,2,3,5) by force
  next
    case Prepared
    then show ?thesis
      using Start assms(1,2,3,5) fun_upd_triv
      by (metis coordinator_step.simps(7) image_empty prod.inject sup_bot.right_neutral)
  next
    case (Committed _ _)
    then show ?thesis
      using Start assms(1,2,3,5) by force
  next
    case (Aborted _ _)
    then show ?thesis
      using Start assms(1,2,3,5) by force
  next
    case Forgotten
    then show ?thesis
      using Start assms(1,2,3,5) fun_upd_triv
      by (metis coordinator_step.simps(22) fun_upd_triv image_is_empty prod.inject sup_bot.right_neutral)
  qed
next
  case (Receive sender msg)
  then show ?thesis
  proof(cases "states 0")
    case (Initial _ _)
    then show ?thesis
      using Initial Receive assms(1,2,3,5) by force
  next
    case (Collecting a y n)
    then show ?thesis
    proof(cases msg)
      case (Prepare _)
      then have "coordinator_step (states 0) event = (Collecting a y n, {})"
        by (simp add: Collecting Receive)
      moreover have "msgs' = msgs"
        using calculation assms(1,2) by auto
      ultimately show ?thesis 
        using Collecting assms(1,3,5) by force
    next
      case Yes
      then show ?thesis
      proof(cases "y \<union> n \<union> {sender} = a")
        case True
        then show ?thesis
        proof (cases "n = {}")
          case True
          then have step:"coordinator_step (states 0) event = ((Committed a {}, {Send p (Commit) | p. p \<in> a}))"
            using Collecting Receive Yes \<open>y \<union> n \<union> {sender} = a\<close> by simp
          moreover have "a \<noteq> {}"
            using \<open>y \<union> n \<union> {sender} = a\<close> by auto
          ultimately have "(\<exists>sender rcpt. (sender, Send rcpt (Commit)) \<in> msgs')"
            using assms(1,2) by fastforce
          then have 1:"inv1 msgs' states'"
            by (simp add: inv1_def)
          from step assms have 2:"inv2 msgs' states'"
            by (metis (mono_tags, lifting) Un_iff fun_upd_apply inv2_def prod.inject state.distinct(25))
          have "(\<forall>sender recpt. ((sender, Send recpt Abort) \<notin> msgs))"
            using inv0_def Collecting assms(5) by metis
          moreover have "(\<forall>sender recpt. ((sender, Send recpt Abort) \<notin> msgs'))"
            using 1 step by (simp add: assms(1,2) calculation image_iff)
          ultimately have 3:"inv3 msgs' states'"
            
            by (simp add: inv3_def)
          then show ?thesis
            using 1 2 3 by simp
        next
          case False
          then have step:"coordinator_step (states 0) event = (Aborted a {}, {Send p (Abort) | p. p \<in> a})"
            using Collecting Receive Yes \<open>y \<union> n \<union> {sender} = a\<close> by simp
          then have "states' = states (0:= Aborted a {})"
            by (simp add: assms(1,3))
          then have "(\<exists>proc a ack'. states proc = Committed a ack') \<longleftrightarrow> (\<exists>proc a ack'. states' proc = Committed a ack')"
            by (metis Collecting fun_upd_apply state.distinct(13,25))
          moreover have "(\<forall>rcpt. (Send rcpt Commit) \<notin> sent)"
            using step assms(1) by simp
          then have msgs:"(\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs')"
            using assms(2) by auto
          ultimately have 1:"inv1 msgs' states'"
            using inv1_def assms(5) by auto
          have 2:"inv2 msgs' states'"
            using step True assms(1,2) inv2_def by fastforce
          have "inv3 msgs' states'"
            by (meson Collecting assms(5) inv0_def inv3_def msgs)
          then show ?thesis 
            using 1 2 by simp
        qed
      next
        case False
        then have step:"coordinator_step (states 0) event = (Collecting a (y \<union> {sender}) n, {})"
          using Collecting Receive Yes by simp
        then have msgs:"msgs' = msgs"
          using assms(2,1) by simp
        then have "(\<exists>sender. (sender, Send proc (Commit)) \<in> msgs) \<longleftrightarrow> (\<exists>sender. (sender, Send proc (Commit)) \<in> msgs')"
          by simp
        moreover have "(\<forall>proc a ack'. states proc = Committed a ack') \<longleftrightarrow> (\<forall>proc a ack'. states' proc = Committed a ack')"
          by (metis (mono_tags, opaque_lifting) False state.inject(3))
        ultimately have 1:"inv1 msgs' states'"
          by (metis (no_types, lifting) assms(1,3,5) fun_upd_apply inv1_def local.step msgs prod.inject
              state.distinct(13))
        have "(\<forall>proc a ack'. states proc = Aborted a ack') \<longleftrightarrow> (\<forall>proc a ack'. states' proc = Aborted a ack')"
          using step by (metis Collecting Pair_inject assms(1,3) fun_upd_same state.distinct(15))
        moreover have "(\<exists>sender. (sender, Send proc (Abort)) \<in> msgs) \<longleftrightarrow> ((\<exists>sender. (sender, Send proc (Abort)) \<in> msgs'))"
          using msgs by simp
        ultimately have 2:"inv2 msgs' states'"
          using assms(5) inv2_def by (metis (mono_tags, lifting) assms(1,3) fun_upd_apply fun_upd_other local.step msgs prod.inject state.distinct(15))
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      qed
    next
      case No
      then show ?thesis
      proof(cases "y \<union> n \<union> {sender} = a")
        case True
        then have step: "coordinator_step (states 0) event = (Aborted a {}, {Send p (Abort) | p. p \<in> a})"
          using True Receive No Collecting by simp
        then have "(\<forall>proc a ack'. (states proc = Committed a ack') \<longleftrightarrow> (states' proc = Committed a ack'))"
          using Collecting assms(1,3) by auto
        moreover have equiv:"\<forall>sender rcpt. ((sender, Send rcpt Commit) \<in> msgs) \<longleftrightarrow> ((sender, Send rcpt Commit) \<in> msgs')"
          using assms(1,2) step by auto
        ultimately have 1:"inv1 msgs' states'"
          by (meson assms(5) inv1_def)
        have "(\<exists>proc a ack'. states' proc = Aborted a ack')"
          using assms(1,3) local.step by auto
        moreover have "{Send p (Abort) | p. p \<in> a} \<noteq> {}"
          using True by auto
        then have "(\<exists>rcpt. (Send rcpt Abort) \<in> sent)"
          using assms(1) local.step by auto
        then have "(\<exists>sender rcpt. (sender, Send rcpt Abort) \<in> msgs')"
          using assms(2) by blast
        ultimately have 2:"inv2 msgs' states'"
          using inv2_def by auto
        have "inv3 msgs' states'"
          by (meson Collecting equiv assms(5) inv0_def inv3_def)
        then show ?thesis
          using 1 2 by simp
      next
        case False
        then have step:"coordinator_step (states 0) event = (Collecting a y (n \<union> {sender}), {})"
          using Collecting Receive No by simp
        then have msgs:"msgs' = msgs"
          using assms(2,1) by simp
        then have "(\<exists>sender. (sender, Send proc (Commit)) \<in> msgs) \<longleftrightarrow> (\<exists>sender. (sender, Send proc (Commit)) \<in> msgs')"
          by simp
        moreover have "(\<forall>proc a ack'. states proc = Committed a ack') \<longleftrightarrow> (\<forall>proc a ack'. states' proc = Committed a ack')"
          by (metis (mono_tags, opaque_lifting) False state.inject(3))
        ultimately have 1:"inv1 msgs' states'"
          by (metis (no_types, lifting) assms(1,3,5) fun_upd_apply inv1_def local.step msgs prod.inject
              state.distinct(13))
        have "(\<forall>proc a ack'. states proc = Aborted a ack') \<longleftrightarrow> (\<forall>proc a ack'. states' proc = Aborted a ack')"
          using step by (metis Collecting Pair_inject assms(1,3) fun_upd_same state.distinct(15))
        moreover have "(\<exists>sender. (sender, Send proc (Abort)) \<in> msgs) \<longleftrightarrow> ((\<exists>sender. (sender, Send proc (Abort)) \<in> msgs'))"
          using msgs by simp
        ultimately have 2:"inv2 msgs' states'"
          using assms(5) inv2_def by (metis (mono_tags, lifting) assms(1,3) fun_upd_apply fun_upd_other local.step msgs prod.inject state.distinct(15))
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      qed
    next
      case Commit
      then have "coordinator_step (states 0) event = (Collecting a y n, {})"
        by (simp add: Collecting Receive)
      moreover from this have "msgs' = msgs"
        using assms(1,2) by auto
      ultimately show ?thesis 
        using Collecting assms(1,3,5) by force
    next
      case Abort
      then have "coordinator_step (states 0) event = (Collecting a y n, {})"
        by (simp add: Collecting Receive)
      moreover from this have "msgs' = msgs"
        using assms(1,2) by auto
      ultimately show ?thesis 
        using Collecting assms(1,3,5) by force
    next
      case Ack
      then have "coordinator_step (states 0) event = (Collecting a y n, {})"
        by (simp add: Collecting Receive)
      moreover from this have "msgs' = msgs"
        using assms(1,2) by auto
      ultimately show ?thesis 
        using Collecting assms(1,3,5) by force
    qed
  next
    case Prepared
    have step: "coordinator_step (states 0) event = (states 0, {})"
      by (simp add: Prepared)
    then have "msgs' = msgs"
      by (simp add: assms(1,2))
    moreover have "states' = states"
      using step assms(1,3) by auto
    ultimately show ?thesis
      using assms(5) by auto
  next
    case (Committed all ack)
    then show ?thesis
    proof(cases "msg = Ack")
      case True
      then show ?thesis
      proof(cases "{sender} \<union> ack = all")
        case True
        then have step:"coordinator_step (states 0) event = (Forgotten, {})"
          using \<open>msg = Ack\<close> Receive assms Committed by simp
        then have msgs:"msgs = msgs'"
          using assms(1,2) by auto
        moreover have "(\<exists>proc a ack'. states' proc = Committed a ack') \<longrightarrow> (\<exists>proc a ack'. states proc = Committed a ack')"
          using Committed by auto
        ultimately have 1:"inv1 msgs' states'"
          using assms(5) inv1_def by auto
        have "(\<exists>proc a ack'. states' proc = Aborted a ack') \<longleftrightarrow> (\<exists>proc a ack'. states proc = Aborted a ack')"
          by (metis Committed assms(1,3,5) fun_upd_apply inv1_def inv2_def inv3_def local.step prod.inject state.distinct(29))
        then have 2:"inv2 msgs' states'"
          using msgs by (metis assms(5) inv2_def)
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      next
        case False
        then have step:"coordinator_step (states 0) event = (Committed all (ack \<union> {sender}), {})"
          using \<open>msg = Ack\<close> Receive assms Committed by simp
         then have msgs:"msgs = msgs'"
          using assms(1,2) by auto
        moreover have "(\<exists>proc a ack'. states' proc = Committed a ack') \<longrightarrow> (\<exists>proc a ack'. states proc = Committed a ack')"
          using Committed by auto
        ultimately have 1:"inv1 msgs' states'"
          using assms(5) inv1_def by auto
        have "(\<exists>proc a ack'. states' proc = Aborted a ack') \<longleftrightarrow> (\<exists>proc a ack'. states proc = Aborted a ack')"
          by (metis Committed Pair_inject assms(1,3) fun_upd_def local.step state.distinct(25))
        then have 2:"inv2 msgs' states'"
          using msgs by (metis assms(5) inv2_def)
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      qed
    next
      case False
      then have step:"coordinator_step (states 0) event = (states 0, {})"
        using Committed Receive by(cases msg; simp)
      then have "msgs' = msgs"
        by (simp add: assms(1,2))
      moreover have "states' = states"
        using step assms(1,3)by auto
      ultimately show ?thesis
        using assms(5) by auto
    qed
  next
    case (Aborted all ack)
        then show ?thesis
    proof(cases "msg = Ack")
      case True
      then show ?thesis
      proof(cases "{sender} \<union> ack = all")
        case True
        then have step:"coordinator_step (states 0) event = (Forgotten, {})"
          using \<open>msg = Ack\<close> Receive assms Aborted by simp
        then have msgs:"msgs = msgs'"
          using assms(1,2) by auto
        moreover have "(\<exists>proc a ack'. states' proc = Committed a ack') \<longrightarrow> (\<exists>proc a ack'. states proc = Committed a ack')"
          using Aborted assms(1,3) step by auto
        ultimately have 1:"inv1 msgs' states'"
          using assms(5) inv1_def by auto
        have 2:"inv2 msgs' states'"
          using msgs by (metis Aborted assms(5) inv2_def)
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      next
        case False
        then have step:"coordinator_step (states 0) event = (Aborted all (ack \<union> {sender}), {})"
          using \<open>msg = Ack\<close> Receive assms Aborted by simp
         then have msgs:"msgs = msgs'"
          using assms(1,2) by auto
        moreover have "(\<exists>proc a ack'. states' proc = Committed a ack') \<longrightarrow> (\<exists>proc a ack'. states proc = Committed a ack')"
          using Aborted assms(1,3) step by auto
        ultimately have 1:"inv1 msgs' states'"
          using assms(5) inv1_def by auto
        have "(\<exists>proc a ack'. states' proc = Aborted a ack') \<longleftrightarrow> (\<exists>proc a ack'. states proc = Aborted a ack')"
          by (metis Aborted Pair_inject assms(1,3) fun_upd_def local.step)
        then have 2:"inv2 msgs' states'"
          using msgs by (metis assms(5) inv2_def)
        have "inv3 msgs' states'"
          by (metis assms(5) inv3_def msgs)
        then show ?thesis
          using 1 2 by simp
      qed
    next
      case False
      then have step:"coordinator_step (states 0) event = (states 0, {})"
        using Aborted Receive by(cases msg; simp)
      then have "msgs' = msgs"
        by (simp add: assms(1,2))
      moreover have "states' = states"
        using step assms(1,3)by auto
      ultimately show ?thesis
        using assms(5) by auto
    qed
  next
    case Forgotten
    then show ?thesis
      by (metis assms(1,2,3,5) coordinator_step.simps(22) fun_upd_triv image_empty prod.inject sup_bot_right)
  qed
next
  case Timeout
  then show ?thesis
    using assms(1,2,3,5) by auto
qed

lemma invariant_participant:
  assumes "participant_step (states proc) event = (new_state, sent)"
    and "proc \<noteq> 0"
    and "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
    and "states' = states (proc := new_state)"
    and "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV) UNIV (events @ [(proc, event)]) msgs' states'"
    and "inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs states"
  shows "inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs' states'"
proof (cases event)
  case (Start)
  then show ?thesis
    using assms(1,2,3,4,6) by auto
next
  case (Receive sender msg)
  then show ?thesis
  proof(cases "states proc")
    case (Initial t all)
    then show ?thesis 
    proof(cases msg)
      case (Prepare t')
      then show ?thesis
      proof(cases "t = t'")
        case True
        then have step:"participant_step (states proc) event = (Prepared, {Send sender Yes})"
          using Receive Initial Prepare by simp
        then have 1:"inv1 msgs' states'"
          by (metis Un_iff assms(1,3,4,6) fun_upd_apply inv1_def old.prod.inject state.distinct(19))
        have 2:"inv2 msgs' states'"
          by (smt (verit, ccfv_threshold) Un_empty_right Un_insert_right assms(1,3,4,6) fun_upd_apply image_insert image_is_empty
              insert_iff inv2_def old.prod.inject state.distinct(21) step)
        have "inv3 msgs' states'"
          sorry
        then show ?thesis
          using 1 2 by simp
      next
        case False
        then have step:"participant_step (states proc) event = (Aborted {} {}, {Send sender No})"
          using Receive Initial Prepare by simp
        then have "\<forall>a ack' p. (states p = Committed a ack') \<longleftrightarrow> (states' p = Committed a ack')"
          using Initial assms(1,4) by auto
        moreover have "\<forall>sender rcpt. (sender, Send rcpt Commit) \<in> msgs \<longleftrightarrow> (sender, Send rcpt Commit) \<in> msgs'"
          using step assms(1,3) by auto
        ultimately have 1:"inv1 msgs' states'"
          using inv1_def by (metis assms(6))
        have "\<forall>a ack' p. (states p = Aborted a ack') \<longleftrightarrow> (states' p = Aborted a ack')"
          using step Initial assms(1,4) sorry
        moreover have "\<forall>rcpt. (Send rcpt Commit) \<notin> sent"
          using step assms(1,3) sorry
        have 2:"inv2 msgs' states'"
          using inv2_def
          sorry
        have "inv3 msgs' states'"
          sorry
        then show ?thesis
          sorry
      qed
    next
      case Yes
      then show ?thesis
        using Initial Receive assms(1,3,4,6) by force
    next
      case No
      then show ?thesis
        using Initial Receive assms(1,3,4,6) by force
    next
      case Commit
      then show ?thesis
        using Initial Receive assms(1,3,4,6) by force
    next
      case Abort
      then show ?thesis
        using Initial Receive assms(1,3,4,6) by force
    next
      case Ack
      then show ?thesis
        using Initial Receive assms(1,3,4,6) by force
    qed
  next
    case (Collecting _ _ _)
    then show ?thesis
      using assms(1,3,4,6) by fastforce
  next
    case Prepared
    then show ?thesis
      sorry
  next
    case (Committed x41 x42)
    then show ?thesis 
      sorry
  next
    case (Aborted x51 x52)
    then show ?thesis 
      sorry
  next
    case Forgotten
    then show ?thesis
      by (metis assms(1,3,4,6) empty_is_image fun_upd_triv participant_step.simps(22) prod.inject sup_bot_right)
  qed
next
  case Timeout
  then show ?thesis
    using assms(1,2,3,4,6) by auto
qed

lemma invariants123:
  assumes \<open>execute tupac_step (\<lambda>p. Initial (init_val p) UNIV) UNIV events msgs' states'\<close>
  shows "inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs' states'"
using assms proof(induction events arbitrary: msgs' states' rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis empty_iff execute_init inv1_def inv2_def inv3_def state.distinct(5,7))
next
  case (snoc x events)
  obtain proc event where "x = (proc, event)"
    by fastforce
  hence exec: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV) UNIV
               (events @ [(proc, event)]) msgs' states'"
    using snoc.prems by blast
  from this obtain msgs states sent new_state
    where step_rel1: "execute tupac_step (\<lambda>p. Initial (init_val p) UNIV) UNIV events msgs states"
      and step_rel2: "tupac_step proc (states proc) event = (new_state, sent)"
      and step_rel3: "msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent)"
      and step_rel4: "states' = states (proc := new_state)"
    by auto
  have inv_before: "inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs states"
    using snoc.IH step_rel1 by fastforce
  then show "inv1 msgs' states' \<and> inv2 msgs' states' \<and> inv3 msgs' states'"
  proof (cases "proc = 0")
    case True
    then have "coordinator_step (states 0) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv0 msgs states \<and> inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs states"
      using inv_before invariant0[of "(\<lambda>p. (init_val p))" events msgs states] step_rel1 by simp
    ultimately show ?thesis
      using invariant_coordinator True step_rel3 step_rel4 exec by metis
  next
    case False
    then have "participant_step (states proc) event = (new_state, sent)"
      using step_rel2 by simp
    moreover have"inv1 msgs states \<and> inv2 msgs states \<and> inv3 msgs states"
      using inv_before by simp
    ultimately show ?thesis
      using invariant_participant False step_rel3 step_rel4 exec by metis
  qed
qed

end