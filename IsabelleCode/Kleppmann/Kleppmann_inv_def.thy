theory Kleppmann_inv_def
  imports Kleppmann_2PC
begin

(* Invariant 1: for any participant p, if p's state is ``Committed'',
   then there exists a message ``Commit''*)

definition inv1 where
  \<open>inv1 msgs states \<longleftrightarrow>
     ((\<exists>proc a ack'. proc \<noteq> 0 \<and> states proc = Committed a ack') \<longrightarrow>
                 (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs))\<close>

definition inv11 where
  \<open>inv11 msgs states procs \<longleftrightarrow>
    ((\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<or> (\<exists>all ack. states 0 = Committed all ack) \<longrightarrow>
                 (\<forall>p \<in> procs. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)))\<close>

definition inv12 where
  \<open>inv12 msgs states procs \<longleftrightarrow>
    (\<forall>p \<in> procs. p \<noteq> 0 \<longrightarrow> ((\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs) \<longrightarrow> (\<forall>rcpt. (p, Send rcpt No) \<notin> msgs)))\<close>

definition inv13 where
  \<open>inv13 msgs states procs \<longleftrightarrow>
    (\<forall>t all yes r. states 0 = Collecting t all yes r \<longrightarrow> 
                (procs = all \<and> (\<forall>p \<in> yes. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs))))\<close>

definition inv14 where
  \<open>inv14 msgs states procs \<longleftrightarrow>
    (\<forall>t all r. states 0 = Initial t all r \<longrightarrow> procs = all)\<close>

definition inv15 where
  \<open>inv15 msgs states \<longleftrightarrow>
    ((\<exists>t all yes r. states 0 = Initial t all r \<or> states 0 = Collecting t all yes r \<or> states 0 = Committed all yes) \<longrightarrow> 
              (\<forall>sender rcpt. (sender, Send rcpt Abort) \<notin> msgs))\<close>

definition inv16 where
  \<open>inv16 msgs states \<longleftrightarrow>
    (\<forall>sender rcpt. (sender, Send rcpt Yes) \<in> msgs \<longrightarrow> (states sender = Prepared \<or> states sender = Aborted {} {} \<or> states sender = Committed {} {}))\<close>

definition inv17 where
  \<open>inv17 msgs states \<longleftrightarrow>
    (\<forall>p. p \<noteq> 0 \<and> (\<exists>all ack. states p = Aborted all ack) \<and> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs) \<longrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs))\<close>

definition inv18 where
  \<open>inv18 msgs states \<longleftrightarrow>
    (\<forall>p t all r. p \<noteq> 0 \<and> states p = Initial t all r \<longrightarrow> (\<forall>rcpt. (p, Send rcpt Yes) \<notin> msgs))\<close>

definition inv19 where
  \<open>inv19 msgs states \<longleftrightarrow>
    ((\<exists>all ack. states 0 = Committed all ack) \<longrightarrow> (\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs))\<close>

definition inv110 where
  \<open>inv110 msgs states \<longleftrightarrow>
    ((\<exists>t all yes r. states 0 = Initial t all r \<or> states 0 = Collecting t all yes r \<or> states 0 = Aborted all yes) \<longrightarrow> 
              (\<forall>sender rcpt. (sender, Send rcpt Commit) \<notin> msgs))\<close>

definition inv111 where
  \<open>inv111 msgs states \<longleftrightarrow>
    ((\<exists>sender rcpt. (sender, Send rcpt Commit) \<in> msgs) \<longrightarrow> (\<exists>all ack. states 0 = Committed all ack \<or> states 0 = Forgotten))\<close>

definition inv112 where
  \<open>inv112 msgs states procs \<longleftrightarrow>
    ((\<exists>all ack. states 0 = Committed all ack) \<longrightarrow> (\<forall>p \<in> procs. p \<noteq> 0 \<longrightarrow> (\<exists>rcpt. (p, Send rcpt Yes) \<in> msgs)))\<close>

(* Invariant 3: if a Commit msg has been sent then an abort or no msg cannot also have been sent*)

definition inv3 where
  \<open>inv3 msgs states \<longleftrightarrow>
    (\<exists>sender recpt. (sender, Send recpt Commit) \<in> msgs) \<longrightarrow> (\<forall>sender recpt. (sender, Send recpt Abort) \<notin> msgs)\<close>

definition inv21 where
  \<open>inv21 p old_state new_state \<longleftrightarrow> 
    (\<exists>all ack. old_state = Committed all ack) \<longrightarrow> (\<exists>all ack. new_state = Committed all ack \<or> (p = 0 \<and> new_state = Forgotten))\<close>

definition inv22 where
  \<open>inv22 p old_state new_state \<longleftrightarrow> 
    (\<exists>all ack. old_state = Aborted all ack) \<longrightarrow> (\<exists>all ack. new_state = Aborted all ack \<or> (p = 0 \<and> new_state = Forgotten))\<close>

definition inv23 where
  \<open>inv23 p old_state new_state \<longleftrightarrow>
    (old_state = Forgotten \<longrightarrow> (p = 0 \<and> new_state = Forgotten))\<close>

definition inv24 where
  \<open>inv24 states \<longleftrightarrow>
    (\<forall>p \<noteq> 0.  states p \<noteq> Forgotten)\<close>

definition inv41 where
  \<open>inv41 msgs states \<longleftrightarrow>
    ((\<exists>t a r. states 0 = Initial t a r) \<longrightarrow> msgs = {})\<close>

definition inv42 where
  \<open>inv42 msgs \<longleftrightarrow>
    (\<forall>proc rcpt t. (proc, Send rcpt (Prepare t)) \<in> msgs \<longrightarrow> proc = 0)\<close>

definition inv43 where
  \<open>inv43 msgs init_val\<longleftrightarrow>
    (\<forall>rcpt t. (0, Send rcpt (Prepare t)) \<in> msgs \<longrightarrow> t = init_val)\<close>

definition inv44 where
  \<open>inv44 msgs states \<longleftrightarrow>
    ((\<exists>t a r. states 0 = Initial t a r) \<longrightarrow> (\<forall>proc rcpt t. (proc, Send rcpt (Prepare t)) \<notin> msgs))\<close>

end