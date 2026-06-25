theory Kleppmann_2PC
  imports Network
begin

datatype 't msg = Prepare (transaction: 't) | Yes | No | Commit | Abort | Ack

datatype ('t, 'proc) state = Initial (transaction: 't) (all: "'proc set") (retry_count:"nat")
  | Collecting (transaction: 't) (all: "'proc set") (yes:"'proc set") (retry_count:"nat")
  | Prepared 
  | Committed (all: "'proc set") (ack: "'proc set") 
  | Aborted (all: "'proc set") (ack: "'proc set") 
  | Forgotten

fun coordinator_step:: 
    "'proc \<Rightarrow> ('t, 'proc) state \<Rightarrow> ('proc, 't msg) event \<Rightarrow> ('t, 'proc) state \<times> ('proc, 't msg) send set"  where
  \<open>coordinator_step pid (Initial t a r) Start = (Collecting t a {pid} r, {Send p (Prepare t) | p. p \<in> a})\<close> |
  \<open>coordinator_step pid (Collecting t a y r) (Receive sender msg) = 
      (case msg of
        Yes \<Rightarrow>(if y \<union> {sender} = a then (Committed a {pid}, {Send p (Commit) | p. p \<in> a}) else (Collecting t a (y \<union> {sender}) r, {})) |
        No \<Rightarrow>(Aborted a {pid}, {Send p (Abort) | p. p \<in> a}) |
        _ \<Rightarrow>(Collecting t a y r, {}))\<close> |
  \<open>coordinator_step pid (Collecting t a y 0) Timeout = (Aborted a {pid}, {Send p (Abort) | p. p \<in> a})\<close> |
  \<open>coordinator_step _ (Collecting t a y (Suc r)) Timeout = (Collecting t a y r, {Send p (Prepare t) | p. p \<in> (a - y)})\<close> |
  \<open>coordinator_step _ (Committed a ack') (Receive sender Ack) = 
      (if {sender} \<union> ack' = a then (Forgotten, {}) else (Committed a (ack' \<union> {sender}), {}))\<close> |
  \<open>coordinator_step _ (Committed a ack') Timeout = (Committed a ack', {Send p Commit | p. p \<in> (a - ack')})\<close> |
  \<open>coordinator_step _ (Committed a ack') Restart = (Committed a ack', {Send p Commit | p. p \<in> a})\<close> |
  \<open>coordinator_step _ (Aborted a ack') (Receive sender Ack) = 
      (if {sender} \<union> ack' = a then (Forgotten, {}) else (Aborted a (ack' \<union> {sender}), {}))\<close> |
  \<open>coordinator_step _ (Aborted a ack') Timeout = (Aborted a ack', {Send p Abort  | p. p \<in> (a - ack')})\<close> |
  \<open>coordinator_step _ (Aborted a ack') Restart = (Aborted a ack', {Send p Abort  | p. p \<in> a})\<close> |
  \<open>coordinator_step _ state _ = (state, {})\<close>

fun participant_step::
    "('t, 'proc) state \<Rightarrow> ('proc, 't msg) event \<Rightarrow> ('t, 'proc) state \<times> ('proc, 't msg) send set" where
  \<open>participant_step (Initial t _ _) (Receive sender (Prepare t')) = (if t = t' then (Prepared, {Send sender Yes}) else (Aborted {} {}, {Send sender No}))\<close> |
  \<open>participant_step (Initial _ _ _) Timeout = (Aborted {} {}, {})\<close> |
  \<open>participant_step Prepared (Receive sender msg) = 
      (case msg of
        Commit \<Rightarrow> (Committed {} {}, {Send sender Ack}) |
        Abort \<Rightarrow> (Aborted {} {}, {Send sender Ack}) |
        _ \<Rightarrow> (Prepared, {}))\<close> |
  \<open>participant_step (Committed _ _) (Receive sender Commit) = (Committed {} {}, {Send sender Ack})\<close> |
  \<open>participant_step (Aborted _ _) (Receive sender Abort) = (Aborted {} {}, {Send sender Ack})\<close> |
  \<open>participant_step state _ = (state, {})\<close>

fun tupac_step where
  \<open>tupac_step proc = (if proc = 0 then coordinator_step proc else participant_step)\<close>

end