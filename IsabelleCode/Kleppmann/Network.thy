theory
  Network
imports
  Main
begin

datatype ('proc, 'msg) send
  = Send (msg_recipient: 'proc) (send_msg: 'msg)

datatype ('proc, 'msg) event
  = Start
  | Receive (msg_sender: 'proc) (recv_msg: 'msg)
  | Timeout
  | Restart

type_synonym ('proc, 'state, 'msg) step_func =
  "'proc \<Rightarrow> 'state \<Rightarrow> ('proc, 'msg) event \<Rightarrow> ('state \<times> ('proc, 'msg) send set)"

fun valid_event :: "('proc, 'msg) event \<Rightarrow> 'proc \<Rightarrow>
                    ('proc \<times> ('proc, 'msg) send) set \<Rightarrow> bool" where
  "valid_event Start _ _ = True" |
  "valid_event (Receive sender msg) proc msgs = ((sender, Send proc msg) \<in> msgs)" |
  "valid_event _ _ _ = True"

inductive execute ::
    "('proc, 'state, 'msg) step_func \<Rightarrow> ('proc \<Rightarrow> 'state) \<Rightarrow> 'proc set \<Rightarrow>
     ('proc \<times> ('proc, 'msg) event) list \<Rightarrow>
     ('proc \<times> ('proc, 'msg) send) set \<Rightarrow> ('proc \<Rightarrow> 'state) \<Rightarrow> bool" where
  "execute step init procs [] {} init" |
  "\<lbrakk>execute step init procs events msgs states;
    proc \<in> procs;
    valid_event event proc msgs;
    step proc (states proc) event = (new_state, sent);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent);
    states' = states (proc := new_state)
   \<rbrakk> \<Longrightarrow> execute step init procs events' msgs' states'"

inductive_cases execute_indcases: "execute step init procs events msg states"

lemma execute_init:
  assumes "execute step init procs [] msgs states"
  shows "msgs = {} \<and> states = init"
  using assms by(auto elim: execute.cases)

inductive_cases execute_snocE [elim!]:
  "execute step init procs (events @ [(proc, event)]) msgs' states'"

lemma execute_step:
  assumes "execute step init procs (events @ [(proc, event)]) msgs' states'"
  shows "\<exists>msgs states sent new_state.
          execute step init procs events msgs states \<and>
          proc \<in> procs \<and>
          valid_event event proc msgs \<and>
          step proc (states proc) event = (new_state, sent) \<and>
          msgs' = msgs \<union> ((\<lambda>msg. (proc, msg)) ` sent) \<and>
          states' = states (proc := new_state)"
  using assms by blast

lemma execute_receive:
  assumes "execute step init procs (events @ [(recpt, Receive sender msg)]) msgs' states'"
  shows "(sender, Send recpt msg) \<in> msgs'"
  using assms execute_step by fastforce

end