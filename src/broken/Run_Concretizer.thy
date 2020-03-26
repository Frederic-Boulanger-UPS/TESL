theory Run_Concretizer

imports Run SymbolicPrimitive

begin

(* Update functionals *)
fun time_update :: "nat \<Rightarrow> clock \<Rightarrow> '\<tau> tag_const \<Rightarrow> ('\<tau>::linordered_field) run \<Rightarrow> '\<tau> run" where
  "time_update n K \<tau> \<rho> =
   Abs_run (\<lambda>n' K'. if K = K' \<and> n = n'
                    then (hamlet ((Rep_run \<rho>) n K), \<tau>)
                    else ((Rep_run \<rho>) n' K'))"

fun run_update :: "('\<tau>::linordered_field) run \<Rightarrow> '\<tau> constr \<Rightarrow> '\<tau> run" ("_ \<langle> _ \<rangle>") where
    "\<rho> \<langle> K \<Up> n \<rangle>  = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (True, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<not>\<Up> n \<rangle> = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (False, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<Down> n @ \<lparr> \<tau> \<rparr> \<rangle> = time_update n K \<tau> \<rho>"
  | "\<rho> \<langle> K \<Down> n @ \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rparr> \<rangle> =
     time_update n K (time ((Rep_run \<rho>) n' K') + \<tau>) \<rho>"
  | "\<rho> \<langle> K \<not>\<Up> < n \<rangle> = Abs_run (\<lambda>n' K'. if K = K' \<and> n' < n then (False, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<not>\<Up> \<ge> n \<rangle> = Abs_run (\<lambda>n' K'. if K = K' \<and> n' \<ge> n then (False, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> \<lfloor>_, _\<rfloor> \<in> _ \<rangle> = undefined"

fun run_update' :: "('\<tau>::linordered_field) constr list \<Rightarrow> '\<tau> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = (\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>)"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<Longrightarrow> consistent_context \<Gamma>"
  unfolding consistent_context_def by (rule exI, auto)

lemma witness_consistency':
  "consistent_context \<Gamma> \<Longrightarrow> \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m"
  oops (* Not sure the idea is true *)

(*<*)
text\<open>Do we want to explain this trick? Is it still useful?\<close>
(* WARNING: Admitting monotonicity to compute faster. Use for debugging purposes only. *)
lemma Abs_run_inverse_rewrite_unsafe:
  "Rep_run (Abs_run \<rho>) = \<rho>"
sorry (* Use [sorry] when testing *)
(*>*)


end
