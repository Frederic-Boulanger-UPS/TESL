theory Hygge_Example
imports
  "Hygge_Solver"

begin

(* To decide finite-satisfiability of TESL specifications *)
inductive finite_SAT :: "('\<tau>::linordered_field) config \<Rightarrow> bool" ("\<TTurnstile> _" 50) where
  finite_SAT_ax: "set (NoSporadic \<Phi>) = set \<Phi> \<Longrightarrow>
                    consistent_run \<Gamma> \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
| finite_SAT_i: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow> (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)"


(* Running on a small example:
  H1 sporadic 1, 2
  H1 implies H2
*)
abbreviation \<H>\<^sub>1 where "\<H>\<^sub>1 \<equiv> Clk ''H1''"
abbreviation \<H>\<^sub>2 where "\<H>\<^sub>2 \<equiv> Clk ''H2''"
abbreviation \<Phi>\<^sub>0 where "\<Phi>\<^sub>0 \<equiv> [
    \<H>\<^sub>1 sporadic \<lparr> \<tau>\<^sub>c\<^sub>s\<^sub>t 1 \<rparr> on \<H>\<^sub>1,
    \<H>\<^sub>1 sporadic \<lparr> \<tau>\<^sub>c\<^sub>s\<^sub>t 2 \<rparr> on \<H>\<^sub>1,
    \<H>\<^sub>1 implies \<H>\<^sub>2
]"


lemma "\<TTurnstile> [], 0 \<turnstile> [] \<triangleright> \<Phi>\<^sub>0"
apply (rule finite_SAT_i)
  apply (rule intro_part)
    apply (rule instant_i)
apply (rule finite_SAT_i)
  apply (rule elims_part)
    apply (rule elims)
apply (rule finite_SAT_i)
  apply (rule elims_part)
    apply (rule elims)
apply (rule finite_SAT_i)
  apply (rule elims_part)
    apply (rule elims)

(*
apply (heron_next_step_UNSAFE) print_run
apply (heron_next_step_UNSAFE) print_run
apply (heron_next_step_UNSAFE) print_run
by (heron_end_UNSAFE)
*)

(* The above reductions admit monotonicity to compute faster.
   They may produce non-monotonic runs but can be computed in reasonable time. *)
(*
apply (heron_next_step) print_run
apply (heron_next_step) print_run
by (heron_end)
*)
end