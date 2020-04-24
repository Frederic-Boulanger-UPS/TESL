(*chapter\<open>Equivalence of Operational and Denotational Semantics\<close>*)
text\<open>\chapter[Semantics Equivalence]{Equivalence of the Operational and Denotational Semantics}\<close>

theory Corecursive_Prop
  imports
    SymbolicPrimitive
    Operational
    Denotational

begin

section \<open>Stepwise denotational interpretation of TESL atoms\<close>

text \<open>
  In order to prove the equivalence of the denotational and operational semantics, 
  we need to be able to ignore the past (for which the constraints are encoded 
  in the context) and consider only the satisfaction of the constraints from
  a given instant index.
  For this purpose, we define an interpretation of TESL formulae for a suffix of a run.
  That interpretation is closely related to the denotational semantics as
  defined in the preceding chapters.
\<close>
fun TESL_interpretation_atomic_stepwise
    :: \<open>('\<tau>::linordered_field) TESL_atomic \<Rightarrow> nat \<Rightarrow> '\<tau> run set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>\<close>)
where
  \<open>\<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<exists>n\<ge>i. ticks ((Rep_run \<rho>) n C\<^sub>1) \<and> time ((Rep_run \<rho>) n C\<^sub>2) = \<tau>}\<close>
| \<open>\<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau>\<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<exists>n\<ge>i. ticks ((Rep_run \<rho>) n C\<^sub>1)
                         \<and> time ((Rep_run \<rho>) n C\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>p\<^sub>a\<^sub>s\<^sub>t C\<^sub>p\<^sub>a\<^sub>s\<^sub>t) + \<delta>\<tau> }\<close>
| \<open>\<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. R (time ((Rep_run \<rho>) n C\<^sub>1), time ((Rep_run \<rho>) n C\<^sub>2))}\<close>
| \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n master) \<longrightarrow> ticks ((Rep_run \<rho>) n slave)}\<close>
| \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n master) \<longrightarrow> \<not> ticks ((Rep_run \<rho>) n slave)}\<close>
| \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) n measuring) in
                \<forall>m \<ge> n. first_time \<rho> measuring m (measured_time + \<delta>\<tau>)
                         \<longrightarrow> ticks ((Rep_run \<rho>) m slave)
               )
      }\<close>
| \<open>\<lbrakk> master time-delayed\<bowtie> by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) n measuring) in
                \<exists>m \<ge> n. ticks ((Rep_run \<rho>) m slave)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
               )
      }\<close>
| \<open>\<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. (run_tick_count \<rho> C\<^sub>2 n) \<le> (run_tick_count \<rho> C\<^sub>1 n)}\<close>
| \<open>\<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. (run_tick_count \<rho> C\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> C\<^sub>1 n)}\<close>
| \<open>\<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n C\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> ticks ((Rep_run \<rho>) m C\<^sub>2))}\<close>
| \<open>\<lbrakk> K1 delayed by d on K2 implies K3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. ticks ((Rep_run \<rho>) n K1) \<longrightarrow>
                 (
                  \<forall>m \<ge> n.  counted_ticks \<rho> K2 n m d
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K3)
                 )
      }\<close>
| \<open>\<lbrakk> from n delay count d on K2 implies K3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
    {\<rho>. \<forall>m\<ge>i. (m \<ge> n \<and> counted_ticks \<rho> K2 n m d) \<longrightarrow> ticks ((Rep_run \<rho>) m K3)}
  \<close>

text \<open>
  The denotational interpretation of TESL formulae can be unfolded into the 
  stepwise interpretation.
\<close>
lemma TESL_interp_unfold_stepwise_sporadicon:
  \<open>\<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_sporadicon_tvar:
  \<open>\<lbrakk> C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
proof (induction \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r)
  case (AddDelay x1a \<tau>)
  then show ?case 
  proof (induction x1a)
    case (TSchematic xa)
    then show ?case
    proof (induction xa)
      case (Pair K n')
      then show ?case by auto
    qed
  qed
qed

lemma TESL_interp_unfold_stepwise_tagrelgen:
  \<open>\<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_implies:
  \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_implies_not:
  \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_timedelayed:
  \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat.
          Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_timedelayed_tvar:
  \<open>\<lbrakk> master time-delayed\<bowtie> by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat.
          Y = \<lbrakk> master time-delayed\<bowtie> by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_weakly_precedes:
  \<open>\<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_strictly_precedes:
  \<open>\<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_kills:
  \<open>\<lbrakk> master kills slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master kills slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_delayed:
  \<open>\<lbrakk> master delayed by d on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n. Y = \<lbrakk> master delayed by d on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_counting:
  \<open>\<lbrakk> from i delay count d on counter implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n. Y = \<lbrakk> from i delay count d on counter implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

text \<open>
  Positive atomic formulae (the ones that create ticks from nothing) are unfolded
  as the union of the stepwise interpretations.
\<close>

theorem TESL_interp_unfold_stepwise_positive_atoms:
  assumes \<open>positive_atom \<phi>\<close>
    shows \<open>\<lbrakk> \<phi>::'\<tau>::linordered_field TESL_atomic \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
            = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
proof (cases \<phi>)
  case SporadicOn thus ?thesis using TESL_interp_unfold_stepwise_sporadicon by simp
next
  case SporadicOnTvar thus ?thesis using TESL_interp_unfold_stepwise_sporadicon_tvar by simp
next
  case TagRelation thus ?thesis using assms by simp
next
  case Implies thus ?thesis using assms by simp
next
  case ImpliesNot thus ?thesis using assms by simp
next
  case TimeDelayedBy thus ?thesis using assms by simp
next
  case RelaxedTimeDelayed thus ?thesis using assms by simp
next
  case WeaklyPrecedes thus ?thesis using assms by simp
next
  case StrictlyPrecedes thus ?thesis using assms by simp
next
  case Kills thus ?thesis using assms by simp
next
  case (DelayedBy x101 x102 x103 x104)
  then show ?thesis sorry
next
  case (DelayCount x121 x122 x123 x124)
  then show ?thesis sorry
qed
(*
proof -
  from positive_atom.elims(2)[OF assms]
    obtain u v w where \<open>\<phi> = (u sporadic v on w)\<close> by blast
  with TESL_interp_unfold_stepwise_sporadicon show ?thesis by simp
qed
*)
  

text \<open>
  Negative atomic formulae are unfolded
  as the intersection of the stepwise interpretations.
\<close>
theorem TESL_interp_unfold_stepwise_negative_atoms:
  assumes \<open>\<not> positive_atom \<phi>\<close>
    shows \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
proof (cases \<phi>)
  case SporadicOn thus ?thesis using assms by simp
next
  case SporadicOnTvar thus ?thesis using assms by simp
next
  case TagRelation
    thus ?thesis using TESL_interp_unfold_stepwise_tagrelgen by simp
next
  case Implies
    thus ?thesis using TESL_interp_unfold_stepwise_implies by simp
next
  case ImpliesNot
    thus ?thesis using TESL_interp_unfold_stepwise_implies_not by simp
next
  case TimeDelayedBy
    thus ?thesis using TESL_interp_unfold_stepwise_timedelayed by simp
next
  case RelaxedTimeDelayed
    thus ?thesis using TESL_interp_unfold_stepwise_timedelayed_tvar by simp
next
  case WeaklyPrecedes
    thus ?thesis
      using TESL_interp_unfold_stepwise_weakly_precedes by simp
next
  case StrictlyPrecedes
    thus ?thesis
      using TESL_interp_unfold_stepwise_strictly_precedes by simp
next
  case Kills
    thus ?thesis
      using TESL_interp_unfold_stepwise_kills by simp
next
  case DelayedBy
    thus ?thesis using TESL_interp_unfold_stepwise_delayed by simp
next
  case DelayCount
    thus ?thesis using TESL_interp_unfold_stepwise_counting by simp
qed

text \<open>
  Some useful lemmas for reasoning on properties of sequences.
\<close>
lemma forall_nat_expansion:
  \<open>(\<forall>n \<ge> (n\<^sub>0::nat). P n) = (P n\<^sub>0 \<and> (\<forall>n \<ge> Suc n\<^sub>0. P n))\<close>
proof -
  have \<open>(\<forall>n \<ge> (n\<^sub>0::nat). P n) = (\<forall>n. (n = n\<^sub>0 \<or> n > n\<^sub>0) \<longrightarrow> P n)\<close>
    using le_less by blast
  also have \<open>... = (P n\<^sub>0 \<and> (\<forall>n > n\<^sub>0. P n))\<close> by blast
  finally show ?thesis using Suc_le_eq by simp
qed

lemma exists_nat_expansion:
  \<open>(\<exists>n \<ge> (n\<^sub>0::nat). P n) = (P n\<^sub>0 \<or> (\<exists>n \<ge> Suc n\<^sub>0. P n))\<close>
proof -
  have \<open>(\<exists>n \<ge> (n\<^sub>0::nat). P n) = (\<exists>n. (n = n\<^sub>0 \<or> n > n\<^sub>0) \<and> P n)\<close>
    using le_less by blast
  also have \<open>... = (\<exists>n. (P n\<^sub>0) \<or> (n > n\<^sub>0 \<and> P n))\<close> by blast
  finally show ?thesis using Suc_le_eq by simp
qed

lemma forall_nat_set_suc:\<open>{x. \<forall>m \<ge> n. P x m} = {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
proof
  { fix x assume h:\<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>x \<in> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
    ultimately have \<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
  } thus \<open>{x. \<forall>m \<ge> n. P x m} \<subseteq> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> ..
next
  { fix x  assume h:\<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>\<forall>m \<ge> Suc n. P x m\<close> by simp
    ultimately have \<open>\<forall>m \<ge> n. P x m\<close> using forall_nat_expansion by blast
    hence \<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close> by simp
  } thus \<open>{x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m} \<subseteq> {x. \<forall>m \<ge> n. P x m}\<close> ..
qed

lemma exists_nat_set_suc:\<open>{x. \<exists>m \<ge> n. P x m} = {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close>
proof
  { fix x assume h:\<open>x \<in> {x. \<exists>m \<ge> n. P x m}\<close>
    hence \<open>x \<in> {x. \<exists>m. (m = n \<or> m \<ge> Suc n) \<and> P x m}\<close>
      using Suc_le_eq antisym_conv2 by fastforce
    hence \<open>x \<in> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close> by blast
  } thus \<open>{x. \<exists>m \<ge> n. P x m} \<subseteq> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close> ..
next
  { fix x  assume h:\<open>x \<in> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close>
    hence \<open>x \<in> {x. \<exists>m \<ge> n. P x m}\<close> using Suc_leD by blast
  } thus \<open>{x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m} \<subseteq> {x. \<exists>m \<ge> n. P x m}\<close> ..
qed

section \<open>Coinduction Unfolding Properties\<close>

text \<open>
  The following lemmas show how  to shorten a suffix, i.e. to unfold one instant 
  in the construction of a run. They correspond to the rules of the operational 
  semantics.
\<close>

lemma TESL_interp_stepwise_sporadicon_coind_unfold:
  \<open>\<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m        \<comment> \<open>rule @{term sporadic_on_e2}\<close>
    \<union> \<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>   \<comment> \<open>rule @{term sporadic_on_e1}\<close>
unfolding TESL_interpretation_atomic_stepwise.simps(1)
          symbolic_run_interpretation_primitive.simps(1,6)
using exists_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. ticks (Rep_run \<rho> n C\<^sub>1)
                                     \<and> time (Rep_run \<rho> n C\<^sub>2) = \<tau>\<close>]
by (simp add: Collect_conj_eq)

lemma TESL_interp_stepwise_sporadicon_tvar_coind_unfold:
  \<open>\<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Down> n @\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rparr> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{ \<rho>. \<exists>m\<ge>n. ticks ((Rep_run \<rho>) m C\<^sub>1) = True \<and> time ((Rep_run \<rho>) m C\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau> }
      = { \<rho>. ticks ((Rep_run \<rho>) n C\<^sub>1) = True \<and> time ((Rep_run \<rho>) n C\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>
             \<or> (\<exists>m\<ge>Suc n. ticks ((Rep_run \<rho>) m C\<^sub>1) = True \<and> time ((Rep_run \<rho>) m C\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>) }\<close>
    using Suc_leD not_less_eq_eq by fastforce
  then show ?thesis by auto
qed

lemma TESL_interp_stepwise_sporadicon_tvar_coind_unfold2:
  \<open>\<lbrakk> C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Down> n @\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m        \<comment> \<open>rule @{term sporadic_on_tvar_e2}\<close>
    \<union> \<lbrakk> C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>   \<comment> \<open>rule @{term sporadic_on_tvar_e1}\<close>
proof -
  from tag_expr.exhaust obtain v \<tau> where \<open> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r=\<lparr> v \<oplus> \<tau> \<rparr>\<close> by blast
  moreover from tag_var.exhaust obtain K n where \<open>v=\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n)\<close> by auto
  ultimately have \<open>\<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r=\<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r(K, n) \<oplus> \<tau> \<rparr>\<close> by simp
  thus ?thesis using TESL_interp_stepwise_sporadicon_tvar_coind_unfold by blast
qed

lemma TESL_interp_stepwise_tagrel_coind_unfold:
  \<open>\<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =        \<comment> \<open>rule @{term tagrel_e}\<close>
     \<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
     \<inter> \<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. R (time ((Rep_run \<rho>) m C\<^sub>1), time ((Rep_run \<rho>) m C\<^sub>2))}
       = {\<rho>. R (time ((Rep_run \<rho>) n C\<^sub>1), time ((Rep_run \<rho>) n C\<^sub>2))}
       \<inter> {\<rho>. \<forall>m\<ge>Suc n. R (time ((Rep_run \<rho>) m C\<^sub>1), time ((Rep_run \<rho>) m C\<^sub>2))}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. R (time ((Rep_run x) y C\<^sub>1),
                                       time ((Rep_run x) y C\<^sub>2))\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_implies_coind_unfold:
  \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (   \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                     \<comment> \<open>rule @{term implies_e1}\<close>
       \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)  \<comment> \<open>rule @{term implies_e2}\<close>
     \<inter> \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. ticks ((Rep_run \<rho>) m master) \<longrightarrow> ticks ((Rep_run \<rho>) m slave)}
        = {\<rho>. ticks ((Rep_run \<rho>) n master) \<longrightarrow> ticks ((Rep_run \<rho>) n slave)}
        \<inter> {\<rho>. \<forall>m\<ge>Suc n. ticks ((Rep_run \<rho>) m master)
                     \<longrightarrow> ticks ((Rep_run \<rho>) m slave)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. ticks ((Rep_run x) y master)
                                \<longrightarrow> ticks ((Rep_run x) y slave)\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_implies_not_coind_unfold:
  \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (    \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                       \<comment> \<open>rule @{term implies_not_e1}\<close>
        \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)  \<comment> \<open>rule @{term implies_not_e2}\<close>
     \<inter> \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. ticks ((Rep_run \<rho>) m master) \<longrightarrow> \<not> ticks ((Rep_run \<rho>) m slave)}
       = {\<rho>. ticks ((Rep_run \<rho>) n master) \<longrightarrow> \<not> ticks ((Rep_run \<rho>) n slave)}
          \<inter> {\<rho>. \<forall>m\<ge>Suc n. ticks ((Rep_run \<rho>) m master)
                     \<longrightarrow> \<not> ticks ((Rep_run \<rho>) m slave)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. ticks ((Rep_run x) y master)
                               \<longrightarrow> \<not>ticks ((Rep_run x) y slave)\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_timedelayed_coind_unfold:
  \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (     \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m               \<comment> \<open>rule @{term timedelayed_e1}\<close>
        \<union> (\<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> measuring @ n \<oplus> \<delta>\<tau> \<Rightarrow> slave \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m))
                                             \<comment> \<open>rule @{term timedelayed_e2}\<close>
     \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?prop = \<open>\<lambda>\<rho> m. ticks ((Rep_run \<rho>) m master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) m measuring) in
                  \<forall>p \<ge> m. first_time \<rho> measuring p (measured_time + \<delta>\<tau>)
                           \<longrightarrow> ticks ((Rep_run \<rho>) p slave))\<close>
  have \<open>{\<rho>. \<forall>m \<ge> n. ?prop \<rho> m} = {\<rho>. ?prop \<rho> n} \<inter> {\<rho>. \<forall>m \<ge> Suc n. ?prop \<rho> m}\<close>
    using forall_nat_set_suc[of \<open>n\<close> ?prop] by blast
  also have \<open>... = {\<rho>. ?prop \<rho> n}
              \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  finally show ?thesis by auto
qed

lemma nat_set_suc:\<open>{x. \<forall>m \<ge> n. P x m} = {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
proof
  { fix x
    assume h:\<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>x \<in> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
    ultimately have \<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
  } thus \<open>{x. \<forall>m \<ge> n. P x m} \<subseteq> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> ..
next
  { fix x
    assume h:\<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>\<forall>m \<ge> Suc n. P x m\<close> by simp
    ultimately have \<open>\<forall>m \<ge> n. P x m\<close> using forall_nat_expansion by blast
    hence \<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close> by simp
  } thus \<open>{x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m} \<subseteq> {x. \<forall>m \<ge> n. P x m}\<close> ..
qed

lemma TESL_interp_stepwise_timedelayed_tvar_coind_unfold:
  \<open>\<lbrakk> master time-delayed\<bowtie> by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (     \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m               \<comment> \<open>rule @{term timedelayed_tvar_e1}\<close>
        \<union> (\<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave sporadic\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(measuring, n) \<oplus> \<delta>\<tau>\<rparr> on measuring \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>))
                                             \<comment> \<open>rule @{term timedelayed_tvar_e2}\<close>
     \<inter> \<lbrakk> master time-delayed\<bowtie> by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{ \<rho>. \<forall>m\<ge>n. ticks ((Rep_run \<rho>) m master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) m measuring) in
                \<exists>p \<ge> m. ticks ((Rep_run \<rho>) p slave)
                      \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}
       = { \<rho>. ticks ((Rep_run \<rho>) n master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) n measuring) in
                \<exists>p \<ge> n. ticks ((Rep_run \<rho>) p slave)
                      \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. ticks ((Rep_run \<rho>) m master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) m measuring) in
                \<exists>p \<ge> m. ticks ((Rep_run \<rho>) p slave)
                      \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}\<close>
  using nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. ticks ((Rep_run x) y master) \<longrightarrow>
               (let measured_time = time ((Rep_run x) y measuring) in
                \<exists>p \<ge> y. ticks ((Rep_run x) p slave)
                      \<and> time ((Rep_run x) p measuring) = measured_time + \<delta>\<tau>)\<close>] by simp
  then show ?thesis by auto
qed

lemma TESL_interp_stepwise_weakly_precedes_coind_unfold:
   \<open>\<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =                 \<comment> \<open>rule @{term weakly_precedes_e}\<close>
      \<lbrakk> (\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>\<le> C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
      \<inter> \<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>p\<ge>n. (run_tick_count \<rho> C\<^sub>2 p) \<le> (run_tick_count \<rho> C\<^sub>1 p)}
         = {\<rho>. (run_tick_count \<rho> C\<^sub>2 n) \<le> (run_tick_count \<rho> C\<^sub>1 n)}
         \<inter> {\<rho>. \<forall>p\<ge>Suc n. (run_tick_count \<rho> C\<^sub>2 p) \<le> (run_tick_count \<rho> C\<^sub>1 p)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. (run_tick_count \<rho> C\<^sub>2 n)
                                  \<le> (run_tick_count \<rho> C\<^sub>1 n)\<close>]
    by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_strictly_precedes_coind_unfold:
   \<open>\<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =               \<comment> \<open>rule @{term strictly_precedes_e}\<close>
      \<lbrakk> (\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>< C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
      \<inter> \<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>p\<ge>n. (run_tick_count \<rho> C\<^sub>2 p) \<le> (run_tick_count_strictly \<rho> C\<^sub>1 p)}
         = {\<rho>. (run_tick_count \<rho> C\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> C\<^sub>1 n)}
         \<inter> {\<rho>. \<forall>p\<ge>Suc n. (run_tick_count \<rho> C\<^sub>2 p) \<le> (run_tick_count_strictly \<rho> C\<^sub>1 p)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. (run_tick_count \<rho> C\<^sub>2 n)
                                  \<le> (run_tick_count_strictly \<rho> C\<^sub>1 n)\<close>]
    by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_kills_coind_unfold:
   \<open>\<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
      (   \<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                        \<comment> \<open>rule @{term kills_e1}\<close>
        \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)    \<comment> \<open>rule @{term kills_e2}\<close>
      \<inter> \<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?kills = \<open>\<lambda>n \<rho>. \<forall>p\<ge>n. ticks ((Rep_run \<rho>) p C\<^sub>1)
                             \<longrightarrow> (\<forall>m\<ge>p. \<not> ticks ((Rep_run \<rho>) m C\<^sub>2))\<close>
  let ?ticks = \<open>\<lambda>n \<rho> c. ticks ((Rep_run \<rho>) n c)\<close>
  let ?dead = \<open>\<lambda>n \<rho> c. \<forall>m \<ge> n. \<not>ticks ((Rep_run \<rho>) m c)\<close>
  have \<open>\<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = {\<rho>. ?kills n \<rho>}\<close> by simp
  also have \<open>... = ({\<rho>. \<not> ?ticks n \<rho> C\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2})\<close>
  proof
    { fix \<rho>::\<open>'\<tau>::linordered_field run\<close>
      assume \<open>\<rho> \<in> {\<rho>. ?kills n \<rho>}\<close>
      hence \<open>?kills n \<rho>\<close> by simp
      hence \<open>(?ticks n \<rho> C\<^sub>1 \<and> ?dead n \<rho> C\<^sub>2) \<or> (\<not>?ticks n \<rho> C\<^sub>1 \<and> ?kills (Suc n) \<rho>)\<close>
        using Suc_leD by blast
      hence \<open>\<rho> \<in> ({\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2})
               \<union> ({\<rho>. \<not> ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>})\<close>
        by blast
    } thus \<open>{\<rho>. ?kills n \<rho>}
           \<subseteq> {\<rho>. \<not> ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>} 
            \<union> {\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2}\<close> by blast
  next
    { fix \<rho>::\<open>'\<tau>::linordered_field run\<close>
      assume \<open>\<rho> \<in> ({\<rho>. \<not> ?ticks n \<rho> C\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2})\<close>
      hence \<open>\<not> ?ticks n \<rho> C\<^sub>1 \<and> ?kills (Suc n) \<rho>
             \<or> ?ticks n \<rho> C\<^sub>1 \<and> ?dead n \<rho> C\<^sub>2\<close> by blast
      moreover have \<open>((\<not> ?ticks n \<rho> C\<^sub>1) \<and> (?kills (Suc n) \<rho>)) \<longrightarrow> ?kills n \<rho>\<close>
        using dual_order.antisym not_less_eq_eq by blast
      ultimately have \<open>?kills n \<rho> \<or> ?ticks n \<rho> C\<^sub>1 \<and> ?dead n \<rho> C\<^sub>2\<close> by blast
      hence \<open>?kills n \<rho>\<close> using le_trans by blast
    } thus \<open>({\<rho>. \<not> ?ticks n \<rho> C\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2})
          \<subseteq> {\<rho>. ?kills n \<rho>}\<close> by blast
  qed
  also have \<open>... = {\<rho>. \<not> ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>}
                 \<union> {\<rho>. ?ticks n \<rho> C\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> C\<^sub>2} \<inter> {\<rho>. ?kills (Suc n) \<rho>}\<close>
    using Collect_cong Collect_disj_eq by auto
  also have \<open>... = \<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                 \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                 \<inter> \<lbrakk> C\<^sub>1 kills C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  finally show ?thesis by blast
qed

lemma stepwise_delay_unfold_zero:\<open>{\<rho>::('a::linordered_field) run. ticks (Rep_run \<rho> n master) 
              \<longrightarrow> (\<forall>p\<ge>n. counted_ticks \<rho> counting n p 0 \<longrightarrow> ticks (Rep_run \<rho> p slave))}
        = \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
        \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> (is \<open>{\<rho>. ?P \<rho>} = ?N \<union> ?T \<inter> ?S\<close>)
proof
  { fix \<rho>::\<open>('a::linordered_field) run\<close>
    assume h:\<open>\<rho> \<in> {\<rho>. ?P \<rho>}\<close>
    have \<open>\<rho> \<in> ?N \<union> ?T \<inter> ?S\<close>
    proof (cases \<open>ticks (Rep_run \<rho> n master)\<close>)
      case master_ticks:True
        with h have \<open>(\<forall>p\<ge>n. counted_ticks \<rho> counting n p 0 \<longrightarrow> ticks (Rep_run \<rho> p slave))\<close> by simp
        hence \<open>ticks (Rep_run \<rho> n slave)\<close> by (simp add: counted_immediate)
        hence \<open>\<rho> \<in> ?T \<inter> ?S\<close> by (simp add: master_ticks)
        thus ?thesis by blast
    next
      case master_doesnot_tick:False
        hence \<open>\<rho> \<in> ?N\<close> by simp
        thus ?thesis by simp
    qed
  } thus \<open>{\<rho>. ?P \<rho>} \<subseteq> ?N \<union> ?T \<inter> ?S\<close> by blast
  { fix \<rho>::\<open>('a::linordered_field) run\<close>
    assume h:\<open>\<rho> \<in> ?N \<union> ?T \<inter> ?S\<close>
    have \<open>\<rho> \<in> {\<rho>. ?P \<rho>}\<close>
    proof (cases \<open>\<rho> \<in> ?N\<close>)
      case True
        hence \<open>\<not>ticks (Rep_run \<rho> n master)\<close> by simp
        thus ?thesis by simp
    next
      case False
        with h have \<open>\<rho> \<in> ?T \<inter> ?S\<close> by simp
        hence \<open>ticks (Rep_run \<rho> n master) \<and> ticks (Rep_run \<rho> n slave)\<close> by simp
        thus ?thesis using counted_zero_same by fastforce
    qed
  } thus \<open>?N \<union> ?T \<inter> ?S \<subseteq> {\<rho>. ?P \<rho>}\<close> by blast
qed

lemma stepwise_delay_unfold_suc:
  \<open>{\<rho>::('a::linordered_field) run. ticks (Rep_run \<rho> n master) 
           \<longrightarrow> (\<forall>p\<ge>n. counted_ticks \<rho> counting n p (Suc d) \<longrightarrow> ticks (Rep_run \<rho> p slave))}
        = \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
        \<inter> \<lbrakk> from n delay count (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> (is \<open>{\<rho>. ?P \<rho>} = ?N \<union> ?T \<inter> ?S\<close>)
proof
  { fix \<rho>::\<open>('a::linordered_field) run\<close>
    assume h:\<open>\<rho> \<in> {\<rho>. ?P \<rho>}\<close>
    have \<open>\<rho> \<in> ?N \<union> ?T \<inter> ?S\<close>
    proof (cases \<open>ticks (Rep_run \<rho> n master)\<close>)
      case master_ticks:True
        with h have \<open>(\<forall>p\<ge>n. counted_ticks \<rho> counting n p (Suc d) \<longrightarrow> ticks (Rep_run \<rho> p slave))\<close> by simp
        hence \<open>\<rho> \<in> ?T \<inter> ?S\<close> by (simp add: master_ticks)
        thus ?thesis by blast
    next
      case master_doesnot_tick:False
        hence \<open>\<rho> \<in> ?N\<close> by simp
        thus ?thesis by simp
    qed
  } thus \<open>{\<rho>. ?P \<rho>} \<subseteq> ?N \<union> ?T \<inter> ?S\<close> by blast
  { fix \<rho>::\<open>('a::linordered_field) run\<close>
    assume h:\<open>\<rho> \<in> ?N \<union> ?T \<inter> ?S\<close>
    have \<open>\<rho> \<in> {\<rho>. ?P \<rho>}\<close>
    proof (cases \<open>\<rho> \<in> ?N\<close>)
      case True
        hence \<open>\<not>ticks (Rep_run \<rho> n master)\<close> by simp
        thus ?thesis by simp
    next
      case False
        with h have 1:\<open>\<rho> \<in> ?T \<inter> ?S\<close> by simp
        have \<open>\<not>counted_ticks \<rho> counting n n (Suc d)\<close> using counted_suc by blast
        hence \<open>counted_ticks \<rho> counting n n (Suc d) \<longrightarrow> ticks (Rep_run \<rho> n slave)\<close> by simp
        with 1 have \<open>ticks (Rep_run \<rho> n master)
          \<and> (\<forall>p\<ge>n. counted_ticks \<rho> counting n p (Suc d) \<longrightarrow> ticks (Rep_run \<rho> p slave))\<close>
          using counted_suc by fastforce
        thus ?thesis by blast
    qed
  } thus \<open>?N \<union> ?T \<inter> ?S \<subseteq> {\<rho>. ?P \<rho>}\<close> by blast
qed

lemma TESL_interp_stepwise_delayed_coind_zero_unfold:
  \<open>\<lbrakk> master delayed by 0 on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (     \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                   \<comment> \<open>rule @{thm delayed_e1}\<close>
        \<union>  (\<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<comment> \<open>rule @{thm delayed_e2}\<close>
     )
     \<inter> \<lbrakk> master delayed by 0 on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?prop = \<open>\<lambda>\<rho> m. ticks ((Rep_run \<rho>) m master) \<longrightarrow>
                 (\<forall>p \<ge> m. counted_ticks \<rho> counting m p 0 \<longrightarrow> ticks ((Rep_run \<rho>) p slave))\<close>
  have \<open>\<lbrakk> master delayed by 0 on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
                {\<rho>. \<forall>m\<ge>n. ?prop \<rho> m} \<close> by simp
  also have \<open>... = {\<rho>. ?prop \<rho> n } \<inter> {\<rho>. \<forall>m\<ge> Suc n. ?prop \<rho> m }\<close>
  using forall_nat_set_suc[of n \<open>?prop\<close>] by blast
  also have \<open>... = {\<rho>. ?prop \<rho> n}
              \<inter> \<lbrakk> master delayed by 0 on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  finally show ?thesis using stepwise_delay_unfold_zero by blast
qed

lemma TESL_interp_stepwise_delayed_coind_suc_unfold:
  \<open>\<lbrakk> master delayed by (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     ( \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                   \<comment> \<open>rule @{thm delayed_e1}\<close>
        \<union> (\<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                \<comment> \<open>rule @{thm delayed_e3}\<close>
           \<inter> \<lbrakk> from n delay count (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
     )
     \<inter> \<lbrakk> master delayed by (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?prop = \<open>\<lambda>\<rho> m. ticks ((Rep_run \<rho>) m master) \<longrightarrow>
                (\<forall>p \<ge> m. counted_ticks \<rho> counting m p (Suc d) \<longrightarrow> ticks ((Rep_run \<rho>) p slave))\<close>
  have \<open>\<lbrakk> master delayed by (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
                {\<rho>. \<forall>m\<ge>n. ?prop \<rho> m} \<close> by simp
  also have \<open>... = {\<rho>. ?prop \<rho> n} \<inter> {\<rho>. \<forall>m \<ge> Suc n. ?prop \<rho> m}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>?prop\<close>] by blast
  also have \<open>... = {\<rho>. ?prop \<rho> n}
              \<inter> \<lbrakk> master delayed by (Suc d) on counting implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  finally show ?thesis using stepwise_delay_unfold_suc by blast
qed

text \<open>
  The stepwise interpretation of a TESL formula is the intersection of the
  interpretation of its atomic components.
\<close>
fun TESL_interpretation_stepwise
  ::\<open>'\<tau>::linordered_field TESL_formula \<Rightarrow> nat \<Rightarrow> '\<tau> run set\<close>
  (\<open>\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>\<close>)
where
  \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = {\<rho>. True}\<close>
| \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>

lemma TESL_interpretation_stepwise_fixpoint:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) ` set \<Phi>)\<close>
by (induction \<Phi>, simp, auto)

text \<open>
  The global interpretation of a TESL formula is its interpretation starting
  at the first instant.
\<close>
lemma TESL_interpretation_stepwise_zero:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>\<close>
proof (induction \<phi>)
case (SporadicOn x1 x2 x3)
  then show ?case by simp
next
  case (SporadicOnTvar C\<^sub>1 \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r C\<^sub>2)
  then show ?case 
  proof (induction \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r)
    case (AddDelay \<tau>\<^sub>v\<^sub>a\<^sub>r\<^sub>0 \<delta>\<tau>)
    then show ?case
    proof (induction \<tau>\<^sub>v\<^sub>a\<^sub>r\<^sub>0)
      case (TSchematic tuple)
      then show ?case
      proof (induction tuple)
        case (Pair C\<^sub>p\<^sub>a\<^sub>s\<^sub>t n\<^sub>p\<^sub>a\<^sub>s\<^sub>t)
        then show ?case by simp
      qed
    qed
  qed
next
case (TagRelation x1 x2 x3)
  then show ?case by simp 
next
  case (Implies x1 x2)
then show ?case by simp 
next
  case (ImpliesNot x1 x2)
  then show ?case by simp
next
  case (TimeDelayedBy x1 x2 x3 x4)
then show ?case by simp
next
  case (RelaxedTimeDelayed x1 x2 x3 x4)
  then show ?case by simp
next
  case (WeaklyPrecedes x1 x2)
  then show ?case by simp
next
  case (StrictlyPrecedes x1 x2)
  then show ?case by simp
next
  case (Kills x1 x2)
then show ?case by simp
next
  case (DelayedBy x1 x2 x3 x4)
  then show ?case sorry
next
  case (DelayCount x1 x2 x3 x4)
  then show ?case sorry
qed

lemma TESL_interpretation_stepwise_zero':
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>\<close>
by (induction \<Phi>, simp, simp add: TESL_interpretation_stepwise_zero)

lemma TESL_interpretation_stepwise_cons_morph:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
by auto

theorem TESL_interp_stepwise_composition:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
by (induction \<Phi>\<^sub>1, simp, auto)

section \<open>Interpretation of configurations\<close>

text \<open>
  The interpretation of a configuration of the operational semantics abstract 
  machine is the intersection of:
  \<^item> the interpretation of its context (the past),
  \<^item> the interpretation of its present from the current instant,
  \<^item> the interpretation of its future from the next instant.
\<close>
fun configuration_interpretation
  ::\<open>'\<tau>::linordered_field config \<Rightarrow> '\<tau> run set\<close>          (\<open>\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> 71)
where
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>

lemma configuration_interp_composition:
   \<open>\<lbrakk> \<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<inter> \<lbrakk> \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
     = \<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2), n \<turnstile> (\<Psi>\<^sub>1 @ \<Psi>\<^sub>2) \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  using TESL_interp_stepwise_composition symrun_interp_expansion
by (simp add: TESL_interp_stepwise_composition
              symrun_interp_expansion inf_assoc inf_left_commute)

text \<open>
  When there are no remaining constraints on the present, the interpretation of
  a configuration is the same as the configuration at the next instant of its future.
  This corresponds to the introduction rule of the operational semantics.
\<close>
lemma configuration_interp_stepwise_instant_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                 = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis by blast
qed

text \<open>
  The following lemmas use the unfolding properties of the stepwise denotational 
  semantics to give rewriting rules for the interpretation of configurations that
  match the elimination rules of the operational semantics.
\<close>
lemma configuration_interp_stepwise_sporadicon_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 =  \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 =  \<lbrakk>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>(\<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
            \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
          = \<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)\<close>
      using TESL_interp_stepwise_sporadicon_coind_unfold by blast
    hence \<open>\<lbrakk>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> C\<^sub>1 sporadic \<tau> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
           = \<lbrakk>\<lbrakk> (C\<^sub>1 sporadic \<tau> on C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> by auto
    thus ?thesis by auto
  qed
qed

lemma configuration_interp_stepwise_sporadicon_tvar_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 sporadic\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r on C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @\<sharp> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  from tag_expr.exhaust obtain v \<delta>\<tau> where \<open> \<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r=\<lparr> v \<oplus> \<delta>\<tau> \<rparr>\<close> by blast
  moreover from tag_var.exhaust obtain C\<^sub>p\<^sub>a\<^sub>s\<^sub>t n\<^sub>p\<^sub>a\<^sub>s\<^sub>t where \<open>v=\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t)\<close> by auto
  ultimately have *:\<open>\<tau>\<^sub>e\<^sub>x\<^sub>p\<^sub>r=\<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr>\<close> by simp
  show ?thesis
  proof -
    have \<open>(\<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Down> n @\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
         \<union> \<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
        \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
      = \<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)\<close>
      using TESL_interp_stepwise_sporadicon_tvar_coind_unfold[of \<open>C\<^sub>1\<close> \<open>C\<^sub>p\<^sub>a\<^sub>s\<^sub>t\<close> \<open>n\<^sub>p\<^sub>a\<^sub>s\<^sub>t\<close> \<open>\<delta>\<tau>\<close> \<open>C\<^sub>2\<close> \<open>n\<close>]
            Int_commute by blast
    then have \<open>\<lbrakk>\<lbrakk> (C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr>) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
            \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            \<inter> \<lbrakk> C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      by auto
    then have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Down> n @\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      by auto
    then show ?thesis using *
      by blast
  qed
qed

lemma configuration_interp_stepwise_tagrel_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
        \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
        \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                 \<inter> \<lbrakk>\<lbrakk> (time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
          \<inter> \<lbrakk> time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (time-relation \<lfloor>C\<^sub>1, C\<^sub>2\<rfloor> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_tagrel_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma configuration_interp_stepwise_implies_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 implies C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 implies C\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (C\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                =  \<lbrakk>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<Up> n) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                 \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have f1: \<open>(\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
                \<inter> \<lbrakk> C\<^sub>1 implies C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
              = \<lbrakk>\<lbrakk> (C\<^sub>1 implies C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      using TESL_interp_stepwise_implies_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    have \<open>\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>2 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
         = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by force
    hence \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 implies C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>2 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
        \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using f1 by (simp add: inf_left_commute inf_assoc)
    thus ?thesis by (simp add: Int_Un_distrib2 inf_assoc)
  qed
qed

lemma configuration_interp_stepwise_implies_not_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 implies not C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies not C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies not C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 implies not C\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies not C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies not C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> (C\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies not C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 implies not C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> n) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies not C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have f1: \<open>(\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
              \<inter> \<lbrakk> C\<^sub>1 implies not C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
              \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
              = \<lbrakk>\<lbrakk> (C\<^sub>1 implies not C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      using TESL_interp_stepwise_implies_not_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    have \<open>\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>2 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
           = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by force
    then have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 implies not C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                    \<inter> \<lbrakk>\<lbrakk> (C\<^sub>2 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                    \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 implies not C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using f1 by (simp add: inf_left_commute inf_assoc)
    thus ?thesis by (simp add: Int_Un_distrib2 inf_assoc)
  qed
qed

lemma configuration_interp_stepwise_timedelayed_cases:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> C\<^sub>3) # \<Gamma>), n
        \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have 1:\<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
         = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (C\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> C\<^sub>3) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (C\<^sub>1 \<Up> n) # (C\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> C\<^sub>3) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
        \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using 1 by blast
    hence \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> C\<^sub>3 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
            \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>))\<close>
      using TESL_interpretation_stepwise_cons_morph
            TESL_interp_stepwise_timedelayed_coind_unfold
    proof -
      have \<open>\<lbrakk>\<lbrakk> (C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            = (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> C\<^sub>3 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
            \<inter> \<lbrakk> C\<^sub>1 time-delayed by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
        using TESL_interp_stepwise_timedelayed_coind_unfold
              TESL_interpretation_stepwise_cons_morph by blast
      then show ?thesis
        by (simp add: Int_assoc Int_left_commute)
    qed
    then show ?thesis by (simp add: inf_assoc inf_sup_distrib2)
  qed
qed

lemma configuration_interp_stepwise_timedelayed_tvar_cases:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # \<Gamma>), n
        \<turnstile> (C\<^sub>3 sporadic\<sharp> \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(C\<^sub>2, n) \<oplus> \<delta>\<tau>\<rparr> on C\<^sub>2) # \<Psi>
        \<triangleright> ((C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
       \<inter> (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>3 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>2, n) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
       \<inter> \<lbrakk> C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
      = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
    using TESL_interp_stepwise_timedelayed_tvar_coind_unfold[of \<open>C\<^sub>1\<close> \<open>\<delta>\<tau>\<close> \<open>C\<^sub>2\<close> \<open>C\<^sub>3\<close> \<open>n\<close>]
          Int_assoc by blast
  then have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> (\<lbrakk> C\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> C\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> C\<^sub>3 sporadic\<sharp> \<lparr> \<tau>\<^sub>v\<^sub>a\<^sub>r (C\<^sub>2, n) \<oplus> \<delta>\<tau> \<rparr> on C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
          \<inter> \<lbrakk> C\<^sub>1 time-delayed\<bowtie> by \<delta>\<tau> on C\<^sub>2 implies C\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
          \<inter> (\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)\<close>
    by force
  then show ?thesis
    by auto
qed

lemma configuration_interp_stepwise_weakly_precedes_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 weakly precedes C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>\<le> C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
      \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 weakly precedes C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 weakly precedes C\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 weakly precedes C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>\<le> C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 weakly precedes C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>\<le> C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 weakly precedes C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>\<le> C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
            \<inter> \<lbrakk> C\<^sub>1 weakly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          = \<lbrakk>\<lbrakk> (C\<^sub>1 weakly precedes C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_weakly_precedes_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma configuration_interp_stepwise_strictly_precedes_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 strictly precedes C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>< C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
      \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 strictly precedes C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (C\<^sub>1 strictly precedes C\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 strictly precedes C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>< C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 strictly precedes C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (\<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>< C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 strictly precedes C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lceil>#\<^sup>\<le> C\<^sub>2 n, #\<^sup>< C\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
            \<inter> \<lbrakk> C\<^sub>1 strictly precedes C\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          = \<lbrakk>\<lbrakk> (C\<^sub>1 strictly precedes C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_strictly_precedes_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma configuration_interp_stepwise_kills_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 kills C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 kills C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 kills C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((C\<^sub>1 kills C\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 kills C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 kills C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (C\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 kills C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((C\<^sub>1 kills C\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (C\<^sub>1 \<Up> n) # (C\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (C\<^sub>1 kills C\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
    proof -
      have \<open>\<lbrakk>\<lbrakk> (C\<^sub>1 kills C\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            = (\<lbrakk> (C\<^sub>1 \<not>\<Up> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> (C\<^sub>1 \<Up> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> (C\<^sub>2 \<not>\<Up> \<ge> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
              \<inter> \<lbrakk> (C\<^sub>1 kills C\<^sub>2) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
        using TESL_interp_stepwise_kills_coind_unfold
              TESL_interpretation_stepwise_cons_morph by blast
      thus ?thesis by auto
    qed
qed

lemma HeronConf_interp_stepwise_delayed_cases_zero:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>3 \<Up> n) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
  \<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g =
        \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have 
    \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using TESL_interpretation_stepwise.simps(2)[of _ \<open>\<Psi>\<close> \<open>n\<close>] by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> {\<rho>. \<forall>z\<ge>n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                 (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using TESL_interpretation_atomic_stepwise.simps(11)[of \<open>K\<^sub>1\<close> \<open>0\<close> \<open>K\<^sub>2\<close> \<open>K\<^sub>3\<close> \<open>n\<close>] by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> n.  counted_ticks \<rho> K\<^sub>2 n m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> z. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                 (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3))\<close>] by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow> ticks ((Rep_run \<rho>) n K\<^sub>3) }
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      using counted_immediate counted_zero_same by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> ( {\<rho>. \<not>ticks ((Rep_run \<rho>) n K\<^sub>1)}
                  \<union> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<and> ticks ((Rep_run \<rho>) n K\<^sub>3)} )
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                          \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>3 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m))
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m 0
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      by (simp add: Collect_conj_eq)
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>3 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m))
                \<inter> \<lbrakk> K\<^sub>1 delayed by 0 on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  finally show ?thesis by auto
qed

lemma HeronConf_interp_stepwise_delayed_cases_suc:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # \<Gamma>), n
        \<turnstile> \<Psi> \<triangleright> ((from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3)
                # (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
  \<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
      \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> \<lbrakk> K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by (simp add: Int_assoc)
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. \<forall>z\<ge>n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> n.  counted_ticks \<rho> K\<^sub>2 n m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> z. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                 (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3))\<close>] by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> ({\<rho>. \<not>ticks ((Rep_run \<rho>) n K\<^sub>1)} \<union> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<and>
                    (\<forall>m \<ge> n.  counted_ticks \<rho> K\<^sub>2 n m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) })
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> ({\<rho>. \<not>ticks ((Rep_run \<rho>) n K\<^sub>1)} \<union> {\<rho>. ticks ((Rep_run \<rho>) n K\<^sub>1) \<and>
                    (\<forall>m \<ge> Suc n.  counted_ticks \<rho> K\<^sub>2 n m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) })
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using counted_suc by force
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                    \<union> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                  )
                \<inter> {\<rho>. \<forall>z\<ge> Suc n. ticks ((Rep_run \<rho>) z K\<^sub>1) \<longrightarrow>
                    (\<forall>m \<ge> z.  counted_ticks \<rho> K\<^sub>2 z m (Suc d)
                            \<longrightarrow> ticks ((Rep_run \<rho>) m K\<^sub>3)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by (simp add: Collect_conj_eq)
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                    \<union> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                  )
                \<inter> \<lbrakk> K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                    \<union> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                  )
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using TESL_interpretation_stepwise.simps(2) by blast
  also have \<open>... = (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                 \<union> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                      \<inter> (\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                   )\<close> by blast
  also have \<open>... = (\<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                 \<union> (\<lbrakk>\<lbrakk> (K\<^sub>1 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m  \<inter> \<lbrakk> from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
            )\<close>
    by (simp add: inf_assoc inf_commute)
  also have \<open>... = (\<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
                 \<union> (\<lbrakk>\<lbrakk> (K\<^sub>1 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (from n delay count (Suc d) on K\<^sub>2 implies K\<^sub>3)
                     # (K\<^sub>1 delayed by (Suc d) on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                    )\<close>
    using TESL_interpretation_stepwise.simps(2) by blast
  finally show ?thesis by simp
qed

lemma counted_exp:
  \<open>(\<forall>z \<ge> n. counted_ticks \<rho> K m z (Suc 0) \<longrightarrow> ticks ((Rep_run \<rho>) z K'))
    = ((counted_ticks \<rho> K m n (Suc 0) \<longrightarrow> ticks ((Rep_run \<rho>) n K'))
    \<and> (\<forall>z \<ge> Suc n. counted_ticks \<rho> K m z (Suc 0) \<longrightarrow> ticks ((Rep_run \<rho>) z K')))\<close>
using forall_nat_expansion[of \<open>n\<close> \<open>\<lambda>z. counted_ticks \<rho> K m z (Suc 0) \<longrightarrow> ticks (Rep_run \<rho> z K')\<close>] .

\<comment> \<open>
  The issue here is that it is assumed that a delay count is removed from the configuration
  as soon as it elapses, but nothing prevents elapsed delay counts to be in a context.
\<close>
lemma HeronConf_interp_stepwise_delay_count_cases_one:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((from m delay count (Suc 0) on K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((from m delay count (Suc 0) on K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
  \<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((from m delay count (Suc 0) on K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (from m delay count (Suc 0) on K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
      \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> \<lbrakk> (from m delay count (Suc 0) on K\<^sub>1 implies K\<^sub>2) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by (simp add: inf.assoc)
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. \<forall>z \<ge> n.  (z \<ge> m \<and> counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. \<forall>z \<ge> n.  (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by (simp add: counted_ticks_def)
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. (counted_ticks \<rho> K\<^sub>1 m n (Suc 0)\<longrightarrow> ticks ((Rep_run \<rho>) n K\<^sub>2))
                      \<and> (\<forall>z \<ge> Suc n. (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using counted_exp by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. (\<not>counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> ticks ((Rep_run \<rho>) n K\<^sub>2))
                      \<and> (\<forall>z \<ge> Suc n. (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2)) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. (\<not>counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> ticks ((Rep_run \<rho>) n K\<^sub>2))
                      \<and> (counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> (\<forall>z \<ge> Suc n. (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2))) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    using counted_one_now_later by fastforce
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. (\<not>counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> ticks ((Rep_run \<rho>) n K\<^sub>2))}
                \<inter> {\<rho>. (counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> (\<forall>z \<ge> Suc n. (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2))) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by blast
  also have \<open>... = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
                \<inter> {\<rho>. (\<not>counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> ticks ((Rep_run \<rho>) n K\<^sub>2))}
                \<inter> {\<rho>. (counted_ticks \<rho> K\<^sub>1 m n (Suc 0) \<or> (\<forall>z \<ge> Suc n. (counted_ticks \<rho> K\<^sub>1 m z (Suc 0))
                            \<longrightarrow> ticks ((Rep_run \<rho>) z K\<^sub>2))) }
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    sorry
   finally show ?thesis  sorry
 qed

end
