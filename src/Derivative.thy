theory Derivative

imports Run

begin

definition increase :: \<open>['\<tau>::linordered_field run, clock, nat, nat] \<Rightarrow> '\<tau> tag_const\<close>
  where \<open>increase \<rho> c n\<^sub>0 n \<equiv> (time (\<rho> n c) - time (\<rho> n\<^sub>0 c))\<close>

definition derivative :: \<open>['\<tau>::linordered_field run, clock, clock] \<Rightarrow> (nat \<Rightarrow> (bool \<times> '\<tau> tag_const))\<close>
  where \<open>derivative \<rho> c t \<equiv> (\<lambda>n. (False, increase \<rho> c n (Suc n)
                                            /increase \<rho> t n (Suc n) ))\<close>

lemma
  assumes \<open>\<forall>n. time (derivative \<rho> c t n) < k\<close>
  shows \<open>increase \<rho> c 0 n < (k * (increase \<rho> t 0 n))\<close>
proof (induction n)
  case 0
  from assms have \<open>time (derivative \<rho> c t 0) < k\<close> by simp
  then show ?case unfolding derivative_def increase_def sorry
next
  case (Suc n)
  then show ?case sorry
qed

end
