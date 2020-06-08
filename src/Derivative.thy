theory Derivative

imports Run

begin
declare [[show_sorts]]
sublocale linordered_field \<subseteq> ordered_ab_group_add by (rule local.ordered_ab_group_add_axioms)

instantiation tag_const :: (linordered_field)linordered_field
begin
definition \<open>zero_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 0\<close>
definition \<open>one_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 1\<close>

instance proof
  fix a::"'a tag_const" and b::\<open>'a tag_const\<close> and c::\<open>'a tag_const\<close>
  show \<open>a \<le> b \<Longrightarrow> c + a \<le> c + b\<close> sorry
next
  fix a::"'a tag_const" and b::\<open>'a tag_const\<close> and c::\<open>'a tag_const\<close>
  show \<open>a < b \<Longrightarrow> (0::'a tag_const) < c \<Longrightarrow> c * a < c * b\<close> sorry
next
  fix a::"'a::linordered_field tag_const"
  show \<open>\<bar>a\<bar> = (if a < (0::'a::linordered_field tag_const) then - a else a)\<close> sorry
(*
next 
  show \<open>\<And>x::'a tag_const.
       sgn x =
       (if x = (zero_tag_const) then zero_tag_const
        else if (zero_tag_const) < x then one_tag_const else - (one_tag_const))\<close>
next
  fix x::"'a::linordered_field tag_const"
  show \<open>(sgn x) =
       (if x = (0::'a tag_const) then 0::'a tag_const
        else (if (0::'a tag_const) < x then 1::'a tag_const else - (1::'a tag_const)))\<close> sorry
*)
qed
end

definition increase :: \<open>['\<tau>::linordered_field run, clock, nat, nat] \<Rightarrow> '\<tau> tag_const\<close>
  where \<open>increase \<rho> c n\<^sub>0 n \<equiv> (time (\<rho> n c) - time (\<rho> n\<^sub>0 c))\<close>

definition derivative :: \<open>['\<tau>::linordered_field run, clock, clock] \<Rightarrow> (nat \<Rightarrow> (bool \<times> '\<tau> tag_const))\<close>
  where \<open>derivative \<rho> c t \<equiv> (\<lambda>n. (False, increase \<rho> c n (Suc n)
                                            / increase \<rho> t n (Suc n) ))\<close>
lemma chrono_increase:
  assumes \<open>is_chrono \<rho> t\<close>
  shows \<open>increase \<rho> t n (Suc n) > 0\<close>
proof -
  from assms have \<open>time (\<rho> n t) < time (\<rho> (Suc n) t)\<close> unfolding is_chrono_def strict_mono_def by simp
  hence \<open>time (\<rho> (Suc n) t) - time (\<rho> n t) > 0\<close> using diff_gt_0_iff_gt sorry
  thus ?thesis unfolding increase_def .
qed

lemma
  assumes \<open>\<forall>n. time (derivative \<rho> c t n) < k\<close>
      and \<open>k > 0\<close>
      and \<open>is_chrono \<rho> t\<close>
    shows \<open>increase \<rho> c 0 (Suc n) < (k * (increase \<rho> t 0 (Suc n)))\<close>
proof (induction n)
  case 0
  from assms(1) have \<open>time (derivative \<rho> c t 0) < k\<close> by simp
  hence \<open>increase \<rho> c 0 (Suc 0) / increase \<rho> t 0 (Suc 0) < k\<close> unfolding derivative_def by simp
  then show ?case using assms(2-3) unfolding is_chrono_def using chrono_increase sorry
next
  case (Suc n)
  then show ?case sorry
qed

end
