theory Misc

imports Main

begin

theorem predicate_Inter_unfold:
  \<open>{\<rho>. \<forall>n. P \<rho> n} = \<Inter> {Y. \<exists>n. Y = {\<rho>. P \<rho> n}}\<close>
by (simp add: Collect_all_eq full_SetCompr_eq)

theorem predicate_Union_unfold:
  \<open>{\<rho>. \<exists>n. P \<rho> n} = \<Union> {Y. \<exists>n. Y = {\<rho>. P \<rho> n}}\<close>
by blast

end
