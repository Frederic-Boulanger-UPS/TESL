theory Examples

imports Run HOL.Real

begin

abbreviation \<open>a \<equiv> ((\<lambda>n::nat. (False, \<tau>\<^sub>c\<^sub>s\<^sub>t (0::real)))
                (0:=(True, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)))
                (1:=(True, \<tau>\<^sub>c\<^sub>s\<^sub>t 1))\<close>
abbreviation \<open>r \<equiv> \<lambda>(n::nat) (c::clock). a n\<close>

abbreviation \<open>Ca \<equiv> (Clk ''a'')\<close>
definition \<open>\<rho> \<equiv> Abs_run r\<close>
term \<open>''a''\<close>
term \<open>r\<close>
value \<open>r 0 Ca\<close>
value \<open>r 1 Ca\<close>
value \<open>r 2 Ca\<close>

\<^cancel>\<open>
value \<open>run_tick_count \<rho> Ca 0\<close>
\<close>

end
