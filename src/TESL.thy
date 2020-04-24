(*chapter\<open>The Core of the TESL Language: Syntax and Basics\<close>*)
text\<open>\chapter[Core TESL: Syntax and Basics]{The Core of the TESL Language: Syntax and Basics}\<close>

theory TESL
imports Main

begin

section\<open>Syntactic Representation\<close>
text\<open>
  We define here the syntax of TESL specifications.
\<close>

subsection\<open>Basic elements of a specification\<close>
text\<open>
  The following items appear in specifications:
  \<^item> Clocks, which are identified by a name.
  \<^item> An instant on a clock is identified by its index, starting from 0
  \<^item> Tag constants are just constants of a type which denotes the metric time space.
\<close>

datatype     clock         = Clk \<open>string\<close>
type_synonym instant_index = \<open>nat\<close>

datatype     '\<tau> tag_const =  TConst   (the_tag_const : '\<tau>)         (\<open>\<tau>\<^sub>c\<^sub>s\<^sub>t\<close>)

text\<open>
  Tag variables are used to refer to the time on a clock at a given instant index.
  Tag expressions are used to build a new tag by adding a constant delay to a tag variable.
\<close>
datatype tag_var =
  TSchematic \<open>clock * instant_index\<close> (\<open>\<tau>\<^sub>v\<^sub>a\<^sub>r\<close>)
datatype '\<tau> tag_expr      =  (* Const    \<open>'\<tau> tag_const\<close>          (\<open>\<lparr> _ \<rparr>\<close>) *)
                              AddDelay \<open>tag_var\<close> \<open>'\<tau> tag_const\<close> (\<open>\<lparr> _ \<oplus> _ \<rparr>\<close>)

subsection\<open>Operators for the TESL language\<close>
text\<open>
  The type of atomic TESL constraints, which can be combined to form specifications.
\<close>
datatype '\<tau> TESL_atomic =
    SporadicOn         \<open>clock\<close> \<open>'\<tau> tag_const\<close>  \<open>clock\<close>  (\<open>_ sporadic _ on _\<close> 55)
  | TagRelation        \<open>clock\<close> \<open>clock\<close> \<open>('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool\<close> 
                                                      (\<open>time-relation \<lfloor>_, _\<rfloor> \<in> _\<close> 55)
  | Implies            \<open>clock\<close> \<open>clock\<close>                  (infixr \<open>implies\<close> 55)
  | ImpliesNot         \<open>clock\<close> \<open>clock\<close>                  (infixr \<open>implies not\<close> 55)
  | TimeDelayedBy      \<open>clock\<close> \<open>'\<tau> tag_const\<close> \<open>clock\<close> \<open>clock\<close>
                                                      (\<open>_ time-delayed by _ on _ implies _\<close> 55)
  | RelaxedTimeDelayed \<open>clock\<close> \<open>'\<tau> tag_const\<close> \<open>clock\<close> \<open>clock\<close>
                                                      (\<open>_ time-delayed\<bowtie> by _ on _ implies _\<close> 55)
  | WeaklyPrecedes     \<open>clock\<close> \<open>clock\<close>                  (infixr \<open>weakly precedes\<close> 55)
  | StrictlyPrecedes   \<open>clock\<close> \<open>clock\<close>                  (infixr \<open>strictly precedes\<close> 55)
  | Kills              \<open>clock\<close> \<open>clock\<close>                  (infixr \<open>kills\<close> 55)
  | DelayedBy          \<open>clock\<close> \<open>nat\<close> \<open>clock\<close> \<open>clock\<close> 
                                                      (\<open>_ delayed by _ on _ implies _\<close> 55)
\<comment> \<open>The following constraints are not part of the TESL language,
    they are added only for implementing the operational semantics\<close>
  | SporadicOnTvar     \<open>clock\<close> \<open>'\<tau> tag_expr\<close>  \<open>clock\<close>   (\<open>_ sporadic\<sharp> _ on _\<close> 55)
\<comment> \<open>State storing constraints for implementing top level constraints\<close>
  | DelayCount       \<open>nat\<close> \<open>nat\<close> \<open>clock\<close> \<open>clock\<close>      (\<open>from _ delay count _ on _ implies _\<close> 55)

text \<open>
  Some constraints were introduced for the implementation of the operational semantics.
  They are not allowed in user-level TESL specification and are not public.
\<close>
fun is_public_atom :: \<open>'\<tau> TESL_atomic \<Rightarrow> bool\<close> where
    \<open>is_public_atom (_ sporadic\<sharp> _ on _)                  = False\<close>
  | \<open>is_public_atom (from _ delay count _ on _ implies _) = False\<close>
  | \<open>is_public_atom _                                     = True\<close>

text\<open>
  A TESL formula is just a list of atomic constraints, with implicit conjunction
  for the semantics.
\<close>
type_synonym '\<tau> TESL_formula = \<open>'\<tau> TESL_atomic list\<close>

fun is_public_spec :: \<open>'\<tau> TESL_atomic list \<Rightarrow> bool\<close> where
    \<open>is_public_spec [] = True\<close>
  | \<open>is_public_spec (\<phi>#S) = ((is_public_atom \<phi>) \<and> (is_public_spec S))\<close>

text\<open>
  We call \<^emph>\<open>positive atoms\<close> the atomic constraints that create ticks from nothing.
  Only sporadic constraints are positive in the current version of TESL.
\<close>
fun positive_atom :: \<open>'\<tau> TESL_atomic \<Rightarrow> bool\<close> where
    \<open>positive_atom (_ sporadic _ on _) = True\<close>
  | \<open>positive_atom (_ sporadic\<sharp> _ on _) = True\<close>
  | \<open>positive_atom _                   = False\<close>

text\<open>
  The @{term \<open>NoSporadic\<close>} function removes sporadic constraints from a TESL formula.
\<close>
abbreviation NoSporadic :: \<open>'\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula\<close>
where 
  \<open>NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)\<close>

subsection\<open>Field Structure of the Metric Time Space\<close>
text\<open>
  In order to handle tag relations and delays, tags must belong to a field.
  We show here that this is the case when the type parameter of @{typ \<open>'\<tau> tag_const\<close>} 
  is itself a field.
\<close>
instantiation tag_const ::(field)field
begin
  fun inverse_tag_const
  where \<open>inverse (\<tau>\<^sub>c\<^sub>s\<^sub>t t) = \<tau>\<^sub>c\<^sub>s\<^sub>t (inverse t)\<close>

  fun divide_tag_const 
    where \<open>divide (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (divide t\<^sub>1 t\<^sub>2)\<close>

  fun uminus_tag_const
    where \<open>uminus (\<tau>\<^sub>c\<^sub>s\<^sub>t t) = \<tau>\<^sub>c\<^sub>s\<^sub>t (uminus t)\<close>

fun minus_tag_const
  where \<open>minus (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (minus t\<^sub>1 t\<^sub>2)\<close>

definition \<open>one_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 1\<close>

fun times_tag_const
  where \<open>times (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (times t\<^sub>1 t\<^sub>2)\<close>

definition \<open>zero_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 0\<close>

fun plus_tag_const
  where \<open>plus (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (plus t\<^sub>1 t\<^sub>2)\<close>

instance proof
  text\<open>Multiplication is associative.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
                               and c::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  moreover obtain w where \<open>c = \<tau>\<^sub>c\<^sub>s\<^sub>t w\<close> using tag_const.exhaust by blast
  ultimately show \<open>a * b * c = a * (b * c)\<close>
    by (simp add: TESL.times_tag_const.simps)
next
  text\<open>Multiplication is commutative.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  ultimately show \<open> a * b = b * a\<close>
    by (simp add: TESL.times_tag_const.simps)
next
  text\<open>One is neutral for multiplication.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  thus \<open>1 * a = a\<close>
    by (simp add: TESL.times_tag_const.simps one_tag_const_def)
next
  text\<open>Addition is associative.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
                               and c::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  moreover obtain w where \<open>c = \<tau>\<^sub>c\<^sub>s\<^sub>t w\<close> using tag_const.exhaust by blast
  ultimately show \<open>a + b + c = a + (b + c)\<close>
    by (simp add: TESL.plus_tag_const.simps)
next
  text\<open>Addition is commutative.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  ultimately show \<open>a + b = b + a\<close>
    by (simp add: TESL.plus_tag_const.simps)
next
  text\<open>Zero is neutral for addition.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  thus \<open>0 + a = a\<close>
    by (simp add: TESL.plus_tag_const.simps zero_tag_const_def)
next
  text\<open>The sum of an element and its opposite is zero.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  thus \<open>-a + a = 0\<close>
    by (simp add: TESL.plus_tag_const.simps
                  TESL.uminus_tag_const.simps
                  zero_tag_const_def)
next
  text\<open>Subtraction is adding the opposite.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  ultimately show \<open>a - b = a + -b\<close>
    by (simp add: TESL.minus_tag_const.simps
                  TESL.plus_tag_const.simps
                  TESL.uminus_tag_const.simps)
next
  text\<open>Distributive property of multiplication over addition.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
                               and c::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  moreover obtain w where \<open>c = \<tau>\<^sub>c\<^sub>s\<^sub>t w\<close> using tag_const.exhaust by blast
  ultimately show \<open>(a + b) * c = a * c + b * c\<close>
    by (simp add: TESL.plus_tag_const.simps
                  TESL.times_tag_const.simps
                  ring_class.ring_distribs(2))
next
  text\<open>The neutral elements are distinct.\<close>
  show \<open>(0::('\<tau>::field tag_const)) \<noteq> 1\<close>
    by (simp add: one_tag_const_def zero_tag_const_def)
next
  text\<open>The product of an element and its inverse is 1.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> assume h:\<open>a \<noteq> 0\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover with h have \<open>u \<noteq> 0\<close> by (simp add: zero_tag_const_def)
  ultimately show \<open>inverse a * a = 1\<close>
    by (simp add: TESL.inverse_tag_const.simps
                  TESL.times_tag_const.simps
                  one_tag_const_def)
next
  text\<open>Dividing is multiplying by the inverse.\<close>
  fix a::\<open>'\<tau>::field tag_const\<close> and b::\<open>'\<tau>::field tag_const\<close>
  obtain u where \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using tag_const.exhaust by blast
  moreover obtain v where \<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using tag_const.exhaust by blast
  ultimately show \<open>a div b = a * inverse b\<close>
    by (simp add: TESL.divide_tag_const.simps
                  TESL.inverse_tag_const.simps
                  TESL.times_tag_const.simps
                  divide_inverse)
next
  text\<open>Zero is its own inverse.\<close>
  show \<open>inverse (0::('\<tau>::field tag_const)) = 0\<close>
    by (simp add: TESL.inverse_tag_const.simps zero_tag_const_def)
qed

end

text\<open>
  For comparing dates (which are represented by tags) on clocks, we need an order on tags.
\<close>

instantiation tag_const :: (order)order
begin
  inductive less_eq_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool\<close>
  where
    Int_less_eq[simp]:      \<open>n \<le> m \<Longrightarrow> (TConst n) \<le> (TConst m)\<close>

  definition less_tag: \<open>(x::'a tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)\<close>

  instance proof
    show \<open>\<And>x y :: 'a tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
      using less_eq_tag_const.simps less_tag by auto
  next
    fix x::\<open>'a tag_const\<close>
    from tag_const.exhaust obtain x\<^sub>0::'a where \<open>x = TConst x\<^sub>0\<close> by blast
    with Int_less_eq show \<open>x \<le> x\<close> by simp
  next
    show \<open>\<And>x y z  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
      using less_eq_tag_const.simps by auto
  next
    show \<open>\<And>x y  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
      using less_eq_tag_const.simps by auto
  qed

end

text\<open>
  For ensuring that time does never flow backwards, we need a total order on tags.
\<close>
instantiation tag_const :: (linorder)linorder
begin
  instance proof
    fix x::\<open>'a tag_const\<close> and y::\<open>'a tag_const\<close>
    from tag_const.exhaust obtain x\<^sub>0::'a where \<open>x = TConst x\<^sub>0\<close> by blast
    moreover from tag_const.exhaust obtain y\<^sub>0::'a where \<open>y = TConst y\<^sub>0\<close> by blast
    ultimately show \<open>x \<le> y \<or> y \<le> x\<close> using less_eq_tag_const.simps by fastforce
  qed

end

end
