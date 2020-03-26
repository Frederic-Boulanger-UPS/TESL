theory Hygge_Solver
imports
  "Run_Concretizer"
  "Operational"
  "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach_Tools" 

keywords "print_run"::diag

begin

section\<open> Pretty-printer for runs \<close>
text\<open> This section defines a pretty-printer for derived symbolic runs by means of the
       command [print_run] \<close>

ML\<open>
local
  datatype clock = Clk of string
  type instant_index = int
  datatype tag_const =
      Unit
    | Int of int
  datatype tag_var =
      Schematic of clock * instant_index
  datatype tag_expr =
      Constant of tag_const
    | AddDelay of tag_var * tag_const
  datatype constr =
      Timestamp of clock * instant_index * tag_expr
    | Ticks     of clock * instant_index
    | NotTicks  of clock * instant_index
    | Affine    of tag_var * tag_const * tag_var * tag_const
in
fun tag_const_of_term t = case t of
    Const ("TESL.tag_const.Unit", _) => Unit
  | Const ("TESL.tag_const.Integer", _) $ int_term => Int (snd (HOLogic.dest_number int_term))
and tag_var_of_term t = case t of
    Const ("TESL.tag_var.Schematic", _) $ (Const ("TESL.clock.Clk", _) $ clock_term) $ instant_index_term =>
      Schematic (Clk (HOLogic.dest_string clock_term), HOLogic.dest_nat instant_index_term)
exception DANGER
fun constr_context_of_term gamma = case gamma of
    Const ("List.list.Nil", _) => []
  | Const ("List.list.Cons", _) $ constr_term $ gamma' => (case constr_term of
        Const ("TESL.constr.Timestamp", _) $ (Const ("TESL.clock.Clk", _) $ clock_term) $ pos_term $ tag_expr_term =>
          Timestamp (Clk (HOLogic.dest_string clock_term),
                     HOLogic.dest_nat pos_term,
                     case tag_expr_term of Const ("TESL.tag_expr.Const", _) $ tag_const_term =>
                                             Constant (tag_const_of_term tag_const_term)
                                         | Const ("TESL.tag_expr.AddDelay", _) $ tag_var_term $ tag_const_term =>
                                             AddDelay (tag_var_of_term tag_var_term, tag_const_of_term tag_const_term))
                                         
      | Const ("TESL.constr.Ticks", _) $ (Const ("TESL.clock.Clk", _) $ clock_term) $ pos_term =>
          Ticks (Clk (HOLogic.dest_string clock_term), HOLogic.dest_nat pos_term)
      | Const ("TESL.constr.NotTicks", _) $ (Const ("TESL.clock.Clk", _) $ clock_term) $ pos_term =>
          Ticks (Clk (HOLogic.dest_string clock_term), HOLogic.dest_nat pos_term)
      | Const ("TESL.constr.Affine", _) $ tvar1 $ tconst1 $ tvar2 $ tconst2 =>
          Affine (tag_var_of_term tvar1, tag_const_of_term tconst1, tag_var_of_term tvar2, tag_const_of_term tconst2)

    ) :: constr_context_of_term gamma'

fun string_of_tag (t : tag_const) =
  case t of
      Unit  => "()"
    | Int n => string_of_int n

fun print_system (step_index: int) (clocks: clock list) (G : constr list) =
  let
    (* Old tick symbol: \226\135\145 to get \<Up> *)
    val TICK_SYM = "\226\134\145"       (* \<up> *)
    val FORBIDDEN_SYM = "\226\138\152"  (* \<oslash> *)
    fun constrs_of_clk_instindex c n =
      List.filter (fn Ticks (c', n') => c = c' andalso n = n' | NotTicks (c', n') => c = c' andalso n = n' | Timestamp (c', n', _) => c = c' andalso n = n' | _ => false) G
    fun string_of_constrs_at_clk_instindex clk n g =
      let
        val timestamps = List.filter (fn Timestamp (_, _, Constant tag) => (case tag of Unit => true | Int _ => true | _ => false) | _ => false) g
	 val tick_string =
	   if List.exists (fn x => x = Ticks (clk, n)) g
	   then TICK_SYM
	   else
	     if List.exists (fn x => x = NotTicks (clk, n)) g
	     then FORBIDDEN_SYM
	     else ""
	 val tag_string =
	     case List.find (fn Timestamp (_, _, _) => true | _ => false) timestamps of
		  NONE                         => " "
		| SOME (Timestamp (_, _, Constant tag)) => string_of_tag tag
      in tick_string ^ " " ^ tag_string
    end
    fun print_clocks () =
      writeln ("\t\t" ^ List.foldr (fn (Clk c, s) => c ^ "\t\t" ^ s) "" clocks)
    fun print_instant n =
      writeln ("[" ^ string_of_int n ^ "]"
		 ^ List.foldl (fn (c, s) => s ^ "\t\t" ^ string_of_constrs_at_clk_instindex c n (constrs_of_clk_instindex c n)) "" clocks)
    fun print_run k =
      if k > step_index
      then ()
      else (print_instant k ; print_run (k + 1))
  in print_clocks (); print_run 1
end

fun uniq l =
  let fun aux (x :: l') acc =
          if List.exists (fn x' => x' = x) acc
          then aux l' acc
          else aux l' (x :: acc)
      | aux [] acc             = acc
  in List.rev (aux l [])
  end
and clocks_of_system (G: constr list) =
  uniq (List.concat (List.map (fn
    Timestamp (c, _, _) => [c]
  | Ticks (c, _)        => [c]
  | NotTicks (c, _)     => [c]
  | _ => []
  ) G))

fun print_run isar_state = let
  val {context, facts, goal} = isar_state (* @{Isar.goal} *)
  val imp_cst $ (true_p $ (sat_sy $ (pair $ gamma $ (pair' $ run_index $ tail))))
              $ original = Thm.prop_of goal
  val parsed_constraints = constr_context_of_term gamma
  in
    writeln "Run diagram:";
    print_system (HOLogic.dest_nat run_index) (clocks_of_system parsed_constraints) parsed_constraints
  end

fun print_run_from_goal (isar_goal: thm) = let
  val imp_cst $ (true_p $ (sat_sy $ (pair $ gamma $ (pair' $ run_index $ tail))))
              $ original = Thm.prop_of isar_goal
  val parsed_constraints = constr_context_of_term gamma
  in
    writeln "Run diagram:";
    print_system (HOLogic.dest_nat run_index) (clocks_of_system parsed_constraints) parsed_constraints
  end

end

val _ =
  Outer_Syntax.command @{command_keyword print_run} "print Hygge run in the current Isar goal"
      let val printer : (Toplevel.state -> unit) =
        fn tl_state => let val {context = ctxt, goal = thm} = Proof.simple_goal (Toplevel.proof_of tl_state)
                       in print_run_from_goal thm end
      in (Scan.succeed (Toplevel.keep (printer))) end
\<close>

section\<open> Main solver at a glance \<close>

method solve_run_witness uses Abs_run_inverse_rewrite =
  rule witness_consistency,
  auto,
  ((simp add: Abs_run_inverse_rewrite mono_iff_le_Suc)+)?,
  (match conclusion in "False" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>succeed\<close>)

method solve_run_witness_end uses Abs_run_inverse_rewrite =
  rule witness_consistency,
  auto,
  ((simp add: Abs_run_inverse_rewrite mono_iff_le_Suc)+)?

named_theorems init
declare instant_i [init]

named_theorems elims
declare sporadic_on_e2 [elims]
declare sporadic_on_e1 [elims]
declare implies_e2 [elims]
declare implies_e1 [elims]

method heron_next_step =
  rule finite_SAT_i, rule init, solve_run_witness Abs_run_inverse_rewrite: Abs_run_inverse_rewrite,
 (rule finite_SAT_i, rule elims, solve_run_witness Abs_run_inverse_rewrite: Abs_run_inverse_rewrite)+
method heron_end =
  rule finite_SAT_ax, simp, solve_run_witness_end Abs_run_inverse_rewrite: Abs_run_inverse_rewrite

method heron_next_step_UNSAFE =
  rule finite_SAT_i, rule init, solve_run_witness Abs_run_inverse_rewrite: Abs_run_inverse_rewrite_unsafe,
 (rule finite_SAT_i, rule elims, solve_run_witness Abs_run_inverse_rewrite: Abs_run_inverse_rewrite_unsafe)+
method heron_end_UNSAFE =
  rule finite_SAT_ax, simp, solve_run_witness_end Abs_run_inverse_rewrite: Abs_run_inverse_rewrite_unsafe

(* Are Eisbach methods recursive? *)
method heron_step for n ::nat = (heron_step \<open>Suc n\<close>)

end