section \<open> Vector Syntax and Code Generation \<close>

theory Vector_Syntax
  imports "HOL-Analysis.Analysis"
begin

instantiation vec :: (zero, finite) default
begin
definition default_vec :: "('a, 'b) vec" where
"default_vec = 0"

instance ..

end

syntax
  "_VecType" :: "type \<Rightarrow> type \<Rightarrow> type" ("_ vec[_]" [999, 0] 999)

translations
  (type) "'a^'n" <= (type) "('a, 'n) vec"
  (type) "'a vec['n]" == (type) "'a^'n"

text \<open> We add standard syntax for some vector operators. \<close>

notation norm ("\<parallel>_\<parallel>") and infnorm ("\<parallel>_\<parallel>\<^sub>\<infinity>") and transpose ("_\<^sup>T" [999] 999)

text \<open> The following class allows us to link natural numbers and numeral indices. Essentially
  this shows an isomorphism between a numeral type and a finite range of naturals. \<close>

class nat = finite + numeral + zero +
  fixes nat_of :: "'a \<Rightarrow> nat"
  assumes nat_of: "nat_of ` UNIV = {0..<CARD('a)}"
  and nat_of_0 [simp]: "nat_of 0 = 0"
  and nat_of_1 [simp]: "CARD('a) > 1 \<Longrightarrow> nat_of 1 = 1"
  and nat_of_numeral: "nat_of (numeral n) = numeral n mod CARD('a)"
begin

abbreviation "of_nat' \<equiv> inv nat_of"

lemma nat_of_less_CARD [simp]: "nat_of x < CARD('a)"
  using nat_of by auto

lemma nat_of_range: "nat_of i \<in> {0..<CARD('a)}"
  using nat_of by auto

lemma inj_nat_of: "inj nat_of"
  using nat_of
  apply (rule_tac inj_onI)
  apply (auto)
  by (simp add: eq_card_imp_inj_on inj_eq)

lemma nat_of_inv [simp]: "of_nat' (nat_of x) = x"
  by (simp add: inj_nat_of)

lemma of_nat'_inv [simp]: "x < CARD('a) \<Longrightarrow> nat_of (of_nat' x) = x"
  by (simp add: f_inv_into_f local.nat_of)

lemma bij_nat_of: "bij_betw nat_of UNIV {0..<CARD('a)} "
  using bij_betw_def inj_nat_of local.nat_of by blast

lemma nat_of_numeral' [simp]: "numeral n < CARD('a) \<Longrightarrow> nat_of (numeral n) = numeral n"
  by (simp add: local.nat_of_numeral)

end

text \<open> Instances of the @{class nat} class for concrete numerals. \<close>

abbreviation "Abs_bit0n \<equiv> (\<lambda> x. Abs_bit0 (int x))"
abbreviation "Rep_bit0n \<equiv> (\<lambda> x. nat (Rep_bit0 x))"

abbreviation "Abs_bit1n \<equiv> (\<lambda> x. Abs_bit1 (int x))"
abbreviation "Rep_bit1n \<equiv> (\<lambda> x. nat (Rep_bit1 x))"

lemma Rep_bit1n:
  fixes x :: "'a::finite bit1"
  shows "Rep_bit1n x \<in> {0..<1 + 2 * CARD('a)}"
  by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)

interpretation bit0n_type:
  type_definition "Rep_bit0n :: 'a::finite bit0 \<Rightarrow> nat" Abs_bit0n "{0..<2 * CARD('a)}"
proof
  fix x :: "'a bit0"
  show "Rep_bit0n x \<in> {0::nat..<(2::nat) * CARD('a)}"
    by (auto, metis bit0.Rep_0 bit0.Rep_less_n card_bit0 int_nat_eq nat_less_as_int)
  show "Abs_bit0n (Rep_bit0n x) = x"
    using Rep_bit0 Rep_bit0_inverse by auto
  show "\<And>y::nat. y \<in> {0::nat..<(2::nat) * CARD('a)} \<Longrightarrow> Rep_bit0n (Abs_bit0n y :: 'a bit0) = y"
    by (auto simp add: bit0.Abs_inverse)
qed

interpretation bit1n_type:
  type_definition "Rep_bit1n :: 'a::finite bit1 \<Rightarrow> nat" Abs_bit1n "{0..<1 + 2 * CARD('a)}"
proof
  fix x :: "'a bit1"
  show "Rep_bit1n x \<in> {0::nat..<1 + (2::nat) * CARD('a)}"
    by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)
  show "Abs_bit1n (Rep_bit1n x) = x"
    using Rep_bit1 Rep_bit1_inverse by auto    
  show "\<And> y. y \<in> {0..<1 + 2 * CARD('a)} \<Longrightarrow> Rep_bit1n (Abs_bit1n y :: 'a bit1) = y"
    by (auto simp add: bit1.Abs_inverse)
qed

instantiation num1 :: nat
begin
definition "nat_of_num1 (x::num1) = (0::nat)"
instance
  by (intro_classes, simp_all add: nat_of_num1_def)
end

instantiation bit0 :: (finite) nat
begin
definition "nat_of_bit0 = Rep_bit0n"
instance
  by (intro_classes, simp_all add: nat_of_bit0_def bit0n_type.Rep_range bit0.Rep_0 bit0.Rep_1
     ,simp add: bit0.Rep_numeral nat_int_comparison(1) of_nat_mod)
end

instantiation bit1 :: (finite) nat
begin
definition "nat_of_bit1 = Rep_bit1n"
instance
  by (intro_classes, simp_all add: nat_of_bit1_def bit1n_type.Rep_range bit1.Rep_0 bit1.Rep_1
     ,metis bit1.Rep_numeral card_bit1 int_ops(3) nat_int of_nat_mod)
end

text \<open> Expand a list with zeros to bring the list up to length @{term n}\<close>

definition ezlist :: "nat \<Rightarrow> 'a::zero list \<Rightarrow> 'a list" where
"ezlist n xs = take n (xs @ replicate (n - length xs) 0)"

lemma length_ezlist [simp]: "length (ezlist n xs) = n"
  by (simp add: ezlist_def)

lemma nth_ezlist: "i < n \<Longrightarrow> ezlist n xs ! i = (if i < length xs then xs ! i else 0)"
  by (auto simp add: ezlist_def nth_append)

text \<open> Construct a vector from a list. \<close>

definition Vec :: "'a::zero list \<Rightarrow> 'a^'m::nat" where
"Vec xs = (\<chi> i. (ezlist CARD('m) xs)!nat_of i)"

code_datatype Vec

lemma Vec_lookup: "(Vec xs :: 'a::zero^'m::nat)$i = ezlist CARD('m) xs ! nat_of i"
  by (auto simp add: Vec_def nth_append less_diff_conv)

lemma Vec_lookup': "(Vec xs)$i = (if (nat_of i < length xs) then xs!nat_of i else 0)"
  apply (auto simp add: ezlist_def Vec_def nth_append less_diff_conv)
  apply (smt (verit) add_diff_inverse_nat add_less_cancel_left linorder_less_linear min.absorb3 nat_of_less_CARD nth_replicate order_less_trans)
  done

definition vec_list :: "'a^'n::nat \<Rightarrow> 'a list" where
"vec_list V = map (vec_nth V \<circ> of_nat') [0..<CARD('n)]"

lemma length_vec_list [simp]: "length (vec_list (V::'a^'n::nat)) = CARD('n)"
  by (simp add: vec_list_def)

lemma vec_list_inverse [simp]: "Vec (vec_list V) = V"
  by (simp add: vec_eq_iff Vec_def ezlist_def vec_list_def comp_def)

lemma Vec_inverse [simp, code]:
  "vec_list (Vec V :: 'a::zero^'m::nat) = ezlist CARD('m) V"
  by (simp add: list_eq_iff_nth_eq vec_list_def Vec_def)

lemma ezlist_vec_list [simp]: "ezlist CARD('b) (vec_list (V :: _^'b::nat)) = vec_list V"
  by (metis Vec_inverse vec_list_inverse)

lemma Vec_lookup_list [code]: "(V :: 'a::zero^'b::nat)$n = vec_list V ! nat_of n"
  by (metis Vec_lookup ezlist_vec_list vec_list_inverse)

lemma Vec_eq_list: "V = W \<longleftrightarrow> vec_list V = vec_list W"
  by (auto simp add: vec_list_def)
     (metis nat_of_inv nat_of_range vec_eq_iff)

lemma Vec_eq_iff: 
  "((Vec V)::'a::zero vec['m::nat]) = Vec W \<longleftrightarrow> (\<forall> i < CARD('m). ezlist CARD('m) V ! i = ezlist CARD('m) W ! i)"
  apply (simp add: vec_eq_iff ezlist_def nth_append Vec_lookup')
  apply (auto)
   apply (rename_tac i)
  apply (drule_tac x="of_nat' i :: 'm" in spec)
  apply (simp)
  apply (metis of_nat'_inv)+
  done

text \<open> Can we find a clever way to formulate these? \<close>

lemma scaleR_Vec:
  "x *\<^sub>R (Vec xs :: 'a::real_vector^'i::nat) = Vec (map (scaleR x) xs)"
  apply (auto simp add: Vec_def ezlist_def scaleR_vec_def fun_eq_iff simp add: less_diff_conv nth_append)
  apply (smt (verit, best) add_diff_inverse_nat add_less_cancel_left linorder_less_linear min.absorb3 nat_of_less_CARD nth_replicate order_less_trans scaleR_eq_0_iff)
  done

lemma scaleR_Vec_list [code]:
  "x *\<^sub>R (V :: 'a::real_vector^'i::nat) = Vec (map (scaleR x) (vec_list V))"
  by (metis scaleR_Vec vec_list_inverse)

lemma sum_nat_of: "(\<Sum>i\<in>(UNIV ::'b::nat set). f (nat_of i)) = (\<Sum>i = 0..<CARD('b). f i)"
  using bij_nat_of sum.reindex_bij_betw by blast  

lemma inner_Vec:
  "(Vec xs :: _^'b::nat) \<bullet> Vec ys 
    = sum_list (map2 (\<bullet>) (ezlist CARD('b) xs) (ezlist CARD('b) ys))"
proof -
  have "sum_list (map2 (\<bullet>) (ezlist CARD('b) xs) (ezlist CARD('b) ys)) = (\<Sum>x = 0..<CARD('b). ezlist CARD('b) xs ! x \<bullet> ezlist CARD('b) ys ! x)"
    by (simp add: sum_list_sum_nth nth_ezlist)
  also have "... = (Vec xs :: _^'b::nat) \<bullet> Vec ys"
    apply (simp add: inner_vec_def Vec_lookup, subst sum_nat_of)
    apply (rule sum.cong, auto)
    done
  finally show ?thesis by simp
qed

lemma zero_Vec [code]:
  "(0 :: _^'b::nat) = Vec (replicate CARD('b) 0)"
  by (simp add: zero_vec_def vec_eq_iff Vec_lookup nth_ezlist)

lemma inner_Vec_list [code]:                      
  "(V :: _^'b::nat) \<bullet> W = sum_list (map2 (\<bullet>) (vec_list V) (vec_list W))"
  by (metis ezlist_vec_list inner_Vec vec_list_inverse)

lemma plus_Vec: "(Vec xs :: _^'b::nat) + Vec ys = Vec (map2 (+) (ezlist CARD('b) xs) (ezlist CARD('b) ys))"
  by (simp add: plus_vec_def vec_eq_iff Vec_lookup nth_ezlist)

lemma plus_Vec_list [code]:
  "(V :: _^'b::nat) + W = Vec (map2 (+) (vec_list V) (vec_list W))"
  by (metis ezlist_vec_list plus_Vec vec_list_inverse)

lemma uminus_Vec: "- (Vec xs :: _^'b::nat) = Vec (map uminus (ezlist CARD('b) xs))"
  by (simp add:  vec_eq_iff Vec_lookup nth_ezlist)

lemma uminus_Vec_list [code]: "- (V :: _^'b::nat) = Vec (map uminus (vec_list V))"
  by (metis Vec_inverse uminus_Vec vec_list_inverse)

lemma minus_Vec: "(Vec xs :: _^'b::nat) - Vec ys = Vec (map2 (-) (ezlist CARD('b) xs) (ezlist CARD('b) ys))"
  by (simp add: vec_eq_iff Vec_lookup nth_ezlist)

lemma minus_Vec_list [code]: "(V :: _^'b::nat) - W = Vec (map2 (-) (vec_list V) (vec_list W))"
  by (metis ezlist_vec_list minus_Vec vec_list_inverse)

instantiation vec :: (real_normed_vector,finite) equal
begin

definition equal_vec :: "'a vec['b] \<Rightarrow> 'a vec['b] \<Rightarrow> bool" where
"equal_vec x y = (x - y = 0)"

instance 
  by (intro_classes, simp add: equal_vec_def)

end

(* Set up the code generator for vectors, so we can compute cardinalties *)

declare card_bit0 [code_unfold]
declare card_bit1 [code_unfold]
declare card_num0 [code_unfold]
declare card_num1 [code_unfold]

lemma zero_num1_code [code]: "(0::num1) = 1"
  by simp

lemma plus_num1_code [code]: "(x + y :: num1) = 1"
  by simp

lemma card_coset_enum [code]: "card (List.coset xs ::'a::enum set) = card (set Enum.enum - set xs)"
  by (simp add: enum_UNIV Compl_eq_Diff_UNIV)

ML \<open>

structure Vector_Utils =
struct

    fun mk_bintype n =
      let
        fun mk_bit 0 = \<^type_name>\<open>bit0\<close>
          | mk_bit 1 = \<^type_name>\<open>bit1\<close>;
        fun bin_of n =
          if n = 1 then Type (\<^type_name>\<open>num1\<close>, [])
          else if n = 0 then Type (\<^type_name>\<open>num0\<close>, [])
          else if n = ~1 then raise TERM ("negative type numeral", [])
          else
            let val (q, r) = Integer.div_mod n 2;
            in Type (mk_bit r, [bin_of q]) end;
      in bin_of n end;


fun dest_list_syn (Const (\<^const_syntax>\<open>List.list.Nil\<close>, _)) = []
  | dest_list_syn (Const (\<^const_syntax>\<open>List.list.Cons\<close>, _) $ t $ u) = t :: dest_list_syn u
  | dest_list_syn t = raise TERM ("Vectors must be ground lists", [t]);


  fun proc_vector (x as Const (\<^const_syntax>\<open>List.list.Cons\<close>, _) $ t $ u) =
    let val len = (1 + length (dest_list_syn u))
        val vecT = Type (\<^type_name>\<open>vec\<close>, [dummyT, mk_bintype len])
        
    in Const(\<^const_syntax>\<open>Vec\<close>, dummyT --> vecT) $ x
    end |
  proc_vector (Const (\<^const_syntax>\<open>List.list.Nil\<close>, _)) = raise (TERM ("Empty vectors are invalid", [])) |
  proc_vector _ = raise Match;
end  
\<close>

syntax 
  "_Vector"  :: "logic \<Rightarrow> logic" ("Vector")
  "_VecList" :: "args \<Rightarrow> logic" ("\<^bold>[_\<^bold>]")

parse_translation \<open> 
let fun vector_tr [t] = Vector_Utils.proc_vector (Term_Position.strip_positions t)
      | vector_tr _ = raise Match in
  [(\<^syntax_const>\<open>_Vector\<close>, K vector_tr)] 
  end
\<close>

translations
  "\<^bold>[x\<^bold>]" => "Vector[x]"
  "\<^bold>[x\<^bold>]" <= "CONST Vec [x]"

term "Vector[1::real,2,3]"

term "Vector[1::real]"

value "2 *\<^sub>R Vector[1::real]"

value "2 *\<^sub>R Vector[1::real,2,3]"

value "Vector[1::real,2,3] + Vector[2,3,4]"

end
