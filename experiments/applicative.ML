signature APPLICATIVE =
sig;
  type afun =
   {pure: term,
    ap: term,
    identity: thm,
    composition: thm,
    homomorphism: thm,
    interchange: thm}
  val add_generic: afun -> Context.generic -> Context.generic
  val add_global: afun -> theory -> theory
  val get: Context.generic -> term -> afun

  val mk_op_pattern: term -> int * int -> term
end;

structure Applicative : APPLICATIVE =
struct

type afun =
 {pure: term,
  ap: term,
  identity: thm,
  composition: thm,
  homomorphism: thm,
  interchange: thm};

fun consts_of {pure, ap, ...} = (pure, ap);

val afun_ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord o apply2 consts_of;

structure Data = Generic_Data
(
  type T = afun Ord_List.T;
  val empty = [];
  val extend = I;
  val merge = Ord_List.merge afun_ord;
);

val add_generic = Data.map o Ord_List.insert afun_ord;

fun add_global af = Context.theory_map (add_generic af);

fun mk_op_pattern t (0, _) = t
  | mk_op_pattern t (n, i) =
    let val v = Var (("", i + 1), dummyT)
    in mk_op_pattern (betapply (t, v)) (n - 1, i + 1) end;

fun get context t =
  let
    val thy = Context.theory_of context;
    fun pat t n = mk_op_pattern t (n, maxidx_of_term t);
    fun matches af = Pattern.matches thy (pat (#ap af) 2, t) orelse
        Pattern.matches thy (pat (#pure af) 1, t);
    fun lookup afs = (case find_first matches afs of
        SOME x => x
      | NONE => raise TERM ("Applicative.get", [t]));
  in lookup (Data.get context) end;

end;
