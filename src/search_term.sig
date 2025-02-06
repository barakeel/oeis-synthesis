signature search_term =
sig
  
  include Abbrev
  
  type prog = kernel.prog
  type seq = kernel.seq
  type ppsisl = string * (string list * int)
  
  datatype searchlimit = Visits of int | Seconds of real * real
  val search : term list -> searchlimit -> term list
   
  val smt_operl : term list 
  val search_smt : term list -> real -> term list
  
  (* syntax *)
  val is_recvar : term -> bool
  val nonesting : bool ref
  val contain_nested : term -> bool
  val rm_forall : term -> term
  val xvar : term 
  val yvar : term
  val zvar : term
  val is_xvar : term -> bool
  val is_yvar : term -> bool
  val is_zvar : term -> bool
  (* works only for first-order terms *)
  val contain_x : term -> bool
  val contain_y : term -> bool
  val contain_z : term -> bool
  
  (* skolemization and instantiation *)
  val arity_of_entry : term -> int
  val instance_skl : term list -> prog * prog -> int -> term list
  val all_instances : int -> (prog * prog) * term list -> term list
  
  val dep_sub : (prog * prog) * term list -> (term * term list) list
  val subst_of_tm : term -> (term,term) subst
  val sub_xyz : int -> term list -> int -> (term,term) subst list
  
  (* ground formulas *)
  val ground_formula : 
    term list -> int -> (prog * prog) * term list -> term list
  val cj_glob : term
  
  (* val subtml_glob : term list ref *)
  (* extra examples *)
  val subz : (prog * prog) * term list -> (prog * prog) * term list
  
  (* z3 calls *)
  val z3_prove : string -> string -> int -> term list -> term list -> 
                 (bool * int)
  
  (* parse *)
  val pp_to_stringtag : prog * prog -> string
  val stringtag_to_pp : string -> prog * prog
  val ppil_to_string : (prog * prog) * term list -> string
  val ignore_errors : bool ref
  val parse_ppil : string -> (prog * prog) * term list
  val string_to_ppsisl : string -> ppsisl
  val ppsisl_to_string : ppsisl -> string
  val inductl_cmp : ((prog * prog) * term list) list *
                    ((prog * prog) * term list) list -> order
  val read_inductl :  string -> ((prog * prog) * term list) list
  val write_inductl : string -> ((prog * prog) * term list) list -> unit
  val read_tinductl :  string -> ((prog * prog) * (term list * int)) list
  val write_tinductl : string -> ((prog * prog) * (term list * int)) list -> unit
  
  (* intermediate representation *)
  datatype nmt = Upper of int | Lower of int | Subf of int * int
  val nmt_compare : nmt * nmt -> order
  val nmt_to_string : nmt -> string
  datatype nmttree = Insn of (nmt * nmttree list)
  
  (* evaluate terms and predicates *)
  val create_fed :  prog * prog -> 
    (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict
  val eval_term : (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict 
    -> term -> (IntInf.int * IntInf.int) -> IntInf.int
  val eval_pred : (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict 
    -> term -> (IntInf.int * IntInf.int) -> bool
  val true_pred : (term, IntInf.int * IntInf.int -> IntInf.int) Redblackmap.dict  
    -> term -> bool
  
  (* induction axiom *)
  val human_out : ppsisl -> string
  val induct_axiom : term
  val induct_cj : term -> term
  val gen_pp : prog * prog -> term list -> term list
  val random_inductl : prog * prog -> term list
  val random_inductl_string : string -> string
  val write_ppils_pb : string -> string -> unit
  val write_ppils_pbl : string -> unit
  val z3_prove_inductl : string -> string -> prog * prog -> term list -> string
  val z3_prove_ppil : string -> string
  val z3_prove_para : string -> unit
  val write_pbl_org : string -> unit
  
  (* conversion of inductions predicates between term and NMT representations *)
  val inductl_to_stringl : prog * prog -> term list -> string list
  val stringl_to_inductl : prog * prog -> string list -> term list
  
  (* generate random predicates in parallel *)
  val good_pp : prog * prog -> bool
  val gen_init : string -> unit
  val gen_prove_string : string -> string
  val gen_prove_init : string -> unit
  
  (* z3 instantiation *)
  val all_instantiation :  
    unit -> (((prog * prog) * term list) * (term * term list) list) list
  
  (* oneline *)
  val init_oneline : string -> unit
  
end
