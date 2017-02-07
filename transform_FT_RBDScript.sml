app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","RBDTheory","FT_deepTheory","VDCTheory","ASN_gatewayTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory
      RBDTheory FT_deepTheory VDCTheory ASN_gatewayTheory;
open HolKernel boolLib bossLib Parse;
val _ = new_theory "transform_FT_RBD";
(*------new tactics for set simplification----*)
(*--------------------*)
infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

(*---------------------------*)
fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN METIS_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);


val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a ->bool) UNION UNIONL ss)`;


val IN_UNIONL = store_thm
("IN_UNIONL",
``!l (v:'a ). v IN UNIONL l = (?s. MEM s l /\ v IN s)``,
Induct >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
++ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
++ PROVE_TAC []);


val elt_rewrs
= [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o,
IN_UNIONL, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];


fun rewr_ss ths =
simpLib.++
(std_ss,
simpLib.SSFRAG
{ac = [],
name = NONE,
convs = [],
dprocs = [],
filter = NONE,
rewrs = set_rewrs @ elt_rewrs,
congs = []});
val pset_set_ss = rewr_ss set_rewrs;
val pset_elt_ss = rewr_ss elt_rewrs;
val pset_ss = rewr_ss (set_rewrs @ elt_rewrs);


fun PSET_TAC ths =
REPEAT (POP_ASSUM MP_TAC)
++ RW_TAC pset_set_ss ths
++ REPEAT (POP_ASSUM MP_TAC)
++ RW_TAC pset_elt_ss ths;


(*--------AND_to_series-------------------*)
val AND_to_series = store_thm("AND_to_series",
  ``!p L. FTree p (AND (gate_list L)) =
       	  rbd_struct p (series (rbd_list L))``,
RW_TAC std_ss[series_rbd_eq_big_inter,AND_gate_eq_big_inter]);

(*---------OR_to_parallel-----------------------------*)
val OR_to_parallel = store_thm("OR_to_parallel",
  ``!p L. FTree p (OR (gate_list L)) =
       	  rbd_struct p (parallel (rbd_list L))``,
GEN_TAC ++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]);

(*-----------AND-OR-to-series-parallel----------------------------*)
val AND_OR_to_series_parallel = store_thm("AND_OR_to_series_parallel",
  ``!p L. (FTree p ((AND of (\a. OR (gate_list a))) L) =
       	  rbd_struct p ((series of (\a. parallel (rbd_list a))) L))``,
GEN_TAC ++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF,OR_to_parallel]);

(*-----------------------OR_AND_to_parallel_series---------------------------------------*)
val OR_AND_to_parallel_series = store_thm("OR_AND_to_parallel_series",
  ``!p L. (FTree p ((OR of (\a. AND (gate_list a))) L) =
       	  rbd_struct p ((parallel of (\a. series (rbd_list a))) L))``,

GEN_TAC ++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF,AND_to_series]);

(*-------------NAND_gate_transform------------------------*)
val NAND_gate_transform = store_thm("NAND_gate_transform",
  ``!L1 L2 n p. (FTree p (AND (gate_list (compl_list p L1 ++ L2)))) =
  	     	 (rbd_struct p (series (rbd_list (compl_list p L1 ++ L2)))) ``,
RW_TAC std_ss[]
++ MP_TAC(Q.ISPECL [`p:α event # α event event # (α event -> real)`,`(compl_list p L1 ++ L2)`] AND_to_series)
++ RW_TAC std_ss[]);

(*-------------NOR_gate_transform------------------------*)
val NOR_gate_transform = store_thm("NOR_gate_transform",
  ``!p L. p_space p DIFF FTree p (OR (gate_list L)) = 
       	  p_space p DIFF rbd_struct p (parallel (rbd_list L))``,

GEN_TAC ++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ RW_TAC std_ss[OR_to_parallel]);
(*-------------Inhibit_gate_transform------------------------*)
val Inhibit_gate_transform = store_thm("Inhibit_gate_transform",
  ``!p A B C. prob_space p /\ C IN events p ==> 
       	      (FTree p (AND [OR [atomic A; atomic B]; NOT (atomic C)]) =
       	      (rbd_struct p (parallel [atomic A; atomic B]) INTER 
	      		    (p_space p DIFF rbd_struct p (atomic C)))) ``,
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``(p_space p DIFF C):('a->bool)``, ``p_space p:('a->bool)``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ DEP_REWRITE_TAC[EVENTS_COMPL]
++ RW_TAC std_ss[]);
(*-------------comp_gate_transform------------------------*)
val comp_gate_transform = store_thm("comp_gate_transform",
  ``!p A B. prob_space p /\ A IN events p /\ B IN events p ==>
       	    (FTree p (OR [AND [atomic A; atomic B]; NOT (OR [atomic A; atomic B])]) =
	    rbd_struct p (series [atomic A; atomic B]) UNION 
	    	       	 (p_space p DIFF rbd_struct p (parallel [atomic A; atomic B])))``,
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]);
(*-------------k_out_N_to_majority_voting_gate------------------------*)
val k_out_N_to_majority_voting_gate = store_thm(
  "k_out_N_to_majority_voting_gate",
  ``!p X k n.
      majority_voting_FT_gate p X k n = K_out_N_struct p X k n``,
RW_TAC std_ss[majority_voting_FT_gate_def,K_out_N_struct_def]);

val _ = export_theory();
