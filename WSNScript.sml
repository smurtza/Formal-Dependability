(* ========================================================================= *)
(* File Name: WSNScript.sml		                                     *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Reliability Analysis of Data Transport Protocol       *)
(*                 using Theorem Proving  			             *)
(*                                                                           *)
(*                HOL4-Kananaskis 10 		 			     *)
(*							          	     *)
(*		Author :  Waqar Ahmad             		     	     *)
(*                                              			     *)
(* 	    School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*	    National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                          		               	     *)
(*                                                                           *)
(* ========================================================================= *)

(*loadPath := "/home/waqar/Downloads/RBD" :: !loadPath;*)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
    	  "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory",
	  "transcTheory", "rich_listTheory", "pairTheory",
	  "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
	  "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","dep_rewrite","RBDTheory","FT_deepTheory","VDCTheory","smart_gridTheory","ASN_gatewayTheory"];
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory 
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite 
      RBDTheory FT_deepTheory VDCTheory smart_gridTheory ASN_gatewayTheory ;

fun K_TAC _ = ALL_TAC;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "WSN";

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

(*--------------------------------------*)
val E2W_WSN = store_thm("E2W_WSN",
  ``!p t X_fil X_aggr X_rout C_fil C_aggr C_rout. 
       	      (0 <= t) /\ 
       	      prob_space p /\
	      exp_dist_list p ([X_fil;X_aggr;X_rout]) 
	      		      ([C_fil;C_aggr;C_rout])  /\
	      mutual_indep p 
	      	(rel_event_list p ([X_fil;X_aggr;X_rout]) t) /\
	      (!x. 
	      	   MEM x (rel_event_list p ([X_fil;X_aggr;X_rout]) t) ==> 
	      	   x IN events p) ==>
	       (prob p (rbd_struct p
	            (series (rbd_list (rel_event_list p [X_fil;X_aggr;X_rout] t)))) =
	        exp (-list_sum[C_fil;C_aggr;C_rout] * t))``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[series_struct_thm]
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[rel_event_list_def])
++ MP_TAC (ISPECL [``p:'a event # 'a event event # ('a event -> real)``, ``t:real``,``[X_fil; X_aggr; X_rout]:('a->extreal) list``,``[C_fil; C_aggr; C_rout]:real list`` ]rel_prod_series_rbd_exp_dist)
++ RW_TAC list_ss[]
++ RW_TAC list_ss[exp_func_list_def,list_sum_def,list_prod_def]
++ RW_TAC real_ss[GSYM EXP_ADD]
++ REAL_ARITH_TAC);
(*------------------------------------*)
val one_minus_exp_equi = store_thm("one_minus_exp_equi",
  ``!t c. (one_minus_list (exp_func_list c t)) = 
       	  (one_minus_exp t c)``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[exp_func_list_def,one_minus_exp_def,one_minus_list_def])
++ RW_TAC list_ss[exp_func_list_def,one_minus_exp_def,one_minus_list_def]
>> (RW_TAC real_ss[REAL_MUL_COMM])
++ FULL_SIMP_TAC list_ss[exp_func_list_def,one_minus_exp_def]);
(*-------------------------------------*)

val ESRT_WSN = store_thm("ESRT_WSN",
  ``!p t X_routing_list C_routing_list. 
       	      (0 <= t) /\ 
       	      prob_space p /\
	      ~NULL (rel_event_list p X_routing_list t) /\
	      exp_dist_list p (X_routing_list) 
	      		      (C_routing_list)  /\
              (LENGTH X_routing_list = LENGTH C_routing_list) /\
	      mutual_indep p 
	      	(rel_event_list p (X_routing_list) t) /\
	      (!x. 
	      	   MEM x (rel_event_list p (X_routing_list) t) ==> 
	      	   x IN events p) ==>
	       (prob p (rbd_struct p
	            (parallel (rbd_list (rel_event_list p X_routing_list t)))) =
	        1 - list_prod (one_minus_exp t C_routing_list))``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[parallel_struct_thm]
++ RW_TAC list_ss[]
++ RW_TAC std_ss[GSYM one_minus_exp_equi]
++ MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate_lemma1
++ RW_TAC list_ss[]);

(*-------------------------------------*)
val parallel_series_struct_rbd_v2 = store_thm("parallel_series_struct_rbd_v2",
  ``!p L.  (!z. MEM z L ==> ~NULL z) /\ prob_space p /\
     (!x'. MEM x' (FLAT L) ==> x' IN events p) /\ mutual_indep p (FLAT L) ==>
     (prob p
        (rbd_struct p ((parallel of (λa. series (rbd_list a))) L)) = 
	 1 - (list_prod o (one_minus_list) of
	      (\a. list_prod (list_prob p a))) L) ``,
RW_TAC std_ss[]
++ (`1 - list_prod 
          ((one_minus_list of 
            (λa. list_prod (list_prob p a))) L) = 
     1 − list_prod 
       	 (one_minus_list (list_prod_rel p L)) ` 
by RW_TAC std_ss[of_DEF,o_DEF,list_prod_rel_def])
++ RW_TAC std_ss [rel_parallel_series_rbd]);


(*---------------------------------------*)

val parallel_series_exp_fail_rate = store_thm("parallel_series_exp_fail_rate",
  ``!p t L C.
     (!z. MEM z L ==> ~NULL z) /\ 0 <= t /\ prob_space p /\
     (!x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ==> x' IN events p) /\
     (LENGTH C = LENGTH L) /\
     (!n.
        n < LENGTH L /\ n < LENGTH C ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) /\
     two_dim_exp_dist_list p L C ==>
     (1 - (list_prod o (one_minus_list) of
	(\a. list_prod (list_prob p a))) 
	     (two_dim_rel_event_list p L t) = 
     1 - (list_prod o (one_minus_list) of
	(\a. list_prod (exp_func_list a t))) C) ``,
GEN_TAC ++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,
		   list_prod_def,list_prob_def,LENGTH_NIL])
++ GEN_TAC ++ Induct
   >> (RW_TAC list_ss[])
++ GEN_TAC ++ RW_TAC std_ss[]
++ RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,
	          list_prod_def,list_prob_def,one_minus_list_def,exp_func_list_def]
++ (`list_prod (list_prob p (rel_event_list p h t)) = 
     list_prod (exp_func_list h' t)` 
   by MATCH_MP_TAC rel_prod_series_rbd_exp_dist)
   >> (FULL_SIMP_TAC list_ss[two_dim_exp_dist_list_def,two_dim_rel_event_list_def]
   ++ (FIRST_X_ASSUM (Q.SPECL_THEN [`0:num`] MP_TAC)
   ++ RW_TAC list_ss[]))
++ POP_ORW
++ FULL_SIMP_TAC std_ss[exp_func_list_def]
++ RW_TAC real_ss[real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
++ RW_TAC real_ss[REAL_EQ_MUL_LCANCEL]
++ DISJ2_TAC
++ FULL_SIMP_TAC real_ss[real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
++ RW_TAC std_ss[GSYM two_dim_rel_event_list_def]
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF]
++ (FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list list`] MP_TAC))
++ DEP_ASM_REWRITE_TAC[]
++ RW_TAC std_ss[]
++ DEP_ASM_REWRITE_TAC[]
++ FULL_SIMP_TAC list_ss[two_dim_exp_dist_list_def,two_dim_rel_event_list_def]
++ RW_TAC std_ss[]
++ FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
++ RW_TAC list_ss[]);
   
(*------------------------------------------------*)
val rel_parallel_series_exp_fail_rate = store_thm("rel_parallel_series_exp_fail_rate",
  ``!p t L C.
     (!z. MEM z L ==> ~NULL z) /\ 0 <= t /\ prob_space p /\
     (!x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ==> x' IN events p) /\
     mutual_indep p (FLAT (two_dim_rel_event_list p L t)) /\
     (LENGTH C = LENGTH L) /\
     (!n.
        n < LENGTH L /\ n < LENGTH C ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) /\
     two_dim_exp_dist_list p L C ==>
(prob p
        (rbd_struct p ((parallel of (λa. series (rbd_list a))) 
		    (two_dim_rel_event_list p L t))) =
      1 - (list_prod o (one_minus_list) of
	(\a. list_prod (exp_func_list a t))) C)``,

REPEAT GEN_TAC ++ REPEAT STRIP_TAC
++ DEP_REWRITE_TAC[parallel_series_struct_rbd_v2]
++ DEP_REWRITE_TAC[parallel_series_exp_fail_rate]
++ RW_TAC std_ss[]
++ POP_ASSUM MP_TAC
++ REWRITE_TAC[two_dim_rel_event_list_def]
++ MATCH_MP_TAC mem_flat_map_not_null3
++ RW_TAC std_ss[]);

(*------------------------------------------------*)
val RMST_fail_rate_list_def = Define 
`(RMST_fail_rate_list a b 0 = []) /\
 (RMST_fail_rate_list a b (SUC n) = [a;b]::(RMST_fail_rate_list a b n)) `;

(*------------------------------------------------*)
val RMST_WSN = store_thm("RMST_WSN",
  ``!p (t:real)  X_rout X_MLD C_rout C_MLD n. 
     	(!z. MEM z (RMST_fail_rate_list X_rout X_MLD n)  ==>  ~NULL z) /\
	 (0 <=  (t:real)) /\ prob_space p /\
   	 (!x'.
	    MEM x' (FLAT ((two_dim_rel_event_list p 
	    	(RMST_fail_rate_list X_rout X_MLD n)  t))) ==>
	    (x' IN events p)) /\
	 (mutual_indep p 
	   (FLAT (two_dim_rel_event_list p 
	   	 (RMST_fail_rate_list X_rout X_MLD n)  t))) /\
	 (LENGTH (RMST_fail_rate_list C_rout C_MLD n)  = 
	  LENGTH (RMST_fail_rate_list X_rout X_MLD n)) /\
	 (!n'. 
	    (n' < LENGTH (RMST_fail_rate_list X_rout X_MLD n)) /\ 
	    (n' < LENGTH (RMST_fail_rate_list C_rout C_MLD n) ) ==>
	 (LENGTH (EL n' (RMST_fail_rate_list X_rout X_MLD n)) = 
	  LENGTH (EL n' (RMST_fail_rate_list C_rout C_MLD n)))) /\
  	 two_dim_exp_dist_list p ((RMST_fail_rate_list X_rout X_MLD n))
	 		       	 ((RMST_fail_rate_list C_rout C_MLD n)) ==> 
(prob p
       (rbd_struct p ((parallel of (λa. series (rbd_list a))) 
		    (two_dim_rel_event_list p (RMST_fail_rate_list X_rout X_MLD n) t))) =
      1 - (list_prod o (one_minus_list) of
	(\a. list_prod (exp_func_list a t))) 
	     (RMST_fail_rate_list C_rout C_MLD n))``,
REPEAT GEN_TAC ++ REPEAT STRIP_TAC
++ MATCH_MP_TAC rel_parallel_series_exp_fail_rate
++ RW_TAC list_ss[]);



val _ = export_theory();