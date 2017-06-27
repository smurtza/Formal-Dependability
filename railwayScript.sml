(* ========================================================================= *)
(* File Name: RailwayScript.sml		                                     *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Fault Tree based Dependability Analysis of            *)
(*                Railway Level Crossing using Theorem Proving               *)
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
val _ = new_theory "railway";

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
val in_events_def = Define 
`in_events p L = (!z. MEM z L ==> z IN events p)`;
(*--------------------------------------*)
val two_dim_fail_event_list_def = Define 
`two_dim_fail_event_list p L t = MAP (\a. fail_event_list p a t) L `;
(*--------------------------------------*)
val three_dim_fail_event_list_def = Define 
`three_dim_fail_event_list p L t = MAP (\a. two_dim_fail_event_list p a t) L `;
(*--------------------------------------*)

val railway_FT_equi_RBD = store_thm("railway_FT_equi_RBD",
  `` prob_space p /\ in_events p (fail_event_list p [x1;x2;x3;x4;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] t) ==>
((FTree p (OR[OR(gate_list (fail_event_list p [x3;x4] t));
		    OR(gate_list (fail_event_list p [x5;x6] t));
		    AND[OR (gate_list (fail_event_list p [x9;x10] t));
		        OR(gate_list (fail_event_list p [x13;x14] t));
			OR(gate_list (fail_event_list p [x15;x16] t));
			OR(gate_list (fail_event_list p [x11;x12] t))];
		    OR(gate_list (fail_event_list p [x7;x8] t));
		    OR(gate_list (fail_event_list p [x1;x2] t))])) =
(rbd_struct p
  ((parallel
     of series of (λa. parallel (rbd_list a)))
        (three_dim_fail_event_list p [[[x3; x4; x5; x6; x7; x8; x1; x2]];
         [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t))))``,
RW_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,FTree_def,of_DEF,o_THM,fail_event_list_def,rbd_list_def,gate_list_def]
++ RW_TAC std_ss[UNION_EMPTY,UNION_ASSOC]
++ RW_TAC std_ss[INTER_ASSOC]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
++ FULL_SIMP_TAC list_ss[in_events_def]
++ DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
++ FULL_SIMP_TAC list_ss[in_events_def]
++ SRW_TAC[][EXTENSION,GSPECIFICATION]
++ SET_TAC[]);

(*--------------------------------------*)

val one_minus_exp_func_list_def = Define 
`one_minus_exp_func_list C t = MAP (λa. 1 - exp (-(a * (t:real)))) C `;


(*--------------------------------------*)
val fail_prob_railway_FT = store_thm("fail_prob_railway_FT",
``(0 <= t) /\ prob_space p /\ 
mutual_indep p
  (FLAT
     (FLAT
        (FLAT
           [three_dim_fail_event_list p
              [[[x3; x4; x5; x6; x7; x8; x1; x2]];
               [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t]))) /\
(∀x'.
   MEM x'
     (FLAT
        (FLAT
           (FLAT
              [three_dim_fail_event_list p
                 [[[x3; x4; x5; x6; x7; x8; x1; x2]];
                  [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]]
                 t]))) ⇒
   x' ∈ events p) /\
 exp_dist_list p [x1;x2;x3;x4;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] [c1;c2;c3;c4;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==> 
(prob p (FTree p (OR[OR(gate_list (fail_event_list p [x3;x4] t));
		    OR(gate_list (fail_event_list p [x5;x6] t));
		    AND[OR (gate_list (fail_event_list p [x9;x10] t));
		        OR(gate_list (fail_event_list p [x13;x14] t));
			OR(gate_list (fail_event_list p [x15;x16] t));
			OR(gate_list (fail_event_list p [x11;x12] t))];
		    OR(gate_list (fail_event_list p [x7;x8] t));
		    OR(gate_list (fail_event_list p [x1;x2] t))])) = 
(1 −
exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
(1 −
 (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
 (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
 (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
 (1 − exp (-(c11 * t)) * exp (-(c12 * t)))))) ``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[railway_FT_equi_RBD]
++ RW_TAC std_ss[in_events_def]
>> (FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC std_ss[of_DEF]
++ DEP_REWRITE_TAC[rel_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (Q.EXISTS_TAC `[]`
   ++ RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
++ RW_TAC list_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM,three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ FULL_SIMP_TAC list_ss[exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def,fail_event_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);

val _ = export_theory();