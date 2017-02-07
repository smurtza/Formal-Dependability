(* ========================================================================= *)
(* File Name: Availability.sml		                                     	 *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Availability Analysis using Theorem Proving           *)
(*                   				                                         *)
(*                                                                           *)
(*                HOL4-Kananaskis 10 		 			      				 *)
(*									     									 *)
(*		Author :  Waqar Ahmed             		     	     				 *)
(*                                              			     			 *)
(* 	    School of Electrical Engineering and Computer Sciences (SEECS)   	 *)
(*	    National University of Sciences and Technology (NUST), PAKISTAN  	 *)
(*                                          		               	     	 *)
(*                                                                           *)
(* ========================================================================= *)







app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
    	  "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory",
	  "transcTheory", "rich_listTheory", "pairTheory",
	  "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
	  "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","dep_rewrite",
	  "RBDTheory","FT_deepTheory","VDCTheory","transform_FT_RBDTheory"];
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory 
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite 
      RBDTheory FT_deepTheory VDCTheory transform_FT_RBDTheory;

fun K_TAC _ = ALL_TAC;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "Availability";

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


(*----------------------------*)
val avail_event_def = Define 
`avail_event (L:(('a->extreal) # ('a->extreal)) list) n t = 
{x | (EXTREAL_SUM_IMAGE 
     	  (\a. (FST (EL a L)) x + (SND (EL a L)) x) (count n)  <= t) /\ 
     (t < EXTREAL_SUM_IMAGE
     	  (\a. (FST (EL a L)) x + (SND (EL a L)) x) (count n) + 
     (FST (EL (n) L)) x)}`;
(*----------------------------*)
val union_avail_events_def = Define 
`union_avail_events L n t = 
(BIGUNION (IMAGE (\a. avail_event L a (Normal t)) (count n)))`;
(*----------------------------*)
val union_avail_events1_def = Define 
`union_avail_events1 L t = 
(BIGUNION (IMAGE (\a. avail_event L a (Normal t)) (count (LENGTH L))))`;
(*----------------------------*)
val union_avail_event_list_def = Define 
`union_avail_event_list L n t = 
 MAP (\a. union_avail_events a n t) L`;
(*----------------------------*)
val union_avail_event_list1_def = Define 
`union_avail_event_list1 L t = 
 MAP (\a. union_avail_events1 a t) L`;
(*----------------------------*)
val list_union_avail_event_list_def = Define 
`list_union_avail_event_list L t = 
 MAP (\a. union_avail_event_list1 a t) L`;
(*----------------------------*)
val avail_event_list_def = Define 
`avail_event_list L n t = 
 MAP (\a. avail_event a n t) L `;
(*---------------------------------*)
val expec_avail_def = Define 
`expec_avail p (L:(('a->extreal) # ('a->extreal)) list) n t = 
 sum (0,n) (\a. prob p (avail_event L a t)) `;

(*---------------------------------*)
val expec_avail1_def = Define 
`expec_avail1 p (L:(('a->extreal) # ('a->extreal)) list) n t = 
 sum (0,n) (prob p o (\a. avail_event L a t)) `;

(*---------------------------------*)
val cdf_def = Define `cdf p X t = distribution p X {y| y <= t} `;

(*---------------------------------*)
val rel_event_def = Define `rel_event1 p X t = PREIMAGE X {y | t < y} INTER p_space p`;

(*---------------------------------*)
val reliability_def = Define 
`reliability p X t = 1 - cdf p X t `;

(*-------------------------*)
val expec_def = Define 
`expec n f = sum (0,n) f`;

(*-------------------------*)
val inst_avail_exp_def = Define 
`inst_avail_exp p L n m = 
 !(t:real). (expec n (\a. prob p (avail_event L a (Normal t))) =  
            (SND (m) / (SND m + FST m)) + (FST m /(SND m + FST m)) * 
	    exp (-((SND m + FST m))*t)) `;
(*-------------------------*)
val inst_avail_exp1_def = Define 
`inst_avail_exp1 p L n m = 
 !t. (prob p ( union_avail_events L n &t) =
     (SND m / (SND m + FST m)) + 
     (FST m / (SND m + FST m)) * exp (-((SND m + FST m)) * &t)) `;
(*-------------------------*)
(*-------------------------*)
val inst_avail_exp2_def = Define 
`inst_avail_exp2 p L m = 
 !t. (prob p ( union_avail_events1 L &t)  =
     (SND (m) / (SND m + FST m)) + 
     (FST m /(SND m + FST m)) * exp (-((SND m + FST m)) * &t)) `;
(*-------------------------*)
val inst_avail_exp3_def = Define 
`inst_avail_exp3 p L m = 
 !t. (prob p ( union_avail_events1 L &t INTER p_space p)  =
     (SND (m) / (SND m + FST m)) + 
     (FST m /(SND m + FST m)) * exp (-((SND m + FST m))* &t)) `;
(*-------------------------*)
val inst_avail_exp_list_def = Define 
`(inst_avail_exp_list p [] n M = T) /\ 
 (inst_avail_exp_list p (h::t) n M = inst_avail_exp p h n (HD M) /\ 
  inst_avail_exp_list p t n (TL M) ) `;
(*-------------------------*)
val inst_avail_exp_list1_def = Define 
`(inst_avail_exp_list1 p [] M = T) /\ 
 (inst_avail_exp_list1 p (h::t) M = inst_avail_exp2 p h (HD M) /\ 
  inst_avail_exp_list1 p t (TL M) ) `;
(*-------------------------*)
val inst_avail_exp_list2_def = Define 
`(inst_avail_exp_list2 p [] M = T) /\ 
 (inst_avail_exp_list2 p (h::t) M = inst_avail_exp3 p h (HD M) /\ 
  inst_avail_exp_list2 p t (TL M) ) `;
(*-------------------------*)
val two_dim_inst_avail_exp_def = Define 
`(two_dim_inst_avail_exp p [] M = T) /\ 
 (two_dim_inst_avail_exp p (h::t) M = inst_avail_exp_list1 p h (HD M) /\ 
  two_dim_inst_avail_exp p t (TL M) ) `;
(*-------------------------*)
val steady_state_avail_def = Define 
`steady_state_avail m = (SND (m:real#real) / (SND m + FST m))`;
(*-------------------------*)
val steady_state_avail_list_def = Define 
`(steady_state_avail_list [] = []) /\ 
 (steady_state_avail_list (h::t) =  steady_state_avail h :: steady_state_avail_list t)`;
(*-------------------------*)
val two_dim_steady_state_avail_list_def = Define 
`(two_dim_steady_state_avail_list [] = []) /\ 
 (two_dim_steady_state_avail_list (h::t) =  
  steady_state_avail_list h :: two_dim_steady_state_avail_list t)`;
(*-------------------------*)
val steady_state_avail_prod_def = Define 
`(steady_state_avail_prod [] = (1:real)) /\ 
 (steady_state_avail_prod (h::t) = 
  steady_state_avail h * steady_state_avail_prod t)`;
(*-------------------------*)
val two_dim_steady_state_avail_prod_def = Define 
`(two_dim_steady_state_avail_prod [] = (1:real)) /\ 
 (two_dim_steady_state_avail_prod (h::t) =  
  steady_state_avail_prod h * two_dim_steady_state_avail_prod t)`;

(*---------------------------------*)
val compl_rel_event_eq_fail_events = store_thm("compl_rel_event_eq_fail_event1",
  ``!p t s. prob_space p ==> 
       	    ((p_space p DIFF PREIMAGE s {y | t < y} INTER p_space p) = 
	     (PREIMAGE s {y | y <= t} INTER p_space p))  ``,
SRW_TAC[][PREIMAGE_def,DIFF_DEF,EXTENSION,GSPECIFICATION,REAL_NOT_LT] 
++ SET_TAC[extreal_not_le]);
(*---------------------------------*)
val compl_fail_event_eq_rel_event1 = store_thm("compl_fail_event_eq_rel_event1",
  ``!X t p. p_space p DIFF PREIMAGE X {y | y ≤ t} INTER p_space p =
       	    rel_event1 p X t  ``,
  RW_TAC std_ss[rel_event_def]
  ++ SRW_TAC[][IN_DIFF,PREIMAGE_def,EXTENSION,GSPECIFICATION]
  ++ RW_TAC std_ss[GSYM extreal_lt_def]
  ++ METIS_TAC[]);
(*--------------------------------*)

(*---------------------------------*)
val avail_ge_rel = store_thm("avail_ge_rel",
  ``!p t L. 
        (0 ≤ t) /\
	(~NULL L) /\
	(!n. avail_event L n t IN events p) /\
	(prob_space p) ==>
	 ((reliability p (FST (HD L)) t) <=
	  expec_avail p L (LENGTH L) t)  ``,
NTAC 2 (GEN_TAC)
++ Cases
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[expec_avail_def,avail_event_def]
++ RW_TAC std_ss[ADD1]
++ ONCE_REWRITE_TAC[ADD_SYM]
++ DEP_REWRITE_TAC[GSYM SUM_TWO]
++ ONCE_REWRITE_TAC[ONE]
++ RW_TAC std_ss[sum]
++ RW_TAC real_ss[count_def]
++ SRW_TAC[][]
++ RW_TAC std_ss[EXTREAL_SUM_IMAGE_THM]
++ RW_TAC real_ss[add_lzero]
++ RW_TAC std_ss[reliability_def]
++ RW_TAC std_ss[cdf_def,distribution_def]
++ DEP_REWRITE_TAC[GSYM PROB_COMPL]
++ RW_TAC std_ss[]
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   ++ RW_TAC real_ss[count_def]
   ++ POP_ASSUM MP_TAC
   ++ SRW_TAC[][]
   ++ FULL_SIMP_TAC std_ss[EXTREAL_SUM_IMAGE_THM,add_lzero]
   ++ POP_ASSUM MP_TAC
   ++ ASM_REWRITE_TAC[]
   ++ RW_TAC std_ss[GSYM compl_rel_event_eq_fail_events]
   ++ DEP_REWRITE_TAC [EVENTS_INTER,EVENTS_DIFF]
   ++ RW_TAC std_ss[EVENTS_SPACE]
   ++ POP_ASSUM MP_TAC
   ++ (`!X. PREIMAGE X {y | t < y} = {y | t < X y}` by SET_TAC[IN_PREIMAGE])
   ++ ASM_REWRITE_TAC[])
++ DEP_REWRITE_TAC[ compl_fail_event_eq_rel_event1]
++ RW_TAC std_ss[rel_event_def]
++ (`!X. PREIMAGE X {x | t < x} = {x | t < X x}` by SET_TAC[IN_PREIMAGE])
++ RW_TAC std_ss[]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   ++ RW_TAC real_ss[count_def]
   ++ POP_ASSUM MP_TAC
   ++ SRW_TAC[][]
   ++ FULL_SIMP_TAC std_ss[EXTREAL_SUM_IMAGE_THM,add_lzero]
   ++ POP_ASSUM MP_TAC
   ++ ASM_REWRITE_TAC[]
   ++ RW_TAC std_ss[GSYM compl_rel_event_eq_fail_events]
   ++ DEP_REWRITE_TAC [EVENTS_INTER,EVENTS_DIFF]
   ++ RW_TAC std_ss[EVENTS_SPACE])
++ RW_TAC std_ss[REAL_LE_ADDR]
++ DEP_REWRITE_TAC[SUM_POS]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[PROB_POSITIVE]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[count_def]);
(*-------------------------------*)
val avail_ge_rel1 = store_thm("avail_ge_rel1",
  ``!p t L. 
       (0 ≤ Normal t) /\
       (~NULL L) /\
       (!a b. (a <> b) ==> DISJOINT (avail_event L a (Normal t))
	                            (avail_event L b (Normal t))) /\
       (!n. avail_event L n (Normal t) IN events p)  /\
       (prob_space p) ==> 
         ((reliability p (FST (HD L)) (Normal t)) <=
	  prob p (union_avail_events L (LENGTH L) (t)))  ``,
RW_TAC std_ss[]
++ (`prob p (union_avail_events L (LENGTH L) t) = sum (0,LENGTH L) (prob p o (\a. avail_event L a (Normal t)))`  by MATCH_MP_TAC EQ_SYM)
>> (MATCH_MP_TAC PROB_FINITELY_ADDITIVE
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[union_avail_events_def]
   ++ FULL_SIMP_TAC std_ss[IN_FUNSET])
++ POP_ORW
++ FULL_SIMP_TAC std_ss[IN_FUNSET]
++ RW_TAC std_ss[o_DEF,GSYM expec_avail_def,IN_FUNSET]
++ MATCH_MP_TAC avail_ge_rel
++ RW_TAC real_ss[]
++ FULL_SIMP_TAC list_ss[IN_COUNT]);


(*-------------------------------*)
(*-------------------------neg_exp_tend0_new-------------------------------------------*)
val neg_exp_tend0_new = store_thm("neg_exp_tend0_new",
  ``!t (c:real). (0 < c) ==> (\t. exp (&t*(-c)))--> 0``,
GEN_TAC
++ REWRITE_TAC[EXP_N]
++ RW_TAC real_ss[]
++ MATCH_MP_TAC SEQ_POWER
++ RW_TAC real_ss[]
++ RW_TAC real_ss[abs]
>> (RW_TAC real_ss[EXP_NEG]
   ++ KNOW_TAC(--`(inv (exp c) < (1:real)) = 
   		(inv (exp c) < (inv (1:real)))`--)
       >> (RW_TAC real_ss[REAL_INV_1OVER])
    ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ASSUM K_TAC
    ++ KNOW_TAC(--`abs (inv (exp (c:real))) = abs (inv (exp c) - 0)`--)
    >> (RW_TAC real_ss[])
    ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ASSUM K_TAC
    ++ KNOW_TAC(--`(inv (exp c) < (inv (1:real))) = (1 < exp (c:real))`--)
    >> (MATCH_MP_TAC REAL_INV_LT_ANTIMONO
       ++ RW_TAC real_ss[EXP_POS_LT])
    ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ASSUM K_TAC
    ++ RW_TAC real_ss[EXP_LT_1])
++ RW_TAC std_ss[EXP_NEG]
++ KNOW_TAC(--`(-inv (exp c) < (1:real)) = (-1:real) < -(-inv (exp c)) `--)
   >> (RW_TAC real_ss[REAL_LT_NEG])
++ RW_TAC real_ss[]
++ MATCH_MP_TAC REAL_LT_TRANS
++ EXISTS_TAC(--`0:real`--)
++ RW_TAC real_ss[]
++ RW_TAC real_ss[EXP_POS_LT]);
(*-----------------steady_avail_temp------------------------------------------*)
val steady_avail_temp = store_thm("steady_avail_temp",
  ``!a b:real. 0 < a /\ 0 < b ==> 0 < a + b``,
REAL_ARITH_TAC);

(*---------------------------------------------*)
val steady_state_avail = store_thm("steady_state_avail",
  ``!p L n m t.  ((0 < FST m)/\ (0 < SND m)) /\ inst_avail_exp p L n m ==> (lim(\t.  (expec_avail p L n (Normal &t))) = SND m / (SND m + FST m))``,
RW_TAC std_ss[]
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC (--`((\t. expec_avail p L n (Normal &t)))`--)
++ STRIP_TAC
>> (RW_TAC std_ss[GSYM SEQ_LIM,convergent]
   ++ RW_TAC std_ss [expec_avail_def]
   ++ FULL_SIMP_TAC std_ss[inst_avail_exp_def,expec_def]
   ++ (`(\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) = (\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t)` by RW_TAC std_ss[])
   ++ POP_ORW
   ++ EXISTS_TAC (--`SND (m:real#real) / (SND m + FST m) + 0`--)
   ++ DEP_REWRITE_TAC[SEQ_ADD]
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> 0) = ((\t. (\t. FST m / (SND m + FST m))t * (\t. exp (-(SND m + FST m) * &t))t) --> ((FST m / (SND m + FST m)) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp])
  ++ (`(\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) = (\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t)` by RW_TAC std_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_ADD
  ++ RW_TAC std_ss[SEQ_CONST]
  ++ (`((\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> 0) = ((\t. (\t. FST m / (SND m + FST m))t * (\t. exp (-(SND m + FST m) * &t))t) --> ((FST m / (SND m + FST m)) *0))` by RW_TAC real_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_MUL
  ++ RW_TAC real_ss[SEQ_CONST]
  ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
  ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
  ++ MATCH_MP_TAC neg_exp_tend0_new
  ++ RW_TAC std_ss[]
  ++ RW_TAC std_ss[steady_avail_temp])
++ RW_TAC std_ss [expec_avail_def]
++ FULL_SIMP_TAC std_ss[inst_avail_exp_def,expec_def]
++ (`((\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> (SND m / (SND m + FST m))) = ((\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t) --> ((SND m / (SND m + FST m)) + 0))` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_ADD
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[SEQ_CONST])
++ (`((\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> 0) = ((\t. (\t. FST m / (SND m + FST m))t * (\t. exp (-(SND m + FST m) * &t))t) --> ((FST m / (SND m + FST m)) *0))` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC real_ss[SEQ_CONST]
++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
++ MATCH_MP_TAC neg_exp_tend0_new
++ RW_TAC std_ss[]
++ RW_TAC std_ss[steady_avail_temp]);
(*---------------------------------------------*)
val steady_state_avail1 = store_thm("steady_state_avail1",
  ``!p L n m. prob_space p /\ 
       	      (!t. (!a b. (a <> b) ==> 
	      	   DISJOINT (avail_event L a (Normal (t))) 
		   	    (avail_event L b (Normal (t)))) /\ 
		   (!n. avail_event L n (Normal t) IN events p)) /\ 
	      ((0 < FST m)/\ (0 < SND m)) /\ 
	      inst_avail_exp p L n m ==> 
	        (lim (\t.  
		       (prob p (union_avail_events L n (&t)))) = 
		 SND m / (SND m + FST m))``,
RW_TAC std_ss[]
++ (`!t. prob p (union_avail_events L n t) = sum (0,n) (prob p o (\a. avail_event L a (Normal t)))`  by RW_TAC std_ss[])
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC PROB_FINITELY_ADDITIVE
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC std_ss[IN_FUNSET,IN_COUNT])
   ++ RW_TAC std_ss[union_avail_events_def]
   ++ FULL_SIMP_TAC std_ss[IN_FUNSET])
++ POP_ORW
++ RW_TAC std_ss[o_DEF,GSYM expec_avail_def,IN_FUNSET]
++ MATCH_MP_TAC steady_state_avail
++ RW_TAC real_ss[]);

(*=======================SUPPORTING_THEOREMS==============*)

(* ------------------------------------------------------------------------- *)
(*                 EXT_LE_LT               *)
(* ------------------------------------------------------------------------- *)
val EXT_LE_LT = store_thm("EXT_LE_LT",
  ``!x y: extreal. (x <=  y) \/ y < x = (x = y) \/ x < y \/ y < x``,
RW_TAC std_ss []
++ RW_TAC std_ss [le_lt]
++ KNOW_TAC (--`(x < y \/ (x = y)) = ( (x = y) \/ x < y)`--)
>> (RW_TAC std_ss [DISJ_COMM]
   ++ DISCH_TAC ++ REWRITE_TAC [])
++ RW_TAC std_ss [DISJ_ASSOC]);
(* ------------------------------------------------------------------------- *)
(*                 PERM_refl               *)
(* ------------------------------------------------------------------------- *)
val PERM_refl = Q.store_thm
("PERM_refl",
    `!L. PERM L L`,
    PROVE_TAC[PERM_DEF]);

(* ------------------------------------------------------------------------- *)
(*                 LET_ANTISYM               *)
(* ------------------------------------------------------------------------- *)
val LET_ANTISYM = store_thm("LET_ANTISYM",
  ``!x y. ~(x < y /\ y <=  x)``,
RW_TAC std_ss[extreal_not_le]);

(*---------not_null_leng-------------*)
val not_null_leng = store_thm("not_null_leng",
  ``! L1 . ~NULL L1  ==> 1 <= LENGTH L1``,
FULL_SIMP_TAC list_ss[GSYM LENGTH_NOT_NULL]);

(*---------------------------*)

(*----------------------------*)
val series_expec_tends_prod_avail = store_thm("series_expec_tends_prod_avail",
  ``!p L M. 
       prob_space p /\
       (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
       (LENGTH L = LENGTH M) /\
       (inst_avail_exp_list1 p L M) ==>
  ((\t.list_prod
     (list_prob p (union_avail_event_list1 L (&t))))-->
  steady_state_avail_prod M)  ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,steady_state_avail_prod_def]
   ++ RW_TAC std_ss[SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++  RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,steady_state_avail_prod_def] 
++ (`!t. (
   prob p (union_avail_events1 h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. union_avail_events1 a (&t)) L))) = (\t.
   prob p (union_avail_events1 h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. union_avail_events1 a (&t)) L))) t` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[inst_avail_exp_list1_def,inst_avail_exp2_def]
   ++ REWRITE_TAC[steady_state_avail_def]
   ++ (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))--> (SND h' / (SND h' + FST h'))) = ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)--> (SND h' / (SND h' + FST h') + 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) = ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t) --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]))
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ RW_TAC std_ss[inst_avail_exp_list1_def, GSYM union_avail_event_list1_def]
++ FULL_SIMP_TAC list_ss[ inst_avail_exp_list1_def]);
(*----------series_rbd_avail--------------------*)
val series_rbd_avail = store_thm("series_rbd_avail",
  ``!p L M.  
       prob_space p /\
       (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
       (LENGTH L = LENGTH M) /\
       (!t'. ~NULL (union_avail_event_list1 L &t') /\
       (!z. MEM z (union_avail_event_list1 L ( (&t'))) ==> z IN events p) /\
       mutual_indep p (union_avail_event_list1 L ( (&t')))) /\
       inst_avail_exp_list1 p L M ==> 
        (lim (\t.  prob p 
	     (rbd_struct p 
	     	(series (rbd_list (union_avail_event_list1 L (&t)))))) =
	 steady_state_avail_prod M)``,
RW_TAC std_ss[]
++ (`!t.  prob p (rbd_struct p
       (series (rbd_list (union_avail_event_list1 L (&t))))) =
        list_prod (list_prob p (union_avail_event_list1 L (&t)))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC series_struct_thm
   ++ FULL_SIMP_TAC std_ss[]
   ++ RW_TAC std_ss[]
   ++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `t:num`)
   ++ RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t. list_prod
         (list_prob p (union_avail_event_list1 L  (&t))))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`steady_state_avail_prod M`--)
   ++ MATCH_MP_TAC series_expec_tends_prod_avail
   ++ RW_TAC std_ss[])
++ MATCH_MP_TAC series_expec_tends_prod_avail
++ RW_TAC std_ss[]);

(*--------lim_inst_parall_series_tend_steady-----------------------------*)
val lim_inst_parall_series_tend_steady = store_thm(
  "lim_inst_parall_series_tend_steady",
  ``!p L M. 
       prob_space p /\
       (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
       ((LENGTH L = LENGTH M)) /\
       (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
       (two_dim_inst_avail_exp p L M) ==> 
        ((\t.
	 (list_prod o one_minus_list of
	  (λa. list_prod (list_prob p a))) 
	       (list_union_avail_event_list L (&t))) -->
	 list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M))) ``,
GEN_TAC
++ REWRITE_TAC[of_DEF,o_THM]
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[list_union_avail_event_list_def,steady_state_avail_prod_def,one_minus_list_def,list_prod_def]
   ++ RW_TAC std_ss[SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++ (RW_TAC std_ss[])
++ RW_TAC list_ss[list_union_avail_event_list_def,steady_state_avail_prod_def,one_minus_list_def,list_prod_def]
++ (`(λt.
   (1 − list_prod (list_prob p (union_avail_event_list1 h (&t)))) *
   list_prod
     (one_minus_list
        (MAP (λa. list_prod (list_prob p a))
           (MAP (λa. union_avail_event_list1 a (&t)) L)))) =
   (\t.
    (λt.
	(1 − list_prod (list_prob p (union_avail_event_list1 h (&t))))) t *
    	(\t. list_prod
     	     (one_minus_list
		(MAP (λa. list_prod (list_prob p a))
           	     (MAP (λa. union_avail_event_list1 a (&t)) L)))) t)` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> ((`(\t. 1 − list_prod (list_prob p (union_avail_event_list1 h (&t)))) = (\t. (\t. 1)t − (\t. list_prod (list_prob p (union_avail_event_list1 h (&t)))) t)` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
   ++ MATCH_MP_TAC series_expec_tends_prod_avail
   ++ FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
   ++ FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   ++ RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ FULL_SIMP_TAC list_ss[]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
++ NTAC 5 (POP_ASSUM MP_TAC)
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[]
++ (`(!n. n < LENGTH M ==> (LENGTH (EL n L) = LENGTH (EL n M)))`  by RW_TAC std_ss[])
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
   ++ RW_TAC arith_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM list_union_avail_event_list_def]);
(*-------------parallel-series ABD--------*)
val steady_state_parallel_series_ABD = store_thm(
  "steady_state_parallel_series_ABD",
  ``!p L M .  prob_space p /\
       	      (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
	      ((LENGTH L = LENGTH M)) /\
	       (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M)))  /\
	        (!t'.
		   (!z. MEM z (list_union_avail_event_list L (&t')) ==> ¬NULL z) /\
        	   (!z. MEM z (FLAT (list_union_avail_event_list L (&t'))) ==> z IN events p) /\
        	mutual_indep p (FLAT (list_union_avail_event_list L (&t')))) /\
		(two_dim_inst_avail_exp p L M) ==> 
		  (lim (\t. 
		  prob p
		       (rbd_struct p ((parallel of (λa. series (rbd_list a))) 
		       		     		(list_union_avail_event_list L (&t))))) =
       		  1 - list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M)))  ``,

RW_TAC std_ss[]
++ (`!t. prob p
   	 (rbd_struct p ((parallel of (λa. series (rbd_list a))) 
		       	(list_union_avail_event_list L (&t)))) = 
	1 −
      	  (list_prod o one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t))` by ALL_TAC)
>> (GEN_TAC
   ++ MATCH_MP_TAC parallel_series_struct_rbd_v2
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC (--`( \t. 1 −
       (list_prod o one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t)))`--)
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> ( EXISTS_TAC (--`1 - list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M))`--)
   ++ (`(\t.
	  1 −
   	   (list_prod ((one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t))))) = 
	(\t.
   	 (\t. 1) t −
   	  (\t. (list_prod ((one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t))))) t)` by RW_TAC real_ss[])
  ++ POP_ORW 
  ++ MATCH_MP_TAC SEQ_SUB
  ++ RW_TAC std_ss[SEQ_CONST]
  ++ (`(λt.
   list_prod
     ((one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))) = 
       (λt.
   (list_prod o
     one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))` by RW_TAC real_ss[o_THM])
  ++ POP_ORW
  ++ MATCH_MP_TAC lim_inst_parall_series_tend_steady
  ++ METIS_TAC[])
++ (`(\t.
	  1 −
   	   (list_prod ((one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t))))) = 
	(\t.
   	 (\t. 1) t −
   	  (\t. (list_prod ((one_minus_list of (λa. list_prod (list_prob p a))) 
      		(list_union_avail_event_list L (&t))))) t)` by RW_TAC real_ss[])
  ++ POP_ORW 
  ++ MATCH_MP_TAC SEQ_SUB
  ++ RW_TAC std_ss[SEQ_CONST]
  ++ (`(λt.
   list_prod
     ((one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))) = 
       (λt.
   (list_prod o
     one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))` by RW_TAC real_ss[o_THM])
  ++ POP_ORW
  ++ MATCH_MP_TAC lim_inst_parall_series_tend_steady
  ++ METIS_TAC[]);

(*-----------------------------------*)
val compl_steady_state_avail_def = Define 
`(compl_steady_state_avail [] = 1) /\
 (compl_steady_state_avail (h::t) = 
 (1 - steady_state_avail h) * compl_steady_state_avail (t))`;
(*-------------------------*)
val lim_inst_parall_tend_steady = store_thm("lim_inst_parall_tend_steady",
  ``!p L M. 
  prob_space p /\
  (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
  (LENGTH L = LENGTH M) /\
  (inst_avail_exp_list1 p L M) ==>
  	((\t. list_prod
     	       (one_minus_list
		(list_prob p (union_avail_event_list1 L (&t)))))-->
        compl_steady_state_avail M)  ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,compl_steady_state_avail_def]
   ++ RW_TAC std_ss[one_minus_list_def,list_prod_def,SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++  RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,compl_steady_state_avail_def]
   ++ RW_TAC std_ss[one_minus_list_def,list_prod_def]
++ (` (\t.
   (1 - prob p (union_avail_events1 h (&t))) *
   list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_avail_events1 a (&t)) L)))) = (\t.
   (\t. (1 − prob p (union_avail_events1 h (&t)))) t *
   (\t. list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_avail_events1 a (&t)) L)))) t)` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> ( (`(\t. 1 − prob p (union_avail_events1 h (&t))) = (\t. (\t. 1)t − (\t. prob p (union_avail_events1 h (&t))) t)` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
   ++ FULL_SIMP_TAC list_ss[inst_avail_exp_list1_def,inst_avail_exp2_def]
   ++ REWRITE_TAC[steady_state_avail_def]
   ++ (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))--> (SND h' / (SND h' + FST h'))) = ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)--> (SND h' / (SND h' + FST h') + 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) = ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t) --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]))
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ RW_TAC std_ss[inst_avail_exp_list1_def, GSYM union_avail_event_list1_def]
++ FULL_SIMP_TAC list_ss[ inst_avail_exp_list1_def]);

(*------------------------*)
val lim_inst_series_parall_tend_steady = store_thm(
  "lim_inst_series_parall_tend_steady",
  ``!p L M.
     prob_space p /\ (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
     (LENGTH L = LENGTH M) /\
     (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
     two_dim_inst_avail_exp p L M ==>
     ((\t.
      (list_prod of
       (λa. 1 − list_prod (one_minus_list (list_prob p a)))) 
       	    (list_union_avail_event_list L (&t))) --> 
     list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M)))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[of_DEF,o_THM,list_union_avail_event_list_def,one_minus_list_def,list_prod_def]
   ++ RW_TAC std_ss[SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[of_DEF,o_THM,list_union_avail_event_list_def,one_minus_list_def,list_prod_def]
++ (`(\t.
   (1 −
    list_prod
      (one_minus_list (list_prob p (union_avail_event_list1 h (&t))))) *
   list_prod
     (MAP (λa. 1 − list_prod (one_minus_list (list_prob p a)))
        (MAP (λa. union_avail_event_list1 a (&t)) L))) = (\t.
   (\t. (1 −
    list_prod
      (one_minus_list (list_prob p (union_avail_event_list1 h (&t))))))t *
   (\t. list_prod
     (MAP (λa. 1 − list_prod (one_minus_list (list_prob p a)))
        (MAP (λa. union_avail_event_list1 a (&t)) L))) t)` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> ( (`(\t.
        1 −
        list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 h (&t))))) = (\t.
        (\t. 1) t −
        (\t. list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 h (&t))))) t)` by RW_TAC real_ss[])
    ++ POP_ORW
    ++ MATCH_MP_TAC SEQ_SUB
    ++ RW_TAC std_ss[SEQ_CONST]
    ++ MATCH_MP_TAC lim_inst_parall_tend_steady
    ++ FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
    ++ FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
    ++ RW_TAC arith_ss[EL,HD])
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[]
++ (`(!n. n < LENGTH M ==> (LENGTH (EL n L) = LENGTH (EL n M)))` by RW_TAC std_ss[])
 >> (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
    ++ RW_TAC arith_ss[EL,TL])
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[of_DEF,o_THM]
++ RW_TAC std_ss[GSYM list_union_avail_event_list_def]);
(*-------------Series_parallel ABD---------------------------------*)

val steady_state_series_parallel_avail = store_thm(
  "steady_state_series_parallel_avail",
  ``!p L M.  
       prob_space p /\
       (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
       ((LENGTH L = LENGTH M)) /\
       (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
       (!t'.
        (!z. MEM z (list_union_avail_event_list L (&t')) ==> ¬NULL z) /\
        (!z. MEM z (FLAT (list_union_avail_event_list L (&t'))) ==> z IN events p) /\
        mutual_indep p (FLAT (list_union_avail_event_list L (&t')))) /\
      (two_dim_inst_avail_exp p L M) ==>
      	 (lim (\t. prob p 
	      (rbd_struct p
                     ((series of (λa. parallel (rbd_list a)))
                        (list_union_avail_event_list L (&t))))) =
          list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M)))  ``,
RW_TAC std_ss[]
++ (`!t. prob p
      (rbd_struct p
          ((series of (λa. parallel (rbd_list a)))
               (list_union_avail_event_list L (&t)))) = (list_prod of
       (λa. 1 − list_prod (one_minus_list (list_prob p a)))) 
       	    (list_union_avail_event_list L (&t))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC series_parallel_struct_thm_v2
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t. 
   		   (list_prod of
       		     (λa. 1 − list_prod (one_minus_list (list_prob p a)))) 
       	    	     	  (list_union_avail_event_list L (&t)))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M))`--)
   ++ MATCH_MP_TAC lim_inst_series_parall_tend_steady
   ++ RW_TAC std_ss[])
++ MATCH_MP_TAC lim_inst_series_parall_tend_steady
++ RW_TAC std_ss[]);

(*--------------------------------------------------------*)
(* Definition. Unavailability Event       *)
(* ------------------------------------------------------------------------- *)
val unavail_event_def =  Define `unavail_event p L n t  =  
p_space p DIFF (avail_event L n t INTER p_space p)`;
(*--------------------------------------------------------*)
(* Definition. Union Unavailability Event       *)
(* ------------------------------------------------------------------------- *)
val union_unavail_events_def =  Define `union_unavail_events p L t  =  
p_space p DIFF (union_avail_events1 L t INTER p_space p)`;
(*---------------------------------------------------------*)
(* Definition : Unavailability event list                   *)
(* ------------------------------------------------------------------------- *)
val union_unavail_event_list_def = Define 
`union_unavail_event_list p L t  =  
MAP (\a. union_unavail_events p a t) L`;
(*---------------------------------------------------------*)
(* Definition : list Unavailability event list                   *)
(* ------------------------------------------------------------------------- *)
val list_union_unavail_event_list_def = Define 
`list_union_unavail_event_list p L t  =  
MAP (\a. union_unavail_event_list p a t) L`;
(* ------------------------------------------------------------------------- *)
(* Definition: steady state unavailiabilility with failure and repair rate                               *)
(* ------------------------------------------------------------------------- *)
val steady_state_unavail_def = Define 
`( steady_state_unavail (m:real#real) = FST m / (SND m + FST m))`;

(* ------------------------------------------------------------------------- *)
(* Definition: steady state unavailiabilility with failure and repair rate  list                             *)
(* ------------------------------------------------------------------------- *)
val steady_state_unavail_list_def = Define 
`( steady_state_unavail_list M = MAP (\a. steady_state_unavail a) M) `;

(*---------------------------------------------------------*)
(* Definition: Instantenous Unavailability pair                  *)
(* ------------------------------------------------------------------------- *)
(*-------------------------*)
val inst_unavail_exp_def = Define 
`inst_unavail_exp p L m = 
 !(t). (prob p ( union_unavail_events p L &t)  =  
       (FST (m) / (SND m + FST m)) - 
       (FST m /(SND m + FST m)) * exp (-((SND m + FST m))* &t)) `;
(*-------------------------*)
val inst_unavail_exp_list_def = Define `(inst_unavail_exp_list p [] M = T) /\ (inst_unavail_exp_list p (h::t) M = inst_unavail_exp p h (HD M) /\ inst_unavail_exp_list p t (TL M) ) `;
(*-------------------------*)
val two_dim_inst_unavail_exp_def = Define 
`(two_dim_inst_unavail_exp p [] M = T) /\ 
 (two_dim_inst_unavail_exp p (h::t) M = 
  inst_unavail_exp_list p h (HD M) /\ two_dim_inst_unavail_exp p t (TL M) ) `;

(* ------------------------------------------------------------------------- *)
(*--- Definition.  Unavailability FT gates     ----  *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(*--- Definition. AND unavail FT gate     ----  *)
(* ------------------------------------------------------------------------- *)
val AND_unavail_FT_gate_def =  Define
`!L p. AND_unavail_FT_gate p L t = 
       FTree p (AND (gate_list (union_unavail_event_list p L t)))`;
(* ------------------------------------------------------------------------- *)
(* Definition. OR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
val OR_unavail_FT_gate_def =  Define
`!L p. OR_unavail_FT_gate p L t = 
       FTree p (OR (gate_list (union_unavail_event_list p L t)))`;
(* ------------------------------------------------------------------------- *)
(* Definition. NOR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
val NOR_unavail_FT_gate_def =  Define
`!L p. NOR_unavail_FT_gate p L t  =
       p_space p DIFF FTree p (OR (gate_list (union_unavail_event_list p L t)))`;
(* ------------------------------------------------------------------------- *)
(* Definition. NAND unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
val NAND_unavail_FT_gate_def =  Define
`!L1 L2 p t. NAND_unavail_FT_gate p L1 L2 t  =
     	     FTree p 
	       (AND (gate_list (compl_list p (union_unavail_event_list p L1 t) ++
	     	     	  	             (union_unavail_event_list p L2 t))))`;

(* ------------------------------------------------------------------------- *)
(* Definition. XOR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
val XOR_unavail_FT_gate_def =  Define
`!p X Y t. XOR_unavail_FT_gate p X Y t  =
      	   (XOR_FT_gate p (atomic (union_unavail_events p X t)) 
	   		  (atomic (union_unavail_events p Y t)))`;

(*---------------------------------------*)
val AND_inst_avail_prod_tends_steady = store_thm(
  "AND_inst_avail_prod_tends_steady",
  `` !p L M.
     prob_space p /\ (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
     (LENGTH L = LENGTH M) /\ inst_unavail_exp_list p L M ==>
     ((\t. list_prod (list_prob p (union_unavail_event_list p L (&t)))) -->
     list_prod (steady_state_unavail_list M))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   ++ RW_TAC std_ss[SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def] 
++ (`!t. (
   prob p (union_unavail_events p h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. union_unavail_events p a (&t)) L))) = (\t.
   prob p (union_unavail_events p h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. union_unavail_events p a (&t)) L))) t` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def,inst_unavail_exp_def]
   ++ REWRITE_TAC[steady_state_unavail_def]
   ++ (`((\t.
     FST (h':real#real) / (SND h' + FST h') -
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))--> (FST h' / (SND h' + FST h'))) = ((\t.
     (\t. FST (h':real#real) / (SND  h'+ FST h')) t -
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)--> (FST h' / (SND h' + FST h') - 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) = ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t) --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]))
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ FULL_SIMP_TAC std_ss[inst_unavail_exp_list_def, GSYM union_unavail_event_list_def, GSYM steady_state_unavail_list_def]
++ FULL_SIMP_TAC list_ss[ inst_unavail_exp_list_def]);

(*---------------------------*)
val AND_gate_unavail = store_thm("AND_gate_unavail",
  ``!p L M.  prob_space p /\
       	     (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
	     (LENGTH L = LENGTH M) /\
	     (!t'.
	       ~NULL (union_unavail_event_list p L &t') /\
	       	(!z. MEM z (union_unavail_event_list p L ( (&t'))) ==> z IN events p) /\
		mutual_indep p (union_unavail_event_list p L ( (&t')))) /\
 	     inst_unavail_exp_list p L M ==>
	      (lim (\t.  prob p (AND_unavail_FT_gate p L &t)) =
	       list_prod (steady_state_unavail_list M))``,
RW_TAC std_ss[]
++ RW_TAC std_ss[AND_unavail_FT_gate_def]
++ (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p L (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p L (&t)))` by RW_TAC std_ss[])
>> ( MATCH_MP_TAC AND_gate_thm
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t. list_prod
         (list_prob p (union_unavail_event_list p L  (&t))))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`list_prod (steady_state_unavail_list M)`--)
   ++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   ++ RW_TAC std_ss[])
++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
++ RW_TAC std_ss[]);
   
(*-------------------*)
val lim_inst_OR_tend_steady = store_thm("lim_inst_OR_tend_steady",
  ``!p L M. prob_space p /\
       	    (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
	    (LENGTH L = LENGTH M) /\
	    (inst_unavail_exp_list p L M) ==>
  	      ((\t. 
	      	 list_prod
     	      	   (one_minus_list
			(list_prob p (union_unavail_event_list p L (&t)))))-->
	       list_prod (one_minus_list (steady_state_unavail_list M)))  ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   ++ RW_TAC std_ss[one_minus_list_def,list_prod_def,SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   ++ RW_TAC std_ss[one_minus_list_def,list_prod_def]
++ (` (\t.
   (1 - prob p (union_unavail_events p h (&t))) *
   list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_unavail_events p a (&t)) L)))) = (\t.
   (\t. (1 − prob p (union_unavail_events p h (&t)))) t *
   (\t. list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_unavail_events p a (&t)) L)))) t)` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> ( (`(\t. 1 − prob p (union_unavail_events p h (&t))) = (\t. (\t. 1)t − (\t. prob p (union_unavail_events p h (&t))) t)` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
   ++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def,inst_unavail_exp_def]
   ++ REWRITE_TAC[steady_state_unavail_def]
   ++ (`((\t.
     FST (h':real#real) / (SND h' + FST h') -
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))--> (FST h' / (SND h' + FST h'))) = ((\t.
     (\t. FST h' / (SND  h'+ FST h')) t -
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)--> (FST h' / (SND h' + FST h') - 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) = ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t) --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]))
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ RW_TAC std_ss[inst_unavail_exp_list_def, GSYM union_unavail_event_list_def,GSYM steady_state_unavail_list_def]
++ FULL_SIMP_TAC list_ss[ inst_unavail_exp_list_def]);

(*----------------------------*)
val OR_steady_state_unavail = store_thm("OR_steady_state_unavail",
  ``!p L M. prob_space p /\
       	    (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
     	    (LENGTH L = LENGTH M) /\
     	    (!t'.
	      ~NULL (union_unavail_event_list p L (&t')) /\
              (!z. MEM z (union_unavail_event_list p L (&t')) ==> z IN events p) /\
              mutual_indep p (union_unavail_event_list p L (&t'))) /\
     	    inst_unavail_exp_list p L M ==>
     	      (lim
               (\t.
                 prob p (OR_unavail_FT_gate p L &t)) =
    	      1 -  list_prod (one_minus_list (steady_state_unavail_list M)))``,
RW_TAC std_ss[]
++ RW_TAC std_ss[OR_unavail_FT_gate_def]
++ (`!t.  
      prob p
       (FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
      1 - list_prod (one_minus_list (list_prob p (union_unavail_event_list p L (&t))))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC OR_gate_thm 
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t. 1 -list_prod
         (one_minus_list (list_prob p (union_unavail_event_list p L  (&t)))))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`1 - list_prod (one_minus_list (steady_state_unavail_list M))`--)
   ++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
   ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ RW_TAC std_ss[])
++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
++ MATCH_MP_TAC lim_inst_OR_tend_steady
++ RW_TAC std_ss[]);
(*------------------------------------*)
val steady_state_NOR_unavail_FT_gate = store_thm(
  "steady_state_NOR_unavail_FT_gate",
  ``!p L M.
       prob_space p /\ (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
       (LENGTH L = LENGTH M) /\
       (!t'.
        ~NULL (union_unavail_event_list p L (&t')) /\
        (!z. MEM z (union_unavail_event_list p L (&t')) ==> z IN events p) /\
        mutual_indep p (union_unavail_event_list p L (&t'))) /\
       inst_unavail_exp_list p L M ==>
       	 (lim
	  (\t.
           prob p (NOR_unavail_FT_gate p L &t)) =
    	 list_prod (one_minus_list (steady_state_unavail_list M)))``,
RW_TAC std_ss[NOR_unavail_FT_gate_def]
++ (`!t. (prob p 
   	   (p_space p DIFF
           	    FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
	 1 - prob p (FTree p (OR (gate_list (union_unavail_event_list p L (&t)))))) ` by RW_TAC std_ss[])
>> (MATCH_MP_TAC PROB_COMPL
   ++ METIS_TAC[OR_lem3])
++ POP_ORW
++ (`!t.  prob p
       (FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
        1 - list_prod (one_minus_list (list_prob p (union_unavail_event_list p L (&t))))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC OR_gate_thm
   ++ METIS_TAC[])
++ POP_ORW
++ RW_TAC real_ss[]
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC (--`( \ t.
       list_prod
         (one_minus_list (list_prob p (union_unavail_event_list p L (&t)))))`--)
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC (--`list_prod (one_minus_list (steady_state_unavail_list M))`--)
   ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ RW_TAC std_ss[])
++ MATCH_MP_TAC lim_inst_OR_tend_steady
++ RW_TAC std_ss[]);
(*------------------------*)
val in_events_normal_events = store_thm("in_events_normal_events",
  ``!p A t. prob_space p /\ (p_space p DIFF (A INTER p_space p) IN events p) ==> (A INTER p_space p IN events p)  ``,
 REPEAT GEN_TAC
 ++ RW_TAC std_ss[]
 ++ (`A INTER p_space p = p_space p DIFF (p_space p DIFF (A INTER p_space p))` by MATCH_MP_TAC EQ_SYM)
 >> (DEP_REWRITE_TAC[DIFF_DIFF_SUBSET]
    ++ RW_TAC std_ss[INTER_SUBSET])
 ++ POP_ORW
 ++ MATCH_MP_TAC EVENTS_COMPL
 ++ RW_TAC std_ss[]);


(*-------------------------*)
val lim_inst_NAND_tend_steady = store_thm("lim_inst_NAND_tend_steady",
  ``!p L M. prob_space p /\
       	    (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
 	    (LENGTH L = LENGTH M) /\ 
	    (!t'. 
	      (!z. MEM z ((union_unavail_event_list p L (&t'))) ==> z IN events p)) /\
	    (inst_avail_exp_list2 p L M) ==>
 	      (\t.
   	        list_prod
		  (list_prob p
        	    (compl_list p (union_unavail_event_list p L (&t))))) -->
	      list_prod (steady_state_avail_list M)  ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[LENGTH_NIL_SYM]
   ++ RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_avail_list_def,compl_list_def]
   ++ RW_TAC std_ss[SEQ_CONST])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_avail_list_def,compl_list_def]
   ++ RW_TAC std_ss[one_minus_list_def,list_prod_def]
++ (` (\t.
   prob p (p_space p DIFF union_unavail_events p h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. p_space p DIFF a)
           (MAP (\a. union_unavail_events p a (&t)) L)))) = (\t.
   (\t. prob p (p_space p DIFF union_unavail_events p h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. p_space p DIFF a)
           (MAP (\a. union_unavail_events p a (&t)) L)))) t)` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_MUL
++ RW_TAC std_ss[]
>> ( RW_TAC std_ss[union_unavail_events_def]
   ++ (`!t. (p_space p DIFF
      (p_space p DIFF union_avail_events1 h (&t) INTER p_space p)) = union_avail_events1 h (&t) INTER p_space p ` by RW_TAC std_ss[])
      >> ( DEP_REWRITE_TAC[DIFF_DIFF_SUBSET]
      	 ++ RW_TAC std_ss[INTER_SUBSET])
      ++ POP_ORW
      ++ FULL_SIMP_TAC list_ss[inst_avail_exp_list2_def,inst_avail_exp3_def]
      ++ RW_TAC std_ss[steady_state_avail_def]
      ++ (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))--> (SND h' / (SND h' + FST h'))) = ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)--> (SND h' / (SND h' + FST h') + 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   >> ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) = ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t) --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]))
++ FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
++ FULL_SIMP_TAC list_ss[ inst_avail_exp_list2_def,union_unavail_event_list_def]
++ RW_TAC std_ss[]
++ (`(!t' z.
         MEM z (MAP (\a. union_unavail_events p a (&t')) L) ==>
         z IN events p)` by RW_TAC std_ss[])
   >> (FIRST_X_ASSUM (Q.SPECL_THEN [`t'`,`z`] MP_TAC)
      ++ RW_TAC list_ss[])
   ++ METIS_TAC[GSYM compl_list_def]);


(*-------------------------*)
val NAND_steady_state_avail = store_thm("NAND_steady_state_avail",
  ``!p L1 L2 M1 M2.
       	  prob_space p /\ 
	  (!z. MEM z (M1++M2) ==> 0 < FST z /\ 0 < SND z) /\
     	  ((LENGTH (L1) = LENGTH (M1)) /\ (LENGTH L2 = LENGTH M2)) /\
     	  (!t'.
	    1 ≤ LENGTH  (union_unavail_event_list p L1 (&t') ++ 
	      		 union_unavail_event_list p L2 (&t')) /\
            (!z. MEM z ((union_unavail_event_list p L1 (&t')) ++ 
	    	        (union_unavail_event_list p L2 (&t'))) ==> z IN events p) /\
            mutual_indep p ((union_unavail_event_list p L1 (&t')) ++ 
	 	      	 (union_unavail_event_list p L2 (&t')))) /\
         inst_avail_exp_list2 p L1 M1 /\ inst_unavail_exp_list p L2 M2 ==>
     	  (lim
	    (\t.
             prob p (NAND_unavail_FT_gate p L1 L2 &t)) =
          list_prod ((steady_state_avail_list M1)) *  
	  list_prod ((steady_state_unavail_list M2)))``,
RW_TAC std_ss[]
++ (`!t. prob p
       	    (NAND_unavail_FT_gate p L1 L2 (&t)) = 
	 list_prod (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
      	 list_prod (list_prob p (union_unavail_event_list p L2 (&t)))`  by RW_TAC std_ss[])
>> (RW_TAC std_ss[NAND_unavail_FT_gate_def]
   ++ MATCH_MP_TAC NAND_FT_gate
   ++ ASM_REWRITE_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t. list_prod
         (list_prob p
            (compl_list p (union_unavail_event_list p L1 (&t)))) *
       list_prod (list_prob p (union_unavail_event_list p L2 (&t))))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`( list_prod (steady_state_avail_list M1) *list_prod (steady_state_unavail_list M2))`--)
   ++ (`(\t.
   list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
   list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) =
   (\t.
	(\t. list_prod
     	     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t))))) t *
   	     	(\t. list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) t)  ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_MUL
   ++ RW_TAC std_ss[]
   >> (MATCH_MP_TAC lim_inst_NAND_tend_steady
      (*++ WEAKEN_TAC (equal (Term `events p =POW (p_space p)`))*)
      ++ FULL_SIMP_TAC list_ss[]
      ++ RW_TAC std_ss[]
      ++ FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC)
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC  AND_inst_avail_prod_tends_steady
   ++ FULL_SIMP_TAC list_ss[])
++ (`(\t.
   list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
   list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) =(\t.
   (\t. list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t))))) t *
   (\t. list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) t)  ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_MUL
   ++ RW_TAC std_ss[]
   >> (MATCH_MP_TAC lim_inst_NAND_tend_steady
      (*++ WEAKEN_TAC (equal (Term `events p =POW (p_space p)`))*)
      ++ FULL_SIMP_TAC list_ss[]
      ++ RW_TAC std_ss[]
      ++ FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC)
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC  AND_inst_avail_prod_tends_steady
   ++ FULL_SIMP_TAC list_ss[]);
(*---------------------*)
val inst_XOR_tends_steady = store_thm("inst_XOR_tends_steadty",
  ``!p X1 m1.  
       inst_unavail_exp p X1 m1 /\
       (0 < FST m1 /\ 0 < SND m1) ==> 
        ((\t. prob p (union_unavail_events p X1 (&t))) --> steady_state_unavail m1) ``,
RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[inst_unavail_exp_def]
     ++ RW_TAC std_ss[steady_state_unavail_def]
     ++ (`((\t.
     FST (m1:real#real) / (SND m1 + FST m1) -
     FST m1 / (SND m1 + FST m1) * exp (-(SND m1 + FST m1) * &t))--> (FST m1 / (SND m1 + FST m1))) = ((\t.
     (\t. FST m1 / (SND  m1+ FST m1)) t -
     (\t. FST m1 / (SND m1 + FST m1) * exp (-(SND m1 + FST m1) * &t))t)--> (FST m1 / (SND m1 + FST m1) - 0))` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[SEQ_CONST])
   ++ (`((\t. FST  (m1:real#real) / (SND m1 + FST m1) * exp (-(SND m1  + FST m1) * &t)) --> 0) = ((\t. (\t. FST m1 / (SND m1 + FST m1))t * (\t. exp (-(SND m1 + FST m1) * &t))t) --> ((FST m1 / (SND m1 + FST m1)) *0))` by RW_TAC real_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_MUL
      ++ RW_TAC real_ss[SEQ_CONST]
      ++ ONCE_REWRITE_TAC[REAL_MUL_SYM]
      ++ RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      ++ MATCH_MP_TAC neg_exp_tend0_new
      ++ RW_TAC std_ss[]
      ++ RW_TAC std_ss[steady_avail_temp]);

(*--------------------*)

val XOR_steady_unavail = store_thm("XOR_steady_unavail",
  ``!p X1 X2 m1 m2 t.
     prob_space p  /\ 
     (!t'. 
       union_unavail_events p X1 (&t') IN events p /\
       union_unavail_events p X2 (&t') IN events p /\ 
       indep p (union_unavail_events p X1 (&t'))
       (union_unavail_events p X2 (&t'))) /\ 
     ((0 < FST m1) /\ (0 < SND m1)) /\
     ((0 < FST m2) /\ 0 < SND m2) /\ 
     (inst_unavail_exp p X1 m1) /\
     (inst_unavail_exp p X2 m2) ==>
       (lim (\t. 
       	    prob p   
	     (XOR_FT_gate p (atomic (union_unavail_events p X1 &t))
       	     		    (atomic (union_unavail_events p X2 &t)))) = 
       steady_state_unavail m1 * (1 - steady_state_unavail m2) + 
       steady_state_unavail m2 * (1 - steady_state_unavail m1))``,
RW_TAC std_ss[]
++ (`!t. prob p
       (XOR_FT_gate p (atomic (union_unavail_events p X1 &t))
       	     	      (atomic (union_unavail_events p X2 &t))) =  prob p(union_unavail_events p X1 (&t))  * (1 - prob p (union_unavail_events p X2 (&t))) + prob p  (union_unavail_events p X2 (&t)) * (1- prob p (union_unavail_events p X1 (&t)))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC XOR_FT_gate_thm
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(\t.
       prob p (union_unavail_events p X1 (&t)) *
       (1 − prob p (union_unavail_events p X2 (&t))) +
       prob p (union_unavail_events p X2 (&t)) *
       (1 − prob p (union_unavail_events p X1 (&t))))`--)  
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`
(steady_state_unavail m1 * (1 − steady_state_unavail m2) +
 steady_state_unavail m2 * (1 − steady_state_unavail m1))`--)
   ++ (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t))) +
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) =(\t.
   (\t. prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) t +
   (\t. prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_ADD
   ++ RW_TAC std_ss[]
   >>( (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X1 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X2 (&t)))) t)` by RW_TAC real_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC SEQ_MUL
     ++ RW_TAC std_ss[]
     >> ( MATCH_MP_TAC inst_XOR_tends_steady
     	++ METIS_TAC[])
     ++ (`(\t. 1 − prob p (union_unavail_events p X2 (&t))) =(\t. (\t. 1) t − (\t. prob p (union_unavail_events p X2 (&t))) t) `  by RW_TAC real_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC SEQ_SUB
     ++ RW_TAC std_ss[SEQ_CONST]
     ++ MATCH_MP_TAC inst_XOR_tends_steady
     ++ METIS_TAC[])
   ++ (`(\t.
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X2 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X1 (&t)))) t)` by RW_TAC real_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_MUL
  ++ RW_TAC std_ss[]
  >> (MATCH_MP_TAC inst_XOR_tends_steady
     ++ METIS_TAC[])
  ++ (`(\t. 1 − prob p (union_unavail_events p X1 (&t))) =(\t. (\t. 1) t − (\t. prob p (union_unavail_events p X1 (&t))) t) `  by RW_TAC real_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_SUB
  ++ RW_TAC std_ss[SEQ_CONST]
  ++ MATCH_MP_TAC inst_XOR_tends_steady
  ++ METIS_TAC[])
++ (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t))) +
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) =(\t.
   (\t. prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) t +
   (\t. prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) t) ` by RW_TAC real_ss[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_ADD
++ RW_TAC std_ss[]   
>> ( (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X1 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X2 (&t)))) t)` by RW_TAC real_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC SEQ_MUL
     ++ RW_TAC std_ss[]
     >> ( MATCH_MP_TAC inst_XOR_tends_steady
     	++ METIS_TAC[])
     ++ (`(\t. 1 − prob p (union_unavail_events p X2 (&t))) =(\t. (\t. 1) t − (\t. prob p (union_unavail_events p X2 (&t))) t) `  by RW_TAC real_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC SEQ_SUB
     ++ RW_TAC std_ss[SEQ_CONST]
     ++ MATCH_MP_TAC inst_XOR_tends_steady
     ++ METIS_TAC[])
++ (`(\t.
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X2 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X1 (&t)))) t)` by RW_TAC real_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_MUL
  ++ RW_TAC std_ss[]
  >> (MATCH_MP_TAC inst_XOR_tends_steady
     ++ METIS_TAC[])
  ++ (`(\t. 1 − prob p (union_unavail_events p X1 (&t))) =(\t. (\t. 1) t − (\t. prob p (union_unavail_events p X1 (&t))) t) `  by RW_TAC real_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_SUB
  ++ RW_TAC std_ss[SEQ_CONST]
  ++ MATCH_MP_TAC inst_XOR_tends_steady
  ++ METIS_TAC[]);


(*-----------Case Study Theorems-----------*)
val solar_array_RBD_avail = store_thm("solar_array_RBD_avail",
  ``!p R1 R2 R3 R4 R5 M1 M2 M3 M4 M5.  
       prob_space p /\ 
       (!z. MEM z (FLAT [[M1;M1];[M2];[M3;M3];[M4];[M4];[M5;M5]]) ==> 
       	    0 < FST z /\ 0 < SND z) /\
       (!t'. 
        (!z. MEM z 
	     (FLAT (list_union_avail_event_list 
	     	   ([[R1;R1];[R2];[R3;R3];[R4];[R4];[R5;R5]]) (&t'))) ==> z IN events p) /\
       mutual_indep p 
	 (FLAT (list_union_avail_event_list 
	       ([[R1;R1];[R2];[R3;R3];[R4];[R4];[R5;R5]]) (&t')))) /\ 
       (two_dim_inst_avail_exp p 
       		([[R1;R1];[R2];[R3;R3];[R4];[R4];[R5;R5]]) 
		([[M1;M1];[M2];[M3;M3];[M4];[M4];[M5;M5]])) ==> 
	  
	  (lim (\t. prob p 
	      (rbd_struct p
                     ((series of (λa. parallel (rbd_list a)))
                        (list_union_avail_event_list 
				([[R1;R1];[R2];[R3;R3];[R4];[R4];[R5;R5]]) (&t))))) =
       	  list_prod 
	    (one_minus_list (MAP 
	       (\a. compl_steady_state_avail a) 
	       	    ([[M1;M1];[M2];[M3;M3];[M4];[M4];[M5;M5]]))))``,
RW_TAC std_ss[]
++ MATCH_MP_TAC steady_state_series_parallel_avail
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[]
   ++ Cases_on `n`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[]
   ++ Cases_on `n'`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[]
   ++ Cases_on `n`
   >> (RW_TAC list_ss[])
  ++ RW_TAC list_ss[]
   ++ Cases_on `n'`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[]
   ++ Cases_on `n`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[]
   ++ Cases_on `n'`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[])
>> (RW_TAC list_ss[]
   >> (FULL_SIMP_TAC list_ss[list_union_avail_event_list_def]
      >> (RW_TAC list_ss[union_avail_event_list1_def])
      >> (RW_TAC list_ss[union_avail_event_list1_def])
      >> (RW_TAC list_ss[union_avail_event_list1_def])
      >> (RW_TAC list_ss[union_avail_event_list1_def])
      >> (RW_TAC list_ss[union_avail_event_list1_def])
   ++ (RW_TAC list_ss[union_avail_event_list1_def]))
   ++ FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC)
   ++ RW_TAC std_ss[])
   ++ METIS_TAC[]);

(*--------------------------------------------------*)

val solar_array_FT_def = Define 
`solar_array_FT p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 t =
 FTree p (OR [OR (gate_list (union_unavail_event_list p [x1;x2;x3;x4] t));
       	      AND (gate_list (union_unavail_event_list p [x5;x6] t));
	      OR (gate_list (union_unavail_event_list p [x7;x8;x9;x10;x11;x12;x13;x14] t))]) `;

(*-------------------------------------------------*)

val solar_array_FT_to_RBD = store_thm("solar_array_FT_to_RBD",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 t.
       prob_space p ==>
         (solar_array_FT p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 t =
	 rbd_struct p (series (rbd_list (union_unavail_event_list p [x5;x6] t))) UNION
	 rbd_struct p (parallel (rbd_list (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] t))))``,
RW_TAC list_ss[solar_array_FT_def,FTree_def,union_unavail_event_list_def,rbd_struct_def,gate_list_def,rbd_list_def]
++ SRW_TAC[][UNION_EMPTY,UNION_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);

(*-------------------------------------------------*)
val solar_array_unavail_lemma = store_thm("solar_array_unavail_lemma",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 t. 
  prob_space p /\
  (!z.  MEM z [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ==>
  	0 < FST z /\ 0 < SND z) /\
   (∀t'.
        (∀z.
           MEM z
             ((union_unavail_event_list p
                   [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
                   (&t'))) ⇒
           z ∈ events p) ∧
        mutual_indep p
          ((union_unavail_event_list p
                [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
                (&t')))) ∧
     inst_unavail_exp_list p
       [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
       [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ⇒
       	    (λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t))))) −
   prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) -->
(list_prod (steady_state_unavail_list [c5; c6]) +
 (1 −
  list_prod
    (one_minus_list
       (steady_state_unavail_list
          [c1; c2; c3; c4; c7; c8; c9; c10; c11; c12; c13; c14]))) −
 list_prod (steady_state_unavail_list [c5; c6]) *
 (1 −
  list_prod
    (one_minus_list
       (steady_state_unavail_list
          [c1; c2; c3; c4; c7; c8; c9; c10; c11; c12; c13; c14]))))``,
RW_TAC std_ss[]
++ (` (λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t))))) -
   prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) =
 (\t.
   (\t.
     prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t))))) ) t -
   (\t.
     prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC real_ss[]
   >> ((`(λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t)))))) =
     (λt.
   (\t. prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t)))))) t +
  (\t.  prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t)))))) t)` by RW_TAC list_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_ADD
      ++ RW_TAC list_ss[]
      >> (DEP_REWRITE_TAC[GSYM AND_to_series]
      	 ++ (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p [x5; x6] (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p [x5; x6] (&t)))` by RW_TAC std_ss[])
	>> (MATCH_MP_TAC AND_gate_thm
	   ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,rbd_list_def,rbd_struct_def]
	   ++ STRIP_TAC
   	   >> (METIS_TAC[])
	   ++ MATCH_MP_TAC mutual_indep_front_append
	   ++ EXISTS_TAC(--`[union_unavail_events p x1 (&t);
           union_unavail_events p x2 (&t);
           union_unavail_events p x3 (&t);
           union_unavail_events p x4 (&t)]`--)
	   ++ MATCH_MP_TAC mutual_indep_flat_append
	   ++ EXISTS_TAC(--`[[union_unavail_events p x7 (&t);
           union_unavail_events p x8 (&t);
           union_unavail_events p x9 (&t);
           union_unavail_events p x10 (&t);
           union_unavail_events p x11 (&t);
           union_unavail_events p x12 (&t);
           union_unavail_events p x13 (&t);
           union_unavail_events p x14 (&t)]]`--)
	   ++ RW_TAC list_ss[])
	++ POP_ORW
	++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   	++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
	++ METIS_TAC[])
   ++ DEP_REWRITE_TAC[GSYM OR_to_parallel]
   ++ (`!t. 
      	 prob p
     	  (FTree p
            (OR
              (gate_list
                (union_unavail_event_list p
                  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                    (&t))))) =
	 1 - list_prod (one_minus_list (list_prob p 
	  (union_unavail_event_list p  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))` by RW_TAC std_ss[])
   >> (MATCH_MP_TAC OR_gate_thm
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
      ++ STRIP_TAC 
      >> (METIS_TAC[])
      ++ (`[union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
      	    union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
      	    union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
      	    union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
      	    union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
      	    union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	(FLAT ([union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   	        union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ::
   	       [[union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   	         union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   		 union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   		 union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]]))` by RW_TAC list_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC mutual_indep_flat_cons3
     ++ EXISTS_TAC (--`[union_unavail_events p x5 (&t);union_unavail_events p x6 (&t)]`--)
     ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
  ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
   ++ METIS_TAC[])
++ (`(!t. 
      prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t))))) =
   prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) *
   prob p (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t))))))` by RW_TAC std_ss[])
   >> (DEP_REWRITE_TAC [series_rbd_indep_series_parallel_rbd]
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,list_union_unavail_event_list_def]
      ++ STRIP_TAC
      >> (METIS_TAC[NULL])
      ++ STRIP_TAC
      >> (METIS_TAC[NULL])
      ++ (`[union_unavail_events p x5 (&t); union_unavail_events p x6 (&t);
   union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
   union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	 [union_unavail_events p x5 (&t); union_unavail_events p x6 (&t)] ++
   [union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ++
   [union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]` by RW_TAC list_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC mutual_indep_append1
      ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`!t. 
     	(λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) *
   prob p
     (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) =
      (λt.
   (\t. prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t)))))) t *
   (\t. prob p
     (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) t)` by RW_TAC list_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_MUL
  ++ RW_TAC std_ss[]
  >> (DEP_REWRITE_TAC[GSYM AND_to_series]
      	 ++ (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p [x5; x6] (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p [x5; x6] (&t)))` by RW_TAC std_ss[])
	>> (MATCH_MP_TAC AND_gate_thm
	   ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,rbd_list_def,rbd_struct_def]
	   ++ STRIP_TAC
   	   >> (METIS_TAC[])
	   ++ MATCH_MP_TAC mutual_indep_front_append
	   ++ EXISTS_TAC(--`[union_unavail_events p x1 (&t);
           union_unavail_events p x2 (&t);
           union_unavail_events p x3 (&t);
           union_unavail_events p x4 (&t)]`--)
	   ++ MATCH_MP_TAC mutual_indep_flat_append
	   ++ EXISTS_TAC(--`[[union_unavail_events p x7 (&t);
           union_unavail_events p x8 (&t);
           union_unavail_events p x9 (&t);
           union_unavail_events p x10 (&t);
           union_unavail_events p x11 (&t);
           union_unavail_events p x12 (&t);
           union_unavail_events p x13 (&t);
           union_unavail_events p x14 (&t)]]`--)
	   ++ RW_TAC list_ss[])
	++ POP_ORW
	++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   	++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
	++ METIS_TAC[])
  ++ (`!t. 
     	(rbd_struct p
	  (series (MAP (λa. parallel (rbd_list a))
	    (list_union_unavail_event_list p
                   [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                   (&t))))) = 
	(rbd_struct p 
             (parallel (rbd_list
	     	   (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t)))))`
		   by RW_TAC list_ss[rbd_list_def,list_union_unavail_event_list_def,union_unavail_event_list_def,rbd_struct_def,UNION_EMPTY])
  >> (ONCE_REWRITE_TAC[INTER_COMM]
     ++ DEP_REWRITE_TAC[INTER_PSPACE]
     ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
     ++ DEP_REWRITE_TAC[EVENTS_UNION]
     ++ METIS_TAC[])
  ++ POP_ORW
  ++ DEP_REWRITE_TAC[GSYM OR_to_parallel]
   ++ (`!t. 
      	 prob p
     	  (FTree p
            (OR
              (gate_list
                (union_unavail_event_list p
                  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                    (&t))))) =
	 1 - list_prod (one_minus_list (list_prob p 
	  (union_unavail_event_list p  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))` by RW_TAC std_ss[])
   >> (MATCH_MP_TAC OR_gate_thm
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
      ++ STRIP_TAC 
      >> (METIS_TAC[])
      ++ (`[union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
      	    union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
      	    union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
      	    union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
      	    union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
      	    union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	(FLAT ([union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   	        union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ::
   	       [[union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   	         union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   		 union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   		 union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]]))` by RW_TAC list_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC mutual_indep_flat_cons3
     ++ EXISTS_TAC (--`[union_unavail_events p x5 (&t);union_unavail_events p x6 (&t)]`--)
     ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
   ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
   ++ METIS_TAC[]);
(*-------------------------------------------------*)
val solar_array_unavail = store_thm("solar_array_unavail",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 t. 
  prob_space p /\
  (!z.  MEM z [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ==>
  	0 < FST z /\ 0 < SND z) /\
   (∀t'.
        (∀z.
           MEM z
             ((union_unavail_event_list p
                   [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
                   (&t'))) ⇒
           z ∈ events p) ∧
        mutual_indep p
          ((union_unavail_event_list p
                [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
                (&t')))) ∧
     inst_unavail_exp_list p
       [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14]
       [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ⇒

       (lim
        (λt.
           prob p
            (rbd_struct p (series (rbd_list (union_unavail_event_list p [x5;x6] (&t)))) UNION
	     rbd_struct p
	      (parallel (rbd_list
	      	 (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t)))))) =
       list_prod (steady_state_unavail_list [c5;c6]) +
       (1 − list_prod (one_minus_list
       	   (steady_state_unavail_list [c1;c2;c3;c4;c7;c8;c9;c10;c11;c12;c13;c14]))) -
       (list_prod (steady_state_unavail_list [c5;c6]) * 
       (1 − list_prod (one_minus_list
          (steady_state_unavail_list [c1;c2;c3;c4;c7;c8;c9;c10;c11;c12;c13;c14])))))``,
RW_TAC std_ss[]
++ (`!t. 
       prob p
         (rbd_struct p 
	    (series (rbd_list (union_unavail_event_list p [x5;x6] (&t)))) UNION
	  rbd_struct p 
	    (parallel (rbd_list 
	      (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t))))) =  
       prob p
         (rbd_struct p (series (rbd_list (union_unavail_event_list p [x5;x6] (&t))))) + 
       prob p 
         (rbd_struct p 
	    (parallel (rbd_list 
               (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t))))) - 
       prob p
         (rbd_struct p (series (rbd_list (union_unavail_event_list p [x5;x6] (&t)))) INTER
	  rbd_struct p 
             (parallel (rbd_list
	     	   (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t)))))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC Prob_Incl_excl
   ++ RW_TAC list_ss[]
   >> (RW_TAC std_ss[series_rbd_eq_big_inter]
      ++ MATCH_MP_TAC in_events_big_inter
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
      ++ METIS_TAC[])
   ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,rbd_list_def,rbd_struct_def,UNION_EMPTY]
   ++ DEP_REWRITE_TAC[EVENTS_UNION]
   ++ METIS_TAC[])
++ POP_ORW
++ (`(!t. (rbd_struct p
          (series
             (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
        rbd_struct p
          (parallel
             (rbd_list
                (union_unavail_event_list p
                   [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                   (&t))))) =
    (rbd_struct p
          (series
             (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
        rbd_struct p (series (MAP (λa. parallel (rbd_list a)) (list_union_unavail_event_list p
                   [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                   (&t))))))` by RW_TAC std_ss[])
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,list_union_unavail_event_list_def,union_unavail_event_list_def,UNION_EMPTY]
   ++ SRW_TAC [][EXTENSION,GSPECIFICATION,UNION_DEF]
   ++ METIS_TAC[])
++ POP_ORW
++ MATCH_MP_TAC SEQ_UNIQ
++ EXISTS_TAC(--`(λt.
       prob p
         (rbd_struct p
            (series
               (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
       prob p
         (rbd_struct p
            (parallel
               (rbd_list
                  (union_unavail_event_list p
                     [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13;
                      x14] (&t))))) −
       prob p
         (rbd_struct p
            (series
               (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
          rbd_struct p
            (series
               (MAP (λa. parallel (rbd_list a))
                  (list_union_unavail_event_list p
                     [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13;
                       x14]] (&t))))))`--)
++ RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>> (EXISTS_TAC(--`
list_prod (steady_state_unavail_list [c5;c6]) +
       (1 − list_prod (one_minus_list
       	   (steady_state_unavail_list [c1;c2;c3;c4;c7;c8;c9;c10;c11;c12;c13;c14]))) -
       (list_prod (steady_state_unavail_list [c5;c6]) * 
       (1 − list_prod (one_minus_list
          (steady_state_unavail_list [c1;c2;c3;c4;c7;c8;c9;c10;c11;c12;c13;c14]))))`--)
   ++ (` (λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t))))) -
   prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) =
 (\t.
   (\t.
     prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t))))) ) t -
   (\t.
     prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC real_ss[]
   >> ((`(λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) +
   prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t)))))) =
     (λt.
   (\t. prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t)))))) t +
  (\t.  prob p
     (rbd_struct p
        (parallel
           (rbd_list
              (union_unavail_event_list p
                 [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                 (&t)))))) t)` by RW_TAC list_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC SEQ_ADD
      ++ RW_TAC list_ss[]
      >> (DEP_REWRITE_TAC[GSYM AND_to_series]
      	 ++ (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p [x5; x6] (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p [x5; x6] (&t)))` by RW_TAC std_ss[])
	>> (MATCH_MP_TAC AND_gate_thm
	   ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,rbd_list_def,rbd_struct_def]
	   ++ STRIP_TAC
   	   >> (METIS_TAC[])
	   ++ MATCH_MP_TAC mutual_indep_front_append
	   ++ EXISTS_TAC(--`[union_unavail_events p x1 (&t);
           union_unavail_events p x2 (&t);
           union_unavail_events p x3 (&t);
           union_unavail_events p x4 (&t)]`--)
	   ++ MATCH_MP_TAC mutual_indep_flat_append
	   ++ EXISTS_TAC(--`[[union_unavail_events p x7 (&t);
           union_unavail_events p x8 (&t);
           union_unavail_events p x9 (&t);
           union_unavail_events p x10 (&t);
           union_unavail_events p x11 (&t);
           union_unavail_events p x12 (&t);
           union_unavail_events p x13 (&t);
           union_unavail_events p x14 (&t)]]`--)
	   ++ RW_TAC list_ss[])
	++ POP_ORW
	++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   	++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
	++ METIS_TAC[])
   ++ DEP_REWRITE_TAC[GSYM OR_to_parallel]
   ++ (`!t. 
      	 prob p
     	  (FTree p
            (OR
              (gate_list
                (union_unavail_event_list p
                  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                    (&t))))) =
	 1 - list_prod (one_minus_list (list_prob p 
	  (union_unavail_event_list p  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))` by RW_TAC std_ss[])
   >> (MATCH_MP_TAC OR_gate_thm
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
      ++ STRIP_TAC 
      >> (METIS_TAC[])
      ++ (`[union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
      	    union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
      	    union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
      	    union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
      	    union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
      	    union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	(FLAT ([union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   	        union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ::
   	       [[union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   	         union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   		 union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   		 union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]]))` by RW_TAC list_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC mutual_indep_flat_cons3
     ++ EXISTS_TAC (--`[union_unavail_events p x5 (&t);union_unavail_events p x6 (&t)]`--)
     ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
  ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
   ++ METIS_TAC[])
++ (`(!t. 
      prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t)))) ∩
      rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t))))) =
   prob p
     (rbd_struct p
        (series (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) *
   prob p (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t))))))` by RW_TAC std_ss[])
   >> (DEP_REWRITE_TAC [series_rbd_indep_series_parallel_rbd]
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,list_union_unavail_event_list_def]
      ++ STRIP_TAC
      >> (METIS_TAC[NULL])
      ++ STRIP_TAC
      >> (METIS_TAC[NULL])
      ++ (`[union_unavail_events p x5 (&t); union_unavail_events p x6 (&t);
   union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
   union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	 [union_unavail_events p x5 (&t); union_unavail_events p x6 (&t)] ++
   [union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ++
   [union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]` by RW_TAC list_ss[])
      ++ POP_ORW
      ++ MATCH_MP_TAC mutual_indep_append1
      ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`!t. 
     	(λt.
   prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t))))) *
   prob p
     (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) =
      (λt.
   (\t. prob p
     (rbd_struct p
        (series
           (rbd_list (union_unavail_event_list p [x5; x6] (&t)))))) t *
   (\t. prob p
     (rbd_struct p
        (series
           (MAP (λa. parallel (rbd_list a))
              (list_union_unavail_event_list p
                 [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                 (&t)))))) t)` by RW_TAC list_ss[])
  ++ POP_ORW
  ++ MATCH_MP_TAC SEQ_MUL
  ++ RW_TAC std_ss[]
  >> (DEP_REWRITE_TAC[GSYM AND_to_series]
      	 ++ (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p [x5; x6] (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p [x5; x6] (&t)))` by RW_TAC std_ss[])
	>> (MATCH_MP_TAC AND_gate_thm
	   ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def,rbd_list_def,rbd_struct_def]
	   ++ STRIP_TAC
   	   >> (METIS_TAC[])
	   ++ MATCH_MP_TAC mutual_indep_front_append
	   ++ EXISTS_TAC(--`[union_unavail_events p x1 (&t);
           union_unavail_events p x2 (&t);
           union_unavail_events p x3 (&t);
           union_unavail_events p x4 (&t)]`--)
	   ++ MATCH_MP_TAC mutual_indep_flat_append
	   ++ EXISTS_TAC(--`[[union_unavail_events p x7 (&t);
           union_unavail_events p x8 (&t);
           union_unavail_events p x9 (&t);
           union_unavail_events p x10 (&t);
           union_unavail_events p x11 (&t);
           union_unavail_events p x12 (&t);
           union_unavail_events p x13 (&t);
           union_unavail_events p x14 (&t)]]`--)
	   ++ RW_TAC list_ss[])
	++ POP_ORW
	++ MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   	++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
	++ METIS_TAC[])
  ++ (`!t. 
     	(rbd_struct p
	  (series (MAP (λa. parallel (rbd_list a))
	    (list_union_unavail_event_list p
                   [[x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]]
                   (&t))))) = 
	(rbd_struct p 
             (parallel (rbd_list
	     	   (union_unavail_event_list p [x1;x2;x3;x4;x7;x8;x9;x10;x11;x12;x13;x14] (&t)))))`
		   by RW_TAC list_ss[rbd_list_def,list_union_unavail_event_list_def,union_unavail_event_list_def,rbd_struct_def,UNION_EMPTY])
  >> (ONCE_REWRITE_TAC[INTER_COMM]
     ++ DEP_REWRITE_TAC[INTER_PSPACE]
     ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
     ++ DEP_REWRITE_TAC[EVENTS_UNION]
     ++ METIS_TAC[])
  ++ POP_ORW
  ++ DEP_REWRITE_TAC[GSYM OR_to_parallel]
   ++ (`!t. 
      	 prob p
     	  (FTree p
            (OR
              (gate_list
                (union_unavail_event_list p
                  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14]
                    (&t))))) =
	 1 - list_prod (one_minus_list (list_prob p 
	  (union_unavail_event_list p  [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))` by RW_TAC std_ss[])
   >> (MATCH_MP_TAC OR_gate_thm
      ++ FULL_SIMP_TAC list_ss[union_unavail_event_list_def]
      ++ STRIP_TAC 
      >> (METIS_TAC[])
      ++ (`[union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
      	    union_unavail_events p x3 (&t); union_unavail_events p x4 (&t);
      	    union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
      	    union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
      	    union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
      	    union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)] =
   	(FLAT ([union_unavail_events p x1 (&t); union_unavail_events p x2 (&t);
   	        union_unavail_events p x3 (&t); union_unavail_events p x4 (&t)] ::
   	       [[union_unavail_events p x7 (&t); union_unavail_events p x8 (&t);
   	         union_unavail_events p x9 (&t); union_unavail_events p x10 (&t);
   		 union_unavail_events p x11 (&t); union_unavail_events p x12 (&t);
   		 union_unavail_events p x13 (&t); union_unavail_events p x14 (&t)]]))` by RW_TAC list_ss[])
     ++ POP_ORW
     ++ MATCH_MP_TAC mutual_indep_flat_cons3
     ++ EXISTS_TAC (--`[union_unavail_events p x5 (&t);union_unavail_events p x6 (&t)]`--)
     ++ RW_TAC list_ss[])
  ++ POP_ORW
  ++ (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p [x1; x2; x3; x4; x7; x8; x9; x10; x11; x12; x13; x14] (&t))))) t) ` by RW_TAC real_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC SEQ_SUB
   ++ RW_TAC std_ss[SEQ_CONST]
  ++ MATCH_MP_TAC lim_inst_OR_tend_steady
   ++ FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def]
   ++ METIS_TAC[])
++ MATCH_MP_TAC solar_array_unavail_lemma
++ RW_TAC std_ss[]
++ METIS_TAC[union_unavail_event_list_def]);

val _ = export_theory();