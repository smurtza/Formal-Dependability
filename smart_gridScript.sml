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
val _ = new_theory "smart_grid";
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

(*----------------casc_series_RBD_def------------------------*)
val casc_series_RBD_def = Define 
`casc_series_RBD p PIED ESW_list CIED t = 
 rbd_struct p (series (rbd_list (rel_event_list p 
 	         	([PIED]++ESW_list++[CIED]) t))) `;

(*----------------rel_casc_seriesRBD------------------------*)
val rel_casc_seriesRBD = store_thm("rel_casc_seriesRBD",
  ``!p t PIED ESW_list CIED C_PIED C_ESW_list C_CIED. 
       	      (0 <= t) /\ 
       	      prob_space p /\
	      ~NULL ESW_list /\
	      exp_dist_list p ([PIED]++ESW_list++[CIED]) 
	      		      ([C_PIED]++C_ESW_list++[C_CIED])  /\
	      (LENGTH C_ESW_list = LENGTH ESW_list) /\
	      mutual_indep p 
	      	(rel_event_list p ([PIED]++ESW_list++[CIED]) t) /\
	      (!x. 
	      	   MEM x (rel_event_list p ([PIED]++ESW_list++[CIED]) t) ==> 
	      	   x IN events p) ==>
	       (prob p (casc_series_RBD p PIED ESW_list CIED t) =
	        list_prod 
		 (exp_func_list ([C_PIED]++C_ESW_list++[C_CIED]) t))``,
RW_TAC std_ss[casc_series_RBD_def]
++ DEP_REWRITE_TAC[series_struct_thm]
++ RW_TAC std_ss[]
>> (RW_TAC list_ss[rel_event_list_def])
++ MATCH_MP_TAC rel_prod_series_rbd_exp_dist
++ RW_TAC list_ss[]);

(*----------------redund_star_ring_RBD------------------------*)
val redund_star_ring_RBD_def = Define 
`redund_star_ring_RBD p PIED list_ESW_list CIED t =
 rbd_struct p 
   ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
   	       ([[PIED]]++list_ESW_list++[[CIED]]))`;

(*---------------------------------------*)
val len_EL_lem1 = store_thm("len_EL_lem1",
  ``!h1 h2 c1 c2 L C n. 
     (LENGTH L = LENGTH C) /\
     (n < LENGTH L + 2) /\
     (!n. 
	(n < LENGTH L) /\ (n < LENGTH C) ==>
	(LENGTH (EL n L) = LENGTH (EL n C))) ==>
	  (LENGTH (EL n ([h1]::(L ++ [[h2]]))) =
     LENGTH (EL n ([c1]::(C ++ [[c2]]))))      ``,
NTAC 4 (GEN_TAC)
++ Induct
>> (RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[LENGTH_NIL_SYM]
   ++ Cases_on `n`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[]
   ++ POP_ASSUM MP_TAC
   ++ ONCE_ASM_REWRITE_TAC[TWO]
   ++ FULL_SIMP_TAC arith_ss[]
   ++ Cases_on `n'`
   >> (RW_TAC list_ss[])
   ++ FULL_SIMP_TAC arith_ss[])
++ GEN_TAC
++ Induct
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[]
++ Cases_on `n`
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[]
++ Cases_on `n'`
>> (RW_TAC list_ss[]
   ++ (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC))
   ++ RW_TAC list_ss[])
++ RW_TAC list_ss[]
++ (FIRST_X_ASSUM (Q.SPECL_THEN [`C'`,`SUC n`] MP_TAC))
++ RW_TAC list_ss[]
++ (`(∀n'. n' < LENGTH C' ⇒ (LENGTH (EL n' L) = LENGTH (EL n' C')))` by RW_TAC list_ss[])
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n'`] MP_TAC)
   ++ RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*----------------rel_redund_star_ringRBD------------------------*)
val rel_redund_star_ringRBD = store_thm("rel_redund_star_ringRBD",
  ``!p (t:real)  PIED list_ESW_list CIED C_PIED C_list_ESW_list C_CIED. 
     	(!z. MEM z list_ESW_list  ==>  ~NULL z) /\
	 (0 <=  (t:real)) /\ prob_space p /\
   	 (!x'.
	    MEM x' (FLAT ((two_dim_rel_event_list p 
	    	([[PIED]]++list_ESW_list++[[CIED]])  t))) ==>
	    (x' IN events p)) /\
	 (mutual_indep p (FLAT (two_dim_rel_event_list p ([[PIED]]++list_ESW_list++[[CIED]]) t))) /\
	 (LENGTH C_list_ESW_list = LENGTH list_ESW_list) /\
	 (!n. 
	      (n < LENGTH list_ESW_list) /\ (n < LENGTH C_list_ESW_list) ==>
	      (LENGTH (EL n list_ESW_list) = LENGTH (EL n C_list_ESW_list))) /\
  	 two_dim_exp_dist_list p ([[PIED]]++list_ESW_list++[[CIED]])
	 		       	 ([[C_PIED]]++C_list_ESW_list++[[C_CIED]]) ==> 
  	   (prob p (redund_star_ring_RBD p PIED list_ESW_list CIED t) =
           (list_prod of
       	   	 (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) 
		      ([[C_PIED]]++C_list_ESW_list++[[C_CIED]]))``,
RW_TAC std_ss[redund_star_ring_RBD_def]
++ DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
++ RW_TAC std_ss[]
++ MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC list_ss[]
++ MATCH_MP_TAC len_EL_lem1 
++ RW_TAC std_ss[]);

(*--------G1_FT------------------------------*)

val G1_FT_def = Define 
`G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
AND (gate_list (fail_event_list p [SW1;L1_220;L2_220;L3_220;L4_220] t))`;


(*--------G2_FT------------------------------*)

val G2_FT_def = Define 
`G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
AND (gate_list (fail_event_list p [SW1;L1_220;L2_220;L3_220;L4_220] t))`;


(*--------G3_FT------------------------------*)

val G3_FT_def = Define 
`G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
AND (gate_list (fail_event_list p [SW2;T1_220;T2_220;BUS_220;SS_220] t))`;


(*--------G4_FT------------------------------*)

val G4_FT_def = Define 
`G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
AND (gate_list (fail_event_list p [SW2;T1_220;T2_220;BUS_220;SS_220] t))`;

(*-----------SABP_FT----------------------*)
val SABP_FT_def = Define 
`SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 =
FTree p (AND [OR [G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220;
      	     	 G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220];
	      OR [G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220;
	      	 G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220]]) `;

(*---------------------------------*)
val SABP_FT_alt_form = store_thm("SABP_FT_alt_form",
  ``!A B C D. (A UNION B) INTER (C UNION D) = (A INTER C) UNION (A INTER D) UNION (B INTER C) UNION (B INTER D) ``,
RW_TAC std_ss[]
++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);

(*---------------------------------*)
val SABP_FT_alt_form1 = store_thm("SABP_FT_alt_form1",
  ``!p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220. 
prob_space p ==>
(SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 =  
rbd_struct p ((parallel of (\a. series (rbd_list a)))
       	      (list_fail_event_list p 
	      	[[SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
		 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
		 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
		 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220]] t))) ``,
RW_TAC std_ss[of_DEF,o_THM]
++ RW_TAC list_ss[SABP_FT_def,FTree_def]
++ PSET_TAC[]
++ RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,rbd_list_def,rbd_struct_def,G1_FT_def,G2_FT_def,G3_FT_def,G4_FT_def,FTree_def,gate_list_def]
++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);

(*---------------------------------*)
val fail_prob_SABP_FT_lem1 = store_thm("fail_prob_SABP_FT_lem1",
  ``!p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220 C_T2_220 C_BUS_220 C_SS_220. 
0 ≤ t ∧ prob_space p ∧
     list_exp p
       [C_SW1; C_SW2; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_T1_220;
         C_T2_220; C_BUS_220; C_SS_220]
        [SW1; SW2; L1_220; L2_220; L3_220; L4_220; T1_220; T2_220;
         BUS_220; SS_220] ⇒
     (list_prod
        (one_minus_list
           (list_prod_rel p
              (list_fail_event_list p
                 [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220]] t))) =
      list_prod
        (one_minus_exp_prod t
           [[C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220]]))``,
RW_TAC list_ss[list_exp_def,exp_dist_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);
(*---------------------------------*)
val fail_prob_SABP_FT = store_thm("fail_prob_SABP_FT",
  `` !p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220 C_T2_220 C_BUS_220 C_SS_220. 
(0 <= t) /\  prob_space p  /\
 (!x'.
    MEM x'
      (fail_event_list p 
      	[SW1;SW2;L1_220;L2_220;L3_220;L4_220;T1_220;T2_220;BUS_220;SS_220] t) ==>
    x' IN events p) /\
 mutual_indep p (FLAT
     (list_fail_event_list p
        [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220]] t))
       /\ (list_exp p ([C_SW1;C_SW2;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_T1_220;C_T2_220;C_BUS_220;C_SS_220]) 
([SW1;SW2;L1_220;L2_220;L3_220;L4_220;T1_220;T2_220;BUS_220;SS_220])
       ) ==> 
(prob p (SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220) =
1 - list_prod
  (one_minus_exp_prod t
	([[C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
		 [C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
		[C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
		[C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;C_T1_220;C_T2_220;C_BUS_220;C_SS_220]])))``,
RW_TAC std_ss[]
++ RW_TAC std_ss[SABP_FT_alt_form1]
++ DEP_REWRITE_TAC[rel_parallel_series_rbd]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[list_fail_event_list_def,fail_event_list_def])
>> (FULL_SIMP_TAC list_ss[list_fail_event_list_def,fail_event_list_def])
++ DEP_REWRITE_TAC[fail_prob_SABP_FT_lem1]
++ FULL_SIMP_TAC list_ss[]);

val _ = export_theory();