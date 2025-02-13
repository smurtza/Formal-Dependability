(*------------------------------------------------------ *)
(* Formal Failure Analysis ASN Gateway			 *)
(*  						   	   						*)
(* 		    by Waqar Ahmed 		   	   					*)
(* 		    Phd Candidate		   	   					*)
(* School of Electrical Engineering and Computer Sciences  *)
(* National University of Sciences and Technology (NUST)   *)
(* 	    	        Islamabad, Pakistan 	  	   		   *)
(*---------------------------------------------------------*)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
    	  "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory",
	  "transcTheory", "rich_listTheory", "pairTheory",
	  "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
	  "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory","dep_rewrite","RBDTheory","FT_deepTheory","VDCTheory"];
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory 
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite RBDTheory FT_deepTheory VDCTheory;

fun K_TAC _ = ALL_TAC;  
open HolKernel boolLib bossLib Parse;
val _ = new_theory "ASN_gateway";
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

(* ------------------------------------------------------------------------- *)
(* Definition                                  *)
(* ------------------------------------------------------------------------- *)
val fail_event_list_def = Define
 `fail_event_list p L t =  
  MAP (\a. fail_event p a t) L`;
 
val list_fail_event_list_def = Define
 `list_fail_event_list p L t =  
  MAP (\a. fail_event_list p a t) L`;
(* ------------------------------------------------------------------------- *)
(*   			exp_func                                 *)
(* ------------------------------------------------------------------------- *)
val exp_func_def = Define
   `exp_func  (x:real) (c:real) = exp(-(c * x))`;

(* ------------------------------------------------------------------------- *)
(*  One Minus exponential                                *)
(* ------------------------------------------------------------------------- *)
val one_minus_exp_def = Define `
    one_minus_exp t C = 
    MAP (\c. 1 - exp(-(t * (c:real)))) C`;

(* ------------------------------------------------------------------------- *)
(*  One Minus exponential product                               *)
(* ------------------------------------------------------------------------- *)
val one_minus_exp_prod_def = Define 
`(one_minus_exp_prod t C = 
  MAP (\a. 1- list_prod (one_minus_list (exp_func_list a t))) C ) `;
(* ------------------------------------------------------------------------- *)
(*   			list_sum                                  *)
(* ------------------------------------------------------------------------- *)

val list_sum_def =  Define
    		     	`(list_sum [] = 0) /\ 
		         (!h t. list_sum (h::t) = 
			 ((h:real) + list_sum(t)))`;

(* ------------------------------------------------------------------------- *)
(* Definition : Exponential Distribution Function                                *)
(* ------------------------------------------------------------------------- *)
val exp_distribution_def = Define
   `exp_dist p X l = 
   !x:real. CDF p X (x) = (if (0 <=  x) then 1 -
   	    	    	      exp(-l * x) else 0)`;
(* ------------------------------------------------------------------------- *)
(* Definition : List of Exponential Distribution Functions                               *)
(* ------------------------------------------------------------------------- *)
val list_exp_def =  Define
    		     	`(list_exp p [] L = T ) /\
		(list_exp p (h::t) L = ( exp_dist p (HD(L)) (h)) /\ (list_exp p (t) (TL L)))`; 

(*=================probability of B1=====================================*)
val B1_FT_def = Define
 `B1_FT p t D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 = 
 (OR
     [OR
        [ atomic (fail_event p D1 t); AND [OR (gate_list (fail_event_list p [E1; E2] t));  atomic (fail_event p E21 t)];
         OR (gate_list(fail_event_list p [E3; E4; E5] t))];
      OR
        [atomic (fail_event p D4 t); AND [OR (gate_list(fail_event_list p [E6; E7] t)); atomic (fail_event p E21 t) ];
         OR (gate_list(fail_event_list p [E8; E9; E10] t))]])`;


(*=================probability of B2=====================================*)

val B2_FT_def = Define
 `B2_FT p t D7 D10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 = 
 (OR
     [OR
        [ atomic (fail_event p D7 t); AND [OR (gate_list (fail_event_list p [E11; E12] t));  atomic (fail_event p E21 t)];
         OR (gate_list(fail_event_list p [E13; E14; E15] t))];
      OR
        [atomic (fail_event p D10 t); AND [OR (gate_list(fail_event_list p [E16; E17] t)); atomic (fail_event p E21 t) ];
         OR (gate_list(fail_event_list p [E18; E19; E20] t))]])`;


(*=================probability of A=====================================*)
val A_FT_def = Define
 ` A_FT p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
       E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 = 
 (OR
       [B1_FT p t D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21;
        B2_FT p t D7 D10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21; AND [OR (gate_list (fail_event_list p [C5; C6; C7] t )); atomic (fail_event p C8 t)]])`;
(*=================probability of RT=====================================*)
val RT_FT_def = Define
 `RT_FT p t AL SL PD Others time =  AND [OR (gate_list (fail_event_list p [AL; SL; PD; Others] t)) ; atomic (fail_event p time t)] `;

(*=================probability of internal=====================================*)

val Internal_FT_def = Define
 `Internal_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD Others time = OR[AND [OR (gate_list(fail_event_list p [FD; AP] t));  atomic (fail_event p FF1 t)]; OR
       [A_FT p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
          E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8;  atomic (fail_event p notshw t);
        RT_FT p t AL SL PD Others time]] `;


(*=================probability of ASN gateway =====================================*)
 val ASN_gateway_FT_def = Define
 `ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD Others time ED EQ1 EN1 EN2 EN3 EN4 human = FTree p (OR
       [AND (gate_list(fail_event_list p [ED; EQ1] t));
        OR [AND (gate_list(fail_event_list p [EN1; EN2; EN3; EN4] t)); atomic (fail_event p human t) ];
        Internal_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5
          E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5
          C6 C7 C8 notshw AL SL PD Others time])  `;
(*================= =====================================*)
val ASN_FT_eq_parallel_series_RBD = store_thm("ASN_FT_eq_parallel_series_RBD",
  ``!p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
      E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
      Others time ED EQ1 EN1 EN2 EN3 EN4 human.
     (ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8
       E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8
       notshw AL SL PD Others time ED EQ1 EN1 EN2 EN3 EN4 human = rbd_struct p ((parallel of (λa. series (rbd_list a ))) (list_fail_event_list p [[ED; EQ1];[EN1; EN2; EN3; EN4];[human];[FD; FF1];[FF1; AP];[D1];[D4];[E1;E21];[E2;E21];[E3];[E4];[E5];[E6;E21];[E7;E21];[E8];[E9];[E10];[D7];[D10];[E11;E21];[E12;E21];[E13];[E14];[E15];[E16;E21];[E17;E21];[E18];[E19];[E20];[C5; C8];[C6; C8];[C7; C8];[notshw];[AL; time];[SL; time];[PD; time];[Others;time]] t)))``,
RW_TAC list_ss[ASN_gateway_FT_def,Internal_FT_def,A_FT_def,B1_FT_def,B2_FT_def,RT_FT_def,FTree_def,INTER_DEF,rbd_struct_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,gate_list_def,rbd_list_def,of_DEF,o_DEF,UNION_DEF]
++ SET_TAC[]);




(*======================================================*)
val B1_FT_lemma2 = store_thm("B1_FT_lemma2",
  ``! a b c d e f g h i j k l:real. 1 - (a *b *c *d *e *f *g *h *i *j *k * l) = (1 - (a * b * e * f * g * j * k * l * c * d * h* i))``,
REAL_ARITH_TAC);
(*======================================================*)
val B1_FT_lemma2_new = store_thm("B1_FT_lemma2_new",
  ``! a b c d e f g h i j k l:real.  (a *b *c *d *e *f *g *h *i *j *k * l) = ( (a * b * e * f * g * j * k * l * c * d * h* i))``,
REAL_ARITH_TAC);
(*======================================================*)
val B1_FT_lemma5 = store_thm("B1_FT_lemma5",
  ``! a b c d e f g h i j k l:real. (a *b *c *d *e *f *g *h *i *j *k * l) = ((a * b * e * f * g * j * k * l * c * d * h* i))``,
REAL_ARITH_TAC);
(*======================================================*)

val B1_FT_lemma3 = store_thm("B1_FT_lemma3",
  ``!p D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 t.
(1 - list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
              [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t ))) = 1 - list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [[D1]; [D4]; [E3]; [E4]; [E5];
               [E8]; [E9]; [E10]] t ))) * list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [ [E1; E21]; [E2; E21];
              [E6; E21]; [E7; E21]] t))))``,

RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,one_minus_list_def,list_prob_def,list_prod_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC std_ss[B1_FT_lemma2]);

(*=================*)
val B1_FT_lemma3_new = store_thm("B1_FT_lemma3_new",
  ``!p D1 D4 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E21 t.
(list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
              [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t ))) = list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [[D1]; [D4]; [E3]; [E4]; [E5];
               [E8]; [E9]; [E10]] t ))) * list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [ [E1; E21]; [E2; E21];
              [E6; E21]; [E7; E21]] t))))``,
RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,one_minus_list_def,list_prob_def,list_prod_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC std_ss[B1_FT_lemma2_new]);

(*======================================================*)
val B1_FT_lemma6 = store_thm("B1_FT_lemma6",
  ``! p t  E1 E2  E6 E7  E21 C_E1 C_E2 C_E6 C_E7  C_E21.
(0<= t) /\ prob_space p /\ (list_exp p (FLAT [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21]; [C_E7; C_E21]]) (FLAT [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]])) ==>
(list_prod
       (one_minus_list
          (list_prod_rel p
             (list_fail_event_list p
                [[E1; E21]; [E2; E21]; [E6; E21]; [E7; E21]] t))) = list_prod
       (one_minus_exp_prod t
          [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21]; [C_E7; C_E21]]))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);



(*=====================================================================*)
val RT_FT_lemma2 = store_thm("RT_FT_lemma2",
  ``!p t AL SL PD Others time C_AL C_SL C_PD C_Others C_time.
(0<= t) /\ prob_space p/\
 (list_exp p (FLAT [[C_AL;C_time]; [C_SL;C_time]; [C_PD;C_time]; [C_Others;C_time]]) (FLAT [[AL;time]; [SL;time]; [PD;time]; [Others;time]]))
 ==> (list_prod
         (one_minus_list
            (list_prod_rel p
               (list_fail_event_list p
                  [[AL; time];
                   [SL; time]; [PD; time]; [Others; time]] t))) = list_prod
       (one_minus_exp_prod t
          [[C_AL;C_time]; [C_SL;C_time]; [C_PD;C_time]; [C_Others;C_time]]))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);
(*======================================================*)


val B1_FT_lemma4 = store_thm("B1_FT_lemma4",
  ``! p t D1 D4 E1  E3 E4 E5 E8 E9 E10 C_D1 C_D4 C_E3 C_E4 C_E5 C_E8 C_E9 C_E10.
(0<= t) /\ prob_space p /\ (list_exp p ([C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10]) (FLAT [[D1]; [D4]; [E3]; [E4]; [E5];
               [E8]; [E9]; [E10]])) ==>
(list_prod
    (one_minus_list
       (list_prod_rel p
          (list_fail_event_list p
             [[D1]; [D4]; [E3]; [E4]; [E5];
               [E8]; [E9]; [E10]] t ))) = exp
  (-(t * list_sum [C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10])))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]
++ RW_TAC real_ss[GSYM EXP_ADD]
++ RW_TAC real_ss[EXP_NEG]
++ RW_TAC real_ss[REAL_LDISTRIB]
++ RW_TAC real_ss[GSYM EXP_NEG]
++ RW_TAC real_ss[REAL_NEG_ADD]
++ RW_TAC real_ss[REAL_MUL_COMM,REAL_ADD_ASSOC]);




(*================================================*)
val A_FT_lemma1 = store_thm("A_FT_lemma1",
  ``!p t D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL time SL PD Others. list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
            [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7]; [D10];
            [E11; E21]; [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
            [E17; E21]; [E18]; [E19]; [E20]; [C5; C8]; [C6; C8];
            [C7; C8]; [notshw]; [AL; time]; [SL; time]; [PD; time];
            [Others; time]] t))) = list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5];
            [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]] t))) * list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p [[D7]; [D10];
            [E11; E21]; [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
            [E17; E21]; [E18]; [E19]; [E20]] t ))) * list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p [[C5; C8]; [C6; C8];
            [C7; C8]; [notshw]; [AL; time]; [SL; time]; [PD; time];
            [Others; time]] t))) ``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);




(*================================================*)
val Internal_FT_lemma1 = store_thm("Internal_FT_lemma1",
  ``!p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
      E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
      Others time. 
list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[FD; FF1]; [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21];
            [E3]; [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10];
            [D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
            [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
            [C6; C8]; [C7; C8]; [notshw]; [AL; time]; [SL; time];
            [PD; time]; [Others; time]] t))) = 
list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[FD; FF1]; [FF1; AP]] t))) * list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p [[D1]; [D4]; [E1; E21]; [E2; E21];
            [E3]; [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10];
            [D7]; [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
            [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
            [C6; C8]; [C7; C8]; [notshw]; [AL; time]; [SL; time];
            [PD; time]; [Others; time]] t)))``,

RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,one_minus_list_def,list_prob_def,list_prod_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);




(*================================================*)

val Internal_FT_lemma2 = store_thm("Internal_FT_lemma2",
  ``! p t FD AP FF1 C_FD C_AP C_FF1.
(0<= t) /\ prob_space p /\ (list_exp p (FLAT [[C_FD;C_FF1];[C_AP;C_FF1]]) (FLAT [[FD;FF1];[AP;FF1]])) ==> 
(list_prod
       (one_minus_list
          (list_prod_rel p
             (list_fail_event_list p [[FD; FF1]; [FF1; AP]] t))) = 
list_prod (one_minus_exp_prod t [[C_FD; C_FF1]; [C_AP; C_FF1]]))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]
++ REAL_ARITH_TAC);


(*================================================*)

(*=========================================================================*)
val ASN_gateway_lemma1 = store_thm("ASN_gateway_lemma1",
  ``!p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
      E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
      Others time ED EQ1 EN1 EN2 EN3 EN4 human.
      (list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]; [FD; FF1];
            [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4];
            [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7]; [D10];
            [E11; E21]; [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
            [E17; E21]; [E18]; [E19]; [E20]; [C5; C8]; [C6; C8];
            [C7; C8]; [notshw]; [AL; time]; [SL; time]; [PD; time];
            [Others; time]] t))) = list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]] t))) *  list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p [[FD; FF1];
            [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4];
            [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7]; [D10];
            [E11; E21]; [E12; E21]; [E13]; [E14]; [E15]; [E16; E21];
            [E17; E21]; [E18]; [E19]; [E20]; [C5; C8]; [C6; C8];
            [C7; C8]; [notshw]; [AL; time]; [SL; time]; [PD; time];
            [Others; time]] t))))``,

RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,one_minus_list_def,list_prob_def,list_prod_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);

(*----------------------*)
val ASN_gateway_lemma2 = store_thm("ASN_gateway_lemma2",
  ``!p t ED EQ1 EN1 EN2 EN3 EN4 human C_ED C_EQ1 C_EN1 C_EN2 C_EN3 C_EN4 C_human.
(0 <= t) /\  prob_space p /\ (list_exp p
       (FLAT
          [[C_ED;C_EQ1];[C_EN1;C_EN2;C_EN3;C_EN4];[C_human]])
       (FLAT
          [[ED;EQ1];[EN1;EN2;EN3;EN4];[human]])) ==> (list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]] t))) = 
list_prod
  (one_minus_exp_prod t
     [[C_ED; C_EQ1]; [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]]))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);
(*---------------------------*)
val ASN_gateway_lem5 = store_thm("ASN_gateway_lem5",
  ``! p t C5 C6 C7 C8 notshw AL time SL PD Others.
(list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[C5; C8]; [C6; C8]; [C7; C8]; [notshw]; [AL; time];
            [SL; time]; [PD; time]; [Others; time]] t))) = list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[C5; C8]; [C6; C8]; [C7; C8]] t))) *  list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p [[notshw]; [AL; time];
            [SL; time]; [PD; time]; [Others; time]] t))))``,

RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,one_minus_list_def,list_prob_def,list_prod_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]);
(*-----------------*)
val ASN_gateway_lem6 = store_thm("ASN_gateway_lem6",``! p t C5 C6 C7 C8 C_C5 C_C6 C_C7 C_C8.
(0<= t) /\ prob_space p /\ (list_exp p (FLAT [[C_C5;C_C8]; [C_C6;C_C8]; [C_C7;C_C8]]) (FLAT [[C5;C8]; [C6;C8]; [C7;C8]])) ==> (list_prod
       (one_minus_list
          (list_prod_rel p
             (list_fail_event_list p [[C5; C8]; [C6; C8]; [C7; C8]]
                t))) = list_prod
       (one_minus_exp_prod t
          [[C_C5;C_C8]; [C_C6;C_C8]; [C_C7;C_C8]]))``,
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ RW_TAC real_ss[]);


(*=========================================================================*)

val ASN_gateway_thm = store_thm("ASN_gateway_thm",
  ``!p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12
      E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8 notshw AL SL PD
      Others time ED EQ1 EN1 EN2 EN3 EN4 human C_ED C_EQ1 C_EN1 C_EN2 C_EN3 C_EN4 C_human C_FD C_AP C_FF1 C_notshw C_AL C_SL C_PD C_Others C_time C_C5 C_C6 C_C7 C_C8 C_E1 C_E2
      C_E6 C_E7 C_D1 C_D4 C_E3 C_E4 C_E5 C_E8 C_E9 C_E10 C_E11 C_E12
      C_E16 C_E17 C_D7 C_D10 C_E13 C_E14 C_E15 C_E18 C_E19 C_E20 C_E21. (0 <= t) /\  prob_space p  /\
 (!x'.
    MEM x'
      (FLAT
         (list_fail_event_list p
              [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]; [FD; FF1];
               [FF1; AP]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4];
               [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7];
               [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
               [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]; [C5; C8];
               [C6; C8]; [C7; C8]; [notshw]; [AL; time]; [SL; time];
               [PD; time]; [Others; time]] t)) ==>
    x' IN events p) /\
 mutual_indep p
   (FLAT (list_fail_event_list p
        [[ED; EQ1]; [EN1; EN2; EN3; EN4]; [human]; [FD; FF1]; [FF1; AP];
         [D1]; [D4]; [E1; E21]; [E2; E21]; [E3]; [E4]; [E5]; [E6; E21];
         [E7; E21]; [E8]; [E9]; [E10]; [D7]; [D10]; [E11; E21];
         [E12; E21]; [E13]; [E14]; [E15]; [E16; E21]; [E17; E21]; [E18];
         [E19]; [E20]; [C5; C8]; [C6; C8]; [C7; C8]; [notshw];
         [AL; time]; [SL; time]; [PD; time]; [Others; time]] t))
       /\ (list_exp p
       (FLAT
          [[C_C5; C_C6; C_C7; C_C8]; [C_D1]; [C_D4]; [C_E1; C_E21];
           [C_E2; C_E21]; [C_E3]; [C_E4]; [C_E5]; [C_E6; C_E21];
           [C_E7; C_E21]; [C_E8]; [C_E9]; [C_E10]; [C_D7]; [C_D10];
           [C_E11; C_E21]; [C_E12; C_E21]; [C_E13]; [C_E14]; [C_E15];
           [C_E16; C_E21]; [C_E17; C_E21]; [C_E18]; [C_E19]; [C_E20];
           [C_AL; C_time]; [C_SL; C_time]; [C_PD; C_time];
           [C_Others; C_time]; [C_FD; C_FF1]; [C_AP; C_FF1];
           [C_notshw];[C_ED;C_EQ1];[C_EN1;C_EN2;C_EN3;C_EN4];[C_human]])
       (FLAT
          [[C5; C6; C7; C8]; [D1]; [D4]; [E1; E21]; [E2; E21]; [E3];
           [E4]; [E5]; [E6; E21]; [E7; E21]; [E8]; [E9]; [E10]; [D7];
           [D10]; [E11; E21]; [E12; E21]; [E13]; [E14]; [E15];
           [E16; E21]; [E17; E21]; [E18]; [E19]; [E20]; [AL; time];
           [SL; time]; [PD; time]; [Others; time]; [FD; FF1]; [AP; FF1];
           [notshw];[ED;EQ1];[EN1;EN2;EN3;EN4];[human]])) ==>
	   (prob p (ASN_gateway_FT p t FD AP FF1 D1 D4 D7 D10 E1 E2 E3 E4 E5 E6 E7 E8
       E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 C5 C6 C7 C8
       notshw AL SL PD Others time ED EQ1 EN1 EN2 EN3 EN4 human) = 1 -
list_prod
  (one_minus_exp_prod t
     [[C_ED; C_EQ1]; [C_EN1; C_EN2; C_EN3; C_EN4]; [C_human]]) *
(list_prod (one_minus_exp_prod t [[C_FD; C_FF1]; [C_AP; C_FF1]]) *
 (exp
    (-(t *
       list_sum [C_D1; C_D4; C_E3; C_E4; C_E5; C_E8; C_E9; C_E10])) *
  list_prod
    (one_minus_exp_prod t
       [[C_E1; C_E21]; [C_E2; C_E21]; [C_E6; C_E21]; [C_E7; C_E21]]) *
  (exp
     (-(t *
        list_sum
          [C_D7; C_D10; C_E13; C_E14; C_E15; C_E18; C_E19; C_E20])) *
   list_prod
     (one_minus_exp_prod t
        [[C_E11; C_E21]; [C_E12; C_E21]; [C_E16; C_E21];
         [C_E17; C_E21]])) *
  list_prod
    (one_minus_exp_prod t [[C_C5; C_C8]; [C_C6; C_C8]; [C_C7; C_C8]])) *
 exp (-(C_notshw * t)) *
 list_prod
   (one_minus_exp_prod t
      [[C_AL; C_time]; [C_SL; C_time]; [C_PD; C_time];
       [C_Others; C_time]])))``,
RW_TAC std_ss[ASN_FT_eq_parallel_series_RBD]
++ DEP_REWRITE_TAC[rel_parallel_series_rbd]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[list_fail_event_list_def,fail_event_list_def])
++ RW_TAC std_ss[ASN_gateway_lemma1]
++ DEP_ASM_REWRITE_TAC[ASN_gateway_lemma2]
++ RW_TAC list_ss[]
>> (FULL_SIMP_TAC list_ss[list_exp_def])
++ AP_TERM_TAC
++ AP_TERM_TAC
++ RW_TAC std_ss[Internal_FT_lemma1]
++ DEP_ASM_REWRITE_TAC[Internal_FT_lemma2]
++ RW_TAC list_ss[]
>> (FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC
++ RW_TAC real_ss[A_FT_lemma1]
++ RW_TAC real_ss[B1_FT_lemma3_new]
++ DEP_ONCE_ASM_REWRITE_TAC[B1_FT_lemma4]
++ RW_TAC list_ss[]
>> (FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC

++ DEP_ONCE_ASM_REWRITE_TAC[B1_FT_lemma6]
++ RW_TAC list_ss[]
>> (FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC
++ (`list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[D7]; [D10]; [E13]; [E14]; [E15]; [E18]; [E19]; [E20]]
           t))) = exp
  (-(t *
     list_sum
       [C_D7; C_D10; C_E13; C_E14; C_E15; C_E18; C_E19; C_E20]))` by MATCH_MP_TAC B1_FT_lemma4)
>> (RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC
++ (`list_prod
  (one_minus_list
     (list_prod_rel p
        (list_fail_event_list p
           [[E11; E21]; [E12; E21]; [E16; E21]; [E17; E21]] t))) = list_prod
  (one_minus_exp_prod t
     [[C_E11; C_E21]; [C_E12; C_E21]; [C_E16; C_E21]; [C_E17; C_E21]])` by MATCH_MP_TAC B1_FT_lemma6)
>> (RW_TAC list_ss[]
   ++ FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC
++ RW_TAC std_ss[ASN_gateway_lem5]
++ DEP_ONCE_ASM_REWRITE_TAC[ASN_gateway_lem6]
++ RW_TAC list_ss[]
>> (FULL_SIMP_TAC list_ss[list_exp_def])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ AP_TERM_TAC
++ NTAC 4 (POP_ASSUM MP_TAC)
++ RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
++ RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
++ RW_TAC real_ss[]);



(*=========================================================================*)

val _ = export_theory();