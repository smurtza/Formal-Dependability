
(* ========================================================================= *)
(* File Name: VDCScript.sml		                                     *)
(*---------------------------------------------------------------------------*)
(* Description: Formalization of Reliability Block Diagram in                *)
(*                   Higher-order Logic                                      *)
(*                                                                           *)
(*                HOL4-Kananaskis 10 		 			     *)
(*									     *)
(*		Author :  Waqar Ahmed             		     	     *)
(*                                              			     *)
(* 	    School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*	    National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                          		               	     *)
(*                                                                           *)
(* ========================================================================= *)
app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "RBD";
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





(*--------------------*)
(*------------------------------*)
(*      RBD datatypes           *)
(*------------------------------*)
val _ = type_abbrev( "event" , ``:'a ->bool``);

val _ = Hol_datatype` rbd = series of rbd list| parallel of rbd list | atomic of 'a  event `;

(*----------------------------------------------*)
(*      RBD Structures Semantic Function        *)
(*----------------------------------------------*)

val rbd_struct_def = Define `
    (rbd_struct p ( atomic a)  = a) /\
    (rbd_struct p (series []) = p_space p) /\
    (rbd_struct p (series (x::xs)) =
                rbd_struct p (x:'a  rbd) INTER rbd_struct p (series (xs))) /\
     (rbd_struct p (parallel []) = {} ) /\
     (rbd_struct p (parallel (x::xs)) =
                 rbd_struct p (x:'a  rbd) UNION rbd_struct p (parallel (xs)))
`;

(*---rbd list from atomic events---*)

val rbd_list_def = Define `
    (rbd_list [] = []) /\
    (rbd_list (h::t) =  atomic h::rbd_list t)`;


(* -------------------- *)
(*      Definitions     *)
(* -------------------- *)
val of_DEF = Q.new_infixr_definition("of_DEF", `$of g f = (g o (\a. MAP f a))`, 800);


val big_inter_def =  Define
 ` (big_inter p []= p_space p) /\
          (!h t. big_inter p (h ::t)  = ( h  INTER big_inter p t ))`;
(* --------------------- *)
(*      list_prod        *)
(* --------------------- *)

val list_prod_def =  Define
 `(list_prod ([]) =  1:real ) /\
                   (!h t . list_prod (h :: t)  =   (h:real) * (list_prod t ))`;

(* --------------------------- *)
(*      list_prob              *)
(* --------------------------- *)
val list_prob_def = Define
                 ` (list_prob p [] = []) /\
                 (!h t.list_prob p (h::t) =  prob p (h) :: list_prob p t )`;

(* --------------------------------------- *)
(*  Mutual Independence of Events          *)
(* --------------------------------------- *)
val mutual_indep_def = Define
                    ` mutual_indep p (L) = !L1 n. (PERM L L1 /\
                       (1 <=  n /\ n <=  LENGTH L) ==>
 (prob p (big_inter p (TAKE n L1)) = list_prod (list_prob p (TAKE n L1 ))))`;
(* ------------------------------------------------------------------------- *)
(* Compliment of a List of Sets                                *)
(* ------------------------------------------------------------------------- *)

val compl_list_def =  Define
` compl_list p L = MAP (\a. p_space p DIFF a) L`;
(* ---------------------------------------------- *)
(*      one_minus_list                                  *)
(* --------------------------------------------- *)
val one_minus_list_def =  Define
                       `(one_minus_list [] = []) /\
                    (!h t. one_minus_list (h::t) = (1 - (h:real)):: one_minus_list t)`;

(* ----------------------------------------- *)
(*      complement prob space                      *)
(* ----------------------------------------- *)
val compl_pspace_def = Define
                    `compl_pspace p s = p_space p DIFF s`;
(* ----------------------------------------- *)
(*  Product of Complement of Reliabilities   *)
(* ----------------------------------------- *)
val list_prod_one_minus_rel_def = Define
                    `list_prod_one_minus_rel p L = MAP (\a. list_prod (one_minus_list (list_prob p a)) ) L`;



(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*    list of product reliabilities                                           *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val list_prod_rel_def = Define `list_prod_rel p L = MAP (\a. list_prod (list_prob p a) ) L`;

(*----------------------Theorems-----------------------------*)
(*----------------------------------------------------------*)
(*      Theorem: Series RBD  Structure                  *)
(*--------------------------------------------------------*)


(*------------------------------------*)
(*      Series Structure Lemma        *)
(*------------------------------------*)

val mutual_indep_cons = store_thm("mutual_indep_cons",
  ``!L h. mutual_indep p (h::L) ==> mutual_indep p L``,
RW_TAC std_ss[mutual_indep_def]THEN
NTAC 3(POP_ASSUM MP_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `(L1 ++ [h]):'a  event list`) THEN
RW_TAC std_ss[] THEN
NTAC 3(POP_ASSUM MP_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`) THEN
RW_TAC std_ss[] THEN
(`(TAKE n ((L1 ++ [h]):'a  event list)) = (TAKE n (L1)) ` by MATCH_MP_TAC TAKE_APPEND1) THENL[
(`LENGTH (L1:('a  -> bool)list) = LENGTH ((L):('a  -> bool)list) ` by MATCH_MP_TAC PERM_LENGTH ) THENL[
         ONCE_REWRITE_TAC[PERM_SYM] THEN
         RW_TAC std_ss[],
         ONCE_ASM_REWRITE_TAC[] THEN
         RW_TAC std_ss[]
                ],
FULL_SIMP_TAC std_ss[] THEN
POP_ASSUM (K ALL_TAC) THEN
(` PERM (((h:('a  -> bool))::L):('a  -> bool)list) ((L1 ++ [h]):('a  -> bool)list) /\ n <= LENGTH ((h::L):('a  -> bool)list) ` by RW_TAC std_ss[]) THENL[
   (` ((h::L):'a  event list) =  [h ]++ (L:('a  -> bool)list) ` by RW_TAC list_ss[]) THEN  ONCE_ASM_REWRITE_TAC[] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MATCH_MP_TAC APPEND_PERM_SYM THEN
   MATCH_MP_TAC PERM_CONG THEN
   RW_TAC std_ss[PERM_REFL],
   MATCH_MP_TAC LESS_EQ_TRANS THEN
   EXISTS_TAC(--`LENGTH (L:('a  -> bool)list)`--) THEN
   RW_TAC list_ss[LENGTH],
FULL_SIMP_TAC std_ss[]
]]);

(*-------series_rbd_eq_big_inter---*)


val series_rbd_eq_big_inter = store_thm("series_rbd_eq_big_inter",
  ``!p L. rbd_struct p (series (rbd_list L)) = big_inter p L``,
GEN_TAC
++ Induct
>> (RW_TAC std_ss[rbd_list_def,rbd_struct_def,big_inter_def])
++ RW_TAC std_ss[rbd_list_def,rbd_struct_def,big_inter_def]);



(*------------------------------------- *)
(*   Reliability of Series Structure   *)
(*-------------------------------------*)

val series_struct_thm = store_thm("series_struct_thm",
  ``!p L. prob_space p /\ ~NULL L /\ (!x'. MEM x' L ==> x'  IN  events p ) /\
 mutual_indep p L ==>
(prob p (rbd_struct p (series (rbd_list L))) =  list_prod (list_prob p L))``,
RW_TAC std_ss[] THEN
(`(rbd_struct p (series (rbd_list L))) = big_inter p L ` by Induct_on `L`) THEN1
RW_TAC std_ss[rbd_list_def,rbd_struct_def,big_inter_def] THENL[
RW_TAC std_ss[big_inter_def] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
RW_TAC std_ss[] THEN
Cases_on `L` THEN1
RW_TAC std_ss[rbd_list_def,rbd_struct_def,big_inter_def] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
(`(!x'. MEM x' ((h'::t):'a  event list) ==> x' IN events p) /\
          mutual_indep p (h'::t)` by RW_TAC std_ss[]) THENL[
FULL_SIMP_TAC list_ss[],
MATCH_MP_TAC mutual_indep_cons THEN
EXISTS_TAC(--`h:'a ->bool`--) THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[rbd_list_def,rbd_struct_def,big_inter_def]],
FULL_SIMP_TAC std_ss[mutual_indep_def] THEN
POP_ASSUM (K ALL_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `(L:'a  event list)`) THEN
RW_TAC std_ss[] THEN
POP_ASSUM (MP_TAC o Q.SPEC `LENGTH((L:'a  event list))`) THEN
RW_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[PERM_REFL] THEN
FULL_SIMP_TAC std_ss[GSYM LENGTH_NOT_NULL] THEN
(`1 <= LENGTH (L:'a  event list)` by ONCE_REWRITE_TAC[ONE]) THENL[
MATCH_MP_TAC LESS_OR THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[TAKE_LENGTH_ID]]]);


(*------------------------------------*)
(*      Parallel RBD  Structure      *)
(*------------------------------------*)
(*----------------Definitions---------*)

(*------------------------------------*)
(*      Lemmma's             *)
(*------------------------------------*)

val parallel_rbd_lem1 = store_thm("parallel_rbd_lem1",
  ``!p L. prob_space p /\ (!x'. MEM x' L ==> x'  IN  events p )   ==> (one_minus_list (list_prob p L) = list_prob p ( compl_list p L))``,
GEN_TAC THEN
Induct THEN1
RW_TAC list_ss[compl_list_def,list_prob_def,one_minus_list_def] THEN
RW_TAC list_ss[compl_list_def,list_prob_def,one_minus_list_def] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC PROB_COMPL THEN
RW_TAC std_ss[]);

(*----------in_events_big_inter-----------------------*)
val in_events_big_inter = store_thm("in_events_big_inter",
  ``!L p. (!x. MEM x L ==> x IN events p) /\
prob_space p ==>
  (big_inter p L IN events p)``,
RW_TAC std_ss []
THEN Induct_on `L`
    THENL[ RW_TAC std_ss[MEM, big_inter_def,EVENTS_SPACE],
RW_TAC std_ss [MEM, big_inter_def]
THEN MATCH_MP_TAC EVENTS_INTER
THEN RW_TAC std_ss []]);
(*-------parallel_rbd_lem2---------*)
val parallel_rbd_lem2 = store_thm("parallel_rbd_lem2",
  ``!L1 (L2:('a ->bool)list) Q. (LENGTH (L1 ++ ((Q::L2))) = LENGTH ((Q::L1) ++ (L2)))``,
RW_TAC list_ss[LENGTH_APPEND]);
(*-------parallel_rbd_lem3---------*)
val parallel_rbd_lem3 = store_thm("parallel_rbd_lem3",
  ``!A B C D. A INTER B INTER C INTER D = (B INTER C) INTER D INTER A ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------parallel_rbd_lem4---------*)
val parallel_rbd_lem4 = store_thm("parallel_rbd_lem4",
  ``!A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C)) ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------parallel_rbd_lem5---------*)
val  parallel_rbd_lem5 = store_thm("parallel_rbd_lem5",
  ``!m (L:('a ->bool)list) x. MEM x (TAKE m L) ==> MEM x L ``,
Induct
THEN1(Induct
 THEN1 (RW_TAC std_ss[TAKE_def,MEM])
 THEN RW_TAC std_ss[TAKE_def,MEM])
 THEN Induct
  THEN1( RW_TAC std_ss[TAKE_def,MEM])
 THEN RW_TAC std_ss[TAKE_def,MEM]
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `L`)
THEN RW_TAC std_ss[] );
(*-------------parallel_rbd_lem6----------------*)
val parallel_rbd_lem6 = store_thm("parallel_rbd_lem6",``!A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C))``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]);
(*-------------parallel_rbd_lem7----------------*)
val parallel_rbd_lem7 =  store_thm("parallel_rbd_lem7",``!(L1:('a ->bool) list) p.
 prob_space p /\
 (!x. MEM x (L1) ==> x IN events p ) ==>
((L1:('a ->bool) list) =  compl_list p (compl_list p L1)) ``,
Induct
>> (RW_TAC list_ss[compl_list_def,MAP])
++ RW_TAC std_ss[compl_list_def,MAP]
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC DIFF_DIFF_SUBSET
   ++ (`h =  h INTER p_space p` by MATCH_MP_TAC EQ_SYM)
      >> (ONCE_REWRITE_TAC[INTER_COMM]
         ++ MATCH_MP_TAC INTER_PSPACE
         ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ NTAC 2 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[compl_list_def]);

(*--------prob_B-------------------*)
val prob_B = store_thm("prob_B",``!p a b . prob_space p /\  (a IN events p /\  b IN events p)  ==> ( prob p b = prob p ( a   INTER b) + prob p (compl_pspace p a  INTER b ))``,
RW_TAC std_ss[] THEN
(`(a INTER b)  UNION ((compl_pspace p a) INTER (b )) = b` by ALL_TAC) THENL[
     ONCE_REWRITE_TAC[INTER_COMM] THEN
     RW_TAC std_ss[GSYM UNION_OVER_INTER] THEN
     RW_TAC std_ss[compl_pspace_def,DIFF_SAME_UNION] THEN
     (`a SUBSET p_space p` by ALL_TAC) THENL[
         (`a = p_space p INTER a` by MATCH_MP_TAC EQ_SYM)THENL[
              MATCH_MP_TAC INTER_PSPACE THEN
              RW_TAC std_ss[],
              ONCE_ASM_REWRITE_TAC[] THEN
              RW_TAC std_ss[INTER_SUBSET]],
         RW_TAC std_ss[UNION_DIFF] THEN
         ONCE_REWRITE_TAC[INTER_COMM] THEN
         MATCH_MP_TAC INTER_PSPACE THEN
         RW_TAC std_ss[]],
(` prob p (a INTER b) + prob p (compl_pspace p a INTER b) = prob p ( a INTER b UNION (compl_pspace p a INTER b))` by MATCH_MP_TAC EQ_SYM ) THENL[
   MATCH_MP_TAC PROB_ADDITIVE THEN
   RW_TAC std_ss[] THENL[
         MATCH_MP_TAC EVENTS_INTER THEN
         RW_TAC std_ss[],
         MATCH_MP_TAC EVENTS_INTER THEN
         RW_TAC std_ss[compl_pspace_def] THEN
         MATCH_MP_TAC EVENTS_COMPL THEN
         RW_TAC std_ss[],
         RW_TAC std_ss[DISJOINT_DEF] THEN
         RW_TAC std_ss[INTER_COMM] THEN
         RW_TAC std_ss[INTER_ASSOC] THEN
         (`(a INTER b INTER b INTER compl_pspace p a) = (a INTER compl_pspace p a) INTER b` by SRW_TAC[][INTER_DEF,EXTENSION,GSPECIFICATION]) THENL[
              EQ_TAC THENL[
                 RW_TAC std_ss[],
                 RW_TAC std_ss[]],
              ONCE_ASM_REWRITE_TAC[] THEN
              RW_TAC std_ss[compl_pspace_def] THEN
              (`a INTER (p_space p DIFF a) = EMPTY` by ONCE_REWRITE_TAC[INTER_COMM]) THENL[
                  RW_TAC std_ss[DIFF_INTER] THEN
                  (`p_space p INTER  a  =  a` by MATCH_MP_TAC INTER_PSPACE) THENL[
                        RW_TAC std_ss[],
                        ONCE_ASM_REWRITE_TAC[] THEN
                        RW_TAC std_ss[DIFF_EQ_EMPTY]],
                  ONCE_ASM_REWRITE_TAC[] THEN
                  RW_TAC std_ss[INTER_EMPTY]]]],
FULL_SIMP_TAC std_ss[]]]);


(*-------Prob_Incl_excl--------------------*)
val Prob_Incl_excl = store_thm("Prob_Incl_excl",``!p a b. prob_space p /\ a IN events p /\ b IN events p ==> ( prob p ((a ) UNION (b )) = prob p (a) + prob p (b) - prob p ((a) INTER (b)))``,
REPEAT GEN_TAC THEN
RW_TAC std_ss[] THEN
(` prob p (a UNION (compl_pspace p a  INTER b)) = prob p (a ) + prob p (compl_pspace p a INTER b)` by  MATCH_MP_TAC PROB_ADDITIVE) THENL[
  RW_TAC std_ss[] THENL[
      MATCH_MP_TAC EVENTS_INTER THEN
      RW_TAC std_ss[compl_pspace_def] THEN
      MATCH_MP_TAC EVENTS_COMPL THEN
      RW_TAC std_ss[],
    RW_TAC std_ss[DISJOINT_DEF] THEN
    RW_TAC std_ss[INTER_ASSOC] THEN
    RW_TAC std_ss[compl_pspace_def] THEN
    (`a INTER (p_space p DIFF a) = EMPTY` by ONCE_REWRITE_TAC[INTER_COMM]) THENL[
      RW_TAC std_ss[DIFF_INTER] THEN
      (`p_space p INTER a  =  a` by MATCH_MP_TAC INTER_PSPACE) THENL[
          RW_TAC std_ss[],
        ONCE_ASM_REWRITE_TAC[] THEN
        RW_TAC std_ss[DIFF_EQ_EMPTY]],
    ONCE_ASM_REWRITE_TAC[] THEN
RW_TAC std_ss[INTER_EMPTY]
]],
  (`(a UNION (compl_pspace p a INTER b) = a UNION b)` by RW_TAC std_ss[INTER_OVER_UNION]) THEN1(
     RW_TAC std_ss[compl_pspace_def] THEN
     (`(a UNION (p_space p DIFF a)) = p_space p` by ALL_TAC) THEN1(
          (`a SUBSET p_space p` by ALL_TAC) THEN1(
             (`a = p_space p INTER a` by MATCH_MP_TAC EQ_SYM)  THEN1(
                  MATCH_MP_TAC INTER_PSPACE THEN
                  RW_TAC std_ss[]) THEN
           ONCE_ASM_REWRITE_TAC[] THEN
           RW_TAC std_ss[INTER_SUBSET]) THEN
       RW_TAC std_ss[UNION_DIFF]) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTER_PSPACE THEN
  RW_TAC std_ss[] THEN
  MATCH_MP_TAC EVENTS_UNION THEN
  RW_TAC std_ss[]) THEN
FULL_SIMP_TAC std_ss[] THEN
(MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `a:'a  event`,`b:'a  event` ]
       prob_B))  THEN
RW_TAC std_ss[] THEN
REAL_ARITH_TAC]);
(*----------prob_compl_subset-----------------*)
val prob_compl_subset = store_thm("prob_compl_subset", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ t SUBSET s ==> (prob p (s DIFF t) = prob p s - prob p t)``,
METIS_TAC [MEASURE_COMPL_SUBSET,prob_space_def,events_def,prob_def,p_space_def]);

(*-----------mutual_indep_cons_append----------------*)
val mutual_indep_cons_append = store_thm("mutual_indep_cons_append",``!L1 L2 h.  mutual_indep p (h::L1 ++ L2) ==>  mutual_indep p (L1 ++ h::L2)``,
RW_TAC std_ss[mutual_indep_def]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a  event list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1 ++ L2) ((L1'):('a  -> bool)list)` by MATCH_MP_TAC PERM_TRANS)
   THEN1( EXISTS_TAC (--`(L1 ++ h::L2):'a  event list`--)
   THEN RW_TAC std_ss[]
   THEN RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]
   THEN MATCH_MP_TAC EQ_SYM
   THEN RW_TAC std_ss[PERM_FUN_APPEND_CONS])
THEN FULL_SIMP_TAC std_ss[]
THEN (` n <= LENGTH (h::((L1):('a  -> bool)list) ++ L2)` by FULL_SIMP_TAC list_ss[LENGTH_APPEND])
     THEN FULL_SIMP_TAC std_ss[]);

(*---------mutual_indep_cons_append1------------------*)
val mutual_indep_cons_append1 = store_thm("mutual_indep_cons_append1",``!L1 L2 Q h.  mutual_indep p (h::L1 ++ Q::L2) ==>  mutual_indep p (L1 ++ Q::h::L2)``,
RW_TAC std_ss[mutual_indep_def]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a  event list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1 ++ Q::L2) ((L1'):('a  -> bool)list)` by MATCH_MP_TAC PERM_TRANS)
   THEN1( EXISTS_TAC (--`(L1 ++ Q::h::L2):'a  event list`--)
   THEN RW_TAC std_ss[]
   THEN RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]
   THEN MATCH_MP_TAC EQ_SYM
   THEN RW_TAC std_ss[PERM_FUN_APPEND_CONS,APPEND,PERM_FUN_SWAP_AT_FRONT]
   THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN (` n <= LENGTH (h::L1 ++ Q::L2)` by FULL_SIMP_TAC list_ss[LENGTH_APPEND])
     THEN FULL_SIMP_TAC std_ss[]);

(*--------mutual_indep_cons_swap---------------------*)
val mutual_indep_cons_swap = store_thm("mutual_indep_cons_swap",``!p L1 h.  mutual_indep p (h::L1) ==>  mutual_indep p (L1 ++ [h])``,
RW_TAC std_ss[mutual_indep_def]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a  event list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1)  ((L1'):('a  -> bool)list)` by MATCH_MP_TAC PERM_TRANS)
   THEN1( EXISTS_TAC (--`(L1 ++ [h]):'a  event list`--)
   THEN RW_TAC std_ss[]
   THEN (`((h::L1) :('a  -> bool)list) = [h] ++ L1` by RW_TAC list_ss[])
   THEN ONCE_ASM_REWRITE_TAC[]
   THEN POP_ASSUM (K ALL_TAC)
   THEN RW_TAC std_ss[PERM_APPEND])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC list_ss[LENGTH]);

(*-----------prob_indep_compl_event_big_inter_list-----------------*)
val prob_indep_compl_event_big_inter_list =  store_thm("prob_indep_compl_event_big_inter_list", ``!L1 n h p.  mutual_indep p (h::L1) /\ (!x.  MEM x (h::L1)  ==>  x  IN  events p) /\ ( prob_space p) /\ (LENGTH L1 = 1) ==> ( prob p ((p_space p DIFF h) INTER  big_inter p (TAKE n (compl_list p L1))) =
prob p (p_space p DIFF (h:'a ->bool)) *
list_prod (list_prob p (TAKE n (compl_list p L1))))``,
Induct
THEN1(RW_TAC list_ss[])
     THEN Induct_on `n`
        THEN1(RW_TAC list_ss[TAKE_def,LENGTH]
        THEN RW_TAC list_ss[big_inter_def,list_prob_def,list_prod_def]
        THEN RW_TAC std_ss[DIFF_INTER,INTER_IDEMPOT]
        THEN REAL_ARITH_TAC )
      THEN RW_TAC std_ss[LENGTH,LENGTH_NIL]
      THEN RW_TAC real_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def]
      THEN  RW_TAC std_ss[DIFF_INTER,INTER_IDEMPOT]
      THEN (`(p_space p INTER  (p_space p DIFF ((h':('a ->bool))))) = ((p_space p DIFF (h':('a ->bool)))) ` by MATCH_MP_TAC INTER_PSPACE)
      THEN1(RW_TAC std_ss[]
       THEN MATCH_MP_TAC EVENTS_DIFF
       THEN RW_TAC std_ss[EVENTS_SPACE]
       THEN FULL_SIMP_TAC list_ss[])
      THEN ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC)
      THEN RW_TAC std_ss[GSYM DIFF_UNION]
      THEN (`prob p (p_space p DIFF (h'  UNION  h)) = 1 - prob p ((((h':('a ->bool)))  UNION  h)) `by MATCH_MP_TAC PROB_COMPL)
       THEN1 (FULL_SIMP_TAC list_ss[EVENTS_UNION])
      THEN ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC)
      THEN (`prob p ((h':('a ->bool))  UNION  h) =
 prob p h' + prob p ((h:('a ->bool))) -
      prob p (h' INTER  h) ` by MATCH_MP_TAC Prob_Incl_excl)
       THEN1 (FULL_SIMP_TAC list_ss[])
      THEN ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC)
      THEN FULL_SIMP_TAC std_ss[mutual_indep_def]
      THEN NTAC 2 (POP_ASSUM MP_TAC)
      THEN POP_ASSUM (MP_TAC o Q.SPEC `[h; (h':('a ->bool))] `)
      THEN RW_TAC std_ss[]
      THEN NTAC 2 (POP_ASSUM MP_TAC)
      THEN POP_ASSUM (MP_TAC o Q.SPEC `LENGTH [h; (h':('a ->bool))] `)
      THEN RW_TAC std_ss[]
      THEN FULL_SIMP_TAC std_ss[LENGTH,PERM_REFL]
      THEN FULL_SIMP_TAC list_ss[TAKE]
      THEN FULL_SIMP_TAC real_ss[big_inter_def,list_prob_def, list_prod_def]
      THEN (`h' INTER  p_space p =  h'` by ONCE_REWRITE_TAC[INTER_COMM])
       THEN1 (MATCH_MP_TAC INTER_PSPACE
       THEN FULL_SIMP_TAC list_ss[])
      THEN FULL_SIMP_TAC std_ss[INTER_COMM]
      THEN (POP_ASSUM (K ALL_TAC))
      THEN (`(prob p (p_space p DIFF (h:('a ->bool)))  =
 1 - prob p (h)) /\  (prob p (p_space p DIFF (h':('a ->bool))) =  1 - prob p (h')) ` by RW_TAC std_ss[])
       THEN1( FULL_SIMP_TAC list_ss[PROB_COMPL] )
       THEN1 (FULL_SIMP_TAC list_ss[PROB_COMPL])
      THEN ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC)
    THEN REAL_ARITH_TAC);

(*-----------prob_indep_big_inter1------------------*)
val prob_indep_big_inter1 = store_thm("prob_indep_big_inter1",
``!(L1:('a ->bool) list) (L2:('a ->bool) list) Q n p. 
	   prob_space p  /\ 
	   mutual_indep p (L1 ++ (Q::L2)) /\ 
	   (!x. MEM x (L1 ++ (Q::L2)) ==> x IN events p ) /\
	    1 <=  (LENGTH (L1 ++ (Q::L2))) ==> 
	      (prob p (big_inter p (TAKE n (compl_list p L1)) INTER  
	      	    big_inter p ((Q::L2) )) =
               list_prod (list_prob p (TAKE (n)(compl_list p L1) )) * 
	       	list_prod (list_prob p (( Q::L2) )))``,
Induct
THEN1(RW_TAC real_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def]
 THEN FULL_SIMP_TAC std_ss[mutual_indep_def]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `((Q::L2):('a ->bool)list) `)
 THEN RW_TAC real_ss[]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `LENGTH ((Q::L2):('a ->bool)list)`)
 THEN RW_TAC real_ss[]
 THEN FULL_SIMP_TAC list_ss[PERM_REFL,big_inter_def]
 THEN (`(p_space p INTER (Q INTER big_inter p ((L2:('a ->bool)list)))) = (Q INTER big_inter p (L2))` by MATCH_MP_TAC INTER_PSPACE)
 THEN1( RW_TAC std_ss[]
  THEN MATCH_MP_TAC EVENTS_INTER
  THEN RW_TAC std_ss[]
  THEN MATCH_MP_TAC in_events_big_inter
  THEN FULL_SIMP_TAC std_ss[])
 THEN ONCE_ASM_REWRITE_TAC[]
 THEN RW_TAC std_ss[]
 THEN RW_TAC std_ss[list_prob_def,list_prod_def])
THEN Induct_on `n`
   THEN1(RW_TAC real_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def]
   THEN FULL_SIMP_TAC std_ss[APPEND,LENGTH,LE_SUC]
    THEN1 (NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `L2:('a ->bool)list`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `Q:('a ->bool)`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `0:num`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
     THEN RW_TAC std_ss[]
     THEN FULL_SIMP_TAC std_ss[]
     THEN (`mutual_indep p (L1 ++ Q::L2) /\
      (!x. MEM x (L1 ++ Q::L2) ==> x IN events p)` by STRIP_TAC)
      THEN1( MATCH_MP_TAC mutual_indep_cons
       THEN EXISTS_TAC (--`h:'a  event`--)
       THEN RW_TAC std_ss[])
      THEN1 (RW_TAC std_ss[]
      THEN FULL_SIMP_TAC list_ss[])
     THEN FULL_SIMP_TAC std_ss[]
     THEN FULL_SIMP_TAC list_ss[]
     THEN FULL_SIMP_TAC list_ss[big_inter_def]
     THEN RW_TAC real_ss[list_prob_def,list_prod_def])
  THEN FULL_SIMP_TAC std_ss[parallel_rbd_lem2]
  THEN FULL_SIMP_TAC list_ss[APPEND,LENGTH_NIL])
THEN RW_TAC std_ss[compl_list_def,MAP,TAKE_def,HD,TL,big_inter_def]
THEN RW_TAC std_ss[INTER_ASSOC]
THEN ONCE_REWRITE_TAC[parallel_rbd_lem3]
THEN RW_TAC std_ss[GSYM compl_list_def]
THEN RW_TAC std_ss[parallel_rbd_lem4]
THEN (`prob p
  (big_inter p (TAKE n (compl_list p (L1:('a ->bool) list))) INTER  Q INTER   big_inter p (L2:('a ->bool) list) INTER
   p_space p DIFF
   big_inter p (TAKE n (compl_list p L1)) INTER  (Q:('a ->bool)) INTER  big_inter p L2 INTER   h) = prob p
  (big_inter p (TAKE n (compl_list p L1)) INTER  Q INTER   big_inter p L2 INTER
   p_space p) -  prob p
   (big_inter p (TAKE n (compl_list p L1)) INTER  Q INTER   big_inter p L2 INTER   h) ` by MATCH_MP_TAC prob_compl_subset)
THEN1(RW_TAC std_ss[]
 THEN1(MATCH_MP_TAC EVENTS_INTER
  THEN RW_TAC std_ss[]
  THEN1(MATCH_MP_TAC EVENTS_INTER
   THEN RW_TAC std_ss[]
   THEN1(MATCH_MP_TAC EVENTS_INTER
     THEN RW_TAC std_ss[]
     THEN1(MATCH_MP_TAC in_events_big_inter
      THEN RW_TAC std_ss[]
      THEN (`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
      THEN1(EXISTS_TAC(--`n:num`--)
       THEN RW_TAC std_ss[])
      THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      THEN MATCH_MP_TAC EVENTS_COMPL
      THEN RW_TAC std_ss[]
      THEN FULL_SIMP_TAC list_ss[])
     THEN FULL_SIMP_TAC list_ss[])
    THEN MATCH_MP_TAC in_events_big_inter
     THEN RW_TAC std_ss[]
     THEN FULL_SIMP_TAC list_ss[])
 THEN MATCH_MP_TAC EVENTS_SPACE
 THEN RW_TAC std_ss[])
THEN1 (MATCH_MP_TAC EVENTS_INTER
 THEN RW_TAC std_ss[]
 THEN1 (MATCH_MP_TAC EVENTS_INTER
  THEN RW_TAC std_ss[]
  THEN1(MATCH_MP_TAC EVENTS_INTER
   THEN RW_TAC std_ss[]
   THEN1(MATCH_MP_TAC in_events_big_inter
    THEN RW_TAC std_ss[]
    THEN(`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
    THEN1(EXISTS_TAC(--`n:num`--)
     THEN RW_TAC std_ss[])
    THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
    THEN MATCH_MP_TAC EVENTS_COMPL
    THEN RW_TAC std_ss[]
    THEN FULL_SIMP_TAC list_ss[])
   THEN FULL_SIMP_TAC list_ss[])
  THEN MATCH_MP_TAC in_events_big_inter
  THEN RW_TAC std_ss[]
  THEN FULL_SIMP_TAC list_ss[])
 THEN FULL_SIMP_TAC list_ss[])
THEN (`big_inter p L2 INTER p_space p =  big_inter p L2` by ONCE_REWRITE_TAC [INTER_COMM])
THEN1(MATCH_MP_TAC INTER_PSPACE
 THEN RW_TAC std_ss[]
 THEN MATCH_MP_TAC in_events_big_inter
 THEN RW_TAC std_ss[]
 THEN FULL_SIMP_TAC list_ss[])
THEN RW_TAC std_ss[GSYM INTER_ASSOC]
THEN POP_ORW
THEN RW_TAC std_ss[INTER_ASSOC,INTER_SUBSET])
THEN POP_ORW
THEN (`(prob p
           (big_inter p (TAKE n (compl_list p L1)) INTER
            big_inter p (Q::L2)) =
         list_prod (list_prob p (TAKE n (compl_list p L1))) *
         list_prod (list_prob p (Q::L2)))` by ALL_TAC)
THEN1( NTAC 5(POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `L2:('a ->bool)list`)
 THEN RW_TAC std_ss[]
 THEN NTAC 5 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `Q:('a ->bool)`)
 THEN RW_TAC std_ss[]
 THEN NTAC 5 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
 THEN RW_TAC std_ss[]
 THEN NTAC 5 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
 THEN RW_TAC std_ss[]
 THEN FULL_SIMP_TAC std_ss[]
 THEN (`mutual_indep p (L1 ++ Q::L2) /\
 (!x. MEM x (L1 ++ Q::L2) ==> x IN events p)` by STRIP_TAC)
 THEN1( MATCH_MP_TAC mutual_indep_cons
  THEN EXISTS_TAC (--`h:'a  event`--)
  THEN FULL_SIMP_TAC list_ss[])
  THEN1 (RW_TAC std_ss[]
   THEN FULL_SIMP_TAC list_ss[])
 THEN FULL_SIMP_TAC std_ss[]
 THEN (` LENGTH (h::L1 ++ Q::L2) =  LENGTH (h::(L1 ++ Q::L2))` by RW_TAC list_ss[])
 THEN FULL_SIMP_TAC std_ss[]
 THEN POP_ASSUM (K ALL_TAC)
 THEN FULL_SIMP_TAC std_ss[LENGTH]
 THEN FULL_SIMP_TAC std_ss[LE_SUC]
 THEN FULL_SIMP_TAC list_ss[])
 THEN (`big_inter p (TAKE n (compl_list p L1)) INTER Q INTER big_inter p L2 INTER p_space p = big_inter p (TAKE n (compl_list p L1)) INTER big_inter p (Q::L2)` by RW_TAC list_ss[big_inter_def])
 THEN1( RW_TAC std_ss[GSYM INTER_ASSOC]
  THEN (`big_inter p L2 INTER p_space p =  big_inter p L2` by ONCE_REWRITE_TAC [INTER_COMM])
  THEN1(MATCH_MP_TAC INTER_PSPACE
   THEN RW_TAC std_ss[]
   THEN MATCH_MP_TAC in_events_big_inter
   THEN RW_TAC std_ss[]
   THEN FULL_SIMP_TAC list_ss[])
  THEN POP_ORW
  THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN POP_ASSUM (K ALL_TAC)
THEN POP_ASSUM (K ALL_TAC)
THEN NTAC 5(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `h::L2:('a ->bool)list`)
THEN RW_TAC std_ss[]
THEN NTAC 5 (POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `Q:('a ->bool)`)
THEN RW_TAC std_ss[]
THEN NTAC 5 (POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN NTAC 5 (POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
THEN RW_TAC std_ss[]
THEN FULL_SIMP_TAC std_ss[]
THEN (`mutual_indep p (L1 ++ Q::h::L2) /\
(!x. MEM x (L1 ++ Q::h::L2) ==> x IN events p)` by STRIP_TAC)
THEN1( MATCH_MP_TAC mutual_indep_cons_append1
 THEN FULL_SIMP_TAC list_ss[])
 THEN1 (RW_TAC std_ss[]
  THEN FULL_SIMP_TAC list_ss[])
 THEN FULL_SIMP_TAC std_ss[]
 THEN (` LENGTH (L1 ++ Q::h::L2) =  LENGTH (h::L1 ++ Q::L2)` by RW_TAC list_ss[])
 THEN FULL_SIMP_TAC std_ss[]
 THEN POP_ASSUM (K ALL_TAC)
 THEN (`(big_inter p (TAKE n (compl_list p L1)) INTER Q INTER big_inter p L2 INTER h) =(big_inter p (TAKE n (compl_list p L1)) INTER big_inter p (Q::h::L2)) ` by RW_TAC list_ss[big_inter_def] )
 THEN1(`(h INTER big_inter p L2) = (big_inter p L2 INTER h)` by RW_TAC std_ss[INTER_COMM]
 THEN POP_ORW
 THEN RW_TAC std_ss[INTER_ASSOC])
THEN FULL_SIMP_TAC std_ss[]
THEN POP_ASSUM (K ALL_TAC)
THEN POP_ASSUM (K ALL_TAC)
THEN RW_TAC list_ss[list_prob_def,list_prod_def]
THEN (`prob p (p_space p DIFF h) = 1 - prob p (h)` by MATCH_MP_TAC PROB_COMPL)
THEN1(FULL_SIMP_TAC list_ss[])
THEN POP_ORW
THEN REAL_ARITH_TAC);


(*-------------prob_big_inter_compl_list--------------*)
val prob_big_inter_compl_list = store_thm("prob_big_inter_compl_list",``!(L1:('a ->bool) list) n p . prob_space p  /\ mutual_indep p (L1) /\ (!x. MEM x (L1) ==> x IN events p ) /\ 1 <=  (LENGTH (L1)) ==> (prob p (big_inter p (TAKE (n)(compl_list p L1) )) =
        list_prod (list_prob p (TAKE (n)(compl_list p L1) )))``,
Induct
>> (RW_TAC std_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def,PROB_UNIV])
++ Induct_on `n`
>>(RW_TAC std_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def,PROB_UNIV])
++ RW_TAC std_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def,PROB_UNIV]
++ RW_TAC std_ss[GSYM compl_list_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[parallel_rbd_lem6]
++ (`prob p
  (big_inter p (TAKE n (compl_list p (L1:('a ->bool) list))) INTER  p_space p DIFF
   big_inter p (TAKE n (compl_list p L1)) INTER  (h:('a ->bool)) ) = prob p
  (big_inter p (TAKE n (compl_list p L1)) INTER  p_space p ) - prob p (big_inter p (TAKE n (compl_list p L1)) INTER  h)` by MATCH_MP_TAC prob_compl_subset)
>> (RW_TAC std_ss[]
   >> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[]
   >> (MATCH_MP_TAC in_events_big_inter
      ++ RW_TAC std_ss[]
      ++(`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
      >> (EXISTS_TAC(--`n:num`--)
         ++ RW_TAC std_ss[])
      ++ FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      ++ MATCH_MP_TAC EVENTS_COMPL
      ++ RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   ++ RW_TAC std_ss [EVENTS_SPACE])
   >>(MATCH_MP_TAC EVENTS_INTER
      ++ RW_TAC std_ss[]
      >>(MATCH_MP_TAC in_events_big_inter
         ++ RW_TAC std_ss[]
         ++(`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
         >> (EXISTS_TAC(--`n:num`--)
            ++ RW_TAC std_ss[])
            ++ FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
            ++ MATCH_MP_TAC EVENTS_COMPL
            ++ RW_TAC std_ss[]
            ++ FULL_SIMP_TAC list_ss[])
         ++ FULL_SIMP_TAC list_ss[])
   ++ (`big_inter p (TAKE n (compl_list p L1)) INTER p_space p =  big_inter p (TAKE n (compl_list p L1))` by ONCE_REWRITE_TAC [INTER_COMM])
   >> (MATCH_MP_TAC INTER_PSPACE
      ++ RW_TAC std_ss[]
      ++ MATCH_MP_TAC in_events_big_inter
      ++ RW_TAC std_ss[]
      ++(`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
      >> (EXISTS_TAC(--`n:num`--)
          ++ RW_TAC std_ss[])
          ++ FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
          ++ MATCH_MP_TAC EVENTS_COMPL
          ++ RW_TAC std_ss[]
          ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ POP_ORW
++ (`big_inter p (TAKE n (compl_list p L1)) INTER p_space p =  big_inter p (TAKE n (compl_list p L1))` by ONCE_REWRITE_TAC [INTER_COMM])
>> (MATCH_MP_TAC INTER_PSPACE
   ++ RW_TAC std_ss[]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC std_ss[]
   ++(`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC parallel_rbd_lem5)
   >> (EXISTS_TAC(--`n:num`--)
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ NTAC 5 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
++ RW_TAC std_ss[]
++ NTAC 5 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`mutual_indep p L1 /\ (!x. MEM x L1 ==> x IN events p)` by STRIP_TAC)
>>(MATCH_MP_TAC mutual_indep_cons
   ++ EXISTS_TAC(--`h:'a  event`--)
   ++ RW_TAC std_ss[])
>> (RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[LENGTH,LE_SUC]
>> (FULL_SIMP_TAC std_ss[]
   ++ (`(prob p (big_inter p (TAKE (n)(compl_list p L1) ) INTER  big_inter p ((h::[]) )) =
        list_prod (list_prob p (TAKE (n)(compl_list p L1) )) * list_prod (list_prob p ((( h::[]):('a ->bool) list) )))` by MATCH_MP_TAC prob_indep_big_inter1)
   >> (RW_TAC std_ss[]
      >> (MATCH_MP_TAC mutual_indep_cons_swap
         ++ RW_TAC std_ss[])
      >> ( FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC(--`LENGTH (L1:'a  event list)`--)
   ++ RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[big_inter_def]
++ (`h INTER p_space p = h` by ONCE_REWRITE_TAC[INTER_COMM])
>> (MATCH_MP_TAC INTER_PSPACE
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC real_ss[list_prob_def,list_prod_def]
++ (`prob p (p_space p DIFF h) = 1 - prob p (h)` by MATCH_MP_TAC PROB_COMPL)
>> (FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ REAL_ARITH_TAC)
++ FULL_SIMP_TAC std_ss[LENGTH_NIL]
++ RW_TAC real_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def,PROB_UNIV]
++ (`p_space p INTER h = h` by MATCH_MP_TAC INTER_PSPACE)
>> (FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ (`prob p (p_space p DIFF h) = 1 - prob p (h)` by MATCH_MP_TAC PROB_COMPL)
>> (FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ REAL_ARITH_TAC);

(*---------------mutual_indep_compl_event_imp_norm_event-------------*)
val mutual_indep_compl_event_imp_norm_event = store_thm("mutual_indep_compl_event_imp_norm_event",
``!(L1:('a ->bool) list) p. 
	   prob_space p /\
	   mutual_indep p (compl_list p L1) /\
	   (!x. MEM x (L1) ==> x IN events p ) /\
	   1 <=  (LENGTH (L1)) ==> 
	      mutual_indep p L1 ``,
RW_TAC std_ss[mutual_indep_def]
++ (`(L1':('a ->bool) list) =  compl_list p (compl_list p L1')` by MATCH_MP_TAC parallel_rbd_lem7)
>> (FULL_SIMP_TAC list_ss[]
   ++ (`(!x. MEM x L1 = MEM x (L1':('a ->bool) list))` by MATCH_MP_TAC PERM_MEM_EQ)
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ MATCH_MP_TAC prob_big_inter_compl_list
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[mutual_indep_def]
   ++ NTAC 8 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L1'':('a ->bool) list`)
   ++ RW_TAC std_ss[]
   ++ NTAC 8 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `n':num`)
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ (` PERM (compl_list p L1) (L1'':('a ->bool) list) /\ (n' <= LENGTH (compl_list p (L1:'a  event list)))` by STRIP_TAC)
   >> (MATCH_MP_TAC PERM_TRANS
      ++ EXISTS_TAC(--`(compl_list p L1')`--)
      ++ RW_TAC std_ss[compl_list_def]
      ++ MATCH_MP_TAC PERM_MAP
      ++ RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[compl_list_def,LENGTH_MAP]
      ++ (`LENGTH (L1:('a ->bool) list) =  LENGTH (L1':('a ->bool) list)` by MATCH_MP_TAC PERM_LENGTH)
      >> (RW_TAC std_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[])
>> (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x L1 = MEM x (L1':('a ->bool) list))` by MATCH_MP_TAC PERM_MEM_EQ)
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ RW_TAC std_ss[compl_list_def,LENGTH_MAP]
++ (`LENGTH (L1:('a ->bool) list) =  LENGTH (L1':('a ->bool) list)` by MATCH_MP_TAC PERM_LENGTH)
>> (RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*--------mutual_indep_compl--------------------*)
val mutual_indep_compl =  store_thm("mutual_indep_compl",
``!(L1:('a ->bool) list) p. 
	   prob_space p /\ 
	   mutual_indep p L1 /\ 
	   (!x. MEM x (L1) ==> x IN events p ) /\
	    1 <=  (LENGTH (L1)) ==> 
	      mutual_indep p (compl_list p L1)``,
RW_TAC std_ss[]
++ MATCH_MP_TAC mutual_indep_compl_event_imp_norm_event
++ RW_TAC std_ss[]
>> ((`compl_list p (compl_list p L1) = (L1:('a ->bool) list)` by MATCH_MP_TAC EQ_SYM)
   >> (MATCH_MP_TAC parallel_rbd_lem7
      ++ RW_TAC std_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[compl_list_def,LENGTH_MAP]);
(*------------------------------------*)
(*------Parallel RBD Configuration----*)
(*------------------------------------*)

(*------Parallel_Lemma1----*)
val parallel_lem1 = store_thm("parallel_lem1",``!p s t. p_space p DIFF (s UNION t) = (p_space p DIFF s) INTER (p_space p DIFF t)``,
SRW_TAC [][EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------- parallel_lem2---------------*)
val parallel_lem2 = store_thm("parallel_lem2",``!p  (L:('a  -> bool) list).  prob_space p /\ (!x. MEM x L ==> x IN  events p)  ==>
         ( rbd_struct p (series (rbd_list (compl_list p L))) = p_space p DIFF (rbd_struct p ( parallel (rbd_list L)) ))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,rbd_list_def,rbd_struct_def,DIFF_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[compl_list_def,rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM compl_list_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[parallel_lem1]);
(*------------parallel_lem3-------------*)
val parallel_lem3 = store_thm("parallel_lem3",``!L p. (!x. MEM x L ==> x IN events p) /\
prob_space p ==>
  (rbd_struct p (parallel (rbd_list L)) IN events p)``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[compl_list_def,rbd_list_def,rbd_struct_def,EVENTS_EMPTY])
++ RW_TAC std_ss[rbd_list_def,MAP, rbd_struct_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ MATCH_MP_TAC EVENTS_UNION
++ FULL_SIMP_TAC list_ss[]);
(*----------------parallel_lem4----------------------*)
val parallel_lem4 = store_thm("parallel_lem4",``!p L. (!x. MEM x L ==> x IN events p) /\
prob_space p /\
  ((rbd_struct p (parallel (rbd_list L))) IN events p) ==> ((rbd_struct p (parallel (rbd_list L))) SUBSET p_space p )``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,rbd_list_def,rbd_struct_def]
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF, NOT_IN_EMPTY])
++ RW_TAC std_ss[compl_list_def,MAP,rbd_list_def,rbd_struct_def]
++ RW_TAC std_ss[UNION_SUBSET]
>> ((`h = h INTER p_space p` by MATCH_MP_TAC EQ_SYM)
   >> (ONCE_REWRITE_TAC[INTER_COMM]
      ++ MATCH_MP_TAC INTER_PSPACE
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ FULL_SIMP_TAC std_ss[]
++ (`(!x. MEM x L ==> x IN events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[parallel_lem3]);
(*----------------parallel_lem5----------------------*)
val parallel_lem5 = store_thm("parallel_lem5",``!p L. rbd_struct p (series (rbd_list L)) = big_inter p L``,
 RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,big_inter_def])
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,big_inter_def]);

(*-----------------parallel_lem6---------------------*)

val parallel_lem6 = store_thm("parallel_lem6",``!p x L.  prob_space p /\ (!x'. MEM x' L ==> x' IN events p)                                ==>
(prob p (rbd_struct p (parallel (rbd_list L))) = 1 - prob p (rbd_struct p (series (rbd_list (compl_list p ( L))))))``,
RW_TAC std_ss[]
++ (`rbd_struct p (parallel (rbd_list L)) SUBSET p_space p` by MATCH_MP_TAC  parallel_lem4)
>> (RW_TAC std_ss[]
   ++ MATCH_MP_TAC parallel_lem3
   ++ RW_TAC std_ss[])
++  (`(1 - prob p (rbd_struct p (series (rbd_list (compl_list p L)))))  = (prob p (p_space p DIFF (rbd_struct p (series (rbd_list (compl_list p L))))))` by MATCH_MP_TAC EQ_SYM)
>> (MATCH_MP_TAC PROB_COMPL
   ++  RW_TAC std_ss[]
   ++  RW_TAC std_ss[parallel_lem5]
   ++  MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC list_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[]
++ RW_TAC std_ss[parallel_lem2]
++ RW_TAC std_ss[DIFF_DIFF_SUBSET]);
(*--------------parallel_lem7----------------------*)
val parallel_lem7 = store_thm("parallel_lem7",``!p (L). prob_space p /\ (!x'. MEM x' L ==> x'  IN  events p )   ==> (one_minus_list (list_prob p L) = list_prob p ( compl_list p L))``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC std_ss[one_minus_list_def,compl_list_def,MAP,list_prob_def])
++ RW_TAC std_ss[one_minus_list_def,compl_list_def,MAP,list_prob_def]
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC PROB_COMPL
   ++ FULL_SIMP_TAC list_ss[])
++ (`(!x'. MEM x' L ==> x' IN events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM compl_list_def]);
(*------------------------------------*)
val parallel_lem8 = store_thm("parallel_lem8",
  `` !L. one_minus_list L =  MAP (\a. 1 - a) L ``,
Induct
++ RW_TAC list_ss[one_minus_list_def]);
(*------------------------------------*)
(*-----------Parallel_struct_thm------*)
(*------------------------------------*)
val parallel_struct_thm = store_thm("parallel_struct_thm", ``!p L . ~NULL L /\ (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ mutual_indep p L  ==> (prob p (rbd_struct p (parallel (rbd_list L))) =
       1 -  list_prod (one_minus_list (list_prob p L)))``,
RW_TAC real_ss[parallel_lem6,real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
++ (`prob p (rbd_struct p (series (rbd_list (compl_list p L)))) = list_prod (list_prob p (compl_list p L))` by MATCH_MP_TAC series_struct_thm)
>> (RW_TAC std_ss[]
   >> (RW_TAC std_ss[GSYM LENGTH_NOT_NULL]
       ++ RW_TAC std_ss[compl_list_def,LENGTH_MAP]
       ++ RW_TAC std_ss[LENGTH_NOT_NULL])
   >> (FULL_SIMP_TAC list_ss[compl_list_def,MEM_MAP]
      ++ MATCH_MP_TAC EVENTS_COMPL
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC mutual_indep_compl
   ++ FULL_SIMP_TAC list_ss[]
   ++ Cases_on `L`
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[parallel_lem7]);

(*------------------------------------*)
(*  Parallel-series RBD Configuration *)
(*------------------------------------*)

(*------------------------------------*)
(*------Parallel-Series Lemma's-------*)
(*------------------------------------*)
(*------parallel_series_lem1---------*)
val parallel_series_lem1 = store_thm("parallel_series_lem1", ``!l1 l2 l3 l4.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (l1 ++ l4) = PERM (l2++(l4++l3)))``,
REPEAT STRIP_TAC
++ MP_TAC (Q.SPECL [`l1`, `l4`, `l2++l4`, `l3`] PERM_CONG)
++ RW_TAC list_ss[GSYM PERM_EQUIVALENCE_ALT_DEF]
++ ONCE_REWRITE_TAC[PERM_SYM]
++ MATCH_MP_TAC APPEND_PERM_SYM
++ ONCE_REWRITE_TAC[PERM_SYM]
++ RW_TAC list_ss[PERM_APPEND_IFF,PERM_APPEND]);
(*-----mutual_indep_flat_cons1------------*)
val mutual_indep_flat_cons1 = store_thm("mutual_indep_flat_cons1",``!L1 h L p. mutual_indep p (FLAT ((h::L1)::L)) ==> mutual_indep p (FLAT (L1::[h]::L))``,
RW_TAC list_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ (` PERM (h::(L1 ++ FLAT (L:('a ->bool) list list))) L1'` by MATCH_MP_TAC PERM_TRANS)
>> (EXISTS_TAC (--` (L1 ++ h::FLAT (L:('a ->bool) list list)) `--)
   ++ RW_TAC list_ss[PERM_EQUIVALENCE_ALT_DEF,PERM_FUN_APPEND_CONS])
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC arith_ss[]);
(*-----------mutual_indep_flat_cons2-------------------------*)
val mutual_indep_flat_cons2 = store_thm("mutual_indep_flat_cons2",``!L1 h L p.  mutual_indep p (FLAT (L1::h::L)) ==> mutual_indep p (FLAT (h::L))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ L1 `)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ L1):('a ->bool) list) = (TAKE n (L1')) ` by MATCH_MP_TAC TAKE_APPEND1)
>> ((`LENGTH (FLAT ((h::L):('a ->bool) list list)) = LENGTH (L1':('a ->bool) list) ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (` n <= LENGTH (FLAT ((L1::h::L):('a ->bool) list list)) ` by MATCH_MP_TAC LESS_EQ_TRANS)
>> (EXISTS_TAC(--` LENGTH (FLAT ((h::L):('a ->bool) list list))`--)
   ++  RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (` PERM (FLAT ((L1::h::L):('a ->bool) list list)) ((L1 ++ L1')) ` by RW_TAC list_ss[])
>> (ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
   ++ RW_TAC list_ss[PERM_APPEND_IFF]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (` PERM (FLAT ((L1::h::L):('a ->bool) list list)) ((L1' ++ L1)) ` by MATCH_MP_TAC PERM_TRANS)
>> (EXISTS_TAC(--` (L1 ++ L1'):('a ->bool)  list`--)
   ++ RW_TAC list_ss[PERM_APPEND])
++ RW_TAC std_ss[]);
(*----mutual_indep_flat_append--------*)
val mutual_indep_flat_append = store_thm("mutual_indep_flat_append",``!L L1 L2 p.  mutual_indep p (FLAT (L1::L2::L)) ==>  mutual_indep p ((L1 ++ L2))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++  FLAT L  `)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ FLAT L):('a ->bool) list) = (TAKE n (L1')) `by MATCH_MP_TAC TAKE_APPEND1)
>> ((`LENGTH ( ((L1 ++ L2):('a ->bool) list)) = LENGTH (L1':('a ->bool) list)  ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ (`PERM (FLAT (L1::L2::L):'a  event list) (L1' ++ FLAT L) /\
      n <= LENGTH (FLAT (L1::L2::L):'a  event list)`by STRIP_TAC)
>> (RW_TAC list_ss[]
   ++ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
   ++ RW_TAC list_ss[PERM_APPEND_IFF]
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC(--`LENGTH ( ((L1 ++ L2):('a ->bool) list))`--)
   ++  RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*------------mutual_indep_flat_cons3-----------------*)
val mutual_indep_flat_cons3 = store_thm("mutual_indep_flat_cons3",``!L L1 L2 p.  mutual_indep p (FLAT (L1::L2::L)) ==>  mutual_indep p ((L1))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ L2 ++ FLAT L `)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ L2 ++ FLAT L):('a ->bool) list) = (TAKE n (L1'))  `by ONCE_REWRITE_TAC[GSYM APPEND_ASSOC])
>> ( MATCH_MP_TAC TAKE_APPEND1
   ++ (`LENGTH ( ((L1):('a ->bool) list)) = LENGTH (L1':('a ->bool) list) ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (`PERM (FLAT (L1::L2::L):('a ->bool) list) (L1' ++ L2 ++ FLAT L) /\
      n <= LENGTH (FLAT (L1::L2::L):('a ->bool) list)` by STRIP_TAC)
>> ( ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
   ++ RW_TAC list_ss[PERM_APPEND_IFF])
>> (MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC(--`LENGTH ( ((L1):('a ->bool) list))`--)
   ++  RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*-------mutual_indep_flat_cons3---*)
val mutual_indep_flat_cons3 = store_thm("mutual_indep_flat_cons3",``!L1 h L p.  mutual_indep p (FLAT (L1::h::L)) ==> mutual_indep p (FLAT (L1::L))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ h `)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ h):('a ->bool) list) = (TAKE n (L1'))  `by ALL_TAC)
>> ( MATCH_MP_TAC TAKE_APPEND1
   ++ (`LENGTH (FLAT ((L1::L):('a ->bool) list list)) = LENGTH (L1':('a ->bool) list)  ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (`PERM (FLAT (L1::h::L):('a ->bool) list) ((L1' ++ h)) /\
      n <= LENGTH (FLAT (L1::h::L):('a ->bool) list)` by STRIP_TAC)
>> (RW_TAC list_ss[]
   ++ ONCE_REWRITE_TAC[PERM_SYM,GSYM APPEND_ASSOC]
   ++ RW_TAC list_ss[PERM_EQUIVALENCE_ALT_DEF]
   ++ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
   ++ MATCH_MP_TAC parallel_series_lem1
   ++ RW_TAC list_ss[GSYM PERM_EQUIVALENCE_ALT_DEF,PERM_SYM]
   ++ FULL_SIMP_TAC list_ss[]
   ++ ONCE_REWRITE_TAC[PERM_SYM]
   ++ RW_TAC list_ss[])
>> (MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC(--`LENGTH (FLAT ((L1::L):('a ->bool) list list))`--)
   ++  RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*---------mutual_indep_flat_append1----*)
val mutual_indep_flat_append1 = store_thm("mutual_indep_flat_append1",``!L h L1 p. mutual_indep p (FLAT (L1::h::L)) ==> mutual_indep p (FLAT ((h ++ L1)::L))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `(L1':('a ->bool) list )  `)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (` PERM ((L1 ++ h ++ FLAT L):('a ->bool) list) (L1')` by MATCH_MP_TAC PERM_TRANS)
>> (EXISTS_TAC (--`(h ++ L1 ++ (FLAT (L))):('a ->bool) list`--)
   ++ RW_TAC std_ss[]
   >> (RW_TAC std_ss[PERM_APPEND_IFF]
      ++ RW_TAC std_ss[PERM_APPEND])
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC list_ss[]);

(*-------mutual_indep_front_append------*)
val mutual_indep_front_append = store_thm("mutual_indep_front_append",``!L1 L p.  mutual_indep p (L1 ++ L) ==> mutual_indep p L``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ L1`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`PERM ((L1 ++ L):'a  event list) (L1' ++ L1) /\ n <= LENGTH (L1 ++ L)` by STRIP_TAC)
>> (MATCH_MP_TAC APPEND_PERM_SYM
   ++ RW_TAC list_ss[PERM_APPEND_IFF])
>> (MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC (--`LENGTH (L:'a  event list)`--)
   ++ RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ L1)) = TAKE n (L1':('a ->bool) list) `by ALL_TAC)
>> ( MATCH_MP_TAC TAKE_APPEND1
   ++ (`LENGTH L = LENGTH (L1': 'a  event list)  ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*--------mutual_indep_FLAT_front_cons----*)

val mutual_indep_FLAT_front_cons = store_thm("mutual_indep_FLAT_front_cons",``!h L p.  mutual_indep p (FLAT (h::L)) ==> mutual_indep p (FLAT (L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`h:'a  event list`--)
++ RW_TAC std_ss[]);
(*--------mutual_indep_append1------*)
val mutual_indep_append1 = store_thm("mutual_indep_append1",``!L1 L2 L p.  mutual_indep p (L1++L2++L) ==> mutual_indep p (L2++L1++L)``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`PERM ((L1 ++ L2 ++ L):'a  event list) (L1') /\
      n <= LENGTH ((L1 ++ L2 ++ L):'a  event list)` by STRIP_TAC)
>> (MATCH_MP_TAC PERM_TRANS
   ++ EXISTS_TAC(--`(L2 ++ L1 ++ L):'a  event list`--)
   ++ RW_TAC std_ss[PERM_APPEND_IFF,PERM_APPEND])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*----------mutual_indep_flat_cons4-------*)
val mutual_indep_flat_cons4 = store_thm("mutual_indep_flat_cons4",``!L1 h L p.  mutual_indep p (FLAT (L1::h::L)) ==> mutual_indep p (FLAT (L1::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`h:'a  event list`--)
++ RW_TAC list_ss[]
++ MATCH_MP_TAC  mutual_indep_append1
++ RW_TAC list_ss[]);
(*----------mutual_indep_append_sym------*)
val mutual_indep_append_sym = store_thm("mutual_indep_append_sym",``!L1 L p.  mutual_indep p (L1++L) ==> mutual_indep p (L++L1)``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`PERM ((L1 ++ L):'a  event list) (L1') /\
      n <= LENGTH ((L1 ++ L):'a  event list)` by STRIP_TAC)
>> (MATCH_MP_TAC PERM_TRANS
   ++ EXISTS_TAC(--`( L ++ L1):'a  event list`--)
   ++ RW_TAC std_ss[PERM_APPEND])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*-------mutual_indep_flat_cons5--------*)
val mutual_indep_flat_cons5 = store_thm("mutual_indep_flat_cons5",``!L L1 L2 p.  mutual_indep p (FLAT (L1::L2::L)) ==>  mutual_indep p ((L1))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--` L2 ++ FLAT L:'a  event list`--)
++ RW_TAC std_ss[]
++ MATCH_MP_TAC mutual_indep_append_sym
++ RW_TAC std_ss[APPEND_ASSOC]);
(*-----------mutual_indep_flat_append1----*)
val mutual_indep_FLAT_append1 = store_thm("mutual_indep_FLAT_append1",``!L L1 L2 p.  mutual_indep p (FLAT (L1::L2::L)) ==>  mutual_indep p ((L1 ++ L2))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`FLAT L:'a  event list`--)
++ MATCH_MP_TAC mutual_indep_append_sym
++ RW_TAC std_ss[]);
(*--------------mutual_indep_cons_append10----*)
val mutual_indep_cons_append10 = store_thm("mutual_indep_cons_append10",``!L1 h L p.  mutual_indep p (FLAT (L1::h::L)) ==> mutual_indep p (FLAT (h::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`L1:'a  event list`--)
++ RW_TAC list_ss[]);
(*------------mutual_indep_cons_append11-----------------------*)
val mutual_indep_cons_append11 = store_thm("mutual_indep_cons_append11",``!h L1 L2 L p. mutual_indep p (L1 ++ h::(L2 ++ L)) ==>
mutual_indep p (h::(L1 ++ L))``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ L2`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(TAKE n (L1' ++ L2):('a ->bool) list) = (TAKE n (L1'))  `by MATCH_MP_TAC TAKE_APPEND1)
>> ( (`LENGTH ( ((h::(L1 ++ L)):('a ->bool) list)) = LENGTH (L1':('a ->bool) list) ` by MATCH_MP_TAC PERM_LENGTH )
   >> (RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (` PERM ((L1 ++ h::(L2 ++ L)):('a ->bool) list) (L1' ++ L2) /\
      n <= LENGTH ((L1 ++ h::(L2 ++ L)):('a ->bool) list)` by STRIP_TAC)
>> (RW_TAC list_ss[PERM_EQUIVALENCE_ALT_DEF]
   ++ RW_TAC list_ss[PERM_FUN_APPEND_CONS]
   ++ RW_TAC std_ss[GSYM APPEND_ASSOC, GSYM APPEND]
   ++ RW_TAC std_ss[GSYM PERM_EQUIVALENCE_ALT_DEF]
   ++ MATCH_MP_TAC PERM_TRANS
   ++ EXISTS_TAC(--`((h::L1 ++ (L ++ L2)):'a  event list)`--)
   ++ RW_TAC std_ss[PERM_APPEND_IFF]
   >> (RW_TAC std_ss[PERM_APPEND])
   ++ RW_TAC std_ss[APPEND_ASSOC]
   ++ RW_TAC std_ss[PERM_APPEND_IFF]
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC LESS_EQ_TRANS
   ++ EXISTS_TAC(--`LENGTH ((h::(L1 ++ L)):'a  event list)`--)
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*--------mutual_indep_cons_append12---*)

val mutual_indep_cons_append12 = store_thm("mutual_indep_cons_append12",``!h L1 L2 L p.  mutual_indep p (FLAT (L1::(h::L2)::L)) ==> mutual_indep p (FLAT ((h::L1)::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_cons_append11
++ EXISTS_TAC(--`L2:'a  event list`--)
++ RW_TAC std_ss[]);

(*--------mutual_indep_cons_append13---*)
val mutual_indep_cons_append13 = store_thm("mutual_indep_cons_append13",``!L L1 L2 p.  mutual_indep p (FLAT (L1::L2::L)) ==>  mutual_indep p ((L1 ++ L2))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`FLAT L:'a  event list`--)
++ MATCH_MP_TAC mutual_indep_append_sym
++ RW_TAC std_ss[]);

(*--------mutual_indep_cons_append14---*)
val mutual_indep_cons_append14 = store_thm("mutual_indep_cons_append14",``!h L1 L p.  mutual_indep p (L1 ++ h::L) ==> mutual_indep p (L1 ++ L) ``,
RW_TAC std_ss[mutual_indep_def]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ [h]`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (` PERM (L1 ++ h::L) ((L1' ++ [h]):'a  event list)` by RW_TAC list_ss[PERM_EQUIVALENCE_ALT_DEF])
>> ((`PERM (L1 ++ h::L) = PERM (h::L1 ++ L)` by RW_TAC list_ss[PERM_FUN_APPEND_CONS])
   ++ POP_ORW
   ++ ONCE_REWRITE_TAC[CONS_APPEND]
   ++ (`PERM ((L1':('a ->bool) list ) ++ ([h] ++ [])) = PERM (([h] ++ L1'))` by RW_TAC list_ss[PERM_FUN_APPEND])
   ++ POP_ORW
   ++ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
   ++ MATCH_MP_TAC PERM_FUN_APPEND_IFF
   ++ RW_TAC list_ss[GSYM PERM_EQUIVALENCE_ALT_DEF])
++ FULL_SIMP_TAC std_ss[]
++ POP_ASSUM (K ALL_TAC)
++ (` n <=  LENGTH ((L1 ++ h::L):'a  event list)` by MATCH_MP_TAC LESS_EQ_TRANS)
>> (EXISTS_TAC(--`LENGTH ((L1 ++ L):'a  event list)`--)
   ++ RW_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ POP_ASSUM (K ALL_TAC)
++ `(TAKE n (L1' ++ [h]):('a ->bool) list) =(TAKE n (L1'))` by MATCH_MP_TAC TAKE_APPEND1
>> ((`LENGTH L1' = LENGTH ((L1 ++ L):'a  event list)` by MATCH_MP_TAC EQ_SYM)
   >> (MATCH_MP_TAC PERM_LENGTH
      ++ RW_TAC std_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*--------mutual_indep_cons_append15---*)
val mutual_indep_cons_append15 = store_thm("mutual_indep_cons_append15",``!h L1 L2 L p.  mutual_indep p (FLAT (L1::(h::L2)::L)) ==> mutual_indep p (FLAT ([(h)]::L))``,
RW_TAC list_ss[]
++ (`(h:: FLAT L) = (h:: ([] ++ FLAT L)):'a  event list ` by RW_TAC list_ss[])
++ POP_ORW
++ MATCH_MP_TAC mutual_indep_cons_append11
++ EXISTS_TAC (--`L2:'a  event list`--)
++ RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC (--`L1:'a  event list`--)
++ RW_TAC list_ss[]);

(*--------mutual_indep_cons_append16---*)
val mutual_indep_cons_append16 = store_thm("mutual_indep_cons_append16",
``!h L1 L2 L p.  mutual_indep p (FLAT (L1::(h::L2)::L)) ==> mutual_indep p (FLAT ([(h)]::L2::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC (--`L1:'a  event list`--)
++ RW_TAC list_ss[]);

(*-------mutual_indep_cons_append17-----------*)

val mutual_indep_cons_append17 = store_thm("mutual_indep_cons_append17",
  ``!h L1 L p.  mutual_indep p (FLAT ((h::L1)::L)) ==> mutual_indep p (FLAT ([(h)]::L))``,
RW_TAC list_ss[]
++ (`(h::FLAT L) =  (h::([]++FLAT L)):'a  event list` by RW_TAC list_ss[])
++ POP_ORW
++ MATCH_MP_TAC  mutual_indep_cons_append11
++ EXISTS_TAC(--`L1:'a  event list`--)
++ RW_TAC list_ss[])
(*-------mutual_indep_cons_append18-----------*)
val mutual_indep_cons_append18 = store_thm("mutual_indep_cons_append18",
  ``!h L1 L p.  mutual_indep p (FLAT ((h::L1)::L)) ==> mutual_indep p (FLAT (L1::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_cons
++ EXISTS_TAC(--`h:'a  event`--)
++ RW_TAC list_ss[]);

(*-------mutual_indep_cons_append19-----------*)
val mutual_indep_cons_append19 = store_thm("mutual_indep_cons_append19",
  ``!h L1 L p.  mutual_indep p (FLAT ((h::L1)::L)) ==> mutual_indep p (FLAT (L1::[h]::L))``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_cons_append
++ RW_TAC list_ss[]);

(*---------------------------------*)
val mutual_indep_flat_cons6 = store_thm("mutual_indep_flat_cons6",
  `` !h L1 L p.  mutual_indep p (FLAT ((h::L1)::L)) ==> mutual_indep p (FLAT [L1;[h]]) ``,
RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_cons_swap
++ RW_TAC list_ss[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC (--`FLAT L: 'a  event list`--)
++ MATCH_MP_TAC mutual_indep_append_sym
++ FULL_SIMP_TAC list_ss[]);
(*--------in_events_parallel_rbd---*)
val in_events_parallel_rbd = prove (``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p )==> (rbd_struct p (parallel (rbd_list L)) IN events p)``,
REPEAT GEN_TAC
++ Induct_on `L`
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,EVENTS_EMPTY])
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[]
++ MATCH_MP_TAC EVENTS_UNION
++ FULL_SIMP_TAC list_ss[]);




(*-------------------------------------------*)
(*   Parallel-Series RBD Lemmas              *)
(*-------------------------------------------*)

val in_events_parallel_series = store_thm("in_events_parallel_series",
  `` !p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p )==> (rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L)) IN events p) ``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ RW_TAC std_ss[EVENTS_EMPTY])
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ( `(!x. MEM x ((FLAT L):'a  event list) ==> x IN events p)` by RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ MATCH_MP_TAC EVENTS_UNION
++ RW_TAC std_ss[]
++ REWRITE_TAC[series_rbd_eq_big_inter]
++ MATCH_MP_TAC in_events_big_inter
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[]);

(*-------series_rbd_append----*)
val series_rbd_append = store_thm("series_rbd_append",
 ``!p h L1. prob_space p /\ (!x. MEM x (h++L1) ==> x IN events p )==> (rbd_struct p (series (rbd_list h)) INTER
rbd_struct p (series (rbd_list L1)) =
rbd_struct p (series (rbd_list (h ++ L1))))``,
REPEAT GEN_TAC
++ Induct_on `h`
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ MATCH_MP_TAC INTER_PSPACE
   ++ RW_TAC std_ss[series_rbd_eq_big_inter]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ (`(!x. MEM x ((h ++ L1):'a  event list) ==> x IN events p)` by RW_TAC std_ss[MEM_APPEND] )
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM INTER_ASSOC]);

(*-------inter_set_arrang1----*)
val inter_set_arrang1 = store_thm("inter_set_arrang1",
  ``!a b c d. a INTER b INTER c INTER d = a INTER (b INTER c) INTER d ``,
SRW_TAC [][IN_INTER,GSPECIFICATION,EXTENSION]
++ METIS_TAC[]);   

(*---MEM_NULL_arrang1--------*)
val MEM_NULL_arrang1 = store_thm("MEM_NULL_arrang1",
  ``!L1 L2 L. (!x. MEM x ((L1::L2::L):('a ->bool) list list)==> ~NULL x ) ==> (!x. MEM x ((L1++L2)::L)  ==>  ~NULL x)``,
RW_TAC list_ss[]
>> (POP_ASSUM (MP_TAC o Q.SPEC `L2 `)
   ++ RW_TAC list_ss[]
   ++ Induct_on `L1`
   >> (RW_TAC list_ss[])
   ++ RW_TAC list_ss[])
++ RW_TAC list_ss[]);

(*----series_rbd_append2----------*)

val series_rbd_append2 = store_thm("series_rbd_append2",
  ``!p h L1. prob_space p /\ (!x. MEM x (h++L1) ==> x IN events p ) /\ (~NULL h) /\ (~NULL L1) /\ mutual_indep p (h++L1) ==> (prob p (rbd_struct p (series (rbd_list (h ++ L1)))) = prob p (rbd_struct p (series (rbd_list (h)))) * prob p (rbd_struct p (series (rbd_list (L1)))))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def, rbd_struct_def])
++ RW_TAC std_ss[]
++ (`prob p (rbd_struct p (series (rbd_list (h'::h ++ L1))))= list_prod (list_prob p (h'::h ++ L1)) ` by MATCH_MP_TAC series_struct_thm )
>> (RW_TAC list_ss[])
++ POP_ORW
++ RW_TAC list_ss[list_prob_def,list_prod_def]
++ (`list_prod (list_prob p (h ++ L1)) = prob p (rbd_struct p (series (rbd_list (h ++ L1))))` by MATCH_MP_TAC EQ_SYM)
>> (MATCH_MP_TAC series_struct_thm
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[]
      ++ Cases_on `h`
      >> (RW_TAC list_ss[])
      ++ RW_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC mutual_indep_cons
   ++ EXISTS_TAC (--`h':'a  event`--)
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ (`(prob p (rbd_struct p (series (rbd_list (h ++ L1)))) =
         prob p (rbd_struct p (series (rbd_list h))) *
         prob p (rbd_struct p (series (rbd_list L1))))` by ALL_TAC)
>> (NTAC 5 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L1 `)
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,PROB_UNIV]
      ++ RW_TAC real_ss[])
   ++ FULL_SIMP_TAC std_ss[NULL]
   ++ (`(!x. MEM x ((h''::t ++ L1):'a  event list) ==> x IN events p) /\
      mutual_indep p (h''::t ++ L1)` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (MATCH_MP_TAC mutual_indep_cons
      ++ EXISTS_TAC (--`h':'a  event`--)
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ (`(prob p (rbd_struct p (series (rbd_list (h':: h)))) =
         prob p (rbd_struct p (series (rbd_list h))) *
         prob p (rbd_struct p (series (rbd_list [h']))))` by ALL_TAC)
>> (NTAC 5 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `[h'] `)
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,PROB_UNIV]
      ++ RW_TAC real_ss[])
   ++ FULL_SIMP_TAC std_ss[NULL]
   ++ (`(!x. MEM x ((h''::t ++ [h']):'a  event list) ==> x IN events p) /\
      mutual_indep p (h''::t ++ [h'])` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (MATCH_MP_TAC mutual_indep_cons_swap
      ++ RW_TAC std_ss[]
      ++ MATCH_MP_TAC mutual_indep_front_append
      ++ EXISTS_TAC(--`L1:'a  event list`--)
      ++ MATCH_MP_TAC mutual_indep_append_sym
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `(h''::t):'a  event list`, `[h']:'a  event list`] (GSYM series_rbd_append))
   ++ FULL_SIMP_TAC std_ss[]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ (`(rbd_struct p (series (rbd_list (h''::t))) INTER
         rbd_struct p (series (rbd_list [h']))) =(rbd_struct p (series (rbd_list (h'::h''::t)))) ` by RW_TAC list_ss[rbd_list_def,rbd_struct_def])
   >> ((`h' INTER p_space p = h'` by ONCE_REWRITE_TAC[INTER_COMM])
      >> (MATCH_MP_TAC INTER_PSPACE
      	 ++ FULL_SIMP_TAC list_ss[])
      ++ POP_ORW
      ++ RW_TAC std_ss[INTER_COMM])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++  RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ (`h' INTER p_space p = h'` by ONCE_REWRITE_TAC[INTER_COMM])
>> (MATCH_MP_TAC INTER_PSPACE
    ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[]
++ REAL_ARITH_TAC);

(*----series_rbd_indep_parallel_series_rbd---*)
val series_rbd_indep_parallel_series_rbd = store_thm(
  "series_rbd_indep_parallel_series_rbd",
  ``!p L L1. prob_space p /\(!x. MEM x (L1::L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L1::L):'a  event list list)) ==> x IN events p) /\ mutual_indep p (FLAT (L1::L)) ==> (prob p
  (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))) =  prob p
  (rbd_struct p (series (rbd_list L1)))*
   prob p (rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L)))) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def, INTER_EMPTY,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ (`rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (series (rbd_list h)) = rbd_struct p (series (rbd_list (h++L1)))` by ONCE_REWRITE_TAC[INTER_COMM])
>> (MATCH_MP_TAC series_rbd_append
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `rbd_struct p (series (rbd_list (h ++ L1)))`, ` rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))`] Prob_Incl_excl)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`rbd_struct p (series (rbd_list (h ++ L1))) IN events p /\
      rbd_struct p (series (rbd_list L1)) INTER
      rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L)) IN
      events p` by STRIP_TAC )
>> (REWRITE_TAC[series_rbd_eq_big_inter]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[]
   >> (REWRITE_TAC[series_rbd_eq_big_inter]
      ++ MATCH_MP_TAC in_events_big_inter
      ++ RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC in_events_parallel_series
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ NTAC 3 (POP_ASSUM (K ALL_TAC))
++  RW_TAC std_ss[INTER_ASSOC]
++  MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `h:'a  event list`, `L1:'a  event list`] (GSYM series_rbd_append))
++ RW_TAC std_ss[]
++ (` (!x. MEM x ((h ++ L1):'a  event list) ==> x IN events p)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[INTER_ASSOC]
++ NTAC 2 (POP_ASSUM (K ALL_TAC))
++ RW_TAC std_ss[inter_set_arrang1]
++ RW_TAC std_ss[INTER_IDEMPOT]
++ MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `h:'a  event list`, `L1:'a  event list`] (series_rbd_append))
++ RW_TAC std_ss[]
++ (` (!x. MEM x ((h ++ L1):'a  event list) ==> x IN events p)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++  NTAC 2 (POP_ASSUM (K ALL_TAC))
++ (`prob p
  (rbd_struct p (series (rbd_list (h ++ L1))) INTER
   rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))) = prob p
  (rbd_struct p (series (rbd_list (h ++ L1)))) *
   prob p (rbd_struct p (parallel (MAP (\ a. series (rbd_list a)) L)))` by ALL_TAC)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `h ++ L1 `)
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x (((h ++ L1)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ((h ++ L1)::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ((h ++ L1)::L)) ` by STRIP_TAC)
   >> (MATCH_MP_TAC MEM_NULL_arrang1
      ++ RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   >> (RW_TAC std_ss[]
      >> (FULL_SIMP_TAC list_ss[])
      ++ MATCH_MP_TAC mutual_indep_flat_append1
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ (`(prob p
           (rbd_struct p (series (rbd_list L1)) INTER
            rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))) =
         prob p (rbd_struct p (series (rbd_list L1))) *
         prob p
           (rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))))` by ALL_TAC)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L1 `)
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x ((L1::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT (L1::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT (L1::L))` by STRIP_TAC )
   >> (RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   >> (RW_TAC std_ss[]
      >> (FULL_SIMP_TAC list_ss[])
      ++ MATCH_MP_TAC mutual_indep_flat_cons4
      ++ EXISTS_TAC(--`h:'a event list`--)
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++  MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `rbd_struct p (series (rbd_list (h)))`, `
   rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))`] Prob_Incl_excl)
++ RW_TAC std_ss[]
++ (`rbd_struct p (series (rbd_list h)) IN events p /\ 
      rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L)) IN events p` by STRIP_TAC)
>> (REWRITE_TAC[series_rbd_eq_big_inter]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC in_events_parallel_series
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ NTAC 3 (POP_ASSUM (K ALL_TAC))
++ (`prob p
   (rbd_struct p (series (rbd_list h)) INTER
    rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))) = prob p
   (rbd_struct p (series (rbd_list h))) *
    prob p (rbd_struct p (parallel (MAP (\ a. series (rbd_list a)) L)))` by ALL_TAC)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `h `)
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x (h::L) ==> ~NULL x) /\
      (!x. MEM x (FLAT (h::L)) ==> x IN events p) /\
      mutual_indep p (FLAT (h::L))` by STRIP_TAC)
   >> (RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   >> (STRIP_TAC
      >> (RW_TAC std_ss[]
      	 ++ FULL_SIMP_TAC list_ss[])
      ++ MATCH_MP_TAC mutual_indep_cons_append10
      ++ EXISTS_TAC(--`L1:'a  event list`--)
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++  MP_TAC(Q.ISPECL [`p:('a  event # 'a  event event # ('a  event -> real))`, `h:'a  event list`, `L1:'a  event list`] (series_rbd_append2))
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`(!x. MEM x (h ++ L1) ==> x IN events p) /\ ~NULL h /\ ~NULL L1 /\
      mutual_indep p (h ++ L1)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++  MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT L: 'a  event list`--)
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_append1
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[]
++ REAL_ARITH_TAC);


(*-------------------------------------------*)
(*   Parallel-Series RBD Theorem             *)
(*-------------------------------------------*)

val Parallel_Series_struct_thm = store_thm("Parallel_Series_struct_thm",
  ``!p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\ (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( mutual_indep p (FLAT L)) ==> (prob p (rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L))) =
        1 -  list_prod (one_minus_list (list_prod_rel  p L) ))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_struct_def,list_prod_rel_def,one_minus_list_def,list_prod_def,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_struct_def,list_prod_rel_def,one_minus_list_def,list_prod_def]
++ FULL_SIMP_TAC std_ss[]
++ MP_TAC(Q.ISPECL [`p:('a  event # 'a event event # ('a event -> real))`, `rbd_struct p (series (rbd_list h))`, `rbd_struct p (parallel (MAP (\ a. series (rbd_list a)) L))`] Prob_Incl_excl)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`rbd_struct p (series (rbd_list h)) IN events p /\
      rbd_struct p (parallel (MAP (\a. series (rbd_list a)) L)) IN
      events p` by STRIP_TAC)
>> (REWRITE_TAC[series_rbd_eq_big_inter]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC in_events_parallel_series
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ NTAC 3 (POP_ASSUM (K ALL_TAC))
++  MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `L:'a  event list list`, `h:'a  event list`] series_rbd_indep_parallel_series_rbd)
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[]
++ POP_ASSUM (K ALL_TAC)
++ (`prob p (rbd_struct p (series (rbd_list h))) = list_prod (list_prob p h)` by MATCH_MP_TAC series_struct_thm)
>> (RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_flat_cons5
   ++ EXISTS_TAC(--`L:'a  event list list`--)
   ++ EXISTS_TAC(--`[]:'a  event list`--)
   ++ FULL_SIMP_TAC list_ss[]))
++ POP_ORW
++ (`(!z. MEM z L ==> ~NULL z) /\ (!x'. MEM x' (FLAT L) ==> x' IN events p) /\
      mutual_indep p (FLAT L)` by RW_TAC std_ss[]) 
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`h:'a  event list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[list_prod_rel_def]
++ REAL_ARITH_TAC);

(*-------------rel_parallel_series_rbd----------*)
val rel_parallel_series_rbd = store_thm("rel_parallel_series_rbd",
  ``!p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\ (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( mutual_indep p (FLAT L)) ==> (prob p (rbd_struct p ((parallel of (\a. series (rbd_list a))) L)) =
        1 -  list_prod (one_minus_list (list_prod_rel  p L) ))``,
RW_TAC list_ss[of_DEF,o_DEF]
++ MATCH_MP_TAC  Parallel_Series_struct_thm
++ RW_TAC std_ss[]);
(*-------------------------------*)
val one_minus_eq_lemm = store_thm("one_minus_eq_lemm",
  `` ! p L. prob_space p ==> (list_prod
  (one_minus_list
     (MAP (\a. list_prod (one_minus_list (list_prob p a))) L)) = list_prod (MAP (\a. 1 - list_prod (one_minus_list (list_prob p a))) L) ) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[list_prob_def,list_prod_def,one_minus_list_def])
++ RW_TAC list_ss[list_prob_def,list_prod_def,one_minus_list_def]);
(* ========================================================================== *)
(*                                                                            *)
(*   Parallel-Series RBD Configuration with Syntactic Sugar                   *)
(*                                                                            *)
(* ========================================================================== *)


val parallel_series_struct_rbd_v2 = store_thm("parallel_series_struct_rbd_v2",
  ``!p L.  (∀z. MEM z L ⇒ ¬NULL z) ∧ prob_space p ∧
     (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) ∧ mutual_indep p (FLAT L) ⇒
     (prob p
        (rbd_struct p ((parallel of (λa. series (rbd_list a))) L)) = 
	1 - (list_prod o (one_minus_list) of
	(\a. list_prod (list_prob p a))) L) ``,

RW_TAC std_ss[]
++ (`1 - list_prod ((one_minus_list of (λa. list_prod (list_prob p a))) L) = 
     1 − list_prod (one_minus_list (list_prod_rel p L)) ` 
       by RW_TAC std_ss[of_DEF,o_DEF,list_prod_rel_def])
++ RW_TAC std_ss [rel_parallel_series_rbd]);
(* ========================================================================== *)
(*                                                                            *)
(*   Series-Parallel RBD Configuration Lemma's                                *)
(*                                                                            *)
(* ========================================================================== *)


(*---------------------------*)

val in_events_series_parallel = store_thm("in_events_series_parallel",
  `` !p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p )==> (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) IN events p) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,EVENTS_SPACE])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ MATCH_MP_TAC EVENTS_INTER
++ RW_TAC std_ss[]
>> (MATCH_MP_TAC in_events_parallel_rbd
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ (`(!x. MEM x ((FLAT L):'a  event list) ==> x IN events p)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*-------series_rbd_indep_series_parallel_rbd-------*)
val series_rbd_indep_series_parallel_rbd = store_thm(
  "series_rbd_indep_series_parallel_rbd",
  `` !p L L1. prob_space p /\ (!x. MEM x (L1::L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L1::L):'a  event list list)) ==> x IN events p) /\ mutual_indep p (FLAT (L1::L)) ==> (prob p (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =  prob p (rbd_struct p (series (rbd_list L1))) * prob p ( 
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_UNIV]
   ++ RW_TAC real_ss[]
   ++ (`(rbd_struct p (series (rbd_list L1)) INTER  p_space p) = (rbd_struct p (series (rbd_list L1)))` by ONCE_REWRITE_TAC[INTER_COMM])
   >> (MATCH_MP_TAC INTER_PSPACE
      ++ RW_TAC std_ss[]
      ++ REWRITE_TAC[series_rbd_eq_big_inter]
      ++ RW_TAC std_ss[in_events_big_inter])
   ++ POP_ORW
   ++ RW_TAC std_ss[])
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_ASSOC]
++ (`!a b c. a INTER b INTER c =  (a INTER c) INTER b` by SET_TAC[])
++ POP_ORW
++ RW_TAC std_ss[UNION_OVER_INTER]
++ MP_TAC(Q.ISPECL [`p:('a  event # 'a  event event # ('a  event -> real))`, `rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER h'`, `rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER  rbd_struct p (parallel (rbd_list h))`] Prob_Incl_excl)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`rbd_struct p (series (rbd_list L1)) INTER
      rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER h' IN
      events p /\
      rbd_struct p (series (rbd_list L1)) INTER
      rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER
      rbd_struct p (parallel (rbd_list h)) IN events p` by RW_TAC std_ss[])
>> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[]
   >> (MATCH_MP_TAC EVENTS_INTER
      ++ RW_TAC std_ss[]
      >> (REWRITE_TAC[series_rbd_eq_big_inter]
      	 ++ MATCH_MP_TAC in_events_big_inter
	 ++ RW_TAC std_ss[]
	 ++ FULL_SIMP_TAC list_ss[])
      ++ MATCH_MP_TAC in_events_series_parallel
      ++ RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[]
   >> (MATCH_MP_TAC EVENTS_INTER
      ++ RW_TAC std_ss[]
      >> (REWRITE_TAC[series_rbd_eq_big_inter]
      	 ++ MATCH_MP_TAC in_events_big_inter
	 ++ RW_TAC std_ss[]
	 ++ FULL_SIMP_TAC list_ss[])
      ++ MATCH_MP_TAC in_events_series_parallel
      ++ RW_TAC std_ss[]
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC in_events_parallel_rbd
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ NTAC 3 (POP_ASSUM (K ALL_TAC))
++ (`!A B C D. A INTER B INTER C INTER (A INTER B INTER D) = ((A INTER C) INTER B INTER D)` by SET_TAC[])
++ POP_ORW
++ (`!A B C. A INTER B INTER C =  (A INTER C) INTER B` by SET_TAC[])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list L1)) INTER h' INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p
  (h' INTER rbd_struct p (series (rbd_list L1))) *  
prob p ( rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by ALL_TAC)
>> (NTAC 5 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `h'::L1`)
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x (((h'::L1)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ((h'::L1)::L)): 'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ((h'::L1)::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> ( MATCH_MP_TAC mutual_indep_cons_append12
      ++ EXISTS_TAC(--`h:'a  event list`--)
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ (`rbd_struct p (series (rbd_list L1)) INTER  h' = rbd_struct p (series (rbd_list (h'::L1)))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def]++ RW_TAC std_ss[INTER_COMM])
   ++ POP_ORW
   ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p
  (rbd_struct p (series (rbd_list L1)))* 
  prob p ( rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by RW_TAC std_ss[])
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L1`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x ((L1::(h''::t)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT (L1::(h''::t)::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT (L1::(h''::t)::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (MATCH_MP_TAC mutual_indep_flat_cons3
      ++ EXISTS_TAC(--`[h']:'a  event list`--)
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list L1)) INTER h' INTER
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p
  (rbd_struct p (series (rbd_list L1)) INTER h') * prob p (
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by RW_TAC std_ss[])
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `h'::L1`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x (((h'::L1)::(h''::t)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ((h'::L1)::(h''::t)::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ((h'::L1)::(h''::t)::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[]
      ++ MATCH_MP_TAC mutual_indep_cons_append11
      ++ EXISTS_TAC(--`[]:'a  event list`--)
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ (`(rbd_struct p (series (rbd_list (h'::L1))) INTER
         rbd_struct p
           (series (MAP (\a. parallel (rbd_list a)) ((h''::t)::L)))) =(rbd_struct p (series (rbd_list L1)) INTER h' INTER
   rbd_struct p (parallel (rbd_list (h''::t))) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by (RW_TAC list_ss[rbd_list_def,rbd_struct_def] ++ SET_TAC[]))   
   ++ FULL_SIMP_TAC std_ss[]
   ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_COMM])
++ POP_ORW
++ (`h' INTER rbd_struct p (series (rbd_list L1)) = rbd_struct p (series (rbd_list ([h']++L1)))` by DEP_REWRITE_TAC[GSYM series_rbd_append])
>> (RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ ONCE_REWRITE_TAC[INTER_COMM]
   ++ (`h' INTER p_space p = h'` by (ONCE_REWRITE_TAC[INTER_COMM]))
   >> ( DEP_REWRITE_TAC[INTER_PSPACE]
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[INTER_COMM]
++ POP_ASSUM (K ALL_TAC)
++ DEP_REWRITE_TAC[series_rbd_append2]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_cons_append13
   ++ EXISTS_TAC(--`h::L:'a  event list list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ (`!a b c d. a*b*c + b * d - a * b * d =  (b:real) * (a*c + d - a * d)` by REAL_ARITH_TAC ) 
++ POP_ORW
++ (`prob p (rbd_struct p (series (rbd_list [h']))) *
 prob p (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p
           (rbd_struct p (series (rbd_list [h'])) INTER
            rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by MATCH_MP_TAC EQ_SYM)
>> (NTAC 5 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `[h']`)
   ++ RW_TAC std_ss[]
   ++ (`(!x. MEM x (([h']::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ([h']::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ([h']::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (MATCH_MP_TAC mutual_indep_cons_append15
      ++ EXISTS_TAC(--`L1:'a  event list`--)
      ++ EXISTS_TAC(--`h:'a  event list`--)
      ++ RW_TAC std_ss[])
  ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ (` prob p (rbd_struct p (series (rbd_list [h']))) *
 prob p
   (rbd_struct p (parallel (rbd_list h)) INTER
    rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =  prob p (rbd_struct p (series (rbd_list [h'])) INTER rbd_struct p (parallel (rbd_list h)) INTER
    rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by MATCH_MP_TAC EQ_SYM)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `[h']`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x (([h']::(h''::t)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ([h']::(h''::t)::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ([h']::(h''::t)::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[]
      ++ MATCH_MP_TAC mutual_indep_front_append
      ++ EXISTS_TAC(--`L1:'a  event list`--)
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ POP_ORW
++ (`!a b c. a INTER b INTER c = (a INTER c) INTER (b INTER c)` by SET_TAC[])
++ POP_ORW
++ DEP_REWRITE_TAC[GSYM Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,series_rbd_eq_big_inter,in_events_big_inter,in_events_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_parallel_rbd,in_events_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
++ (DEP_ONCE_REWRITE_TAC[INTER_COMM, GSYM UNION_OVER_INTER])
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ (`h' INTER p_space p = h'` by (ONCE_REWRITE_TAC[INTER_COMM]))
>> ( DEP_REWRITE_TAC[INTER_PSPACE]
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[]);

(*-----parallel_rbd_indep_series_parallel_rbd----------*)
val parallel_rbd_indep_series_parallel_rbd = store_thm(
  "parallel_rbd_indep_series_parallel_rbd",
  `` !p L1 L. prob_space p /\ (!x. MEM x (L1::L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L1::L):'a  event list list)) ==> x IN events p) /\ mutual_indep p (FLAT (L1::L)) ==> (prob p
  (rbd_struct p (parallel (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =   prob p
  (rbd_struct p (parallel (rbd_list L1)))* prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ (`(rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER h UNION
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)) INTER
   rbd_struct p (parallel (rbd_list L1))) = (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) ([h]::L))) UNION
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (L1::L))))` by ALL_TAC)
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]
   ++ RW_TAC std_ss[INTER_COMM])
++ POP_ORW
++ MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `rbd_struct p (series (MAP (\a. parallel (rbd_list a)) ([h]::L)))`, `rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (L1::L)))`] Prob_Incl_excl)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`rbd_struct p (series (MAP (\a. parallel (rbd_list a)) ([h]::L))) IN
      events p /\
      rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (L1::L))) IN
      events p` by RW_TAC std_ss[])
>> (MATCH_MP_TAC in_events_series_parallel
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
 >> (MATCH_MP_TAC in_events_series_parallel
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ NTAC 3 (POP_ASSUM (K ALL_TAC)) 
++ (`prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) ([h]::L)))) = prob p h * prob p
  (rbd_struct p (series (MAP (\ a. parallel (rbd_list a)) (L))))` by RW_TAC std_ss[MAP,rbd_list_def,rbd_struct_def])
>> (RW_TAC std_ss[UNION_EMPTY]
   ++ (`h = rbd_struct p (series (rbd_list [h]))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def])
   >> (ONCE_REWRITE_TAC[INTER_COMM]
      ++ MATCH_MP_TAC (GSYM INTER_PSPACE)
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (MATCH_MP_TAC mutual_indep_flat_cons4)
   ++ EXISTS_TAC(--`L1:'a  event list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c. a INTER b INTER c INTER b =  c INTER (a INTER b)` by SET_TAC[])
++ POP_ORW
++ (`(prob p
           (rbd_struct p (parallel (rbd_list L1)) INTER 
            rbd_struct p
              (series (MAP (\ a. parallel (rbd_list a)) ([h]::L)))) =
         prob p (rbd_struct p (parallel (rbd_list L1))) *
         prob p
           (rbd_struct p (series (MAP (\ a. parallel (rbd_list a)) ([h]::L)))))` by RW_TAC std_ss[])
    >> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `[h]::L`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `L1`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x (((h'::t)::[h]::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ((h'::t)::[h]::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ((h'::t)::[h]::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (MATCH_MP_TAC mutual_indep_flat_cons1
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ASSUM MP_TAC
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]
++ POP_ASSUM (K ALL_TAC)
++ (`prob p
  (rbd_struct p (parallel (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p
  (rbd_struct p (parallel (rbd_list L1))) * prob p (
   rbd_struct p (series (MAP (\ a. parallel (rbd_list a)) L)))` by ALL_TAC)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `L1`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x (((h'::t)::L):'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT ((h'::t)::L)):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT ((h'::t)::L))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[]
      ++ MATCH_MP_TAC mutual_indep_cons
      ++ EXISTS_TAC(--`h:'a  event`--)
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ (`prob p (h INTER rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = prob p (h) * prob p ( rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L)))` by ALL_TAC)  
>> ((`h = rbd_struct p (series (rbd_list [h]))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def])
   >> (ONCE_REWRITE_TAC[INTER_COMM]
      ++ MATCH_MP_TAC (GSYM INTER_PSPACE)
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC mutual_indep_flat_cons3
   ++ EXISTS_TAC(--`L1:'a  event list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ (`prob p (rbd_struct p (parallel (rbd_list L1))) * prob p h = prob p (rbd_struct p (parallel (rbd_list L1)) INTER h)` by ALL_TAC)
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `[[h]]`)
   ++ RW_TAC std_ss[]
   ++ Cases_on `L1`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ (`(!x. MEM x ([h'::t; [h]]:'a  event list list) ==> ~NULL x) /\
      (!x. MEM x ((FLAT [h'::t; [h]]):'a  event list) ==> x IN events p) /\
      mutual_indep p (FLAT [h'::t; [h]])` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> ( MATCH_MP_TAC mutual_indep_flat_cons6
      ++ EXISTS_TAC(--`L:'a  event list list`--)
      ++ RW_TAC std_ss[])
   ++ FULL_SIMP_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]
   ++ (`h INTER p_space p = h` by (ONCE_REWRITE_TAC[INTER_COMM]))
   >> ( DEP_REWRITE_TAC[INTER_PSPACE]
      ++ FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ ONCE_REWRITE_TAC[INTER_COMM]
++ (`!a b c d. a* (b:real)+ c *b - d * b =  b* (a + c - d)` by REAL_ARITH_TAC)
++ POP_ORW
++ DEP_REWRITE_TAC[GSYM Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[in_events_parallel_rbd]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ REAL_ARITH_TAC);
(******************************************************************************)
(*                                                                            *) 
(*  Series-Parallel RBD Reliability                                           *)
(*                                                                            *)
(******************************************************************************)

val series_parallel_struct_thm = store_thm("series_parallel_struct_thm",
  `` !p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\ (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( mutual_indep p (FLAT L)) ==> (prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L)) =
        list_prod (one_minus_list (list_prod_one_minus_rel p L) )) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,list_prod_one_minus_rel_def,one_minus_list_def,list_prod_def,rbd_list_def,rbd_struct_def,PROB_UNIV])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[of_DEF,o_DEF,list_prod_one_minus_rel_def,one_minus_list_def,list_prod_def,rbd_list_def,rbd_struct_def]
++ DEP_REWRITE_TAC[parallel_rbd_indep_series_parallel_rbd]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[parallel_struct_thm]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_flat_cons5
   ++ EXISTS_TAC(--`L:'a  event list list`--)
   ++ EXISTS_TAC(--`[]:'a  event list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ (`(!z. MEM z (L:'a  event list list) ==> ~NULL z) /\ prob_space p /\
      (!x'. MEM x' (FLAT (L:'a  event list list)) ==> x' IN events p) /\ mutual_indep p (FLAT L)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_FLAT_front_cons
   ++ EXISTS_TAC(--`h:'a  event list`--)
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF]
++ RW_TAC list_ss[list_prod_one_minus_rel_def]);
(* ========================================================================== *)
(*                                                                            *)
(*   Series-Parallel RBD Configuration with Syntatic Sugar                    *)
(*                                                                            *)
(* ========================================================================== *)

(*-------------------------*)
(*-------------------------*)
val series_parallel_struct_thm_v2 = store_thm("series_parallel_struct_thm_v2",
  `` !p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\ (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( mutual_indep p (FLAT L)) ==> (prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L)) =
        (list_prod of
   ((\a. 1 - list_prod (one_minus_list (list_prob p a))))) L) ``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[series_parallel_struct_thm]
++ RW_TAC std_ss[]
++ RW_TAC list_ss[of_DEF,o_DEF]
++ RW_TAC list_ss[list_prod_one_minus_rel_def]
++ RW_TAC std_ss[one_minus_eq_lemm]);
(* -------------------------------------------------------------------------- *)
(*     Nested Series-Parallel RBD Lemmas                                      *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val in_events_parallel_of_series_parallel = store_thm(
  "in_events_parallel_of_series_parallel",
  `` !p L. prob_space p /\  (!x'. MEM x' (FLAT (FLAT L)) ==> (x' IN events p))==>
rbd_struct p
  (parallel
     (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L)) IN events p ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,EVENTS_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ DEP_REWRITE_TAC[EVENTS_UNION]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[in_events_series_parallel]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (`!x'. MEM x' ((FLAT (FLAT L)):'a  event list) ==> x' IN events p` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*---in_events_series_parallel_of_series_parallel -----------*)

val in_events_series_parallel_of_series_parallel = store_thm(
  "in_events_series_parallel_of_series_parallel",
  ``!p L. prob_space p /\  (!x'. MEM x' (FLAT (FLAT (FLAT L))) ==> (x' IN events p)) ==> (rbd_struct p
  (series
     (MAP
        (parallel o
         (\a. MAP (series o (\a. MAP (\ a. parallel (rbd_list a)) a)) a))
        L)) IN events p) ``,
 GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,EVENTS_SPACE])
++ RW_TAC std_ss[] 
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ DEP_REWRITE_TAC[EVENTS_INTER]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[in_events_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ (`(!x'. MEM x' ((FLAT (FLAT (FLAT L))):'a  event list) ==> x' IN events p)` by RW_TAC std_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);

(*---------------------------*)
val series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel = store_thm(
  "series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel",
  `` !p h' L1 L .prob_space p /\ ( ! z. MEM z ( (FLAT (FLAT ([[[L1]]] ++ [(h')]::L))))  ==>   ~ NULL z) /\ ( ! x'.
         MEM x' ((FLAT (FLAT (FLAT ([[[L1]]] ++ [(h')]::L)))))  ==> 
        x'  IN  events p) /\ ( mutual_indep p (L1 ++ FLAT (FLAT (FLAT ([(h')]::L))))) /\ (!L1.
        prob_space p /\
        (!z. MEM z (FLAT (FLAT ([[[L1]]] ++ L))) ==> ~NULL z) /\
        (!x'.
           MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ++ L)))) ==>
           x' IN events p) /\
        mutual_indep p (L1 ++ FLAT (FLAT (FLAT L))) ==>
        (prob p
           (rbd_struct p (series (rbd_list L1)) INTER
            rbd_struct p
              (series
                 (MAP
                    (parallel o
                     (\a.
                        MAP
                          (series o
                           (\a. MAP (\a. parallel (rbd_list a)) a)) a))
                    L))) =
         prob p (rbd_struct p (series (rbd_list L1))) *
         prob p
           (rbd_struct p
              (series
                 (MAP
                    (parallel o
                     (\a.
                        MAP
                          (series o
                           (\a. MAP (\a. parallel (rbd_list a)) a)) a))
                    L))))) ==>

(prob p
  (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list L1))) * prob p (
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))) ``,

GEN_TAC
++ Induct
>> (RW_TAC std_ss[]
   ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ DEP_REWRITE_TAC[INTER_PSPACE]
   ++ RW_TAC std_ss[]
   >> (DEP_REWRITE_TAC[in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
   ++ ONCE_REWRITE_TAC[GSYM INTER_ASSOC,INTER_COMM]
   ++ DEP_REWRITE_TAC[INTER_PSPACE]
   ++ RW_TAC std_ss[]
   >> (DEP_REWRITE_TAC[in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L1`)
   ++ RW_TAC std_ss[]
   ++ (`(!z. MEM z (FLAT (FLAT ([[[L1]]] ++ L))) ==> ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ++ L)))) ==> x' IN events p) /\
      mutual_indep p (L1 ++ FLAT (FLAT (FLAT L)))` by RW_TAC std_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC std_ss[])
++ Induct
>> (RW_TAC std_ss[]
   ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ RW_TAC std_ss[INTER_EMPTY]
   ++ RW_TAC real_ss[PROB_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[INTER_ASSOC,UNION_OVER_INTER]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[INTER_ASSOC,UNION_OVER_INTER]
++ DEP_REWRITE_TAC [Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel,series_rbd_eq_big_inter,in_events_big_inter]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel,series_rbd_eq_big_inter,in_events_big_inter,in_events_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel,in_events_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
++ (`rbd_struct p (series (rbd_list L1)) INTER h'' = rbd_struct p (series (rbd_list (h''::L1)))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_COMM])
++ RW_TAC std_ss[GSYM INTER_ASSOC]
++ POP_ORW
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c. a INTER b INTER c = c INTER a INTER b` by SET_TAC[] )
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list (h''::L1))) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list (h''::L1)))) * prob p (
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
    >> (NTAC 6 (POP_ASSUM MP_TAC)
       ++ POP_ASSUM (MP_TAC o Q.SPEC `(h''::L1)`)
       ++ RW_TAC std_ss[]
       ++ NTAC 6 (POP_ASSUM MP_TAC)
       ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
       ++ RW_TAC std_ss[]
       ++ FULL_SIMP_TAC std_ss[]
       ++ (`(!z. MEM z (FLAT (FLAT ([[[h''::L1]]] ++ [h']::L))) ==> ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([[[h''::L1]]] ++ [h']::L)))) ==>
         x' IN events p) /\
      mutual_indep p (h''::L1 ++ FLAT (FLAT (FLAT ([h']::L))))` by RW_TAC std_ss[])
      >> (FULL_SIMP_TAC list_ss[])
      >> (FULL_SIMP_TAC list_ss[])
      >> (FULL_SIMP_TAC list_ss[]
      	 ++ RW_TAC std_ss[GSYM APPEND_ASSOC]
      	 ++ DEP_REWRITE_TAC[mutual_indep_cons_append11]
	 ++ EXISTS_TAC(--`h:'a event list`--)
	 ++ FULL_SIMP_TAC list_ss[])
      ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c d. a INTER b INTER c INTER d = d INTER a INTER b INTER c` by SET_TAC[])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list L1))) * prob p (
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by ALL_TAC)
>> (NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `(L1)`)
    ++ RW_TAC std_ss[]
    ++ NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ Cases_on `h`
    >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
       ++ RW_TAC real_ss[PROB_EMPTY])
    ++ (`(!z.
         MEM z (FLAT (FLAT ([[[L1]]] ++ [(h'''::t)::h']::L))) ==>
         ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ++ [(h'''::t)::h']::L)))) ==>
         x' IN events p) /\
      mutual_indep p (L1 ++ FLAT (FLAT (FLAT ([(h'''::t)::h']::L))))` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ DEP_REWRITE_TAC[mutual_indep_cons_append14]
       ++ EXISTS_TAC(--`h'':'a event`--)
       ++ RW_TAC std_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`rbd_struct p
           (series (MAP (\a. parallel (rbd_list a)) ((h'''::t)::h'))) = rbd_struct p (parallel (rbd_list (h'''::t))) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h'))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def])
    ++ FULL_SIMP_TAC std_ss[INTER_ASSOC])
++ POP_ORW
++ (`!a b c d e . a INTER (b INTER c INTER d INTER a INTER e) INTER c INTER d = e INTER a INTER b INTER c INTER d` by SET_TAC[])
++ POP_ORW
++ (`h'' INTER rbd_struct p (series (rbd_list L1)) = rbd_struct p (series (rbd_list ([h'']++L1)))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def] )
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list ([h''] ++ L1))) INTER
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list ([h''] ++ L1)))) * prob p (
   rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by ALL_TAC)
>> (NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `([h'']++L1)`)
    ++ RW_TAC std_ss[]
    ++ NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ Cases_on `h`
    >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
       ++ RW_TAC real_ss[PROB_EMPTY])
    ++ (`(!z.
         MEM z (FLAT (FLAT ([[[[h''] ++ L1]]] ++ [(h'''::t)::h']::L))) ==>
         ~NULL z) /\
      (!x'.
         MEM x'
           (FLAT
              (FLAT (FLAT ([[[[h''] ++ L1]]] ++ [(h'''::t)::h']::L)))) ==>
         x' IN events p) /\
      mutual_indep p
        ([h''] ++ L1 ++ FLAT (FLAT (FLAT ([(h'''::t)::h']::L)))) ` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ DEP_REWRITE_TAC[mutual_indep_cons_append11]
       ++ EXISTS_TAC(--`[]:'a event list`--)
       ++ FULL_SIMP_TAC list_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`rbd_struct p (series (rbd_list ([h''] ++ L1))) INTER rbd_struct p (parallel (rbd_list (h'''::t))) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) = rbd_struct p (series (rbd_list ([h''] ++ L1))) INTER rbd_struct p
           (series (MAP (\a. parallel (rbd_list a)) ((h'''::t)::h'))) ` by RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
    ++ POP_ORW
    ++ FULL_SIMP_TAC std_ss[]
    ++ RW_TAC list_ss[rbd_list_def,rbd_struct_def])
++ POP_ORW
++ (`(rbd_list (h''::L1)) = (rbd_list ([h''] ++ L1))` by RW_TAC list_ss[rbd_list_def])
++ POP_ORW
++ DEP_REWRITE_TAC[series_rbd_append2]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ (`(h''::L1) = (h''::(L1 ++ []):'a event list)` by RW_TAC list_ss[])
   ++ POP_ORW
   ++ MATCH_MP_TAC mutual_indep_cons_append11
   ++ EXISTS_TAC(--`(h ++ FLAT h' ++ FLAT (FLAT (FLAT L))):'a event list`--)
   ++ FULL_SIMP_TAC list_ss[])
++ (`!a b c:real. a * b * c = b * a * c` by REAL_ARITH_TAC)
++ POP_ORW
++ (`prob p (rbd_struct p (series (rbd_list [h'']))) *
prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p (rbd_struct p (series (rbd_list [h''])) INTER (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))))` by RW_TAC std_ss[])
>> (MATCH_MP_TAC EQ_SYM
    ++ NTAC 6 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `([h''])`)
    ++ RW_TAC std_ss[]
    ++ NTAC 6 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`(!z. MEM z (FLAT (FLAT ([[[[h'']]]] ++ [h']::L))) ==> ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([[[[h'']]]] ++ [h']::L)))) ==>
         x' IN events p) /\
      mutual_indep p ([h''] ++ FLAT (FLAT (FLAT ([h']::L))))`by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ (`(h''::(FLAT h' ++ FLAT (FLAT (FLAT L)))) = ((h''::([] ++ FLAT h' ++ FLAT (FLAT (FLAT L)))):'a event list)` by RW_TAC list_ss[])
       ++ POP_ORW
       ++ RW_TAC std_ss[GSYM APPEND_ASSOC]
       ++ MATCH_MP_TAC mutual_indep_cons_append11
       ++ EXISTS_TAC(--`h:'a event list`--)
       ++ FULL_SIMP_TAC list_ss[]
       ++ MATCH_MP_TAC mutual_indep_front_append
       ++ EXISTS_TAC(--`L1:'a event list`--)
       ++ RW_TAC std_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ RW_TAC std_ss[INTER_ASSOC])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ POP_ASSUM (K ALL_TAC)
++ (`(prob p (rbd_struct p (series (rbd_list [h'']))) *
 prob p
   (rbd_struct p (parallel (rbd_list h)) INTER
    rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
    rbd_struct p
      (series
         (MAP
            (parallel o
             (\a.
                MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                  a)) L))))  = (prob p (rbd_struct p (series (rbd_list [h''])) INTER
   (rbd_struct p (parallel (rbd_list h)) INTER
    rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h')) INTER
    rbd_struct p
      (series
         (MAP
            (parallel o
             (\a.
                MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                  a)) L))))) ` by RW_TAC std_ss[])
>> (MATCH_MP_TAC EQ_SYM
    ++ NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `([h''])`)
    ++ RW_TAC std_ss[]
    ++ NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ Cases_on `h`
    >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
       ++ RW_TAC real_ss[PROB_EMPTY])
    ++ (`(!z.
         MEM z (FLAT (FLAT ([[[[h'']]]] ++ [(h'''::t)::h']::L))) ==>
         ~NULL z) /\
      (!x'.
         MEM x'
           (FLAT (FLAT (FLAT ([[[[h'']]]] ++ [(h'''::t)::h']::L)))) ==>
         x' IN events p) /\
      mutual_indep p
        ([h''] ++ FLAT (FLAT (FLAT ([(h'''::t)::h']::L))))` by RW_TAC std_ss[])
     >> (FULL_SIMP_TAC list_ss[])
     >> (FULL_SIMP_TAC list_ss[])
     >> (FULL_SIMP_TAC list_ss[]
     	++ MATCH_MP_TAC mutual_indep_front_append
	++ EXISTS_TAC(--`L1:'a event list`--)
	++ RW_TAC std_ss[])
     ++ FULL_SIMP_TAC std_ss[]
     ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ RW_TAC std_ss[GSYM REAL_MUL_ASSOC]
++ POP_ASSUM (K ALL_TAC)
++ (`!a b c d:real. a *b + a * c - a * d =  a * (b + c -d)` by REAL_ARITH_TAC)
++ POP_ORW
++ (`!a b c d. a INTER (b INTER c INTER a) INTER d INTER c = d INTER b INTER c INTER a` by SET_TAC[])
++ POP_ORW
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ (`h'' INTER p_space p = h''` by (ONCE_REWRITE_TAC[INTER_COMM]++MATCH_MP_TAC INTER_PSPACE))
>> (FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[INTER_ASSOC]);
(*--------------------------*)
val series_rbd_indep_series_parallel_of_series_parallel = store_thm(
  "series_rbd_indep_series_parallel_of_series_parallel",
  `` !p L L1 .prob_space p /\ ( ! z. MEM z (FLAT (FLAT( [[[L1]]]++L)))  ==>   ~ NULL z) /\ ( ! x'.
        MEM x' (FLAT (FLAT (FLAT ([[[L1]]]++L))))  ==> 
        x'  IN  events p) /\ (mutual_indep p (L1 ++FLAT (FLAT (FLAT L)))) ==>


(prob p
  (rbd_struct  p (series (rbd_list L1)) INTER rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) =  prob p
  (rbd_struct  p (series (rbd_list L1))) * prob p ( rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ ONCE_REWRITE_TAC[INTER_COMM]
   ++ DEP_REWRITE_TAC[INTER_PSPACE,series_rbd_eq_big_inter,in_events_big_inter]
   ++ RW_TAC std_ss[]
   ++ RW_TAC real_ss[PROB_UNIV])
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def]
   ++ RW_TAC std_ss[INTER_EMPTY]
   ++ RW_TAC real_ss[PROB_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[INTER_ASSOC,UNION_OVER_INTER]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel_of_series_parallel,in_events_series_parallel,series_rbd_eq_big_inter,in_events_big_inter]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel_of_series_parallel,in_events_parallel_of_series_parallel,series_rbd_eq_big_inter,in_events_big_inter]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel_of_series_parallel,in_events_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel_of_series_parallel,in_events_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
++ (`!a b c. a INTER (b INTER c) =  b INTER c INTER a` by SET_TAC[])++ POP_ORW
++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT (FLAT h):'a event list`--)
   ++ ONCE_REWRITE_TAC[APPEND_ASSOC]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[])
++ (`prob p
  (rbd_struct p (series (rbd_list L1)) INTER
   rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) h)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list L1))) * prob p (
   rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) h)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
>> (NTAC 4 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L1`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`(!z. MEM z (FLAT (FLAT ([[[L1]]] ++ h::L))) ==> ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([[[L1]]] ++ h::L)))) ==>
         x' IN events p) /\
      mutual_indep p (L1 ++ FLAT (FLAT (FLAT (h::L))))` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ RW_TAC std_ss[GSYM APPEND_ASSOC]
       ++ MATCH_MP_TAC mutual_indep_append_sym
       ++ MATCH_MP_TAC mutual_indep_front_append
       ++ EXISTS_TAC(--`(FLAT h'):'a event list`--)
       ++ RW_TAC std_ss[APPEND_ASSOC]
       ++ MATCH_MP_TAC mutual_indep_append_sym
       ++ RW_TAC list_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ POP_ORW
++ (`! a b c d. a INTER (b INTER c) INTER (a INTER (b INTER d)) = b INTER d INTER c INTER a` by SET_TAC[])
++ POP_ORW
++ (`rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) h)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)) =
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) (h::L)))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ ONCE_ASM_REWRITE_TAC[]
++ ONCE_REWRITE_TAC[GSYM INTER_ASSOC]
++ POP_ORW
++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ (FULL_SIMP_TAC list_ss[])
++ (`!a b c d:real. a*b + a * c - a * d = a * (b + c - d)` by REAL_ARITH_TAC)
++ POP_ORW
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC]
++ (`!a b c. a INTER b INTER a INTER c = c INTER b INTER a` by SET_TAC[])
++ POP_ORW
++ RW_TAC std_ss[INTER_COMM]);
(*------------------------*)
val series_parallel_rbd_indep_series_parallel_of_series_parallel = store_thm(
  "series_parallel_rbd_indep_series_parallel_of_series_parallel",
  ``!p L1 L. prob_space p /\ ( !z.
        MEM z (FLAT (FLAT ([L1]::L))) ==>  ~NULL z) /\ 
( !x'.
        MEM x'
          (FLAT (FLAT (FLAT ([L1]::L)))) ==>  x' IN events p) /\
 (mutual_indep p  (FLAT (FLAT (FLAT (([L1]::L)))))) ==> (prob p
       (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) INTER
        rbd_struct p
          (series
             (MAP
                (parallel o
                 (\a.
                    MAP
                      (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                      a)) L)))  = prob p
       (rbd_struct p (series (MAP (\ a. parallel (rbd_list a)) L1))) * prob p (
        rbd_struct p
          (series
             (MAP
                (parallel o
                 (\ a.
                    MAP
                      (series o (\ a. MAP (\ a. parallel (rbd_list a)) a))
                      a)) L))))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_UNIV]
   ++ DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
   ++ RW_TAC real_ss[]
   ++ DEP_REWRITE_TAC[in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[])
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[INTER_ASSOC,UNION_OVER_INTER]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel,in_events_series_parallel_of_series_parallel,in_events_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_parallel_rbd,in_events_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]))
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[GSYM INTER_ASSOC]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ (`prob p
  (h' INTER rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (h') * prob p (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) INTER (
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))))` by ALL_TAC)
>> ((`h' = rbd_struct p (series (rbd_list [h']))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def])
      >> (MATCH_MP_TAC EQ_SYM
      	 ++ ONCE_REWRITE_TAC[INTER_COMM]
	 ++ MATCH_MP_TAC INTER_PSPACE
	 ++ FULL_SIMP_TAC list_ss[])
    ++ POP_ORW
    ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel]
    ++ RW_TAC std_ss[]
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       	 ++ ONCE_REWRITE_TAC[CONS_APPEND]
	 ++ MATCH_MP_TAC mutual_indep_append_sym
	 ++ MATCH_MP_TAC mutual_indep_front_append
	 ++ EXISTS_TAC (--`h:'a event list`--)
	 ++ ONCE_REWRITE_TAC[APPEND_ASSOC]
	 ++ MATCH_MP_TAC mutual_indep_append_sym
	 ++ FULL_SIMP_TAC list_ss[])
    ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_of_series_parallel]
    ++ RW_TAC std_ss[])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1))) * prob p (
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
>> (NTAC 5 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`(!z. MEM z (FLAT (FLAT ([L1]::L))) ==> ~NULL z) /\
      (!x'. MEM x' (FLAT (FLAT (FLAT ([L1]::L)))) ==> x' IN events p) /\
      mutual_indep p (FLAT (FLAT (FLAT ([L1]::L))))` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ MATCH_MP_TAC mutual_indep_front_append
       ++ EXISTS_TAC(--`h'::h:'a event list`--)
       ++ FULL_SIMP_TAC list_ss[])
    ++ FULL_SIMP_TAC std_ss[])
++ POP_ORW
++ (`prob p
  (rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1))) * prob p (
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
>> (NTAC 4 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `L`)
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ RW_TAC std_ss[]
   ++ (`(!z. MEM z (FLAT (FLAT ([(h''::t)::L1]::L))) ==> ~NULL z) /\
      (!x'.
         MEM x' (FLAT (FLAT (FLAT ([(h''::t)::L1]::L)))) ==>
         x' IN events p) /\
      mutual_indep p (FLAT (FLAT (FLAT ([(h''::t)::L1]::L))))` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ MATCH_MP_TAC mutual_indep_cons
       ++ EXISTS_TAC(--`h':'a event`--)
       ++ RW_TAC std_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ POP_ORW
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c d . a INTER b INTER c INTER a INTER d INTER c = d INTER b INTER c INTER a ` by SET_TAC[])
++ POP_ORW
++ (`(h' = rbd_struct p (series (rbd_list [h']))) /\ (rbd_struct p (parallel (rbd_list h)) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1)) = 
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1)))) ` by RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
>> (ONCE_REWRITE_TAC[INTER_COMM]
   ++ MATCH_MP_TAC EQ_SYM
   ++ DEP_REWRITE_TAC[INTER_PSPACE]
   ++ FULL_SIMP_TAC list_ss[])
++ (`!a b c d. a INTER b INTER c INTER d = a INTER (b INTER c) INTER d` by SET_TAC[])
++ POP_ORW
++ POP_ORW
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (rbd_list [h'])) INTER
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1))) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (rbd_list [h']))) * prob p (
   rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1))) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
>> (Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_inter_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[])
++ POP_ORW
++ (`prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1))) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1)))) * prob p (
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L)))` by RW_TAC std_ss[])
>> (Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ DEP_ONCE_ASM_REWRITE_TAC[]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]
      ++ MATCH_MP_TAC mutual_indep_cons
      ++ EXISTS_TAC(--`h':'a event`--)
      ++ RW_TAC std_ss[]))
++ POP_ORW
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ (`prob p (rbd_struct p (series (rbd_list [h']))) *
prob p (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1))) = prob p (rbd_struct p (series (rbd_list [h'])) INTER (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L1))))` by MATCH_MP_TAC EQ_SYM)
>> (DEP_REWRITE_TAC[series_rbd_indep_series_parallel_rbd]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]
   ++ ONCE_REWRITE_TAC[CONS_APPEND]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`h:'a event list`--)
   ++ RW_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT (FLAT (FLAT L)):'a event list`--)
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[]))
++ POP_ORW
++ (`prob p (rbd_struct p (series (rbd_list [h']))) *
prob p
  (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1)))) = prob p (rbd_struct p (series (rbd_list [h'])) INTER
rbd_struct p (series (MAP (\a. parallel (rbd_list a)) (h::L1))))` by MATCH_MP_TAC EQ_SYM )
>> (Cases_on `h`
   >> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY]
      ++ RW_TAC real_ss[PROB_EMPTY])
   ++ DEP_REWRITE_TAC[series_rbd_indep_series_parallel_rbd]
   ++ RW_TAC std_ss[]   
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT (FLAT (FLAT L)):'a event list`--)
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ FULL_SIMP_TAC list_ss[]))
++ POP_ORW
++ (`!a b c d:real. a * b + c * b - d * b = (a + c - d) * b` by REAL_ARITH_TAC)
++ POP_ORW
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c. a INTER b INTER a INTER c = b INTER c INTER a` by SET_TAC[])
++ POP_ORW
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC]);

(*-------------------------*)
val parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd = store_thm(
  "parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd",
  `` !p L1 L. prob_space p /\ ( !z.
        MEM z (FLAT (FLAT (L1::L))) ==>  ~NULL z) /\ 
( !x'.
        MEM x'
          (FLAT (FLAT (FLAT (L1::L)))) ==>  x' IN events p) /\
 (mutual_indep p  (FLAT (FLAT (FLAT ((L1::L)))))) ==> (prob p
  (rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L1)) INTER
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\a.
               MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                 a)) L))) = prob p
  (rbd_struct p
     (parallel
        (MAP (series o (\ a. MAP (\ a. parallel (rbd_list a)) a)) L1))) * prob p (
   rbd_struct p
     (series
        (MAP
           (parallel o
            (\ a.
               MAP (series o (\ a. MAP (\ a. parallel (rbd_list a)) a))
                 a)) L)))) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_EMPTY,PROB_EMPTY]
   ++ RW_TAC real_ss[])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ RW_TAC std_ss[UNION_OVER_INTER]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ DEP_REWRITE_TAC[in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,in_events_parallel_of_series_parallel,in_events_series_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[in_events_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[]))
>> (DEP_REWRITE_TAC[in_events_parallel_of_series_parallel]
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[]))
++ ONCE_REWRITE_TAC[INTER_COMM]
++ DEP_REWRITE_TAC[series_parallel_rbd_indep_series_parallel_of_series_parallel]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT (FLAT L1):'a event list`--)
   ++ RW_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[])
++ DEP_ONCE_ASM_REWRITE_TAC[]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT h: 'a event list`--)
   ++ RW_TAC list_ss[])
++ RW_TAC std_ss[INTER_ASSOC]
++ (`!a b c. a INTER b INTER a INTER c = c INTER b INTER a` by SET_TAC[])
++ POP_ORW
++ RW_TAC std_ss[GSYM INTER_ASSOC]
++ (`(rbd_struct p
      (parallel
         (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L1)) INTER
    rbd_struct p
      (series
         (MAP
            (parallel o
             (\a.
                MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                  a)) L))) = (
      (rbd_struct p
      (series
         (MAP
            (parallel o
             (\a.
                MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                  a)) (L1::L)))))` by RW_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC])
++ POP_ORW
++ DEP_REWRITE_TAC[series_parallel_rbd_indep_series_parallel_of_series_parallel]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def]
++ DEP_ONCE_ASM_REWRITE_TAC[]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT h:'a event list`--)
   ++ RW_TAC list_ss[])
++ RW_TAC std_ss[REAL_MUL_ASSOC]
++ (`prob p (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h))) *
prob p
  (rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L1))) = prob p (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h)) INTER
  rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L1)))` by MATCH_MP_TAC EQ_SYM)
>> (NTAC 4 (POP_ASSUM MP_TAC)
    ++ POP_ASSUM (MP_TAC o Q.SPEC `[[h]]`)
    ++ RW_TAC std_ss[]
    ++ FULL_SIMP_TAC std_ss[]
    ++ (`(!z. MEM z (FLAT (FLAT [L1; [h]])) ==> ~NULL z) /\
      (!x'. MEM x' (FLAT (FLAT (FLAT [L1; [h]]))) ==> x' IN events p) /\
      mutual_indep p (FLAT (FLAT (FLAT [L1; [h]])))` by RW_TAC std_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[])
    >> (FULL_SIMP_TAC list_ss[]
       ++ MATCH_MP_TAC mutual_indep_append_sym
       ++ MATCH_MP_TAC mutual_indep_front_append
       ++ EXISTS_TAC(--`FLAT (FLAT (FLAT L)):'a event list`--)
       ++ MATCH_MP_TAC mutual_indep_append_sym
       ++ RW_TAC list_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ FULL_SIMP_TAC list_ss[rbd_list_def,rbd_struct_def,INTER_ASSOC,UNION_EMPTY,INTER_COMM]
    ++ (`p_space p INTER
         rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h)) =
         rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h))` by DEP_REWRITE_TAC[INTER_PSPACE,in_events_series_parallel])
    >> (FULL_SIMP_TAC list_ss[])
    ++ FULL_SIMP_TAC std_ss[]
    ++ RW_TAC std_ss[REAL_MUL_COMM])
++ POP_ORW
++ (`!a b c d:real. a * b + c * b - d * b = (a + c - d) * b` by REAL_ARITH_TAC)
++ POP_ORW
++ RW_TAC std_ss[INTER_COMM]);

(*-----------------------------------*)

val rel_parallel_of_series_parallel_rbd = store_thm(
  "rel_parallel_of_series_parallel_rbd",
  ``!p L1 L  . ( ! z.
        MEM z (FLAT (FLAT ((L1::L))))  ==> 
         ~ NULL z) /\ (prob_space p) /\ ( ! x'.
        MEM x'
          (FLAT (FLAT (FLAT ((L1::L) ))))  ==> 
        x'  IN  events p) /\ (mutual_indep p (FLAT (FLAT (FLAT ( (L1::L))))))
==> (prob p
  (rbd_struct p
     (parallel
        (MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a)) L1))) = (1 -
 list_prod
   (one_minus_list
      (MAP
         ((\a. list_prod a) o
          (\a.
             MAP (\a. 1 - list_prod (one_minus_list (list_prob p a)))
               a)) L1)))) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[rbd_list_def,rbd_struct_def,list_prob_def,one_minus_list_def,list_prod_def]
   ++ RW_TAC real_ss[PROB_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,list_prob_def,one_minus_list_def,list_prod_def]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[in_events_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
>> (DEP_REWRITE_TAC[in_events_parallel_of_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
++ (`rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h)) = rbd_struct p
      (series
         (MAP
            (parallel o
             (\a.
                MAP (series o (\a. MAP (\a. parallel (rbd_list a)) a))
                  a)) [[h]]))` by (RW_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]++ONCE_REWRITE_TAC[INTER_COMM]++MATCH_MP_TAC EQ_SYM))
>> (DEP_REWRITE_TAC[INTER_PSPACE,in_events_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ ONCE_REWRITE_TAC[INTER_COMM]
++ DEP_REWRITE_TAC[parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT (FLAT (FLAT L)):'a event list`--)
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[])
++ DEP_ONCE_ASM_REWRITE_TAC[]
++ RW_TAC std_ss[]
>> (EXISTS_TAC(--`L:'a event list list list list`--)
   ++ RW_TAC std_ss[]
   >> (FULL_SIMP_TAC list_ss[])
   >> (FULL_SIMP_TAC list_ss[])
   ++ (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`FLAT h:'a event list`--)
   ++ RW_TAC list_ss[]))
++ RW_TAC list_ss[rbd_list_def,rbd_struct_def,UNION_EMPTY]
++ ONCE_REWRITE_TAC[INTER_COMM]
++ DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[in_events_series_parallel]
   ++ FULL_SIMP_TAC list_ss[])
++ (`(rbd_struct p (series (MAP (\a. parallel (rbd_list a)) h))) = (rbd_struct p ((series of (\a. parallel (rbd_list a))) h))` by RW_TAC list_ss[of_DEF,o_DEF])
++ POP_ORW
++ DEP_REWRITE_TAC[series_parallel_struct_thm]
++ RW_TAC std_ss[]
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[]
   ++ MATCH_MP_TAC mutual_indep_front_append
   ++ EXISTS_TAC(--`(FLAT (FLAT L1) ++ FLAT (FLAT (FLAT L))):'a event list`--)
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[])
++ RW_TAC list_ss[list_prod_one_minus_rel_def]
++ RW_TAC real_ss[REAL_MUL_ASSOC]
++ (`!a b:real. a + (1 - b) - (1 -b)*a = 1 - (1 - a)*b` by REAL_ARITH_TAC)
++ POP_ORW
++ RW_TAC real_ss[one_minus_eq_lemm]);


(******************************************************************************)
(*  Nested Series-Parallel RBD Reliability                                    *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

val rel_nested_series_parallel_rbd = store_thm("rel_nested_series_parallel_rbd",
  ``!p L. prob_space p /\ (!z. MEM z (FLAT (FLAT L))  ==>  ~NULL z) /\
  (!x'. MEM x' (FLAT (FLAT (FLAT L))) ==> (x' IN events p))/\
 ( mutual_indep p (FLAT (FLAT (FLAT L)))) ==> (prob p (rbd_struct p ((series of parallel of series of (\a. parallel (rbd_list a))) L)) = (list_prod of (\a. (1 -  list_prod (one_minus_list a ))) of (\a. list_prod a) of (\a. (1 -  list_prod (one_minus_list (list_prob p a))))) L) ``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,rbd_list_def,rbd_struct_def, list_prod_def,PROB_UNIV])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[of_DEF,rbd_list_def,rbd_struct_def, list_prod_def]++ DEP_REWRITE_TAC[ parallel_series_parallel_rbd_indep_series_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[rel_parallel_of_series_parallel_rbd]
++ RW_TAC std_ss[]
>> (EXISTS_TAC(--`L:'a event list list list list`--)
   ++ RW_TAC std_ss[])
++ FULL_SIMP_TAC list_ss[of_DEF]
++ DEP_ONCE_ASM_REWRITE_TAC[]
++ MATCH_MP_TAC mutual_indep_front_append
++ EXISTS_TAC(--`FLAT (FLAT h):'a event list`--)
++ RW_TAC list_ss[]);


val _ = export_theory();
