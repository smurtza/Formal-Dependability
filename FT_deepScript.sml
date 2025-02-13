app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory;
load "RBDTheory";
open RBDTheory
open HolKernel boolLib bossLib Parse;
val _ = new_theory "FT_deep";
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
(*      Fault Tree Gates datatypes           *)
(*------------------------------*)
val _ = type_abbrev( "event" , ``:'a ->bool``);

(*val _ = Hol_datatype` gate = AND of gate list | OR of gate list | atomic of 'a  event `; *)

val _ = Hol_datatype` gate = AND of gate list | OR of gate list  | NOT of gate | atomic of 'a  event `;


(*----------------------------------------------*)
(*      Fault Tree  Semantic Function        *)
(*----------------------------------------------*)
val FTree_def = Define `
    (FTree p (atomic a)  = a) /\
    (FTree p (NOT a) =  p_space p DIFF FTree p a)/\
    (FTree p (AND []) = p_space p) /\
    (FTree p (AND (x::xs)) =
                FTree p (x:'a gate) INTER FTree p (AND (xs))) /\
     (FTree p (OR []) = {} ) /\
     (FTree p (OR (x::xs)) =
                 FTree p (x:'a gate) UNION FTree p (OR (xs)))`;


(* val FTree_def = Define `
    (FTree p ( atomic a)  = a) /\
    (FTree p (AND []) = p_space p) /\
    (FTree p (AND (x::xs)) =
                FTree p (x:'a gate) INTER FTree p (AND (xs))) /\
     (FTree p (OR []) = {} ) /\
     (FTree p (OR (x::xs)) =
                 FTree p (x:'a gate) UNION FTree p (OR (xs)))`;
*)
(*---rbd list from atomic events---*)

val gate_list_def = Define `
    (gate_list [] = []) /\
    (gate_list (h::t) =  atomic h::gate_list t)`;

(**)
(* -------------------- *)
(*      Definitions     *)
(* -------------------- *)

(*-------AND_gate_eq_big_inter---*)


val AND_gate_eq_big_inter = store_thm("AND_gate_eq_big_inter",
  ``!p L. FTree p (AND (gate_list L)) = 
       	  big_inter p L``,
GEN_TAC
++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,big_inter_def])
++ RW_TAC std_ss[gate_list_def,FTree_def,big_inter_def]);



(*-------------------------------------*)
(*		AND Gate	       *)
(*-------------------------------------*)

val AND_gate_thm = store_thm("AND_gate_thm",
  ``!p L. prob_space p /\ 
       	  ~NULL L /\ 
	  (!x'. MEM x' L ==> x' IN events p) /\
 	  mutual_indep p L ==>
	   (prob p (FTree p (AND (gate_list L))) =
	    list_prod (list_prob p L))``,
RW_TAC std_ss[] THEN
(`(FTree p (AND (gate_list L))) = big_inter p L ` by Induct_on `L`) THEN1
RW_TAC std_ss[gate_list_def,FTree_def,big_inter_def] THENL[
RW_TAC std_ss[big_inter_def] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
RW_TAC std_ss[] THEN
Cases_on `L` THEN1
RW_TAC std_ss[gate_list_def,FTree_def,big_inter_def] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
(`(!x'. MEM x' ((h'::t):'a  event list) ==> x' IN events p) /\
          mutual_indep p (h'::t)` by RW_TAC std_ss[]) 
THENL[
FULL_SIMP_TAC list_ss[],
MATCH_MP_TAC mutual_indep_cons THEN
EXISTS_TAC(--`h:'a ->bool`--) THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[gate_list_def,FTree_def,big_inter_def]],
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
(*      OR Fault Tree Gate	      *)
(*------------------------------------*)

(*------------------------------------*)
(*      Lemmma's             *)
(*------------------------------------*)

val OR_gate_lem1 = store_thm("OR_gate_lem1",
  ``!p L. prob_space p /\
       	   (!x'. MEM x' L ==> x'  IN  events p) ==> 
	   (one_minus_list (list_prob p L) =
	    list_prob p ( compl_list p L))``,
GEN_TAC THEN
Induct THEN1
RW_TAC list_ss[compl_list_def,list_prob_def,one_minus_list_def] THEN
RW_TAC list_ss[compl_list_def,list_prob_def,one_minus_list_def] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC PROB_COMPL THEN
RW_TAC std_ss[]);

(*-------OR_gate_lem2---------*)
val OR_gate_lem2 = store_thm("OR_gate_lem2",
  ``!L1 (L2:('a ->bool)list) Q. (LENGTH (L1 ++ ((Q::L2))) = LENGTH ((Q::L1) ++ (L2)))``,
RW_TAC list_ss[LENGTH_APPEND]);
(*-------OR_gate_lem3---------*)
val OR_gate_lem3 = store_thm("OR_gate_lem3",
  ``!A B C D. A INTER B INTER C INTER D = (B INTER C) INTER D INTER A ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------OR_gate_lem4---------*)
val OR_gate_lem4 = store_thm("OR_gate_lem4",
  ``!p A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C)) ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------OR_gate_lem5---------*)
val  OR_gate_lem5 = store_thm("OR_gate_lem5",
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
(*-------------OR_gate_lem6----------------*)
val OR_gate_lem6 = store_thm("OR_gate_lem6",``!A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C))``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]);
(*-------------OR_gate_lem7----------------*)
val OR_gate_lem7 =  store_thm("OR_gate_lem7",``!(L1:('a ->bool) list) p.
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

(*--------------------------*)
val prob_indep_big_inter2 = store_thm("prob_indep_big_inter2",
``!(L1:('a ->bool) list) (L2:('a ->bool) list) n p.
	   prob_space p  /\ mutual_indep p (L1 ++ (L2)) /\
	   (!x. MEM x (L1 ++ (L2)) ==> x IN events p ) /\
	    1 <=  (LENGTH (L1 ++ (L2))) ==>
	     (prob p (big_inter p (TAKE n (compl_list p L1)) INTER 
	     	      big_inter p ((L2) )) =
              list_prod (list_prob p (TAKE (n)(compl_list p L1) )) *
	       list_prod (list_prob p (( L2) )))``,
Induct
THEN1(RW_TAC real_ss[compl_list_def,MAP,TAKE_def,big_inter_def,list_prob_def,list_prod_def]
 THEN FULL_SIMP_TAC std_ss[mutual_indep_def]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `((L2):('a ->bool)list) `)
 THEN RW_TAC real_ss[]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `LENGTH ((L2):('a ->bool)list)`)
 THEN RW_TAC real_ss[]
 THEN FULL_SIMP_TAC list_ss[PERM_REFL,big_inter_def]
 THEN (`(p_space p INTER (big_inter p ((L2:('a ->bool)list)))) = (big_inter p (L2))` by MATCH_MP_TAC INTER_PSPACE)
 THEN1( RW_TAC std_ss[]
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
     THEN POP_ASSUM (MP_TAC o Q.SPEC `0:num`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
     THEN RW_TAC std_ss[]
     THEN FULL_SIMP_TAC std_ss[]
     THEN (`mutual_indep p (L1 ++ L2) /\
      (!x. MEM x (L1 ++ L2) ==> x IN events p)` by STRIP_TAC)
      THEN1( MATCH_MP_TAC mutual_indep_cons
       THEN EXISTS_TAC (--`h:'a  event`--)
       THEN RW_TAC std_ss[])
      THEN1 (RW_TAC std_ss[]
      THEN FULL_SIMP_TAC list_ss[])
     THEN FULL_SIMP_TAC std_ss[]
     THEN FULL_SIMP_TAC list_ss[]
     THEN FULL_SIMP_TAC list_ss[big_inter_def]
     THEN RW_TAC real_ss[list_prob_def,list_prod_def])
  THEN FULL_SIMP_TAC list_ss[OR_gate_lem2]
  THEN FULL_SIMP_TAC list_ss[APPEND,LENGTH_NIL]
  THEN RW_TAC real_ss[big_inter_def,list_prob_def,list_prod_def,INTER_IDEMPOT,PROB_UNIV])
THEN RW_TAC std_ss[compl_list_def,MAP,TAKE_def,HD,TL,big_inter_def]
THEN RW_TAC std_ss[INTER_ASSOC]
THEN (`!a b c. a INTER b INTER c =  b INTER c INTER a` by SET_TAC[])
THEN POP_ORW
THEN RW_TAC std_ss[GSYM compl_list_def]
THEN RW_TAC std_ss[OR_gate_lem4]
THEN DEP_REWRITE_TAC[prob_compl_subset]
THEN RW_TAC std_ss[]
THEN1 (MATCH_MP_TAC EVENTS_INTER
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC EVENTS_INTER
      	    THEN RW_TAC std_ss[]
	    THEN1 (MATCH_MP_TAC in_events_big_inter
      	    	  THEN RW_TAC std_ss[]
		  THEN (`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC OR_gate_lem5)
		  THEN1 (EXISTS_TAC(--`n:num`--)
       		  	THEN RW_TAC std_ss[])
		  THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      		  THEN MATCH_MP_TAC EVENTS_COMPL
      		  THEN RW_TAC std_ss[]
      		  THEN FULL_SIMP_TAC list_ss[])
	    THEN MATCH_MP_TAC in_events_big_inter
     	    THEN RW_TAC std_ss[]
     	    THEN FULL_SIMP_TAC list_ss[])
      THEN RW_TAC std_ss[EVENTS_SPACE])
THEN1 (MATCH_MP_TAC EVENTS_INTER
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC EVENTS_INTER
      	    THEN RW_TAC std_ss[]
	    THEN1 (MATCH_MP_TAC in_events_big_inter
      	    	  THEN RW_TAC std_ss[]
		  THEN (`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC OR_gate_lem5)
		  THEN1 (EXISTS_TAC(--`n:num`--)
       		  	THEN RW_TAC std_ss[])
		  THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      		  THEN MATCH_MP_TAC EVENTS_COMPL
      		  THEN RW_TAC std_ss[]
      		  THEN FULL_SIMP_TAC list_ss[])
	    THEN MATCH_MP_TAC in_events_big_inter
     	    THEN RW_TAC std_ss[]
     	    THEN FULL_SIMP_TAC list_ss[])
      THEN FULL_SIMP_TAC list_ss[])
THEN1 ((`big_inter p L2 INTER p_space p =  big_inter p L2` by ONCE_REWRITE_TAC [INTER_COMM])
      THEN1 (MATCH_MP_TAC INTER_PSPACE
      	    THEN RW_TAC std_ss[]
 	    THEN MATCH_MP_TAC in_events_big_inter
 	    THEN RW_TAC std_ss[]
 	    THEN FULL_SIMP_TAC list_ss[])
      THEN RW_TAC std_ss[GSYM INTER_ASSOC]
      THEN RW_TAC std_ss[INTER_ASSOC,INTER_SUBSET])
THEN (`big_inter p L2 INTER p_space p =  big_inter p L2` by ONCE_REWRITE_TAC [INTER_COMM])
  THEN1(MATCH_MP_TAC INTER_PSPACE
   THEN RW_TAC std_ss[]
   THEN MATCH_MP_TAC in_events_big_inter
   THEN RW_TAC std_ss[]
   THEN FULL_SIMP_TAC list_ss[])
THEN RW_TAC std_ss[GSYM INTER_ASSOC]
THEN RW_TAC std_ss[INTER_ASSOC]
THEN POP_ASSUM (K ALL_TAC)
THEN (` LENGTH (h::L1 ++ L2) =  LENGTH (h::(L1 ++ L2))` by RW_TAC list_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN POP_ASSUM (K ALL_TAC)
THEN FULL_SIMP_TAC std_ss[LENGTH]
THEN FULL_SIMP_TAC std_ss[LE_SUC]
THEN1 (DEP_ONCE_ASM_REWRITE_TAC[]
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC mutual_indep_cons
      	    THEN EXISTS_TAC (--`h:'a  event`--)
      	    THEN FULL_SIMP_TAC list_ss[])
      THEN1 (RW_TAC std_ss[]
      	    THEN FULL_SIMP_TAC list_ss[])
      THEN FIRST_X_ASSUM (Q.SPECL_THEN [`(h::L2):('a ->bool)list`,`n:num`,`p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`] MP_TAC)
      THEN RW_TAC std_ss[]
      THEN (` mutual_indep p (L1 ++ h::L2) ∧
      (∀x. MEM x (L1 ++ h::L2) ⇒ x ∈ events p) ∧
      1 ≤ LENGTH (L1 ++ h::L2)` by RW_TAC std_ss[])
      THEN1 (MATCH_MP_TAC mutual_indep_cons_append
      	    THEN RW_TAC std_ss[])
      THEN1 (FULL_SIMP_TAC list_ss[])
      THEN1 ((`LENGTH (L1 ++ h::L2) =  LENGTH (h::L1 ++ L2)` by RW_TAC list_ss[])
      	    THEN POP_ORW
	    THEN RW_TAC list_ss[])
      THEN FULL_SIMP_TAC std_ss[]
      THEN FULL_SIMP_TAC std_ss[big_inter_def]
      THEN RW_TAC std_ss[GSYM INTER_ASSOC]
      THEN (`!a b c. a INTER (b INTER c) =  a INTER (c INTER b)` by SET_TAC[])
      THEN POP_ORW
      THEN RW_TAC std_ss[]
      THEN RW_TAC list_ss[list_prob_def,list_prod_def]
      THEN DEP_REWRITE_TAC[PROB_COMPL]
      THEN RW_TAC std_ss[]
      THEN1 (FULL_SIMP_TAC list_ss[])
      THEN REAL_ARITH_TAC)
THEN FULL_SIMP_TAC list_ss[]
THEN FULL_SIMP_TAC std_ss[LENGTH_NIL]
THEN RW_TAC list_ss[compl_list_def,big_inter_def,list_prob_def,list_prod_def]
THEN RW_TAC real_ss[INTER_IDEMPOT]
THEN RW_TAC std_ss[PROB_UNIV]
THEN DEP_REWRITE_TAC[PROB_COMPL]
THEN RW_TAC std_ss[]
THEN DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
THEN RW_TAC std_ss[]);

(*------------------------------------*)
(*------OR RBD Configuration----*)
(*------------------------------------*)

(*------OR_Lemma1----*)
val OR_lem1 = store_thm("OR_lem1",``!p s t. p_space p DIFF (s UNION t) = (p_space p DIFF s) INTER (p_space p DIFF t)``,
SRW_TAC [][EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------- OR_lem2---------------*)
val OR_lem2 = store_thm("OR_lem2",``!p  (L:('a  -> bool) list).  prob_space p /\ (!x. MEM x L ==> x IN  events p)  ==>
         ( FTree p (AND (gate_list (compl_list p L))) = p_space p DIFF (FTree p ( OR (gate_list L)) ))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def,DIFF_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM compl_list_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[OR_lem1]);
(*------------OR_lem3-------------*)
val OR_lem3 = store_thm("OR_lem3",``!L p. (!x. MEM x L ==> x IN events p) /\
prob_space p ==>
  (FTree p (OR (gate_list L)) IN events p)``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def,EVENTS_EMPTY])
++ RW_TAC std_ss[gate_list_def,MAP, FTree_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ MATCH_MP_TAC EVENTS_UNION
++ FULL_SIMP_TAC list_ss[]);
(*----------------OR_lem4----------------------*)
val OR_lem4 = store_thm("OR_lem4",``!p L. (!x. MEM x L ==> x IN events p) /\
prob_space p /\
  ((FTree p (OR (gate_list L))) IN events p) ==> ((FTree p (OR (gate_list L))) SUBSET p_space p )``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def]
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF, NOT_IN_EMPTY])
++ RW_TAC std_ss[compl_list_def,MAP,gate_list_def,FTree_def]
++ RW_TAC std_ss[UNION_SUBSET]
>> ((`h = h INTER p_space p` by MATCH_MP_TAC EQ_SYM)
   >> (ONCE_REWRITE_TAC[INTER_COMM]
      ++ MATCH_MP_TAC INTER_PSPACE
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ FULL_SIMP_TAC std_ss[]
++ (`(!x. MEM x L ==> x IN events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[OR_lem3]);
(*----------------OR_lem5----------------------*)
val OR_lem5 = store_thm("OR_lem5",``!p L. FTree p (AND (gate_list L)) = big_inter p L``,
 RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[gate_list_def,FTree_def,big_inter_def])
++ RW_TAC list_ss[gate_list_def,FTree_def,big_inter_def]);

(*-----------------OR_lem6---------------------*)

val OR_lem6 = store_thm("OR_lem6",``!p x L.  prob_space p /\ (!x'. MEM x' L ==> x' IN events p)                                ==>
(prob p (FTree p (OR (gate_list L))) = 1 - prob p (FTree p (AND (gate_list (compl_list p ( L))))))``,
RW_TAC std_ss[]
++ (`FTree p (OR (gate_list L)) SUBSET p_space p` by MATCH_MP_TAC  OR_lem4)
>> (RW_TAC std_ss[]
   ++ MATCH_MP_TAC OR_lem3
   ++ RW_TAC std_ss[])
++  (`(1 - prob p (FTree p (AND (gate_list (compl_list p L)))))  = (prob p (p_space p DIFF (FTree p (AND (gate_list (compl_list p L))))))` by MATCH_MP_TAC EQ_SYM)
>> (MATCH_MP_TAC PROB_COMPL
   ++  RW_TAC std_ss[]
   ++  RW_TAC std_ss[OR_lem5]
   ++  MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC list_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[]
++ RW_TAC std_ss[OR_lem2]
++ RW_TAC std_ss[DIFF_DIFF_SUBSET]);
(*--------------OR_lem7----------------------*)
val OR_lem7 = store_thm("OR_lem7",``!p (L). prob_space p /\ (!x'. MEM x' L ==> x'  IN  events p )   ==> (one_minus_list (list_prob p L) = list_prob p ( compl_list p L))``,
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
val OR_lem8 = store_thm("OR_lem8",
  `` !L. one_minus_list L =  MAP (\a. 1 - a) L ``,
Induct
++ RW_TAC list_ss[one_minus_list_def]);
(*------------------------------------*)
(*-----------OR_gate_thm------*)
(*------------------------------------*)
val OR_gate_thm = store_thm("OR_gate_thm", ``!p L . ~NULL L /\ (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ mutual_indep p L  ==> (prob p (FTree p (OR (gate_list L))) =
       1 -  list_prod (one_minus_list (list_prob p L)))``,
RW_TAC real_ss[OR_lem6,real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
++ (`prob p (FTree p (AND (gate_list (compl_list p L)))) = list_prod (list_prob p (compl_list p L))` by MATCH_MP_TAC AND_gate_thm)
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
++ RW_TAC std_ss[OR_lem7]);
(*----------------------------*)
(*  NAND Fault Tree Gate      *)
(*----------------------------*)
(*-------AND_gate_append----*)
val AND_gate_append = store_thm("AND_gate_append",
 ``!p h L1. prob_space p /\ (!x. MEM x (h++L1) ==> x IN events p) ==> 
      	    (FTree p (AND (gate_list h)) INTER
	      FTree p (AND (gate_list L1)) =
	     FTree p (AND (gate_list (h ++ L1))))``,
REPEAT GEN_TAC
++ Induct_on `h`
>> (RW_TAC list_ss[gate_list_def,FTree_def]
   ++ MATCH_MP_TAC INTER_PSPACE
   ++ RW_TAC std_ss[AND_gate_eq_big_inter]
   ++ MATCH_MP_TAC in_events_big_inter
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC list_ss[gate_list_def,FTree_def]
++ (`(!x. MEM x ((h ++ L1):'a  event list) ==> x IN events p)` by RW_TAC std_ss[MEM_APPEND] )
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM INTER_ASSOC]);

(*----------------------------*)
val NAND_eq_big_inter_alt_form = store_thm("NAND_eq_big_inter_alt_form",
  ``!p L1 L2. (prob_space p ∧ ∀x. MEM x (compl_list p L1 ++ L2) ⇒ x ∈ events p) ==> 
       	      		((big_inter p (compl_list p L1) ∩ big_inter p L2) = 
			(FTree p (AND (gate_list (compl_list p L1 ++ L2)))))``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[GSYM AND_gate_append]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[AND_gate_eq_big_inter]);


(*---------------------------*)
val NAND_FT_gate = store_thm("NAND_FT_gate",
  ``!p L1 L2. 
       prob_space p /\
       (1 ≤ LENGTH (L1 ++ L2)) /\
       (!x'. MEM x' (L1++L2) ==> x' IN  events p) /\
       mutual_indep p (L1++L2) ==>
        (prob p (FTree p (AND (gate_list (compl_list p L1 ++ L2)))) =
	 list_prod (list_prob p (compl_list p L1)) * list_prod (list_prob p L2))  ``,
RW_TAC std_ss[]
++ MP_TAC(Q.ISPECL [`(L1:('a->bool)list)`,`(L2:('a->bool)list)`,`(LENGTH (compl_list p L1)):num`,`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`] prob_indep_big_inter2)
++ RW_TAC std_ss[TAKE_LENGTH_ID]
++ DEP_REWRITE_TAC[GSYM NAND_eq_big_inter_alt_form]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[]
++ FULL_SIMP_TAC list_ss[compl_list_def]
++ FULL_SIMP_TAC list_ss[MEM_MAP]
++ MATCH_MP_TAC EVENTS_COMPL
++ RW_TAC std_ss[]);

(*-------------------*)
(* ------------------------------------------------------------------------- *)
(*                 NOR_FT gate Theorem     *)
(* ------------------------------------------------------------------------- *)
val NOR_FT_gate_def = Define `NOR_FT_gate p L = (p_space p DIFF FTree p (OR (gate_list L)))`;

(*-------------------*)
val NOR_gate_thm = store_thm("NOR_gate_thm", ``!p L . ~NULL L /\ (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ mutual_indep p L  ==> (prob p (NOR_FT_gate p L) =
       list_prod (one_minus_list (list_prob p L)))``,
RW_TAC std_ss[NOR_FT_gate_def]
++ DEP_REWRITE_TAC[PROB_COMPL]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[OR_lem3]
   ++ RW_TAC std_ss[])
++ DEP_REWRITE_TAC [OR_gate_thm]
++ RW_TAC real_ss[]);

(*----------------------------------------------------*)
(*---------------------xor_gate_temp1-----------------------------------*)
val xor_gate_temp1 = store_thm("xor_gate_temp1",
  ``!A B. ((COMPL A INTER B) UNION (COMPL B INTER A)) = (A DIFF B) UNION (B DIFF A)  ``,
SRW_TAC[][COMPL_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------- xor_gate_temp2---------------------------------*)
val xor_gate_temp2 = store_thm("xor_gate_temp2",
``!A B . A DIFF B = A DIFF (A INTER B)``,
SRW_TAC[][COMPL_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------PROB_COMPL_SUBSET----------------------------------*)
val PROB_COMPL_SUBSET = store_thm("PROB_COMPL_SUBSET",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ t SUBSET s ==> (prob p (s DIFF t) = prob p s - prob p t)  ``,
METIS_TAC [MEASURE_COMPL_SUBSET,prob_space_def,events_def,prob_def,p_space_def]);
(*--------------------PROB_XOR_GATE------------------------------------*)
val PROB_XOR_GATE = store_thm("PROB_XOR_GATE",
  ``!A B p .  prob_space p /\ A IN events p /\ B IN events p ==>
(prob p  ((COMPL A INTER B) UNION (COMPL B INTER A)) = prob p A + prob p B - 2 *prob p (A INTER B))``,
RW_TAC std_ss[xor_gate_temp1]
++ MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `A DIFF B:'a->bool`,`(B DIFF A):'a->bool`,
                 `(A DIFF B UNION (B DIFF A)):'a->bool`]
       PROB_ADDITIVE )
++ FULL_SIMP_TAC std_ss[EVENTS_DIFF]
++ KNOW_TAC(--`DISJOINT (A DIFF B) (B DIFF (A:'a->bool))`--)
>> (RW_TAC std_ss[DISJOINT_DIFF]
   ++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ ONCE_REWRITE_TAC[xor_gate_temp2]
++  MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `A:'a->bool`,`(A INTER B):'a->bool`]
       PROB_COMPL_SUBSET)
++ FULL_SIMP_TAC std_ss[INTER_SUBSET,EVENTS_INTER]
++ MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `B:'a->bool`,`(B INTER A):'a->bool`]
       PROB_COMPL_SUBSET)
++ FULL_SIMP_TAC std_ss[INTER_SUBSET,EVENTS_INTER]
++ RW_TAC std_ss[INTER_COMM]
++ REAL_ARITH_TAC);
(*-----prob_compl_A_INTER_B-----------------*)
val prob_compl_A_INTER_B = store_thm("prob_compl_A_INTER_B",
  ``!a b p. prob_space p ∧ a ∈ events p ∧ b ∈ events p ⇒
     (prob p (compl_pspace p a ∩ b) = prob p b - prob p (a ∩ b))``,
RW_TAC std_ss[]
++ REWRITE_TAC[REAL_EQ_SUB_LADD]
++ MATCH_MP_TAC EQ_SYM
++ ONCE_REWRITE_TAC[REAL_ADD_SYM]
++ RW_TAC std_ss[prob_B]);
(*-----compl_event_nevent_empty-----------------*)
val compl_event_nevent_empty = store_thm("compl_event_nevent_empty",
  ``!p A. compl_pspace p A INTER A = EMPTY``,
RW_TAC std_ss[compl_pspace_def]
++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]);

(*--------------------PROB_XOR_GATE1------------------------------------*)
val PROB_XOR_GATE1 = store_thm("PROB_XOR_GATE1",
  ``!A B p .  prob_space p /\ A IN events p /\ B IN events p ==>
(prob p  (((p_space p DIFF A) INTER B) UNION ((p_space p DIFF B) INTER A)) = 
prob p A + prob p B - 2 *prob p (A INTER B)) ``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_COMPL]
   ++ RW_TAC std_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_COMPL]
   ++ RW_TAC std_ss[])
++ REWRITE_TAC[GSYM  compl_pspace_def]
++ RW_TAC std_ss[prob_compl_A_INTER_B]
++ (`compl_pspace p A ∩ B ∩ (compl_pspace p B ∩ A) = EMPTY` by ALL_TAC)
>> (FULL_SIMP_TAC std_ss[prove (``!a b c d. (a INTER b INTER (c INTER d)) = ((a INTER d) INTER (c INTER b ))``, RW_TAC std_ss[]++(SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]))]
++ RW_TAC std_ss[compl_event_nevent_empty]
++ RW_TAC std_ss[INTER_IDEMPOT])
++ POP_ORW 
++ RW_TAC real_ss[PROB_EMPTY]
++ RW_TAC real_ss[real_sub,REAL_ADD_ASSOC]
++  SUBST_OCCS_TAC [([1], SPECL [``B:('a->bool)``, ``A:('a->bool)``] 
                               INTER_COMM)]
++ REAL_ARITH_TAC);
(*--------------------*)
val XOR_FT_gate_def = Define 
    `XOR_FT_gate p A B = 
     FTree p (OR [AND [NOT A; B] ; AND [A;NOT B]])`;
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*    XOR Fault Tree Gate                                                     *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*--------------------XOR_FT_gate Theorem------------------------------------*)
val XOR_FT_gate_thm = store_thm("XOR_FT_gate_thm",
  ``!a b p.  prob_space p /\ a IN events p /\ 
       	      b IN events p /\ indep p a b ==>
	    (prob p  (XOR_FT_gate p (atomic a) (atomic b)) = 
	    prob p a * (1 - prob p b) + prob p b * 
	    	 (1 - prob p a))``,
RW_TAC std_ss[XOR_FT_gate_def, FTree_def]
++ RW_TAC std_ss[UNION_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``b:('a->bool)``, ``p_space p:('a->bool)``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[INTER_ASSOC]
++ FULL_SIMP_TAC std_ss[prove (``!a b c. a INTER b INTER c = b INTER (c INTER a)``, RW_TAC std_ss[]++(SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]))]
++ SUBST_OCCS_TAC [([1], SPECL [``b:('a->bool)``, ``p_space p:('a->bool)``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[PROB_XOR_GATE1]
++ FULL_SIMP_TAC std_ss[indep_def]
++ REAL_ARITH_TAC);



(******************************************************************************)
(*                                                                            *)
(*  Inhibit Gate                                                              *)
(*                                                                            *)
(******************************************************************************)
val inhibit_FT_gate_def = Define 
    `inhibit_FT_gate p A B C =
     FTree p (AND [OR [A;B]; NOT C])`;

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
(*-----------------------------*)
val indep_compl_event_nevents = store_thm("indep_compl_event_nevents",
  ``!p A B C. prob_space p /\  A IN events p /\ 
       	      B IN events p /\ C IN events p /\ 
	      mutual_indep p [A;B;C] ==>
       (prob p (compl_pspace p C INTER A INTER B) = 
       prob p A * prob p B − prob p A * prob p B * prob p C) ``,
RW_TAC std_ss[]
++ REWRITE_TAC [GSYM INTER_ASSOC]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[EVENTS_INTER])
++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``A INTER B:'a event``] 
                               INTER_COMM)]
++ `((A INTER B) = FTree p (AND (gate_list [A;B]))) /\
   		 	       	      	 ((A INTER B INTER C) =  FTree p (AND (gate_list [A;B;C])))` by RW_TAC list_ss[gate_list_def,FTree_def] 
>> (SUBST_OCCS_TAC [([1], SPECL [``B:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
    ++ RW_TAC std_ss[INTER_PSPACE])
>> (SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
    ++ RW_TAC std_ss[INTER_PSPACE]
    ++ REWRITE_TAC[INTER_ASSOC])
++ POP_ORW ++ POP_ORW
++ DEP_REWRITE_TAC[AND_gate_thm]
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_cons
   ++ EXISTS_TAC(--`C:'a event`--)
   ++ RW_TAC std_ss[prove (``[C;A;B] = [C] ++ [A;B]``, RW_TAC list_ss[])]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[list_prob_def,list_prod_def]
++ RW_TAC real_ss[]
++ REAL_ARITH_TAC);
(*-----------------------------*)
val inhibit_FT_gate_thm = store_thm("inhibit_FT_gate_thm",
  ``!p A B C.  prob_space p /\ A IN events p /\ 
       	      B IN events p /\ C IN events p /\ 
	      mutual_indep p [A;B;C] ==>
	    (prob p (inhibit_FT_gate p (atomic A) (atomic B) (atomic C)) = 
	    (1 - (1 - prob p A) * (1 - prob p B)) * (1 - prob p C))``,
RW_TAC std_ss[inhibit_FT_gate_def, FTree_def]
++ RW_TAC std_ss[UNION_EMPTY,UNION_ASSOC]
++ SUBST_OCCS_TAC [([1], SPECL [``(p_space p DIFF C)``, ``p_space p``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[EVENTS_COMPL])
++ ONCE_REWRITE_TAC[INTER_COMM]
++ REWRITE_TAC[UNION_OVER_INTER]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER]
   ++ RW_TAC std_ss[EVENTS_COMPL])
>> (DEP_REWRITE_TAC[EVENTS_INTER]
   ++ RW_TAC std_ss[EVENTS_COMPL])
++ REWRITE_TAC[GSYM compl_pspace_def]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[prove(``!A B C. A INTER B INTER (A INTER C) = A INTER B INTER C``, RW_TAC std_ss[] ++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[])]
++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``B:'a event``] 
                               INTER_COMM)]
++ (`mutual_indep p [C;A] /\ 
   mutual_indep p [B;C]` by RW_TAC std_ss[])
>> (MATCH_MP_TAC mutual_indep_cons
   ++ EXISTS_TAC(--`B:'a->bool`--)
   ++ FULL_SIMP_TAC std_ss[prove(``!A B C. [B;C;A] = [B;C]++[A]``, RW_TAC list_ss[])]
   ++ MATCH_MP_TAC mutual_indep_append_sym
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC mutual_indep_cons
   ++ EXISTS_TAC(--`A:'a->bool`--)
   ++ RW_TAC std_ss[])
++ DEP_REWRITE_TAC[indep_compl_event_nevents]
++ RW_TAC std_ss[]
++ (`((C INTER A) = FTree p (AND (gate_list [C;A]))) /\ ((B INTER C) = FTree p (AND (gate_list [B;C])))` by RW_TAC std_ss[])
>> (RW_TAC std_ss[FTree_def,gate_list_def]
   ++ SUBST_OCCS_TAC [([1], SPECL [``A:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
   ++ RW_TAC std_ss[INTER_PSPACE])
>> (RW_TAC std_ss[FTree_def,gate_list_def]
   ++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
   ++ RW_TAC std_ss[INTER_PSPACE])
++ POP_ORW ++ POP_ORW
++ DEP_REWRITE_TAC[AND_gate_thm]
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[list_prod_def,list_prob_def]
++ REAL_ARITH_TAC);

(******************************************************************************)
(*                                                                            *)
(*          Comparator Fault Tree Gate                                        *)
(*                                                                            *)
(******************************************************************************)

val comp_FT_gate_def = Define 
    `comp_FT_gate p A B = FTree p (OR [AND [A; B]; NOT (OR [A;B])])`;


val comp_FT_gate_thm = store_thm("comp_FT_gate_thm",
  ``!p A B. prob_space p /\ A IN events p /\ 
       	      B IN events p /\ 
	      indep p A B ==> 
	      (prob p (comp_FT_gate p (atomic A) (atomic B)) = 
	      (1 − (prob p A + prob p B − 2* (prob p A * prob p B))))``,
RW_TAC std_ss[comp_FT_gate_def,FTree_def,UNION_EMPTY]
++ REWRITE_TAC[OR_lem1]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (MATCH_MP_TAC EVENTS_INTER
   ++ ONCE_REWRITE_TAC[INTER_COMM]
   ++ RW_TAC std_ss[INTER_PSPACE])
>> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[EVENTS_COMPL])
++ REWRITE_TAC[GSYM OR_lem1]
++ DEP_REWRITE_TAC[PROB_COMPL]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ REWRITE_TAC[OR_lem1]
++ (`(A ∩ (B ∩ p_space p) ∩ ((p_space p DIFF A) ∩ (p_space p DIFF B))) = EMPTY` by 
   SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION])
>> (METIS_TAC[])
++ POP_ORW
++ DEP_ASM_REWRITE_TAC[EVENTS_UNION]
++ RW_TAC real_ss[PROB_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``B:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
++ DEP_ASM_REWRITE_TAC[INTER_PSPACE]
++ FULL_SIMP_TAC std_ss[indep_def]
++ REAL_ARITH_TAC);

(*-----------------------------------------------------*)
(* ----------------------------------------------------*)
(* 	K-out-N RBD	                               *)
(* ----------------------------------------------------*)


val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);


val binomial_def= 
Define `(binomial n 0 = (1:num)) /\
        (binomial 0 (SUC k) = (0:num)) /\
        (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)`;

(*--------------------sum_set------------------------------------*)

val sum_set_def =  Define `sum_set s f =  REAL_SUM_IMAGE f s`;
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Definition:         K_out_N_struct_def                                    *)
(* ------------------------------------------------------------------------- *)
val K_out_N_struct_def =  Define `
K_out_N_struct p X k n = 
(BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) 
	  ({x|(k:num) <= x /\ x < SUC n})))`;

(* ------------------------------------------------------------------------- *)
(* SUM_0_SUM_1			                                             *)
(* ------------------------------------------------------------------------- *)

val SUM_0_SUM_1 = store_thm("SUM_0_SUM_1",
  ``!n f. (sum (0,SUC n) f = f (0) + sum (1,n) f )``,
Induct_on `n` THEN 
RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
(* ------------------------------------------------------------------------- *)
(* SUM_0_SUM_2			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_0_SUM_2 = store_thm("SUM_0_SUM_2",
  ``!n f. sum (0,SUC (SUC n)) f = f(0) + f(1)+ sum (2,n) f``,
Induct_on `n`
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);

(* ------------------------------------------------------------------------- *)
(* SUM_1_SUM_2			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_1_SUM_2 = store_thm("SUM_1_SUM_2",
  ``!n f. sum (1,SUC n) f = f (1) + sum (2,n) f``,
Induct_on `n` 
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
(* ------------------------------------------------------------------------- *)
(* SUM_SHIFT			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SHIFT = store_thm("SUM_SHIFT",
  ``!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))``,
Induct_on `n` THEN RW_TAC real_ss [sum]);
(* ------------------------------------------------------------------------- *)
(* SUM_SHIFT_P			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SHIFT_P = store_thm("SUM_SHIFT_P",
  ``!n p f. sum (p, n) (\i. f ((i+1))) = sum (p+1, n) f``,
RW_TAC std_ss []
++ Induct_on `n`
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum]);
(* ------------------------------------------------------------------------- *)
(* SUM_C_EQ			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_C_EQ = store_thm("SUM_C_EQ",
  ``!n m (c:real). sum (n,SUC m) (\i. c)= &(m + 1)*c``,
RW_TAC std_ss []
++ Induct_on`m`
++ RW_TAC real_ss [sum]
++ ONCE_REWRITE_TAC [sum]
++ RW_TAC std_ss []
++ ONCE_REWRITE_TAC [GSYM add_ints]
++ RW_TAC real_ss [SUC_ONE_ADD]
++ ONCE_REWRITE_TAC [GSYM add_ints]
++ REAL_ARITH_TAC);
(* ------------------------------------------------------------------------- *)
(* SUM_SWITCH_SUM		                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SWITCH_SUM = store_thm("SUM_SWITCH_SUM",
  ``!f n1 n2 m1 m2. 
       sum (n1,m1) (\i. sum (n2,m2)(\j. f i j)) = 
       sum (n2,m2) (\j. sum (n1,m1)(\i. f i j))``,
RW_TAC std_ss []
++ Induct_on `m1`
++ RW_TAC real_ss [sum,SUM_0]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]
++ POP_ORW
++ RW_TAC real_ss [SUM_ADD]);

(* ------------------------------------------------------------------------- *)
(* 	SUM_POS_LT	                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_POS_LT = store_thm("SUM_POS_LT",
  ``!f. (!n. 0 < f n) ==> (!m n. 0 < sum (m,SUC n) f)``,
RW_TAC std_ss []
++ Induct_on `n`
>> (RW_TAC real_ss [sum])
++ ONCE_REWRITE_TAC [sum]
++ METIS_TAC [REAL_LT_ADD]);

(* ---------------------------------------------------*)
(* 	BINOMIAL_DEF1	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF1 = store_thm("BINOMIAL_DEF1",
  ``!n. binomial n  0 = 1``,
Cases_on `n` THEN REWRITE_TAC [binomial_def]); 
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF2	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF2 = store_thm("BINOMIAL_DEF2",
  ``!n k. n < k ==> (binomial n k = 0)``,
Induct_on `n`
>> (Cases_on `k`
>> (RW_TAC real_ss [])
   ++ REWRITE_TAC [binomial_def])
++ Cases_on `k`
>> (RW_TAC real_ss [])
++ RW_TAC arith_ss [binomial_def]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF3	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF3 = store_thm("BINOMIAL_DEF3",
  ``!n. (binomial n n = 1)``,
Induct_on `n` THEN 
REWRITE_TAC [binomial_def] THEN 
RW_TAC arith_ss [BINOMIAL_DEF2]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF4	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF4 = store_thm("BINOMIAL_DEF4",
  ``!n k. (binomial (SUC n) (SUC k) = 
       	   binomial n (SUC k) + binomial n k)``,
REWRITE_TAC [binomial_def]); 
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF5	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF5 = store_thm("BINOMIAL_DEF5",
  ``!n k. k <= n ==> (binomial n k <> 0)``,
Induct_on `n`
>> (Cases_on `k`
   >> (RW_TAC real_ss []
      ++ RW_TAC real_ss [binomial_def])
   ++ RW_TAC real_ss [])
++ Cases_on `k`
>> (RW_TAC real_ss []
   ++ RW_TAC arith_ss [binomial_def])
++ RW_TAC arith_ss [binomial_def]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_FACT	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_FACT = store_thm("BINOMIAL_FACT",
  ``!a b. binomial (a+b) b * (FACT a * FACT b) = FACT (a+b)``,
Induct_on `b`
>> (REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ Induct_on `a`
>> (REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ `SUC a + SUC b = SUC (SUC a + b)` by RW_TAC arith_ss [ADD_CLAUSES]
++ (ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB])
++ POP_ORW
++ `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b)) =
    (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b))) * SUC a` 
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC[]
++ POP_ORW
++ `binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b)) =
                       (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC [ADD_CLAUSES, FACT]
++ REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
++ `SUC a + SUC b = SUC (SUC (a + b))` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[]
++ RW_TAC arith_ss []);
(* --------------------------------------------------- *)
(* 	BINOMIAL_DEF6	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_DEF6 = store_thm("BINOMIAL_DEF6",
  ``!n. (binomial (SUC n) 1 = SUC n)``,
RW_TAC std_ss []
++ ONCE_REWRITE_TAC[ONE]
++ (MP_TAC o Q.SPECL [`n`,`SUC 0`]) BINOMIAL_FACT
++ ONCE_REWRITE_TAC[FACT]
++ ONCE_REWRITE_TAC[GSYM ONE]
++ ONCE_REWRITE_TAC[ADD_COMM]
++ ONCE_REWRITE_TAC[GSYM SUC_ONE_ADD]
++ ONCE_REWRITE_TAC[FACT]
++ STRIP_TAC
++ FULL_SIMP_TAC real_ss [EQ_MULT_LCANCEL]
++ METIS_TAC [FACT_LESS, NOT_ZERO_LT_ZERO]);
(* --------------------------------------------------- *)
(* 	BINOMIAL_DEF7	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_DEF7 = store_thm("BINOMIAL_DEF7",
  ``!n k. 0 <= binomial n k``,
Induct_on `n`
++ RW_TAC arith_ss [binomial_def]
++ RW_TAC arith_ss [binomial_def]);
(* --------------------------------------------------- *)
(* 	BINOMIAL_FACT	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_FACT = store_thm("BINOMIAL_FACT",
  ``!a b. binomial (a+b) b * (FACT a * FACT b) = FACT (a+b)``,
Induct_on `b`
 >> (REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ Induct_on `a`
>> (REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ `SUC a + SUC b = SUC (SUC a + b)` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
++ POP_ORW
++  `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b)) =
                   (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b))) * SUC a` 
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC[]
++ POP_ORW
++ `binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b)) =
                       (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC [ADD_CLAUSES, FACT]
++ REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
++ `SUC a + SUC b = SUC (SUC (a + b))` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[]
++ RW_TAC arith_ss []);
(* -----------------BINOMIAL_DEF2--------------------------- *)
val BINOMIAL_DEF2 = store_thm("BINOMIAL_DEF2",
  ``!n k. n < k ==> (binomial n k = 0)``,
Induct_on `n`
>> (Cases_on `k`
   >> (RW_TAC real_ss [])
   ++ REWRITE_TAC [binomial_def])
++ Cases_on `k`
>> (RW_TAC real_ss [])
++ RW_TAC arith_ss [binomial_def]);
(* -----------------BINOMIAL_DEF3--------------------------- *)
val BINOMIAL_DEF3 = store_thm("BINOMIAL_DEF3",
  ``!n. (binomial n n = 1)``,
Induct_on `n` THEN REWRITE_TAC [binomial_def] THEN RW_TAC arith_ss [BINOMIAL_DEF2]);
(* -----------------BINOMIAL_DEF4--------------------------- *)
val BINOMIAL_DEF4 = store_thm("BINOMIAL_DEF4",
  ``!n k. (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)``,
REWRITE_TAC [binomial_def]); 
(* -----------------BINOMIAL_DEF6--------------------------- *)
val BINOMIAL_DEF6 = store_thm("BINOMIAL_DEF6",
  ``!n. (binomial (SUC n) 1 = SUC n)``,
RW_TAC std_ss []
++ ONCE_REWRITE_TAC[ONE]
++ (MP_TAC o Q.SPECL [`n`,`SUC 0`]) BINOMIAL_FACT
++ ONCE_REWRITE_TAC[FACT]
++ ONCE_REWRITE_TAC[GSYM ONE]
++ ONCE_REWRITE_TAC[ADD_COMM]
++ ONCE_REWRITE_TAC[GSYM SUC_ONE_ADD]
++ ONCE_REWRITE_TAC[FACT]
++ STRIP_TAC
++ FULL_SIMP_TAC real_ss [EQ_MULT_LCANCEL]
++ METIS_TAC [FACT_LESS, NOT_ZERO_LT_ZERO]);
(* --------------------------------------------------------- *)
(* 	EXP_PASCAL_REAL	                                     *)
(* --------------------------------------------------------- *)
val EXP_PASCAL_REAL = store_thm("EXP_PASCAL_REAL",
  ``!(a:real) (b:real) n. 
((a + b) pow n = REAL_SUM_IMAGE (\x. &(binomial n x) * a pow (n - x) * b pow x) (count (SUC n)))``,
Induct_on `n`
>> (RW_TAC real_ss [pow, BINOMIAL_DEF3]
   ++ `count 1 = 0 INSERT {}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
   ++ POP_ORW
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_SING,BINOMIAL_DEF1])
++ ONCE_REWRITE_TAC [pow]
++ POP_ORW
++ RW_TAC real_ss []
++ ONCE_REWRITE_TAC [REAL_ADD_RDISTRIB]
++ `FINITE (count (SUC n))` by METIS_TAC [COUNT_SUC, FINITE_INSERT,FINITE_COUNT]
++ RW_TAC real_ss [GSYM REAL_SUM_IMAGE_CMUL]
++ RW_TAC real_ss [REAL_SUM_IMAGE_COUNT]
++ Know ` sum (0,SUC n) (\x. a* (&binomial n x * a pow (n  - x) * b pow x)) =
a pow (n+1)+ sum (1, SUC n) (\x. a*(&binomial n x * a pow (n - x) * b pow x)) `
>> (RW_TAC real_ss [SUM_0_SUM_1, BINOMIAL_DEF1,sum, BINOMIAL_DEF2,GSYM pow,ADD1]
   ++ RW_TAC real_ss [])
++ DISCH_TAC
++ POP_ORW
++ Know ` sum (0,SUC n) (\x. b* (&binomial n x * a pow (n - x) * b pow x)) =
sum (0, n) (\x. b*(&binomial n x * a pow (n - x) * b pow x)) + b pow (n+1) `
>> (RW_TAC real_ss [sum, BINOMIAL_DEF3,GSYM pow,ADD1]
   ++ RW_TAC real_ss [])
++ DISCH_TAC
++ POP_ORW
++ RW_TAC real_ss [GSYM ADD1,pow]
++ RW_TAC real_ss [SUM_SHIFT]
++ RW_TAC real_ss [REAL_ADD_ASSOC]
++ Know ` sum (1,SUC n) (\x. a * (&binomial n x * a pow (n - x) * b pow x))=
sum (1, n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)`
>> (RW_TAC real_ss [sum, BINOMIAL_DEF2]
   ++ MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss []
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ Know ` a * &binomial n r * a pow (n - r)= &binomial n r * a pow (n + 1 - r)`
   >> (ONCE_REWRITE_TAC [REAL_MUL_COMM]
      ++ RW_TAC real_ss [REAL_MUL_ASSOC]
      ++ Know ` a pow (n - r) * a= a pow (n + 1 - r) `
      >> (ONCE_REWRITE_TAC [REAL_MUL_COMM]
      	 ++ RW_TAC real_ss [GSYM pow]
	 ++ RW_TAC real_ss [ADD1])
      ++ RW_TAC real_ss [])
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss []
++ POP_ORW
++ ONCE_REWRITE_TAC [REAL_ADD_COMM]
++ Know ` sum (1,n) (\i. b * (&binomial n (i - 1) * a pow (n - (i - 1)) * b pow (i - 1)))=
sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i) `
>> (MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ Suff ` b pow (r - 1) * b= b pow r `
   >> (RW_TAC real_ss [])
   ++ `r=SUC (r - 1)` by RW_TAC real_ss []	
   ++ ONCE_ASM_REWRITE_TAC []
   ++ RW_TAC real_ss [pow, ADD, REAL_MUL_COMM]
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss[]
++ POP_ORW
++ Know ` sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)=
sum (1,n) (\i. &binomial (SUC n) (SUC (i-1)) * a pow (n - i + 1) * b pow i)`
>> (RW_TAC real_ss [GSYM SUM_ADD]
   ++ MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss [BINOMIAL_DEF4]
   ++ ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC]
   ++ RW_TAC real_ss [GSYM REAL_ADD_RDISTRIB,ADD1]
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss [GSYM pow]
++ RW_TAC real_ss[]
++ `b pow (SUC n) +
    (a pow (SUC n) +
     sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)= 
b pow (SUC n)+ a pow (SUC n) +
     sum (1,n) (\i. &binomial (SUC n) (SUC (i - 1)) * a pow (n - i + 1) * b pow i)` by ALL_TAC
>> (RW_TAC real_ss []
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
   ++ RW_TAC real_ss [REAL_EQ_LADD]
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
   ++ RW_TAC real_ss [REAL_EQ_LADD])
++ FULL_SIMP_TAC std_ss[REAL_ADD_ASSOC]
++ POP_ORW
++ `sum (1,SUC (SUC n))
      (\i. (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i) (i-1))=
sum (0,SUC (SUC n))
      (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i)` by RW_TAC real_ss [GSYM SUM_SHIFT]
++ FULL_SIMP_TAC real_ss []
++ POP_ORW
++ ONCE_REWRITE_TAC [sum]
++ ONCE_REWRITE_TAC [SUM_0_SUM_1]
++ RW_TAC real_ss [pow,BINOMIAL_DEF1, BINOMIAL_DEF3]
++ ONCE_REWRITE_TAC [GSYM pow]
++ ONCE_REWRITE_TAC [ADD1]
++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
++ `a pow (n + 1) +
    (sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i) +
     b pow (n + 1))= b pow (n + 1) +
    (a pow (n + 1) +
    sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i))` by REAL_ARITH_TAC
++ POP_ORW
++ RW_TAC real_ss [REAL_EQ_LADD]
++ MATCH_MP_TAC SUM_EQ
++ RW_TAC real_ss [ADD1]);
(* ---------------------------------------------------------- *)
(* 	EXP_PASCAL_REAL1	                              *)
(* ---------------------------------------------------------- *)
val EXP_PASCAL_REAL1 = store_thm("EXP_PASCAL_REAL1",
  ``!(a:real) (b:real) n. 
((a + b) pow n = 
 sum_set (count (SUC n))  (\x. &(binomial n x) * a pow (n - x) * b pow x))``,
RW_TAC std_ss[sum_set_def,EXP_PASCAL_REAL]);

(*------------------------------------------------------------*)

(*-----------------num_neq------------------------------------*)
 val num_neq = store_thm("num_neq",
  ``!a b:num.  (a <> b) = a < b \/ b < a``,
RW_TAC std_ss []
++ RW_TAC std_ss [NOT_NUM_EQ]
++ EQ_TAC
>> (RW_TAC arith_ss[])
++ RW_TAC arith_ss[]);
(*------------------disj_thm---------------------------------*)
val disj_thm = store_thm("disj_thm",
  ``!X (m:num) (n:num).(m <> n)==>  DISJOINT ((PREIMAGE X {Normal &m} INTER p_space p) ) ((PREIMAGE X {Normal &n} INTER p_space p) )``,
RW_TAC std_ss [DISJOINT_ALT]
++ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]
++ RW_TAC std_ss [DISJOINT_ALT]
++ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]);


(*--------------k_out_n_lemma1--------------------------*)
val k_out_n_lemma1 = store_thm("k_out_n_lemma1",
  ``!p s n k.
       prob_space p /\ 
       ((\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count n) -> events p)) ==> 
        ((IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) (count n)) SUBSET events p)``,
FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[SUBSET_DEF]
++ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]);
(*------------------k_out_n_lemma2---------------------*)
val k_out_n_lemma2 = store_thm("k_out_n_lemma2",
  ``!k n:num. 
       {x |  k<= x /\ x < n} = {x |  k<= x } INTER {x |x < n}``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
(*----------------------k_out_ntemp1-------------------*)
val k_out_ntemp1 = store_thm("k_out_ntemp1",
  ``!k n:num. 
       n INSERT {x |  k <= x /\ x < n} =  
       n INSERT {x | x < n /\  k <= x }``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]
++ METIS_TAC[]);
(*--------------------------k_out_n_temp2--------------*)
val k_out_n_temp2 = store_thm("k_out_n_temp2",
  ``!k n:num. 
       {x | x < n /\ k <= x} = {x |x < n} INTER {x | k <= x}``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
(*-------------------------------------------------------*)
(*val k_out_n_temp1 = store_thm("k_out_n_temp1",
  ``!k n:num.  {x |  k <= x /\ x < (SUC n)}  = n INSERT  {x | k <= x /\ x < n}``,
RW_TAC std_ss[k_out_ntemp1]
++ RW_TAC std_ss[k_out_n_temp2]
++ RW_TAC std_ss[GSYM count_def]
++ ` n INSERT count n INTER {x | k <= x} =  
     (n INSERT count n) INTER {x | k <= x}` by ALL_TAC
>> (RW_TAC std_ss[GSYM COUNT_SUC]
   ++ RW_TAC std_ss[]);
e (KNOW_TAC (--`{x | k <= x /\ x < n} = {x |  x < n /\ k <= x}`--));
e (SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
e (METIS_TAC[]);
e (RW_TAC std_ss[k_out_ntemp1]);
e (RW_TAC std_ss[k_out_n_lemma2]);
e (SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
val k_out_n_temp1 = top_thm();
drop();
*)
(*---------------------k_out_n_lemma3---------------------*)
val k_out_n_lemma3 = store_thm("k_out_n_lemma3",
  ``!k n:num. FINITE {x | k <= x /\ x < n}``,
GEN_TAC
++ RW_TAC std_ss[k_out_n_lemma2]
++ FULL_SIMP_TAC std_ss[k_out_n_lemma2]
++ MATCH_MP_TAC FINITE_INTER
++ DISJ2_TAC
++ ONCE_REWRITE_TAC[GSYM count_def]
++ RW_TAC std_ss[FINITE_COUNT]);
(*------------------k_out_n_lemma4------------------------*)
val k_out_n_lemma4 = store_thm("k_out_n_lemma4",
  ``!k (n:num). (k < n) ==>  (({x | k <= x /\ x < n} UNION count k) = count n)``,
SRW_TAC[][EXTENSION,IN_COUNT,GSPECIFICATION,IN_UNION]
++ EQ_TAC
>> (RW_TAC arith_ss[])
++ RW_TAC arith_ss[]);
(*---------------------k_out_n_temp5---------------------*)
val k_out_n_temp5 = store_thm("k_out_n_temp5",
  ``!p n k X.
       prob_space p /\ 
       (k < (SUC n)) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count (SUC n)) -> events p) /\
       (s = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) ({x|(k:num) <= x /\ 
       x < (SUC n)}))) ==>
       	 (sum (k, (SUC n)-k) (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p)) = 
       	  prob p s)``,
RW_TAC std_ss []
++ ONCE_REWRITE_TAC[SUM_DIFF]
++ RW_TAC real_ss[]
++ KNOW_TAC (--`(sum (0,SUC n) (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p)) = 
prob p (BIGUNION (IMAGE (\x. PREIMAGE X {Normal &x} INTER p_space p) (count (SUC n)))))`--)
>> (MATCH_MP_TAC PROB_FINITELY_ADDITIVE 
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC disj_thm
   ++ RW_TAC std_ss [])
++ DISCH_TAC ++ POP_ORW
++ KNOW_TAC (--`(sum (0,k) (prob p o (\x. PREIMAGE X {Normal &x} INTER p_space p)) = prob p (BIGUNION (IMAGE (\x. PREIMAGE X {Normal &x} INTER p_space p) (count k))))`--)
>> (MATCH_MP_TAC PROB_FINITELY_ADDITIVE 
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC real_ss [IN_FUNSET,IN_COUNT]
   ++ MATCH_MP_TAC disj_thm
   ++ RW_TAC std_ss [])
++ DISCH_TAC ++ POP_ORW
++ RW_TAC std_ss [REAL_EQ_SUB_RADD]
++ MATCH_MP_TAC PROB_ADDITIVE
++ RW_TAC std_ss []
>> (MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ RW_TAC std_ss []
   >> (FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
      ++ RW_TAC std_ss []
      ++ FULL_SIMP_TAC std_ss[EXTENSION,GSPECIFICATION])
   ++ MATCH_MP_TAC COUNTABLE_IMAGE
   ++ MATCH_MP_TAC FINITE_COUNTABLE
   ++ RW_TAC std_ss[k_out_n_lemma2]
   ++ MATCH_MP_TAC FINITE_INTER
   ++ DISJ2_TAC
   ++ RW_TAC std_ss [GSYM count_def]
   ++ RW_TAC std_ss [FINITE_COUNT])
>> (MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ RW_TAC std_ss []
   >> (FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
      ++ RW_TAC std_ss []
      ++ KNOW_TAC (--`x' < SUC n`--)
      >> (MATCH_MP_TAC LESS_TRANS
      	 ++ EXISTS_TAC(--`k:num`--)
   	 ++ RW_TAC std_ss [])
      ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC COUNTABLE_IMAGE
   ++ RW_TAC std_ss [COUNTABLE_COUNT])
>> (RW_TAC std_ss[ DISJOINT_BIGUNION]
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   ++ MATCH_MP_TAC disj_thm
   ++ RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss[EXTENSION,GSPECIFICATION]
   ++ RW_TAC arith_ss[num_neq])
++ RW_TAC std_ss [GSYM BIGUNION_UNION]
++ RW_TAC std_ss [GSYM IMAGE_UNION]
++ RW_TAC std_ss[k_out_n_lemma4]);

(*---------------------k_out_n_lemma5---------------------*)
val k_out_n_lemma5 = store_thm("k_out_n_lemma5",
  ``!p s n k X.
       prob_space p /\ (k < n) /\ (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count n) -> events p) /\
       (s = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) ({x|(k:num) <= x /\ x < n}))) ==>
       (sum (k, n-k) (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p)) = prob p s)``,
REPEAT GEN_TAC
++ MP_TAC(Q.ISPECL [`p:α event # α event event # (α event -> real)`,`n:num - 1`,
   		   	  `k:num`,`X:'a->extreal`] k_out_n_temp5)
++ FULL_SIMP_TAC arith_ss[ADD1]
++ RW_TAC real_ss[]
++ FULL_SIMP_TAC arith_ss[]);

(*-------------------k_out_n_lemma6_new-----------------------*)
val k_out_n_lemma6_new = store_thm("k_out_n_lemma6_new",
  ``!p s n k X pr.
       prob_space p /\ (k < SUC n) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN 
       	    ((count (SUC n)) -> events p) /\
       (s = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER 
       	  p_space p) ({x|(k:num) <= x /\ x < (SUC n)}))) /\ 
       (!x. (distribution p X {Normal (&x)} = 
       ((&binomial (SUC n) x)* (pr pow x) * 
       		   ((1 - pr) pow ((SUC n)-x))))) ==>
       (sum (k, (SUC n)-k) (\x. (&binomial (SUC n) x)* (pr pow x) * 
       	    ((1- pr) pow ((SUC n)-x) )) = prob p s) ``,
RW_TAC std_ss[]
++ KNOW_TAC (--`prob p
  (BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | k <= x /\ x < (SUC n)})) = sum (k,(SUC n) - k)
        (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p))`--)
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC  k_out_n_temp5
   ++ RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW
++ FULL_SIMP_TAC std_ss[distribution_def,o_DEF]);

(*------------------k_out_n_lemma6_new1------------------------*)
val k_out_n_lemma6_new1 = store_thm("k_out_n_lemma6_new1",
  ``!p s n k X pr.
       prob_space p /\ (k < SUC n) /\ (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count (SUC n)) -> events p) /\
       (s = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) ({x|(k:num) <= x /\ x < (SUC n)}))) /\ (!x. (distribution p X {Normal (&x)} = ((& binomial (n) x)* (pr pow x) * ((1- pr) pow ((n)-x)))))==>
       (sum (k, (SUC n)-k) (\x. (& binomial (n) x)* (pr pow x) * ((1- pr) pow ((n)-x) )) = prob p s)``,
RW_TAC std_ss []
++ KNOW_TAC (--`prob p
  (BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | k ≤ x /\ x < (SUC n)})) = sum (k,(SUC n) − k)
        (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p))`--)
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC k_out_n_temp5
   ++ RW_TAC std_ss [])
++ DISCH_TAC ++ POP_ORW
++ FULL_SIMP_TAC std_ss[distribution_def,o_DEF]);
(*-------------------k_out_n_lemma6-----------------------*)
val k_out_n_lemma6 = store_thm("k_out_n_lemma6",
  ``!p s n k X pr.
       prob_space p /\ (k < n) /\ (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count n) -> events p) /\
       (s = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) ({x|(k:num) <= x /\ x < n}))) /\ (!x. (distribution p X {Normal (&x)} = ((& binomial n x)* (pr pow x) * ((1- pr) pow (n-x)))))==>
       (sum (k, n-k) (\x. (& binomial n x)* (pr pow x) * ((1- pr) pow (n-x) )) = prob p s)``,
RW_TAC std_ss []
++ KNOW_TAC (--`prob p
  (BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | k ≤ x /\ x < n})) = sum (k,n − k)
        (prob p o (\x. PREIMAGE X {Normal (&x)} INTER p_space p))`--)
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC  k_out_n_lemma5
   ++ RW_TAC std_ss [])
++ DISCH_TAC ++ POP_ORW
++ FULL_SIMP_TAC std_ss[distribution_def,o_DEF]);
(*--------------------------------------------------------*)
(*---------------------K-out_N Stucture Theorem-----------*)
(*--------------------------------------------------------*)
val k_out_n_RBD = store_thm("k_out_n_RBD",
  ``!p n k X pr.
       prob_space p /\ (k < (SUC n)) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN 
       ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} = 
       ((& binomial (SUC n) x)* (pr pow x) * ((1- pr) pow ((SUC n)-x))))) ==>
       	  (prob p 
	     (BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) 
	     	       ({x|(k:num) <= x /\ x < (SUC n)}))) = 
	    sum (k, (SUC n)-k) 
	    	(\x. (& binomial (SUC n) x)* (pr pow x) * ((1- pr) pow ((SUC n)-x) )))``,
RW_TAC std_ss []
++ MATCH_MP_TAC EQ_SYM
++ MATCH_MP_TAC  k_out_n_lemma6_new
++ EXISTS_TAC (--`X: ('a -> extreal)`--)
++ RW_TAC std_ss []);

(*----------------------------*)
val k_out_n_RBD_v1 = store_thm("k_out_n_RBD_v1",
  ``!p n k X pr.
       prob_space p /\ (k < (SUC n)) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN 
       ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} = 
       ((& binomial n x)* (pr pow x) * ((1- pr) pow (n - x))))) ==>
       	 (prob p (K_out_N_struct p X k n) = 
	    sum (k, (SUC n)-k) 
	    	(\x. (& binomial n x) * (pr pow x) * ((1 - pr) pow (n - x) )))``,
RW_TAC std_ss [K_out_N_struct_def]
++ MATCH_MP_TAC EQ_SYM
++ MATCH_MP_TAC  k_out_n_lemma6_new1
++ EXISTS_TAC (--`X: ('a -> extreal)`--)
++ RW_TAC std_ss []);
(*--------------------------------------------------------*)
(*---------------------Case: When k = 1, Parallel Structure components with
 -----------------------Identical Reliabilities-----------*)
(*--------------------------------------------------------*)
val K_out_N_Parallel_Struct = store_thm("K_out_N_Parallel_Struct",
  ``!p n X pr.
       prob_space p /\ (1 < (SUC n)) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN 
       ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} = 
	    ((& binomial n x) * (pr pow x) * ((1- pr) pow (n - x))))) ==>
       (prob p 
       	  (BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) 
	  	    ({x|(1:num) <= x /\ x < (SUC n)}))) = 
	1 - (1 - pr) pow n )``,
RW_TAC std_ss []
++ KNOW_TAC (--`(prob p
   	    	     (BIGUNION
			(IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        		       {x | 1 ≤ x /\ x < SUC n})) =  
		sum (1, (SUC n)-1) 
		    (\x. (& binomial n x) * ((pr:real) pow x) * ((1- pr) pow (n -x) ))) `--)
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC k_out_n_lemma6_new1
   ++ RW_TAC std_ss []
   ++ EXISTS_TAC(--`X:'a->extreal`--)
   ++ RW_TAC real_ss[])
++ DISCH_TAC ++ POP_ORW
++ RW_TAC arith_ss []
++ ONCE_REWRITE_TAC [SUM_DIFF]
++ RW_TAC arith_ss []
++ RW_TAC std_ss [GSYM ADD1]
++ RW_TAC std_ss [SUM_1]
++ RW_TAC real_ss [binomial_def]
++ RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
++ RW_TAC std_ss [GSYM sum_set_def]
++ KNOW_TAC (--` sum_set (count (SUC n))
  (\x. &binomial n x * pr pow x * (1 − pr) pow (n − x)) = ((pr:real)+ (1 - pr)) pow n `--)
>> (ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC]
   ++  `!x. (pr pow x * (1 − pr) pow (n − x)) = ((1 − pr) pow (n − x)* pr pow x)` by RW_TAC arith_ss [REAL_MUL_COMM]
   ++ ONCE_ASM_REWRITE_TAC[]
   ++ POP_ORW
   ++ RW_TAC std_ss[REAL_MUL_ASSOC]
   ++ ONCE_REWRITE_TAC[REAL_ADD_SYM]
   ++ RW_TAC std_ss[ EXP_PASCAL_REAL1])
++ RW_TAC real_ss[POW_ONE]);
(*--------------------------------------------------------*)
(*---------------------Case: When k = n, Series Structure components with
 -----------------------Identical Reliabilities-----------*)
(*--------------------------------------------------------*)
val K_out_N_Series_Struct = store_thm("K_out_N_Series_Struct",
  ``!p n X pr.
       prob_space p /\  (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count (SUC n)) -> events p) /\
        (!x. (distribution p X {Normal (&x)} = ((& binomial ( n) x)* (pr pow x) * ((1- pr) pow ((n)-x)))))==>
       ( prob p (BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) ({x|(n:num) <= x /\ x < (SUC n)}))) = pr pow n )``,
RW_TAC std_ss []
++ KNOW_TAC (--`(prob p
  (BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | n ≤ x /\ x < SUC n}))=  sum (n, (SUC n)-n) (\x. (& binomial (n) x)* ((pr:real) pow x) * ((1- pr) pow ((n)-x) ))) `--)
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC k_out_n_lemma6_new1
   ++ EXISTS_TAC(--`X:'a->extreal`--)
   ++ RW_TAC std_ss [])
++ DISCH_TAC ++ POP_ORW
++ RW_TAC real_ss [ADD1]
++ RW_TAC real_ss [SUM_1]
++ RW_TAC real_ss [BINOMIAL_DEF3]);



(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*            Majority Voting Gate                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val majority_voting_FT_gate_def = Define 
    `majority_voting_FT_gate p X k n = BIGUNION
        (IMAGE (λx. PREIMAGE X {Normal (&x)} ∩ p_space p)
           {x | k ≤ x ∧ x < SUC n}) `;

val majority_voting_FT_gate_thm = store_thm("majority_voting_FT_gate_thm",
  ``!p n k X pr.
       prob_space p /\ (k < (SUC n)) /\ 
       (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN 
       ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} = 
       ((& binomial (SUC n) x)* (pr pow x) * ((1- pr) pow ((SUC n)-x))))) ==>
       	  (prob p 
	     (majority_voting_FT_gate p X k n) = 
	    sum (k, (SUC n)-k) 
	    	(\x. (& binomial (SUC n) x)* (pr pow x) * ((1- pr) pow ((SUC n)-x) )))``,
RW_TAC std_ss[majority_voting_FT_gate_def,k_out_n_RBD]);

(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*       Inclusion-Exclusion Principle                                        *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*--------------------HAS_SIZE------------------------------------*)
val has_size_def =  Define `has_size s n  =  FINITE (s) /\ (CARD s = (n))`;

(* ------------------------------------------------------------------------- *)
(*   			inter_list                                  *)
(* ------------------------------------------------------------------------- *)
val inter_list_def =  Define
 ` (inter_list p ([]) = (p_space p  )) /\ 
 	  (!h t . inter_list p (h ::t)  = ( (h)  INTER (inter_list p t )))`;

(*--------------------union list def------------------------------------*)
val union_list_def =  Define
 ` (union_list ([]) = {} ) /\ 
 	  (!h t . union_list (h ::t)  =  h  UNION (union_list t ))`;

(*------------SUBSET_INSERT_EXISTS_NEW------------------------------------------ *)
val SUBSET_INSERT_EXISTS_NEW = store_thm("SUBSET_INSERT_EXISTS_NEW",
  ``!s x t. s SUBSET (x INSERT t) =
            (s SUBSET t) \/ 
	       (?u. u SUBSET t /\ (s = x INSERT u))``,
RW_TAC std_ss[]
++ EQ_TAC
>> ((MATCH_MP_TAC (PROVE [] (Term`((a /\ ~b ==> c) ==> (a ==> b \/ c))`)))
   ++ DISCH_TAC
   ++ EXISTS_TAC (--`s DELETE (x)`--)
   ++ SRW_TAC [][SUBSET_DEF,INSERT_DEF,EXTENSION,GSPECIFICATION]
   >> (METIS_TAC[])
   ++ METIS_TAC[])
++ SRW_TAC [][SUBSET_DEF,INSERT_DEF,EXTENSION,GSPECIFICATION]
>> (METIS_TAC[])
++ METIS_TAC[]);
(*----------------------FINITE_SUBSETS_RESTRICT_NEW----------------------------------*)
val FINITE_SUBSETS_RESTRICT_NEW = store_thm("FINITE_SUBSETS_RESTRICT_NEW",
  ``!s:'a->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}``,
REPEAT STRIP_TAC
++ MATCH_MP_TAC SUBSET_FINITE_I
++ EXISTS_TAC (--`{t:'a->bool | t SUBSET s}`--)
++ REWRITE_TAC[GSYM POW_DEF]
++ RW_TAC std_ss[FINITE_POW]
++ SRW_TAC[][SUBSET_DEF,POW_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------FINITE_SUBSETS_RESTRICT_NEW1----------------------------------*)
val FINITE_SUBSETS_RESTRICT_NEW1 = store_thm("FINITE_SUBSETS_RESTRICT_NEW1",
  ``!s:'a->bool p. FINITE s ==> FINITE {t | t SUBSET s}``,
REPEAT STRIP_TAC
++ MATCH_MP_TAC SUBSET_FINITE_I
++ EXISTS_TAC (--`{t:'a->bool | t SUBSET s}`--)
++ REWRITE_TAC[GSYM POW_DEF]
++ RW_TAC std_ss[FINITE_POW]
++ SRW_TAC[][SUBSET_DEF,POW_DEF,EXTENSION,GSPECIFICATION]);
(*------------------lemma_NEW--------------------------------*)
val lemma_NEW = store_thm("lemma_NEW",
  ``{t | t SUBSET (a INSERT s) /\ P t} =
     {t | t SUBSET s /\ P t} UNION
     {a INSERT t |t| t SUBSET s /\ P(a INSERT t)}``,
RW_TAC std_ss[SUBSET_INSERT_EXISTS_NEW]
++ ONCE_REWRITE_TAC [EXTENSION]
++ RW_TAC std_ss[GSPECIFICATION,IN_UNION]
++ METIS_TAC[]);
(*-------------------temp1--------------------------------*)
val temp1 = store_thm("temp1",
  ``!P. (!s n. has_size s n ==> P s) ==> (!s. FINITE s ==> P s)``,
RW_TAC std_ss[has_size_def]);
(*-----------------------temp3----------------------------*)
val temp3 = store_thm("temp3",
  ``!P. (!n. (!m. (m:num) < n ==> P m) ==> P n) ==> (!n. P n)``,
GEN_TAC
++ KNOW_TAC (--`((\n. !m. m < n ==> P m) 0 /\
  (!n. (\n. !m. m < n ==> P m) n ==> (\n. !m. m < n ==> P m) (SUC n))
  ==> (!n. (\n. !m. m < n ==> P m) n))`--)
>> (DISCH_TAC
   ++ MATCH_MP_TAC INDUCTION
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[BETA_THM]
++ KNOW_TAC (--`(!n. (!m. m < n ==> P m) ==> !m. m < SUC n ==> P m)`--)
>> (RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[LT_SUC])
++ METIS_TAC[LT_SUC]);
(*-----------------------temp2---------------------------*)
val temp2 = store_thm("temp2",
  ``(!P (f:('a->bool) -> real) (A:'b->bool) (x:'b->('a->bool)) (n:num).
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        (has_size A n) /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  (- &1) pow (CARD B + 1) * f(BIGINTER(IMAGE x B)))))==>(!P (f:('a->bool) -> real) (A:'b->bool) (x:'b->('a->bool)).
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  (- &1) pow (CARD B + 1) * f(BIGINTER(IMAGE x B)))))``,
RW_TAC std_ss[has_size_def]);
(*-----------------------temp4---------------------------*)
val temp4 = store_thm("temp4",
  ``!A:'a->bool.  has_size s 0 =  (s = {})``,
RW_TAC std_ss[has_size_def]
++ METIS_TAC[CARD_EQ_0,FINITE_EMPTY]);

(*-------------------has_size_suc-------------------------------*)
val has_size_suc = store_thm("has_size_suc",
  ``!(s:'a->bool) n. (has_size s (SUC n) =
                   (~(s = EMPTY) /\ ( !a. (a IN s) ==> has_size (s DELETE a) n )))``,
RW_TAC std_ss[has_size_def]
++ Cases_on `s:'a->bool= {}`
>> (ASM_REWRITE_TAC[CARD_DEF]
   ++ METIS_TAC[FINITE_EMPTY,NOT_SUC])
++ REWRITE_TAC [FINITE_DELETE]
++ Cases_on `FINITE (s:'a->bool)`
>> (ASM_REWRITE_TAC[NOT_FORALL_THM, MEMBER_NOT_EMPTY]
   ++ EQ_TAC
   >> (REPEAT STRIP_TAC
      ++ MP_TAC (Q.ISPECL [`s DELETE a:'a`] (CONJUNCT2 CARD_DEF))
      ++ FULL_SIMP_TAC std_ss[FINITE_DELETE]
      ++ RW_TAC std_ss[IN_DELETE]
      ++ POP_ASSUM (MP_TAC o Q.SPEC `a:'a`)
      ++ ASM_REWRITE_TAC[]
      ++ KNOW_TAC(--`a INSERT (s DELETE a:'a) = s`--)
      >> (POP_ASSUM MP_TAC
      	 ++ RW_TAC std_ss[INSERT_DELETE])
      ++ RW_TAC std_ss[])
   ++ KNOW_TAC(--`?a:'a. a IN s:'a->bool`--)
   >> (RW_TAC std_ss[MEMBER_NOT_EMPTY])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ MP_TAC(Q.ISPECL [`s DELETE a:'a`] (CONJUNCT2 CARD_DEF))
   ++ FULL_SIMP_TAC std_ss[FINITE_DELETE]
   ++ RW_TAC std_ss[IN_DELETE]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `a:'a`)
   ++ ASM_REWRITE_TAC[]
   ++ KNOW_TAC(--`a INSERT (s DELETE a:'a) = s`--)
   >> (POP_ASSUM MP_TAC
      ++ RW_TAC std_ss[INSERT_DELETE])
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ RW_TAC std_ss[MEMBER_NOT_EMPTY]);
(*------------------FORALL_INSERT--------------------------------*)
val FORALL_INSERT = store_thm("FORALL_INSERT",
  ``!P a s. (!x. x IN a INSERT s ==> P x) <=> P a /\ (!x. x IN s ==> P x)``,
RW_TAC std_ss[IN_INSERT]
++ EQ_TAC
>> (RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[]);
(*------------------INTER_BIGUNION--------------------------------*)
val INTER_BIGUNION = store_thm("INTER_BIGUNION",
  ``(!s t. BIGUNION s INTER t = BIGUNION {x INTER t | x IN s}) /\
   (!s t. t INTER BIGUNION s = BIGUNION {t INTER x | x IN s})``,
ONCE_REWRITE_TAC[EXTENSION]
++ REWRITE_TAC[IN_BIGUNION,EXTENSION,IN_INTER]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[GSPECIFICATION]
>> (METIS_TAC[IN_INTER])
++ RW_TAC std_ss[GSPECIFICATION]
++ METIS_TAC[IN_INTER]);
(*------------------has_size_clauses--------------------------------*)
val has_size_clauses = store_thm("has_size_clauses",
  ``(has_size (s:'a->bool) 0 = (s = {})) /\
    (has_size s (SUC n) =
        ?a t. has_size t n /\ ~(a IN t) /\ (s = a INSERT t))``,
REWRITE_TAC[temp4]
++ REPEAT STRIP_TAC ++ EQ_TAC
>> (REWRITE_TAC[has_size_suc]
   ++ RW_TAC std_ss[]
   ++ KNOW_TAC (--`?a:'a. a IN s:'a->bool`--)
   >> (RW_TAC std_ss[MEMBER_NOT_EMPTY])
   ++ RW_TAC std_ss[]
   ++ EXISTS_TAC(--`a:'a`--)
   ++ EXISTS_TAC(--` s:'a->bool DELETE a`--)
   ++ RW_TAC std_ss[ IN_DELETE]
   ++ KNOW_TAC (--` (s:'a->bool = a INSERT (s DELETE a)) `--)
   >> (METIS_TAC[INSERT_DELETE])
   ++ RW_TAC std_ss[ IN_DELETE])
++ FULL_SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM]
++ FULL_SIMP_TAC std_ss[has_size_def,CARD_DEF,FINITE_INSERT]);
(*--------------------temp5------------------------------*)
val temp5 = store_thm("temp5",
  ``!s t. s UNION (t DIFF s):'a->bool = s UNION t``,
RW_TAC std_ss[]
++ SRW_TAC [][IN_UNION,DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (RW_TAC std_ss[]
   >> (DISJ1_TAC
      ++ RW_TAC std_ss[])
   ++ DISJ2_TAC
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
>> (DISJ1_TAC
   ++ RW_TAC std_ss[])
++ Cases_on `(x IN s)`
>> (DISJ1_TAC
   ++ RW_TAC std_ss[])
++ DISJ2_TAC
++ RW_TAC std_ss[]);
(*----------------incl_excl_temp1----------------------------------*)
val incl_excl_temp1 = store_thm("incl_excl_temp1",
  ``!fa fas s  s'. ((fa + s) - fas:real = s + s') = (fa - fas = s')``,
REAL_ARITH_TAC);
(*--------------temp6------------------------------------*)
val temp6 = store_thm("temp6",
  ``!s t. (s INTER t) UNION (t DIFF s) = t``,
RW_TAC std_ss[]
++ SRW_TAC [][IN_UNION,DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (RW_TAC std_ss[])
++ RW_TAC std_ss[]);
(*-----------------simple_image_gen---------------------------------*)
val simple_image_gen = store_thm("simple_image_gen",
  ``! f P. {f s| P s} = IMAGE f {s | P s}``,
RW_TAC std_ss[IMAGE_DEF]
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]);
(*------------------FINITE_RESTRICT--------------------------------*)
val FINITE_RESTRICT = store_thm("FINITE_RESTRICT",
  ``!(s:'a->bool) P. {x | x IN s /\ P x} SUBSET s``,
RW_TAC std_ss[SUBSET_DEF]
++ POP_ASSUM MP_TAC
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]);
(*---------------------incl_excl_temp2-----------------------------*)
val incl_excl_temp2 = store_thm("incl_excl_temp2",
  ``!a b x. (x - a:real = x + b) = (b = -a)``,
REAL_ARITH_TAC);
(*------------------incl_excl_temp3--------------------------------*)
val incl_excl_temp3 = store_thm("incl_excl_temp3",
  ``!f s. BIGINTER (IMAGE f s) = {y | !x. x IN s ==> y IN f x}``,
RW_TAC std_ss[IMAGE_DEF,BIGINTER]
++ RW_TAC std_ss[EXTENSION,GSPECIFICATION]
++ EQ_TAC
>> (METIS_TAC[])
++ METIS_TAC[]);
(*-----------------incl_excl_temp4---------------------------------*)
val incl_excl_temp4 = store_thm("incl_excl_temp4",
  ``!P e. {s | P s /\ ~(s = e)} = {s | P s} DELETE e``,
RW_TAC std_ss[]
++ SRW_TAC[][DELETE_DEF,DIFF_DEF,EXTENSION,GSPECIFICATION]);
(*----------------incl_excl_temp5----------------------------------*)
val incl_excl_temp5 = store_thm("incl_excl_temp5",
  ``!x s. (x IN s) ==>  (x INSERT s =  s)``,
SRW_TAC[][INSERT_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*-----------------incl_excl_temp6---------------------------------*)
val incl_excl_temp6 = store_thm("incl_excl_temp6",
  ``!s. EMPTY IN {B| B SUBSET s}``,
RW_TAC std_ss[GSYM POW_DEF,IN_POW,EMPTY_SUBSET]);
(*------------incl_excl_temp7--------------------------------------*)
val incl_excl_temp7 = store_thm("incl_excl_temp7",
  ``!a b c:real. (a = b - c) = (b = c + a)``,
REAL_ARITH_TAC);
(*---------------incl_excl_temp8-----------------------------------*)
val incl_excl_temp8 = store_thm("incl_excl_temp8",
  ``!f e s. FINITE s ==> (sum_set (s DELETE e) f = sum_set (e INSERT s) f - f e)``,
RW_TAC std_ss[incl_excl_temp7]
++ RW_TAC std_ss[sum_set_def,REAL_SUM_IMAGE_THM]);
(*------------------------incl_excl_temp9--------------------------*)
val incl_excl_temp9 = store_thm("incl_excl_temp9",
  ``!f e s. e IN s /\ FINITE s ==> (sum_set (s DELETE e) f = sum_set (s) f - f e)``,
RW_TAC std_ss[incl_excl_temp8]
++ RW_TAC std_ss[incl_excl_temp5]);
(*-----------------BIGINTER_SET------------------------------------------------------*)
val BIGINTER_SET = store_thm("BIGINTER_SET",
  ``!s p. FINITE s /\ prob_space p  ==> ( BIGINTER (s) INTER p_space p  =  inter_list p  (SET_TO_LIST s))``,
Induction.recInduct SET_TO_LIST_IND
++ RW_TAC bool_ss []
++ RW_TAC std_ss [SET_TO_LIST_THM]
++ RW_TAC std_ss[BIGINTER_EMPTY,inter_list_def,INTER_UNIV]
++ KNOW_TAC (--`BIGINTER (s:(('a -> bool) -> bool)) =  (BIGINTER (CHOICE s INSERT REST s) )`--)
>> (RW_TAC std_ss[CHOICE_INSERT_REST])
++ DISCH_TAC ++ POP_ORW
++ RW_TAC std_ss[BIGINTER_INSERT,inter_list_def]
++ FULL_SIMP_TAC std_ss[FINITE_REST]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `p`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM INTER_ASSOC]);
(*------------------INCLUSION_EXCLUSION_RESTRICTED--------------------------------*)

val REAL_SUM_IMAGE_IMAGE1 = store_thm
  ("REAL_SUM_IMAGE_IMAGE1",
   ``!P f' f. FINITE P /\
	  INJ f' P (IMAGE f' P) ==>
               (REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P)``,
	       FULL_SIMP_TAC std_ss[AND_IMP, RIGHT_FORALL_IMP_THM] THEN
   Induct_on `FINITE`
   THEN SRW_TAC [][REAL_SUM_IMAGE_THM]
   THEN `IMAGE f' P DELETE f' e = IMAGE f' P`
   by (SRW_TAC [][EXTENSION]
       THEN EQ_TAC THEN1 (METIS_TAC[])
       THEN POP_ASSUM MP_TAC
       THEN ASM_SIMP_TAC (srw_ss()) [INJ_DEF]
       THEN METIS_TAC[])
   THEN `P DELETE e = P` by METIS_TAC [DELETE_NON_ELEMENT]
   THEN SRW_TAC [][]
   THEN FIRST_X_ASSUM MATCH_MP_TAC
   THEN Q.PAT_ASSUM `INJ f' SS1 SS2` MP_TAC
   THEN CONV_TAC (BINOP_CONV (SIMP_CONV (srw_ss()) [INJ_DEF]))
   THEN METIS_TAC[]);



(*-----------------------INCLUSION_EXCLUSION_RESTRICTED---------------------------*)
val INCLUSION_EXCLUSION_RESTRICTED = store_thm("INCLUSION_EXCLUSION_RESTRICTED",
  ``!P (f:('a->bool) -> real) (A:'b->bool) (x:'b->('a->bool)).
      (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> (f(BIGUNION(IMAGE x A)) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B.  (- &1) pow (CARD B + 1) * f(BIGINTER(IMAGE x B))))``,
FULL_SIMP_TAC std_ss[AND_IMP, RIGHT_FORALL_IMP_THM]
++ REWRITE_TAC [AND_IMP_INTRO]
++ REWRITE_TAC [GSYM CONJ_ASSOC]
++ REWRITE_TAC [PULL_FORALL]
++ FULL_SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM]
++ FULL_SIMP_TAC std_ss[AND_IMP_INTRO]
++ RW_TAC std_ss[]
++ POP_ASSUM MP_TAC
++ POP_ASSUM MP_TAC
++ Q.SPEC_TAC (`x`, `x`) 
++ FULL_SIMP_TAC std_ss[AND_IMP,RIGHT_FORALL_IMP_THM]
++ KNOW_TAC (--` 
 (!(x:'b->('a->bool)). (!a. a IN A ==> P (x a))==>
  (f (BIGUNION (IMAGE x (A:'b->bool))) =
   sum_set {B | B SUBSET A /\ ~(B = {})}
     (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))))) = (\A. !(x:'b->('a->bool)).  
  (!a. a IN A ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ ~(B={})}
     (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))) A `--)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW 
++ Q.SPEC_TAC (`A`, `A`)
++ MATCH_MP_TAC ( PROVE[has_size_def] (Term`(!A n. has_size A n ==> P A) ==> (!A. FINITE A ==> P A)`))
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[]
++ Q.SPEC_TAC (`A`, `A`) 
++ KNOW_TAC (--` 
  (!(A:'b->bool). has_size (A:('b->bool))  n ==>
!(x:'b->('a->bool)).
 (!a. a IN (A:'b->bool) ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ (B <> {})}
     (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))))) = ((\n:num. !(A:'b->bool). has_size A n ==>
!(x:'b->('a->bool)).
  (!a. a IN A ==> P (x a)) ==>
  (f (BIGUNION (IMAGE x A)) =
   sum_set {B | B SUBSET A /\ (B <> {}) }
     (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))) n) `--)
>> (RW_TAC std_ss[])
++ DISCH_TAC ++ POP_ORW
++ Q.SPEC_TAC (`n`, `n`) 
++ MATCH_MP_TAC temp3
++ FULL_SIMP_TAC std_ss[]
++ Induct_on `n`
>> (FULL_SIMP_TAC std_ss[has_size_clauses]
   ++ RW_TAC std_ss[]
   ++ RW_TAC std_ss[IMAGE_EMPTY,BIGUNION_EMPTY,SUBSET_EMPTY]
   ++ RW_TAC std_ss[GSPEC_F, sum_set_def,REAL_SUM_IMAGE_THM]
   ++ REPEAT(FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `{}:'a->bool`]))
   ++ FULL_SIMP_TAC std_ss[UNION_EMPTY, DISJOINT_EMPTY]
   ++ RW_TAC std_ss[]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `EMPTY`)
   ++ RW_TAC std_ss[]
   ++ NTAC 2 (POP_ASSUM MP_TAC)
   ++ POP_ASSUM (MP_TAC o Q.SPEC `EMPTY`)
   ++ RW_TAC std_ss[]
   ++ NTAC 3 (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC)
++ DISCH_TAC
++ FULL_SIMP_TAC std_ss[has_size_clauses]
++ REPEAT GEN_TAC
++ FULL_SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM]
++ REPEAT GEN_TAC
++ REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
++ FULL_SIMP_TAC std_ss[FORALL_INSERT]
++ STRIP_TAC
++ REWRITE_TAC[IMAGE_INSERT,BIGUNION_INSERT]
++ STRIP_TAC
++ STRIP_TAC
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC(-- `(f(x a) + f(BIGUNION (IMAGE (x:'b->('a->bool)) t))) -
              f(x a INTER BIGUNION (IMAGE x t)):real`--)
++ CONJ_TAC
>> (KNOW_TAC(--`P(x a) /\ P(BIGUNION(IMAGE (x:'b->('a->bool)) t))`--)
   >> (ASM_REWRITE_TAC[]
      ++ POP_ASSUM MP_TAC
      ++ KNOW_TAC(--`FINITE (t:'b->bool)`--)
      >> (FULL_SIMP_TAC std_ss[has_size_def])
      ++ KNOW_TAC(--`(!a'. a' IN t ==> P (x a')) ==> P (BIGUNION (IMAGE (x:'b->('a->bool)) t)) =
 (\ (t:'b->bool). ((!a'. a' IN t ==> P (x a')) ==> P (BIGUNION (IMAGE x t))))t`--)
      >> (RW_TAC std_ss[])
      ++ DISCH_TAC ++ POP_ORW
      ++ Q.SPEC_TAC (`t`, `u`) 
      ++ MATCH_MP_TAC FINITE_INDUCT
      ++ FULL_SIMP_TAC std_ss[IMAGE_EMPTY,IMAGE_INSERT,BIGUNION_EMPTY,BIGUNION_INSERT]
      ++ FULL_SIMP_TAC std_ss[FORALL_INSERT])
   ++ FULL_SIMP_TAC std_ss[ PULL_FORALL,AND_IMP_INTRO]
   ++ PAT_ASSUM (Term `P (x a) `) MP_TAC
   ++ Q.SPEC_TAC(`BIGUNION (IMAGE x t)`,`t'`)
   ++ Q.SPEC_TAC(`x a`,`s'`)
   ++ RW_TAC std_ss[]
   ++ KNOW_TAC (--`P (s' INTER t':'a->bool) /\ P (t' DIFF s':'a->bool) /\ DISJOINT (s' INTER t') (t' DIFF s':'a->bool) ==> (f (s' INTER t':'a->bool UNION (t' DIFF s':'a->bool)) = (f:('a->bool) -> real) (s' INTER t':'a->bool) + f (t' DIFF s':'a->bool))`--)
   >> (PAT_ASSUM (Term ` !s t. (P s /\ P t) /\ DISJOINT s t ==> (f (s UNION t) = f s + (f:('a->bool) -> real) t)`) (MP_TAC o Q.SPECL [`s' INTER t':'a->bool`, `t' DIFF s':'a->bool`])
      ++ RW_TAC std_ss[])
   ++ PAT_ASSUM (Term ` !s t. (P s /\ P t) /\ DISJOINT s t ==> (f (s UNION t) = f s + (f:('a->bool) -> real) t)`) MP_TAC
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`s':'a->bool`, `t' DIFF s':'a->bool`])
   ++ FULL_SIMP_TAC std_ss[temp5,temp6]
   ++ KNOW_TAC (--`DISJOINT s' (t' DIFF s')`--)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ RW_TAC std_ss[DISJ_ASSOC]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ KNOW_TAC (--`DISJOINT (s' INTER t') (t' DIFF s')`--)
   >> (RW_TAC std_ss[DISJOINT_DEF]
      ++ SIMP_TAC (srw_ss()) [DISJOINT_DEF,DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,EXCLUDED_MIDDLE]
      ++ ONCE_REWRITE_TAC[DISJ_SYM]
      ++ RW_TAC std_ss[GSYM DISJ_ASSOC]
      ++ DISJ2_TAC
      ++ RW_TAC std_ss[DISJ_ASSOC])
   ++ RW_TAC std_ss[]
   ++ FULL_SIMP_TAC std_ss[]
   ++ REAL_ARITH_TAC)
++ FULL_SIMP_TAC std_ss[INTER_BIGUNION]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_DEF]
++ FULL_SIMP_TAC std_ss[GSYM IMAGE_COMPOSE,o_DEF]
++ FIRST_X_ASSUM(MP_TAC o Q.SPEC `n:num`) 
++ REWRITE_TAC[LT_SUC]
++ DISCH_THEN(MP_TAC o Q.SPEC `t:'b->bool`) ++ ASM_REWRITE_TAC[]
++ DISCH_TAC
++ KNOW_TAC (--`((!a'. a' IN t ==> P ((\s. (x:'b->('a->bool)) a INTER x s) a')) ==>
 (f (BIGUNION (IMAGE (\s. x a INTER x s) t)) =
  sum_set {B | B SUBSET t /\ B <> EMPTY}
    (\B.
       -1 pow (CARD B + 1) * f (BIGINTER (IMAGE (\s. x a INTER x s) B)))))`--)
>> (PAT_ASSUM (Term ` !x.
        (!a. a IN t ==> P (x a)) ==>
        (f (BIGUNION (IMAGE x t)) =
         sum_set {B | B SUBSET t /\ B <> EMPTY}
           (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))))`) MP_TAC
     ++ DISCH_THEN(MP_TAC o Q.SPEC `\s. (x:'b->('a->bool)) a INTER x s`) ++ ASM_REWRITE_TAC[]) 
++ POP_ASSUM MP_TAC
++ DISCH_THEN(MP_TAC o Q.SPEC `(x:'b->('a->bool))`) ++ ASM_REWRITE_TAC[]
++ REPEAT(DISCH_THEN SUBST1_TAC)
++ FULL_SIMP_TAC std_ss[lemma_NEW]
++ DISCH_TAC
++ KNOW_TAC (--`sum_set
  ({B | B SUBSET t:'b->bool /\ B <> EMPTY} UNION {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY})
  (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE (x:'b->('a->bool)) B))) = sum_set
  ({B | B SUBSET t /\ B <> EMPTY})(\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))) + sum_set ( {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY})
  (\B. -1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B)))`--)
>> (RW_TAC std_ss[sum_set_def]
   ++ MATCH_MP_TAC  REAL_SUM_IMAGE_DISJOINT_UNION
   ++ KNOW_TAC (--`FINITE {B | B SUBSET t /\ B <> EMPTY} /\
FINITE {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} /\
DISJOINT {B | B SUBSET t:'b->bool /\ B <> EMPTY} {a INSERT B | B | B SUBSET t /\ a INSERT B <> EMPTY} = (FINITE( IMAGE (\B. B) {B | B SUBSET t /\ B <> EMPTY}) /\
FINITE  (IMAGE (\B. a INSERT B){ B | B SUBSET t /\ a INSERT B <> EMPTY}) /\
DISJOINT  (IMAGE (\B. B){B | B SUBSET t /\ B <> EMPTY}) ( IMAGE (\B. a INSERT B){ B | B SUBSET t /\ a INSERT B <> EMPTY}))`--)
   >> (RW_TAC std_ss[GSYM simple_image_gen])
   ++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW,IMAGE_FINITE]
   ++ RW_TAC std_ss[GSYM simple_image_gen]
   ++ RW_TAC std_ss[IN_DISJOINT,GSPECIFICATION]
   ++ METIS_TAC [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
++ DISCH_THEN SUBST1_TAC
++ RW_TAC std_ss[NOT_INSERT_EMPTY]
++ RW_TAC std_ss[incl_excl_temp1]
++ MATCH_MP_TAC EQ_TRANS
++ EXISTS_TAC(--`f((x:'b->('a->bool)) a) +
              sum_set {B | B SUBSET t /\ ~(B = {})}
                  (\B. -(&1) pow (CARD B) *
                       f(BIGINTER(IMAGE x (a INSERT B))))`--)
++ CONJ_TAC
>> (RW_TAC std_ss[incl_excl_temp2]
   ++ FULL_SIMP_TAC std_ss[has_size_def]
   ++ KNOW_TAC(--`FINITE {B | B SUBSET t:'b->bool /\ B <> EMPTY}`--)
   >> (RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW])
   ++ REWRITE_TAC[sum_set_def]
   ++ RW_TAC std_ss[GSYM REAL_SUM_IMAGE_NEG]
   ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
   ++ FULL_SIMP_TAC std_ss[IMAGE_INSERT,BIGINTER_INSERT,o_DEF,GSPECIFICATION]
   ++ REPEAT STRIP_TAC
   ++ RW_TAC real_ss[REAL_POW_ADD, POW_1, REAL_MUL_RNEG, REAL_MUL_LNEG]
   ++ AP_TERM_TAC
   ++ AP_TERM_TAC
   ++ RW_TAC real_ss[incl_excl_temp3]
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_INTER,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC [SUBSET_DEF,EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV])
++ RW_TAC std_ss[incl_excl_temp4]
++ KNOW_TAC(--`EMPTY IN {B | B SUBSET t:'b->bool} `--)
>> (RW_TAC std_ss[incl_excl_temp6])
++ KNOW_TAC(--`FINITE  {B | B SUBSET t:'b->bool}`--)
>> (FULL_SIMP_TAC std_ss[has_size_def]
   ++ RW_TAC std_ss[FINITE_SUBSETS_RESTRICT_NEW1])
++ RW_TAC std_ss[incl_excl_temp9]
++ RW_TAC real_ss[CARD_EMPTY]
++ RW_TAC real_ss[IMAGE_SING,BIGINTER_SING]
++ KNOW_TAC(--` {a INSERT B | B SUBSET t:'b->bool} = (IMAGE (\B. a INSERT B) {B | B SUBSET t:'b->bool })`--)
>> (RW_TAC real_ss[GSYM simple_image_gen])
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ KNOW_TAC (--`sum_set (IMAGE (\B. a INSERT B) {B | B SUBSET (t:'b->bool)})
      (\B. - &1 pow (CARD B + 1) *  (f:('a->bool) -> real) (BIGINTER (IMAGE (x:'b->('a->bool)) B))) =
      sum_set {B | B SUBSET (t:'b->bool)}
      ((\B. - &1 pow (CARD B + 1) * f (BIGINTER (IMAGE x B))) o
       (\B. a INSERT B))`--)
>> (RW_TAC std_ss[sum_set_def]
   ++ MATCH_MP_TAC REAL_SUM_IMAGE_IMAGE1
   ++ ASM_SIMP_TAC(srw_ss())[INJ_DEF,INSERT_DEF,SUBSET_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[])
++ DISCH_TAC ++ PURE_ONCE_ASM_REWRITE_TAC [] ++ POP_ORW
++ RW_TAC real_ss[o_DEF]
++ RW_TAC real_ss[sum_set_def]
++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
++ RW_TAC real_ss[GSPECIFICATION]
++ RW_TAC real_ss[REAL_POW_ADD,REAL_NEG_NEG]
++ KNOW_TAC (--`FINITE (x':'b->bool)`--)
>> (MATCH_MP_TAC SUBSET_FINITE_I
   ++ EXISTS_TAC(--`t:'b->bool`--)
   ++ RW_TAC real_ss[has_size_def]
   ++ FULL_SIMP_TAC std_ss[has_size_def])
++ RW_TAC real_ss[CARD_INSERT]
>> (METIS_TAC[SUBSET_DEF])
++ RW_TAC real_ss[IMAGE_INSERT,pow]);
(*------------------INCLUSION_EXCLUSION_RESTRICTED_REAL--------------------------------------*)
val INCLUSION_EXCLUSION_RESTRICTED_REAL = store_thm(
  "INCLUSION_EXCLUSION_RESTRICTED_REAL",
  ``!P (f:('a->bool)->real) (A:('a->bool)->bool).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> (f(s UNION t) = f(s) + f(t))) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(a))
        ==> (f(BIGUNION A) =
            sum_set {B | B SUBSET A /\ ~(B = {})}
                (\B. (- &1) pow (CARD B + 1) * f(BIGINTER B)))``,
REPEAT STRIP_TAC
++ MP_TAC(Q.ISPECL [`P:('a->bool)->bool`, `f:('a->bool)->real`,
                 `A:('a->bool)->bool`, `\x:'a->bool. x`]
        INCLUSION_EXCLUSION_RESTRICTED)
++ ASM_REWRITE_TAC[IMAGE_ID]
++ METIS_TAC[IMAGE_ID]);
(*----------------------PROB_INCLUSION_EXCLUSION----------------------------------*)
val PROB_INCLUSION_EXCLUSION = store_thm("PROB_INCLUSION_EXCLUSION",
  ``!p (s:('a->bool)->bool). prob_space p /\ (!a. a IN s ==> a IN events p) /\
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> ((prob p(BIGUNION s)) =
                sum_set {t | t SUBSET s /\ ~(t = {})}
                    (\t. (- &1) pow (CARD t + 1) * (prob p(BIGINTER t))))``,
REPEAT STRIP_TAC
++ MP_TAC(Q.ISPECL [`\s. s IN events p`, `(\s'. prob p (s':'a->bool))`,
                 `s:('a->bool)->bool`]
       INCLUSION_EXCLUSION_RESTRICTED_REAL )
++ FULL_SIMP_TAC real_ss[PROB_ADDITIVE,EVENTS_EMPTY,EVENTS_INTER,EVENTS_UNION,EVENTS_DIFF]);
(*------------------PROB_INCLUSION_EXCLUSION_list--------------------------------------*)
val PROB_INCLUSION_EXCLUSION_list = store_thm("PROB_INCLUSION_EXCLUSION_list",
  ``! p L. prob_space p  /\ (!x. MEM x (L) ==> x IN events p)
==> ((prob p(BIGUNION (set L))) =
                sum_set {t | t SUBSET (set L) /\ ~(t = {})}
                    (\t. (- &1) pow (CARD t + 1) * (prob p(BIGINTER t))))``,
REPEAT STRIP_TAC
++ MP_TAC(Q.ISPECL [`\s. s IN events p`, `(\s'. prob p (s':'a->bool))`,
                 `(set L):('a->bool)->bool`]
       INCLUSION_EXCLUSION_RESTRICTED_REAL )
++ FULL_SIMP_TAC real_ss[PROB_ADDITIVE,EVENTS_EMPTY,EVENTS_INTER,EVENTS_UNION,EVENTS_DIFF]
++ RW_TAC list_ss[]);
(*---------------BIGUNION_EQ_UNION_LIST-----------------------------------------*)
val BIGUNION_EQ_UNION_LIST = store_thm("BIGUNION_EQ_UNION_LIST",
  ``!L. BIGUNION (set L) =  union_list L``,
Induct
>> (RW_TAC std_ss[LIST_TO_SET_THM,union_list_def]
   ++ RW_TAC std_ss[BIGUNION_EMPTY])
++ RW_TAC std_ss[LIST_TO_SET_THM,union_list_def]
++ RW_TAC std_ss[BIGUNION_INSERT]);
(*--------------------PROB_INCLUSION_EXCLUSION_PRINCIPLE---------------------------------------------------*)
val PROB_INCLUSION_EXCLUSION_PRINCIPLE = store_thm(
  "PROB_INCLUSION_EXCLUSION_PRINCIPLE",
  ``! p L. prob_space p  /\ (!x. MEM x (L) ==> x IN events p )
==> ((prob p(union_list L)) =
                sum_set {t | t SUBSET (set L) /\ ~(t = {})}
                    (\t. (- &1) pow (CARD t + 1) * (prob p(BIGINTER t))))``,
RW_TAC std_ss[GSYM BIGUNION_EQ_UNION_LIST, PROB_INCLUSION_EXCLUSION_list]);

val _ = export_theory();