Module sfts Import subject_reduction;

(* for semi-full gts *)
%\VerbFileOpen semiFull
[semiFull = {s1|SS}(Ex2 [s2,s3:SS]rl s1 s2 s3)->{s2:SS}Ex [s3:SS]rl s1 s2 s3];
%\VerbFileClos semiFull

(* A judgement for semi-full gts *)
%\VerbFileOpen sfts
Inductive [sfts:Cxt->Trm->Trm->Prop]   NoReductions   Constructors
[sfAx:{s1,s2|SS}                                                 {sc:ax s1 s2}
         sfts nilCxt (sort s1) (sort s2)]

[sfStart:{G|Cxt}{A|Trm}{s|SS}{p|PP}                 {noccG:is_ff (Poccur p G)}
      {prem:sfts G A (sort s)}
     (*****************************************)
         sfts (CONS (Gb p A) G) (par p) A]

[sfvWeak:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}             {noccG:is_ff (Poccur p G)}
      {l_prem:sfts G (par n) D}
      {r_prem:sfts G A (sort s)}
     (*****************************************)
         sfts (CONS (Gb p A) G) (par n) D]

[sfsWeak:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}             {noccG:is_ff (Poccur p G)}
      {l_prem:sfts G (sort t) D}
      {r_prem:sfts G A (sort s)}
     (*****************************************)
         sfts (CONS (Gb p A) G) (sort t) D]

[sfPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}               {sc:rl s1 s2 s3}
                                                    {noccB:is_ff (poccur p B)}
      {l_prem:sfts G A (sort s1)}
      {r_prem:sfts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
         sfts G (pi n A B) (sort s3)]

[sfLda:{G|Cxt}{A,M,B|Trm}{s,s2,s3|SS}{p|PP}{n,m|VV}            {sc:rl s s2 s3}
                        {sc_ts:{t:SS}(is_tt (Trm_eq B (sort t)))->typedsort t}
                                                    {noccM:is_ff (poccur p M)}
                                                    {noccB:is_ff (poccur p B)}
      {l_prem:sfts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
      {r_prem:sfts G A (sort s)}
     (*****************************************)
         sfts G (lda n A M) (pi m A B)]

[sfApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
      {l_prem:sfts G M (pi n A B)}
      {r_prem:sfts G L A}
     (*****************************************)
         sfts G (app M L) (vsub L n B)]

[sftCnv:{G|Cxt}{M,A,B|Trm}{s|SS}                                  {sc:cnv A B}
      {l_prem:sfts G M A}
      {r_prem:sfts G B (sort s)}
     (*****************************************)
         sfts G M B];
%\VerbFileClos sfts

[sftsRec=sfts_elim];


(** Vclosed lemma for sfts  **)
Goal sfts_Vclosed: {G|Cxt}{M,A|Trm}(sfts G M A)->and (Vclosed M) (Vclosed A);
Refine sftsRec [G:Cxt][M,A:Trm][_:sfts G M A]and (Vclosed M) (Vclosed A);
(* ax *) 
intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *) 
intros;Refine pair;Refine Vclosed_par;Refine fst prem_ih;
(* vWeak *) 
intros;Refine pair;Refine Vclosed_par;Refine snd l_prem_ih;
(* sWeak *) 
intros;Refine l_prem_ih;
(* pi *) 
intros;Refine pair;
Refine Vclosed_pi (fst l_prem_ih) (fst r_prem_ih);
Refine Vclosed_sort;
(* lda *) 
intros;Refine pair;
Refine Vclosed_lda (fst r_prem_ih) (fst l_prem_ih);
Refine Vclosed_pi (fst r_prem_ih) (snd l_prem_ih);
(* app *) 
intros;Refine pair;
Refine Vclosed_app (fst l_prem_ih) (fst r_prem_ih);
Refine PPinf (params B);intros p noccB;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine psub_resp_Vclosed;
Refine (fst r_prem_ih);Refine (snd (Vclosed_pi_lem (snd l_prem_ih)));
(* cnv *) 
intros;Refine pair;Refine fst l_prem_ih;Refine fst r_prem_ih;
Save;

(* we prove these by induction to be able to see that gts->sdsf
 * does not depend on semiFull-ness
 *)
Goal sfts_only_typedsort_in_left:
 {G|Cxt}{M,A|Trm}(sfts G M A)->{s|SS}(is_tt (soccur s M))->typedsort s;
Refine sfts_elim [G:Cxt][M,A:Trm][_:sfts G M A]
            {s|SS}{occ:is_tt (soccur s M)}typedsort s;
(* Ax *)
intros ____; Qrepl socc_sort_lem s s1;
intros eqS; Qrepl SSdecide eqS;Refine ExIn; Immed;
(* Start *)
intros; Refine tt_not_ff (Q_sym occ);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym occ);
(* sWeak *)
intros; Refine l_prem_ih; Immed;
(* Pi *)
intros; Refine socc_compound_lem occ;
intros; Refine l_prem_ih; Immed;
intros; Refine r_prem_ih; Refine socc_vsub_lem; Immed;
(* Lda *)
intros; Refine socc_compound_lem occ;
intros; Refine r_prem_ih; Immed;
intros; Refine l_prem_ih; Refine socc_vsub_lem; Immed;
(* App *)
intros; Refine socc_compound_lem occ;
intros; Refine l_prem_ih; Immed;
intros; Refine r_prem_ih; Immed;
(* tCnv *)
intros; Refine l_prem_ih; Immed;
Save;

%\VerbFileOpen sfts_typedsort_maybe_in_right
Goal sfts_typedsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(sfts G M A)->
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
%\VerbFileClos sfts_typedsort_maybe_in_right
Refine sftsRec [G:Cxt][M,A:Trm][_:sfts G M A]
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
(* ax *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s s2);
Refine Q_refl;
(* Start *)
intros; Refine sfts_only_typedsort_in_left prem; Immed;
(* vWeak *)
intros; Refine l_prem_ih; Immed;
(* sWeak *)
intros; Refine l_prem_ih; Immed;
(* Pi *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s s3);
Refine Q_refl;
(* Lda *)
intros; Refine socc_compound_lem H;
intros sinA; Refine sfts_only_typedsort_in_left r_prem; Immed;
intros sinB; Refine tt_or_ff (Trm_eq B (sort s1));
 intros eqsB; Refine sc_ts; Immed;
 intros neqsB; Refine l_prem_ih; Refine socc_vsub_lem;
  Qrepl +1 Trm_eq_sym (sort s1) (vsub (par p) m B);
  Qrepl +1 Trm_eq_vsub_sort B p m s1; Immed;
(* App *)
intros; Refine socc_vsub_lem2 H;
Refine sfts_only_typedsort_in_left; Immed;
intros; Refine l_prem_ih; Refine socc_split_lem; Refine inr; Immed;
Refine Q_refl;
(* tCnv *)
intros; Refine sfts_only_typedsort_in_left r_prem; Immed;
Save;

(* this is really the contrapositive of typedsort_maybe_in_right *)
Goal sfts_topsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(sfts G M A)->
     {s|SS}{ts:topsort s}(is_tt (soccur s A))->is_tt (Trm_eq A (sort s));
intros; Refine snd (is_tt_isnot_ff ?);
Qrepl Trm_eq_sym A (sort s); 
Refine contrapos (sfts_typedsort_maybe_in_right H H1);
Immed;
Save;


(**  generation lemmas for sfts  **)
Goal {G|Cxt}{A,B,C|Trm}{v|VV}(sfts G (pi v A B) C)->
     Ex4 [s1,s2,s3:SS][p:PP]
        and5 (rl s1 s2 s3)
             (sfts G A (sort s1))
             (is_ff (poccur p B))
             (sfts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
             (cnv (sort s3) C);
intros;
Refine sftsRec [G:Cxt][M,C:Trm][_:sfts G M C]
     {eqPi:is_tt (Trm_eq M (pi v A B))}
      Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (sfts G A (sort s1))
               (is_ff (poccur p B))
               (sfts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
Immed;
(* ax *) intros; Refine tt_not_ff (Q_sym eqPi);
(* start *) intros; Refine tt_not_ff (Q_sym eqPi);
(* vWeak *) intros; Refine tt_not_ff (Q_sym eqPi);
(* sWeak *) intros; Refine tt_not_ff (Q_sym eqPi);
(* pi *)
intros;Refine Trm_eq_pi_lem eqPi;
intros eqV eqA eqB;
Refine Ex4In s1 s2 s3 p;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair5; Immed;
Refine cnv_refl; Refine Vclosed_sort;
(* lda *) intros; Refine tt_not_ff (Q_sym eqPi);
(* app *) intros; Refine tt_not_ff (Q_sym eqPi);
(* cnv *)
intros; Refine l_prem_ih eqPi; intros s1 s2 s3 p hyp;
Refine hyp; intros rule hypA pFresh hypB hypCnv;
Refine Ex4In s1 s2 s3 p; Refine pair5; Immed;
Refine cnv_trans; Immed;
Refine Trm_eq_refl;
Save sf_gen_pi;

Goal {G|Cxt}{s|SS}{C|Trm}{d:sfts G (sort s) C}
      Ex [s1:SS]and (ax s s1) (cnv (sort s1) C);
intros;
Refine sftsRec [G:Cxt][M,C:Trm][_:sfts G M C]
              {s|SS}{eqSS:is_tt (Trm_eq M (sort s))}
               Ex [s1:SS]and (ax s s1) (cnv (sort s1) C);
Immed;
(* ax *) intros;Qrepl Q_sym (SSdecide eqSS);
Refine ExIn s2;Refine pair;Refine sc;
Refine cnv_refl;Refine Vclosed_sort;
(* start *) intros;Refine tt_not_ff (Q_sym eqSS);
(* vWeak *) intros;Refine tt_not_ff (Q_sym eqSS);
(* sWeak *) intros;Refine l_prem_ih eqSS;
(* pi *) intros;Refine tt_not_ff (Q_sym eqSS);
(* lda *) intros;Refine tt_not_ff (Q_sym eqSS);
(* app *) intros;Refine tt_not_ff (Q_sym eqSS);
(* cnv *) intros;Refine l_prem_ih eqSS;
intros s3 hyp; Refine hyp; intros;
Refine ExIn s3;Refine pair; Immed;
Refine cnv_trans; Immed;
Refine Trm_eq_refl;
Save sf_gen_sort;

(* completeness of sfts *)
%\VerbFileOpen gts_sfts
Goal gts_sfts: {G|Cxt}{M,A|Trm}(gts G M A)->sfts G M A;
%\VerbFileClos gts_sfts
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]sfts G M A;
(* ax *)
intros; Refine sfAx; Immed;
(* Start *)
intros; Refine sfStart; Immed;
(* vWeak *)
intros; Refine sfvWeak; Immed;
(* sWeak *)
intros; Refine sfsWeak; Immed;
(* pi *)
intros; Refine sfPi; Immed;
(* Lda *)
intros;
(* use sfts generation lemma on r_ih to get some ss with sfts G A ss *)
Refine sf_gen_pi r_ih; intros s1 s2 s3 q spec;
Refine spec; intros l1 l2 l3 l4 l5;
Refine sfLda l1; Immed;
intros t tst;
(***** with an alternative system, could make a better argument
Refine sf_gen_sort|(CONS (Gb q A) G)|t|(sort s2);
Qrepl Q_sym (Trm_eq_subst tst); Refine l4;
************************************)
Refine only_typedsort_in_left r_prem; Qrepl Trm_eq_subst tst;
Refine socc_split_lem; Refine inr;
Qrepl socc_sort_lem t t; Refine SSrefl;
(* app *)
intros; Refine sfApp; Immed;
(* cnv *)
intros; Refine sftCnv; Immed;
Save;

(* soundness of sfts for semi-full gts *)
%\VerbFileOpen sfts_gts
Goal sfts_gts: {sf:semiFull}{G|Cxt}{M,A|Trm}(sfts G M A)->gts G M A;
%\VerbFileClos sfts_gts
intros _;
Refine sftsRec [G:Cxt][M,A:Trm][_:sfts G M A]gts G M A;
(* ax *)
intros; Refine Ax; Immed;
(* Start *)
intros; Refine Start; Immed;
(* vWeak *)
intros; Refine vWeak; Immed;
(* sWeak *)
intros; Refine sWeak; Immed;
(* pi *)
intros; Refine Pi; Immed;
(* Lda *)
intros; Refine type_correctness l_prem_ih; 
intros t tSpec; Refine tSpec;
intros BinSS; Refine sc_ts t;
Qrepl Q_sym (Trm_eq_vsub_sort B p m t); Refine BinSS;
intros u uSpec; Refine sf (Ex2In s2 s3 ? sc) u; intros t2 rlt2;
Refine Lda ?? l_prem_ih (Pi ?? r_prem_ih ?); Immed;
Qrepl Trm_eq_subst BinSS; Refine sStartLem l_prem_ih uSpec;
intros Btyped; Refine sf (Ex2In s2 s3 ? sc) t; intros t2 rlt2;
Refine Lda ?? l_prem_ih (Pi ?? r_prem_ih ?); Immed;
(* app *)
intros; Refine App; Immed;
(* cnv *)
intros; Refine tCnv; Immed;
Save;


(* PR for sfts *)
Goal {sf:semiFull}
     {G|Cxt}{M,A|Trm}(sfts G M A)->
          {A'|Trm}(par_redn A A')->sfts G M A';
intros; Refine gts_sfts; Refine gtsPR ? H1;
Refine sfts_gts sf H;
Save sftsPR;

(* type_correctness_pi for sfts *)
Goal {sf:semiFull}
     {G|Cxt}{u|VV}{M,A,B|Trm}(sfts G M (pi u A B))->
      Ex [s:SS]sfts G (pi u A B) (sort s);
intros;
Refine type_correctness_pi (sfts_gts sf H); intros s hyp;
Refine ExIn s; Refine gts_sfts; Immed;
Save sftsType_correctness_pi;
