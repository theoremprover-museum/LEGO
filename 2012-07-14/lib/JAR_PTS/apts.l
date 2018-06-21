Module apts Import gts renaming;

(* an alternative presentation of pts *)
%\VerbFileOpen apts
Inductive [apts:Cxt->Trm->Trm->Prop] Constructors
[aAx:{s1,s2|SS}{sc:ax s1 s2}apts nilCxt (sort s1) (sort s2)]

[aStart:{G|Cxt}{A|Trm}{s|SS}{p|PP}                  {noccG:is_ff (Poccur p G)}
         {prem:apts G A (sort s)}
     (*****************************************)
           apts (CONS (Gb p A) G) (par p) A]

[avWeak:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}              {noccG:is_ff (Poccur p G)}
         {l_prem:apts G (par n) D}
         {r_prem:apts G A (sort s)}
     (*****************************************)
           apts (CONS (Gb p A) G) (par n) D]

[asWeak:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}              {noccG:is_ff (Poccur p G)}
         {l_prem:apts G (sort t) D}
         {r_prem:apts G A (sort s)}
     (*****************************************)
           apts (CONS (Gb p A) G) (sort t) D]

[aPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{n|VV}                      {sc:rl s1 s2 s3}
         {l_prem:apts G A (sort s1)}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
              apts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
           apts G (pi n A B) (sort s3)]

[aLda:{G|Cxt}{A,M,B|Trm}{s|SS}{n,m|VV}
         {l_prem:{p|PP}{noccG:is_ff (Poccur p G)}
              apts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
         {r_prem:apts G (pi m A B) (sort s)}
     (*****************************************)
           apts G (lda n A M) (pi m A B)]

[aApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:apts G M (pi n A B)}
         {r_prem:apts G L A}
     (*****************************************)
           apts G (app M L) (vsub L n B)]

[atCnv:{G|Cxt}{M,A,B|Trm}{s|SS}                                   {sc:cnv A B}
         {l_prem:apts G M A}
         {r_prem:apts G B (sort s)}
     (*****************************************)
           apts G M B]
NoReductions;
%\VerbFileClos apts


[aptsRec = apts_elim
         :{C:{G|Cxt}{M,A|Trm}(apts G M A)->Prop}
      {AX:{s1,s2|SS}
         {sc:ax s1 s2}
           C (aAx sc)}
      {START:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:apts G A (sort s)}
         {ih:C prem}
           C (aStart noccG prem)}
      {vWEAK:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:apts G (par n) D}
         {r_prem:apts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (avWeak noccG l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:apts G (sort t) D}
         {r_prem:apts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (asWeak noccG l_prem r_prem)}
      {PI:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{n|VV}
         {sc:rl s1 s2 s3}
         {l_prem:apts G A (sort s1)}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       apts (CONS (Gb p A) G) (vsub (par p) n B)
                                              (sort s2)}
         {l_ih:C l_prem}
         {r_ih:{p|PP}{noccG:is_ff (Poccur p G)}
                     C (r_prem noccG)}
           C (aPi sc l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{s|SS}{n,m|VV}
         {l_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       apts (CONS (Gb p A) G) (vsub (par p) n M)
                                              (vsub (par p) m B)}
         {r_prem:apts G (pi m A B) (sort s)}
         {l_ih:{p|PP}{noccG:is_ff (Poccur p G)}
                     C (l_prem noccG)}
         {r_ih:C r_prem}
           C (aLda l_prem r_prem)}
      {APP:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:apts G M (pi n A B)}
         {r_prem:apts G L A}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (aApp l_prem r_prem)}
      {tCONV:{G|Cxt}{M,A,B|Trm}{s|SS}
         {sc:cnv A B}
         {l_prem:apts G M A}
         {r_prem:apts G B (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (atCnv sc l_prem r_prem)}
      {G|Cxt}{M,A|Trm}{t:apts G M A}C t];

%\VerbFileOpen apts_gts
Goal apts_gts : {G|Cxt}{M,A|Trm}(apts G M A)->gts G M A;
%\VerbFileClos apts_gts
Refine aptsRec [G:Cxt][M,A:Trm][_:apts G M A]gts G M A;
(* ax *) 
intros; Refine Ax; Immed;
(* start *) 
intros; Refine Start; Immed;
(* vWeak *) 
intros; Refine vWeak; Immed;
(* sWeak *) 
intros; Refine sWeak; Immed;
(* pi *)
intros;Refine fresh_params_lem1G G B; 
intros p pFresh;Refine pFresh;
intros noccG noccB;Refine Pi;Immed;
Refine r_ih noccG;
(* lda *) 
intros;Refine fresh_params_lem2G G M B; 
intros p pFresh;Refine pFresh;
intros noccG noccM noccB;Refine Lda;Immed;
Refine l_ih noccG;
(* app *) 
intros; Refine App; Immed;
(* cnv *) 
intros; Refine tCnv; Immed;
Save;

(* the obvious induction only proves apts is closed under _bijective_
 * renamings (because of the negative  occurrence of \verb!Poccur! in
 * the premises of \verb!aPi! and \verb!aLda!).  We need this to show
 * gts_apts, but later we can show apts is closed under _injective_
 * renamings, inherited from pts.
 *)
%\VerbFileOpen bij_ren_resp_apts
Goal bij_ren_resp_apts :
     {rho|Renaming}(inj rho)->(sur rho)->
     {G|Cxt}{M,A|Trm}(apts G M A)->
     apts (renCxt rho G) (renTrm rho M) (renTrm rho A);
%\VerbFileClos bij_ren_resp_apts
intros rho injRho surRho;
Refine aptsRec [G|Cxt][M,A|Trm][_:apts G M A]
       apts (renCxt rho G) (renTrm rho M) (renTrm rho A);
(* ax *)
intros; Refine aAx sc;
(* Start *)
intros; Refine aStart ? ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* vWeak *)
intros; Refine avWeak ? l_ih r_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* sWeak *)
intros; Refine asWeak ? l_ih r_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* pi *)
intros; 
Equiv apts ? (pi n (renTrm rho A) (renTrm rho B)) (sort s3);
Refine aPi sc l_ih; intros;
Refine surRho p; intros q hypq; Qrepl Q_sym (PPdecide hypq);
Equiv apts (renCxt rho (CONS (Gb q A) G)) ? ?;
Qrepl vsub_renTrm_commutes rho (par q) n B;
Refine r_ih;
Refine renaming_not_Poccur; Refine rho; Qrepl PPdecide hypq; Immed;
(* lda *)
intros; 
Equiv apts ? (lda n (renTrm rho A) (renTrm rho M))
             (pi m (renTrm rho A) (renTrm rho B));
Refine aLda; Refine s;
intros;
Refine surRho p; intros q hypq; Qrepl Q_sym (PPdecide hypq);
Equiv apts (renCxt rho (CONS (Gb q A) G)) ? ?;
Qrepl vsub_renTrm_commutes rho (par q) n M;
Qrepl vsub_renTrm_commutes rho (par q) m B;
Refine l_ih;
Refine renaming_not_Poccur; Refine rho; Qrepl PPdecide hypq; Immed;
Refine r_ih;
(* app *)
intros;
Qrepl Q_sym (vsub_renTrm_commutes rho L n B);
Equiv apts ? (app (renTrm rho M) (renTrm rho L)) ?;
Refine aApp; Immed;
(* cnv *)
intros; Refine atCnv; Immed; Refine renTrm_resp_cnv sc;
Save;

%\VerbFileOpen gts_apts
Goal gts_apts : {G|Cxt}{M,A|Trm}(gts G M A)->apts G M A;
%\VerbFileClos gts_apts
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]apts G M A;
(* ax *)
intros; Refine aAx; Immed;
(* start *)
intros; Refine aStart; Immed;
(* vWeak *)
intros; Refine avWeak; Immed;
(* sWeak *)
intros; Refine asWeak; Immed;
(* pi *)
intros; Refine aPi; Immed;
intros r _;
[nopG : is_ff (Poccur p G) = CxtCorrect0 r_prem];
[nopA : is_ff (poccur p A) = CxtCorrect1 r_prem];
[norA : is_ff (poccur r A) = cxt_free_params_lem r_prem noccG];
Claim Q (CONS (Gb r A) G) (renCxt (swap r p) (CONS (Gb p A) G));
Claim Q (vsub (par r) n B) (renTrm (swap r p) (vsub (par p) n B));
Qrepl ?+1; Qrepl ?+2;
Refine bij_ren_resp_apts (swap_inj r p) (swap_sur r p) r_ih;
Equiv Q ? (CONS (Gb (renPar (swap r p) p) (renTrm (swap r p) A))
                (renCxt (swap r p) G));
Qrepl swap_right_lem r p;
Qrepl triv_renTrm_lem (unit (Pr p r)) p norA;
Qrepl triv_renTrm_lem (NIL|rp) r nopA;
Qrepl Q_sym (renTrm_Id A);
Qrepl triv_renCxt_lem (unit (Pr p r)) p (Poccur_POCCUR_lem l_prem noccG);
Qrepl triv_renCxt_lem (NIL|rp) r (Poccur_POCCUR_lem l_prem nopG);
Qrepl Q_sym (renCxt_Id G); Refine Q_refl;
Refine tt_or_ff (PPeq r p);
intros eqrp; (* (swap r r) does nothing *)
  Qrepl PPdecide eqrp;
  Qrepl triv_swap_Trm p (vsub (par p) n B); Refine Q_refl;
intros neqrp; (* r not in [p/n]B *)
  Refine free_params_lem1 r_prem|r;
  Refine snd (deMorgan (PPeq ??) (Poccur ??)); Refine pair; Immed;
  intros norB _; Expand swap; 
  Qrepl triv_renTrm_lem (unit (Pr p r)) p norB;
  Qrepl Q_sym (vsub_renTrm_commutes (unit (Pr p r)) (par p) n B);
  Equiv Q ? (vsub (par (if (PPeq p p) r p)) ??);
  Qrepl PPrefl p; Qrepl triv_renTrm_lem (NIL|rp) r noccB;
  Qrepl Q_sym (renTrm_Id B); Refine Q_refl;
(* lda *)  (* a slightly different proof for lda, just for laughs *)
intros; Refine aLda; Immed;
intros r _;
[nopG : is_ff (Poccur p G) = CxtCorrect0 l_prem];
[nopA : is_ff (poccur p A) = CxtCorrect1 l_prem];
[norA : is_ff (poccur r A) = cxt_free_params_lem l_prem noccG];
Claim Q (CONS (Gb r A) G) (renCxt (swap p r) (CONS (Gb p A) G));
Claim Q (vsub (par r) n M) (renTrm (swap p r) (vsub (par p) n M));
Claim Q (vsub (par r) m B) (renTrm (swap p r) (vsub (par p) m B));
Qrepl ?+1; Qrepl ?+2; Qrepl ?+3;
Refine bij_ren_resp_apts (swap_inj p r) (swap_sur p r) l_ih;
Equiv Q ? (CONS (Gb (if (PPeq p p) r ?) (renTrm (swap p r) A))
                (renCxt (swap p r) G));
Qrepl (PPrefl p); Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r nopA;
Qrepl triv_renTrm_lem (NIL|rp) p norA;
Qrepl Q_sym (renTrm_Id A);
Qrepl triv_renCxt_lem (unit (Pr r p)) r (Poccur_POCCUR_lem r_prem nopG);
Qrepl triv_renCxt_lem (NIL|rp) p (Poccur_POCCUR_lem r_prem noccG);
Qrepl Q_sym (renCxt_Id G); Refine Q_refl;
Qrepl Q_sym (vsub_renTrm_commutes (swap p r) (par p) n M);
Equiv Q ? (vsub (par (if (PPeq p p) r ?)) n (renTrm ? M));
Qrepl PPrefl p; Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r noccM;
Claim is_ff (poccur r M);
Qrepl triv_renTrm_lem (NIL|rp) p ?+2;
Qrepl Q_sym (renTrm_Id M); Refine Q_refl;
Qrepl Q_sym (vsub_renTrm_commutes (swap p r) (par p) m B);
Equiv Q ? (vsub (par (if (PPeq p p) r ?)) m (renTrm ? B));
Qrepl PPrefl p; Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r noccB;
Claim is_ff (poccur r B);
Qrepl triv_renTrm_lem (NIL|rp) p ?+2;
Qrepl Q_sym (renTrm_Id B); Refine Q_refl;
(* how to get r not in M and B? *)
Claim and (is_ff (poccur r M)) (is_ff (poccur r B));
Refine fst ?+2; Refine snd ?+1;

Refine tt_or_ff (PPeq p r);
intros eqpr; Qrepl Q_sym (PPdecide eqpr); Refine pair noccM noccB;
intros neqpr;
Refine pair (not_pocc_vsub_lem2 ?) (not_pocc_vsub_lem2 ?);
Refine +2 (fst (free_params_lem1 l_prem ?));
Refine +3 (snd (free_params_lem1 l_prem ?));
Refine ?+1;
Refine snd (deMorgan (PPeq r p) (Poccur r G));
Qrepl PPsym r p; Refine pair neqpr noccG;
(* app *)
intros; Refine aApp; Immed;
(* cnv *)
intros; Refine atCnv; Immed;
Save;

Goal inj_ren_resp_apts :
     {rho|Renaming}(inj rho)->
     {G|Cxt}{M,A|Trm}(apts G M A)->
     apts (renCxt rho G) (renTrm rho M) (renTrm rho A);
intros; Refine gts_apts; Refine inj_ren_resp_gts H;
Refine apts_gts; Immed;
Save;


Goal {G|Cxt}{M,A|Trm}(apts G M A)->and (Vclosed M) (Vclosed A);
intros; Refine gts_Vclosed_lem (apts_gts H);
Save apts_Vclosed_lem;

(* the "a"-generation lemmas for PTSs *)

(* ax *) (* the same as before *)
(* par *)  (* the same as before *)
(* pi *)
%\VerbFileOpen apts_gen_pi
Goal apts_gen_pi:
     {G|Cxt}{A,B,C|Trm}{v|VV}{d:gts G (pi v A B) C}
     Ex3 [s1,s2,s3:SS]
         and4 (rl s1 s2 s3)
              (gts G A (sort s1))
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   gts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
              (cnv (sort s3) C);
%\VerbFileClos apts_gen_pi
intros;
Refine aptsRec [G:Cxt][M,C:Trm][_:apts G M C]
     {eqPi:is_tt (Trm_eq M (pi v A B))}
      Ex3 [s1,s2,s3:SS]
          and4 (rl s1 s2 s3)
               (gts G A (sort s1))
               ({p|PP}{noccG:is_ff (Poccur p G)}
                    gts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);

(* ax *) intros;Refine tt_not_ff (Q_sym eqPi);
(* start *) intros;Refine tt_not_ff (Q_sym eqPi);
(* vWeak *) intros;Refine tt_not_ff (Q_sym eqPi);
(* sWeak *) intros;Refine tt_not_ff (Q_sym eqPi);
(* pi *) 
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eqPi)];
[eqA = and3_out2 (Trm_eq_pi_lem eqPi)];
[eqB = and3_out3 (Trm_eq_pi_lem eqPi)];
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex3In;Refine +3 pair4;Immed;
Refine apts_gts;Refine l_prem;
intros;Refine apts_gts;Refine r_prem;Immed;
Refine cnv_refl; Refine Vclosed_sort;
(* lda *) intros;Refine tt_not_ff (Q_sym eqPi);
(* app *) intros;Refine tt_not_ff (Q_sym eqPi);
(* cnv *) 
intros;Refine l_ih eqPi;
intros s1 s2 s3 hyp;
[vclA = snd (gts_Vclosed_lem (apts_gts l_prem))];
[rule = and4_out1 hyp];
[hypA = and4_out2 hyp];
[hypB = and4_out3 hyp];
[hypCnv = and4_out4 hyp];
Refine Ex3In;Refine +3 pair4;Immed;
Refine cnv_trans;Immed;

Refine +2 Trm_eq_refl;Refine gts_apts;Immed;
Save;

(* lda *) 
%\VerbFileOpen apts_gen_lda
Goal apts_gen_lda:
     {G|Cxt}{A,N,C|Trm}{v|VV}{d:gts G (lda v A N) C}
     Ex3 [s:SS][B:Trm][u:VV]
         and3 (gts G (pi u A B) (sort s))
              ({p|PP}{noccG:is_ff (Poccur p G)}
                  gts (CONS (Gb p A) G) (vsub (par p) v N) (vsub (par p) u B))
              (cnv (pi u A B) C);
%\VerbFileClos apts_gen_lda
intros;
Refine aptsRec [G:Cxt][M,C:Trm][_:apts G M C]
               {eqLda:is_tt (Trm_eq M (lda v A N))}
     Ex3 [s:SS][B:Trm][u:VV]
         and3 (gts G (pi u A B) (sort s))
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   gts (CONS (Gb p A) G) (vsub (par p) v N) (vsub (par p) u B))
              (cnv (pi u A B) C);
(* ax *) intros;Refine tt_not_ff (Q_sym eqLda);
(* start *) intros;Refine tt_not_ff (Q_sym eqLda);
(* vWeak *) intros;Refine tt_not_ff (Q_sym eqLda);
(* sWeak *) intros;Refine tt_not_ff (Q_sym eqLda);
(* pi *) intros;Refine tt_not_ff (Q_sym eqLda);
(* lda *) intros;
Refine Trm_eq_pi_lem eqLda; intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex3In s B m;Refine pair3;
Refine apts_gts r_prem;
intros;Refine apts_gts;Refine l_prem;Immed;
Refine cnv_refl; Refine fst (apts_Vclosed_lem r_prem);
(* app *) intros;Refine tt_not_ff (Q_sym eqLda);
(* cnv *) intros;Refine l_ih eqLda;
intros s1 B1 m hyp;
Refine Ex3In s1 B1 m;Refine pair3;
Refine and3_out1 hyp;
Refine and3_out2 hyp;
Refine cnv_trans (and3_out3 hyp) sc;

Refine +2 Trm_eq_refl;Refine gts_apts;Immed;
Save;
