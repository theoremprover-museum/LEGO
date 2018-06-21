Module vc Import gts;

(* strong valid contexts presentation *)
%\VerbFileOpen vcxt_vtyp_def
Inductive [vcxt:Cxt->Prop][vtyp:Cxt->Trm->Trm->Prop] Constructors
                                         (** vcxt **)
[vcNil:vcxt nilCxt]

[vcCons:{G|Cxt}{p|PP}{A|Trm}{s|SS}                  {noccG:is_ff (Poccur p G)}
       {prem:vtyp G A (sort s)}
     (*****************************************)
       vcxt (CONS (Gb p A) G)]

                                         (** vtyp **)
[vtSort:{G|Cxt}{s1,s2|SS}                                        {sc:ax s1 s2}
       {prem:vcxt G}
     (*****************************************)
       vtyp G (sort s1) (sort s2)]

[vtPar:{G|Cxt}{p|PP}{A|Trm}                    {sc:is_tt (GBoccur (Gb p A) G)}
       {prem:vcxt G}
     (*****************************************)
       vtyp G (par p) A]

[vtPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}               {sc:rl s1 s2 s3}
                                                    {noccB:is_ff (poccur p B)}
       {l_prem:vtyp G A (sort s1)}
       {r_prem:vtyp (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
       vtyp G (pi n A B) (sort s3)]

[vtLda:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}       {noccM:is_ff (poccur p M)}
                                                    {noccB:is_ff (poccur p B)}
       {l_prem:vtyp (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
       {r_prem:vtyp G (pi m A B) (sort s)}
     (*****************************************)
       vtyp G (lda n A M) (pi m A B)]

[vtApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
       {l_prem:vtyp G M (pi n A B)}
       {r_prem:vtyp G L A}
     (*****************************************)
       vtyp G (app M L) (vsub L n B)]

[vttCnv:{G|Cxt}{M,A,B|Trm}{s|SS}                                 {sc:cnv A B}
       {l_prem:vtyp G M A}
       {r_prem:vtyp G B (sort s)}
     (*****************************************)
       vtyp G M B]
NoReductions;
%\VerbFileClos vcxt_vtyp_def


(* vtyp is sound for gts *)
%\VerbFileOpen vtyp_gts
Goal vtyp_gts: {G|Cxt}{M,A|Trm}(vtyp G M A)->(gts G M A);
Refine vtyp_elim ([G|Cxt][_:vcxt G]or (Q G nilCxt) (Valid G))
                 ([G|Cxt][M,A|Trm][_:vtyp G M A]gts G M A);
%\VerbFileClos vtyp_gts
(* nil *)
Refine inl; Refine Q_refl;
(* cons *)
intros; Refine inr;
Refine Ex2In (par p) A; Refine Start noccG prem_ih;
(* sort *)
intros; Refine prem_ih;
intros Gnil; Qrepl Gnil; Refine Ax; Immed;
intros Gval; Refine Gval; intros M A p; Refine sStartLem; Immed;
(* par *)
intros; Refine prem_ih;
intros Gnil; Refine tt_not_ff; Qrepl Q_sym sc; Qrepl Gnil; Refine Q_refl;
intros Gval; Refine Gval; intros C D gtsCD; Refine vStartLem gtsCD sc;
(* pi *)
intros; Refine Pi; Immed;
(* lda *)
intros; Refine Lda; Immed;
(* app *)
intros; Refine App; Immed;
(* cnv *)
intros; Refine tCnv; Immed;
Save;

(* the "complementary" case is easily proved *)
%\VerbFileOpen vcxt_Valid
Goal vcxt_Valid: {G|Cxt}(vcxt G)->or (Q G nilCxt) (Valid G);
%\VerbFileClos vcxt_Valid
Refine vcxt_elim ([G|Cxt][_:vcxt G]or (Q G nilCxt) (Valid G))
                 ([G|Cxt][M,A|Trm][_:vtyp G M A]TT);
(* nil *)
Refine inl; Refine Q_refl;
(* cons *)
intros; Refine inr;
Refine Ex2In (par p) A; Refine Start noccG (vtyp_gts prem);
(* vtyp constructors are trivial *)
intros; Refine true;
intros; Refine true;
intros; Refine true;
intros; Refine true;
intros; Refine true;
intros; Refine true;
Save;

(* some technical lemmas about vtyp *)
Goal {G|Cxt}{M,A|Trm}(vtyp G M A)->vcxt G;
Refine vtyp_elim 
  ([G:Cxt][_:vcxt G]{b|GB}TT)
  ([G|Cxt][M,A|Trm][_:vtyp G M A]vcxt G);
(* nil *)
intros; Refine true;
(* cons *)
intros; Refine true;
(* sort *)
intros; Immed;
(* par *)
intros; Immed;
(* pi *)
intros; Immed;
(* lda *)
intros; Immed;
(* app *)
intros; Immed;
(* cnv *)
intros; Immed;
Save vtyp_vcxt;

(* well-typed in vtyp is Vclosed *)
(* must combine the 3 cases here; can't seperate them as with gts *)
Goal {G|Cxt}{M,A|Trm}(vtyp G M A)->
     and3 ({b|GB}(is_tt (GBoccur b G))->Vclosed (typOf b))
          (Vclosed M)
          (Vclosed A);
Refine vtyp_elim 
  ([G:Cxt][_:vcxt G]{b|GB}(is_tt (GBoccur b G))->Vclosed (typOf b))
  ([G|Cxt][M,A|Trm][_:vtyp G M A]
     and3 ({b|GB}(is_tt (GBoccur b G))->Vclosed (typOf b))
          (Vclosed M)
          (Vclosed A));
(* nil *)
intros; Refine tt_not_ff (Q_sym H);
(* cons *)
intros; Refine GBoccur_split_lem|G|nilCxt H;
intros h; Refine tt_not_ff (Q_sym h);
intros h; Qrepl GBeq_subst h; Refine and3_out2 prem_ih;
Refine and3_out1 prem_ih;
(* sort *)
intros; Refine pair3 (prem_ih) (Vclosed_sort ?) (Vclosed_sort ?);
(* par *)
intros; Refine pair3 (prem_ih) (Vclosed_par ?) (prem_ih sc);
(* pi *)
intros; Refine pair3 (and3_out1 l_prem_ih);
Refine Vclosed_pi (and3_out2 l_prem_ih) (and3_out2 r_prem_ih);
Refine Vclosed_sort;
(* lda *)
intros; Refine pair3 (and3_out1 r_prem_ih);
Refine Vclosed_lda (fst (Vclosed_pi_lem (and3_out2 r_prem_ih)))
                   (and3_out2 l_prem_ih);
Refine and3_out2 r_prem_ih;
(* app *)
intros; Refine pair3 (and3_out1 r_prem_ih);
Refine Vclosed_app (and3_out2 l_prem_ih) (and3_out2 r_prem_ih);
Refine PPinf (params B); intros p pFresh;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n pFresh));
Refine psub_resp_Vclosed;
Refine (and3_out2 r_prem_ih);
Refine (snd (Vclosed_pi_lem (and3_out3 l_prem_ih)));
(* cnv *)
intros; Refine pair3 (and3_out1 r_prem_ih);
Refine and3_out2 l_prem_ih; Refine and3_out2 r_prem_ih;
Save vtyp_Vclosed_lem;


(* vtyp generation lemmas *)
(* sort *)
Goal {G|Cxt}{u|SS}{A|Trm}{j:vtyp G (sort u) A}
     Ex [t:SS]and (ax u t)
                  (or (Q A (sort t))
                      (Ex [s:SS] and (vtyp G A (sort s))
                                     (cnv (sort t) A)));
intros;
Refine vtyp_elim ([G:Cxt][_:vcxt G]TT)
                 ([G:Cxt][M,A:Trm][_:vtyp G M A]
                  {u:SS}{eqMu:is_tt (Trm_eq M (sort u))}
                    Ex [t:SS]and (ax u t)
                                 (or (Q A (sort t))
                                     (Ex [s:SS] and (vtyp G A (sort s))
                                                    (cnv (sort t) A))));
Immed;
(* nil *)
intros; Refine true;
(* cons *)
intros; Refine true;
(* sort *)
intros; Refine ExIn s2; Refine pair;
Qrepl Q_sym (SSdecide eqMu); Refine sc; Refine inl; Refine Q_refl;
(* par *)
intros; Refine tt_not_ff (Q_sym eqMu);
(* pi *)
intros; Refine tt_not_ff (Q_sym eqMu);
(* lda *)
intros; Refine tt_not_ff (Q_sym eqMu);
(* app *)
intros; Refine tt_not_ff (Q_sym eqMu);
(* cnv *)
intros;
Refine l_prem_ih; Immed; intros X Xhyp; Refine ExIn X; Refine pair;
Refine fst Xhyp; Refine snd Xhyp;
intros QA1X; Refine inr; Refine ExIn s;
    Refine pair r_prem ?; Qrepl Q_sym QA1X; Refine sc;
intros Exs; Refine inr; Refine Exs; intros t ht; Refine ExIn s;
    Refine pair r_prem ?; Refine cnv_trans (snd ht) sc;
Refine Trm_eq_refl;
Save vtyp_gen_sort;


(* par *)
Goal {G|Cxt}{p|PP}{A|Trm}{j:vtyp G (par p) A}
     Ex [B:Trm]and (is_tt (GBoccur (Gb p B) G))
                   (or (Q A B)
                       (Ex [s:SS] and (vtyp G A (sort s))
                                      (cnv B A)));
intros;
Refine vtyp_elim ([G:Cxt][_:vcxt G]TT)
                 ([G:Cxt][M,A:Trm][_:vtyp G M A]
                  {q|PP}{eqP:is_tt (Trm_eq M (par q))}
                    Ex [B:Trm]and (is_tt (GBoccur (Gb q B) G))
                                  (or (Q A B)
                                      (Ex [s:SS] and (vtyp G A (sort s))
                                                     (cnv B A))));
Immed;
(* nil *)
intros; Refine true;
(* cons *)
intros; Refine true;
(* sort *)
intros; Refine tt_not_ff (Q_sym eqP);
(* par *)
intros; Refine ExIn A1; Refine pair;
Qrepl Q_sym (PPdecide eqP); Refine sc; Refine inl; Refine Q_refl;
(* pi *)
intros; Refine tt_not_ff (Q_sym eqP);
(* lda *)
intros; Refine tt_not_ff (Q_sym eqP);
(* app *)
intros; Refine tt_not_ff (Q_sym eqP);
(* cnv *)
intros;
Refine l_prem_ih; Immed; intros X Xhyp; Refine ExIn X; Refine pair;
Refine fst Xhyp; Refine snd Xhyp;
intros QA1X; Refine inr; Refine ExIn s;
    Refine pair r_prem ?; Qrepl Q_sym QA1X; Refine sc;
intros Exs; Refine inr; Refine Exs; intros t ht; Refine ExIn s;
    Refine pair r_prem ?; Refine cnv_trans (snd ht) sc;
Refine Trm_eq_refl;
Save vtyp_gen_par;


(* pi *)
Goal {G|Cxt}{A,B,C|Trm}{v|VV}{d:vtyp G (pi v A B) C}
      Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (vtyp G A (sort s1))
               (is_ff (poccur p B))
               (vtyp (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
intros;
Refine vtyp_elim ([G:Cxt][_:vcxt G]TT)
                 ([G:Cxt][M,C:Trm][_:vtyp G M C]
     {A,B|Trm}{v|VV}{eqPi:is_tt (Trm_eq M (pi v A B))}
      Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (vtyp G A (sort s1))
               (is_ff (poccur p B))
               (vtyp (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C));
Immed;
(* nil *) Refine true;
(* cons *) intros; Refine true;

(* sort *) intros;Refine tt_not_ff (Q_sym eqPi);
(* par *) intros;Refine tt_not_ff (Q_sym eqPi);
(* pi *) 
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eqPi)];
[eqA = and3_out2 (Trm_eq_pi_lem eqPi)];
[eqB = and3_out3 (Trm_eq_pi_lem eqPi)];
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_refl; Refine Vclosed_sort;
(* lda *) intros;Refine tt_not_ff (Q_sym eqPi);
(* app *) intros;Refine tt_not_ff (Q_sym eqPi);
(* cnv *) 
intros; Refine l_prem_ih eqPi;
intros s1 s2 s3 p hyp;
[vclA:Vclosed A1 = and3_out3 (vtyp_Vclosed_lem l_prem)];
[rule = and5_out1 hyp];
[hypA = and5_out2 hyp];
[pFresh = and5_out3 hyp];
[hypB = and5_out4 hyp];
[hypCnv = and5_out5 hyp];
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_trans;Immed;

Refine Trm_eq_refl;
Save vtyp_gen_pi;

(***********  vtyp thinning is as hard as gts thinning ********)
Inductive [avtyp:Cxt->Trm->Trm->Prop]
Constructors

[avtSort:{G|Cxt}{s1,s2|SS}
       {sc:ax s1 s2}
       {prem:vcxt G}
     (*****************************************)
       avtyp G (sort s1) (sort s2)]

[avtPar:{G|Cxt}{p|PP}{A|Trm}
       {sc:is_tt (GBoccur (Gb p A) G)}
       {prem:vcxt G}
     (*****************************************)
       avtyp G (par p) A]

[avtPi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{n|VV}
       {sc:rl s1 s2 s3}
       
       {l_prem:avtyp G A (sort s1)}
       {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                avtyp (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
     (*****************************************)
       avtyp G (pi n A B) (sort s3)]

[avtLda:{G|Cxt}{A,M,B|Trm}{s|SS}{n,m|VV}
       {l_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                avtyp (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
       {r_prem:avtyp G (pi m A B) (sort s)}
     (*****************************************)
       avtyp G (lda n A M) (pi m A B)]

[avtApp:{G|Cxt}{M,A,B,L|Trm}{n|VV}
       {l_prem:avtyp G M (pi n A B)}
       {r_prem:avtyp G L A}
     (*****************************************)
       avtyp G (app M L) (vsub L n B)]

[avttCnv:{G|Cxt}{M,A,B|Trm}{s|SS}
       {sc:cnv A B}
       {l_prem:avtyp G M A}
       {r_prem:avtyp G B (sort s)}
     (*****************************************)
       avtyp G M B]
NoReductions;

Goal {G|Cxt}{M,A|Trm}(avtyp G M A)->vcxt G;
Refine avtyp_elim 
  (*[G:Cxt][_:vcxt G]{b|GB}TT*)
  ([G|Cxt][M,A|Trm][_:avtyp G M A]vcxt G);
(* nil
intros; Refine true;
(* cons *)
intros; Refine true; *)
(* sort *)
intros; Immed;
(* par *)
intros; Immed;
(* pi *)
intros; Immed;
(* lda *)
intros; Immed;
(* app *)
intros; Immed;
(* cnv *)
intros; Immed;
Save avtyp_vcxt;

Goal {G|Cxt}{M,A|Trm}(avtyp G M A)->vtyp G M A;
Refine avtyp_elim [G:Cxt][M,A:Trm][_:avtyp G M A]vtyp G M A;
(* ax *) 
intros; Refine vtSort; Immed;
(* start *) 
intros; Refine vtPar; Immed;
(* pi *)
intros;Refine fresh_params_lem1G G B; 
intros p pFresh;Refine pFresh;
intros noccG noccB;Refine vtPi;Immed;
Refine r_prem_ih noccG;
(* lda *) 
intros;Refine fresh_params_lem2G G M B; 
intros p pFresh;Refine pFresh;
intros noccG noccM noccB;Refine vtLda;Immed;
Refine l_prem_ih noccG;
(* app *) 
intros; Refine vtApp; Immed;
(* cnv *) 
intros; Refine vttCnv; Immed;
Save avtyp_vtyp;

Goal {G|Cxt}{M,A|Trm}(vtyp G M A)->
     {rho|Renaming}[G' = renCxt rho G]
     {val:vcxt G'}avtyp G' (renTrm rho M) (renTrm rho A);
Refine vtyp_elim ([G:Cxt][_:vcxt G]TT)
                 ([G:Cxt][M,A:Trm][_:vtyp G M A]
     {rho|Renaming}[G' = renCxt rho G]{val:vcxt G'}
         avtyp G' (renTrm rho M) (renTrm rho A));

(* nil *)
intros; Refine true;
(* cons *)
intros; Refine true;

(* ax *)
intros; Refine avtSort; Immed;

(* start *)
intros; Refine avtPar; Refine renaming_GBoccur;Immed;

(* pi *) 
intros; Equiv avtyp ? (pi n (renTrm rho A) (renTrm rho B)) (sort s3);
Refine avtPi sc (l_prem_ih val);
intros q; intros;

(* for the right premise, we specify a renaming to use with the 
 * right induction hyp 
 *)
Claim ex [sigma:Renaming]and4 (Q (renPar sigma p) q)
                              (Q (renTrm sigma B) (renTrm rho B))
                              (Q (renTrm sigma A) (renTrm rho A))
                              (Q (renCxt sigma G) (renCxt rho G));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Equiv avtyp (renCxt sigma (CONS (Gb p A) G))
          ?
          (renTrm sigma (sort s2));
Qrepl alpha_renTrm_commutes sigma p n B;
Refine r_prem_ih|sigma;
Equiv vcxt (CONS (Gb (renPar sigma p) (renTrm sigma A))
                  (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec3;
Qrepl sigmaSpec4;
Refine vcCons;
Refine +2 avtyp_vtyp;
Refine +2 l_prem_ih; Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair4;
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(* Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
[lemA : is_ff (poccur p A)
      = CxtCorrect1 (vtyp_gts r_prem)];
Qrepl triv_renTrm_lem rho q lemA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[lemG : is_ff (POCCUR p G)
      = notPOCCURinTl (vtyp_gts r_prem)];
Qrepl triv_renCxt_lem rho q lemG; Refine Q_refl;

(* lda *) 
intros;
Equiv avtyp ? (lda n (renTrm rho A) (renTrm rho M))
             (pi m (renTrm rho A) (renTrm rho B));
Refine avtLda; Refine +2 r_prem_ih val; intros q; intros;
(* for the left premise, we specify a renaming to use with the 
 * left induction hyp 
 *)
Claim ex [sigma:Renaming]and5 (Q (renPar sigma p) q)
                              (Q (renTrm sigma M) (renTrm rho M))
                              (Q (renTrm sigma B) (renTrm rho B))
                              (Q (renTrm sigma A) (renTrm rho A))
                              (Q (renCxt sigma G) (renCxt rho G));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4 sigmaSpec5;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Qrepl Q_sym sigmaSpec5;
Equiv avtyp (renCxt sigma (CONS (Gb p A) G)) ? ?;
Qrepl alpha_renTrm_commutes sigma p n M;
Qrepl alpha_renTrm_commutes sigma p m B;
Refine l_prem_ih|sigma;
Equiv vcxt (CONS (Gb (renPar sigma p) (renTrm sigma A)) (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec4;
Qrepl sigmaSpec5;
Refine vtyp_gen_pi (avtyp_vtyp (r_prem_ih val)
      : vtyp (renCxt rho G) (pi m (renTrm rho A) (renTrm rho B)) (sort s));
intros s1 s2 s3 fresh lem;
[welltypedA : vtyp (renCxt rho G) (renTrm rho A) (sort s1)
            = and5_out2 lem];
Refine vcCons noccG welltypedA;

(* now for the substitution sigma, and its properties, as for the pi case *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair5;
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma M) (renTrm rho M) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccM; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(*Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
[lemA : is_ff (poccur p A)
      = CxtCorrect1 (vtyp_gts l_prem)];
Qrepl triv_renTrm_lem rho q lemA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[lemG : is_ff (POCCUR p G)
      = notPOCCURinTl (vtyp_gts l_prem)];
Qrepl triv_renCxt_lem rho q lemG; Refine Q_refl;

(* app *)
intros;Qrepl Q_sym (vsub_renTrm_commutes rho L n B);
Equiv avtyp ? (app (renTrm rho M) (renTrm rho L)) ?;
Refine avtApp (l_prem_ih val) (r_prem_ih val);

(* cnv *) 
intros;
Refine avttCnv (renTrm_resp_cnv sc rho) (l_prem_ih val) (r_prem_ih val);
Save vtyp_avtyp_lem;

Goal {G|Cxt}{M,A|Trm}(vtyp G M A)->avtyp G M A;
intros;
Qrepl renCxt_Id G;
Qrepl renTrm_Id M;
Qrepl renTrm_Id A;
Refine vtyp_avtyp_lem;Immed;
Qrepl Q_sym (renCxt_Id G); 
Refine vtyp_vcxt;Immed;
Save vtyp_avtyp;

Goal {G|Cxt}{M,A|Trm}{j:avtyp G M A}
     {G'|Cxt}{sub:subCxt G G'}{val:vcxt G'}
      avtyp G' M A;
Refine avtyp_elim [G:Cxt][M,A:Trm][_:avtyp G M A]
     {G'|Cxt}{sub:subCxt G G'}{val:vcxt G'}
      avtyp G' M A;
(* ax *)
intros; Refine vtyp_avtyp; Refine vtSort; Immed;
(* start *)
intros; Refine vtyp_avtyp; Refine vtPar; Refine sub; Immed;
(* pi *) 
intros;Refine avtPi sc; Refine l_prem_ih; Immed;
intros; Refine r_prem_ih;
Refine Poccur_subCxt_lem sub noccG;
Refine subCxt_extension sub;
Refine vcCons;Refine +2 avtyp_vtyp;Refine +2 l_prem_ih;Immed;
(* lda *) 
intros;Refine avtLda;Refine +2 r_prem_ih; Immed;
intros; Refine l_prem_ih; 
Refine Poccur_subCxt_lem sub noccG;
Refine subCxt_extension sub;
(* now use the pi case of the generation lemma *)
Refine vtyp_gen_pi (avtyp_vtyp (r_prem_ih sub val));
intros s1 s2 s3 fresh lem;
[welltypedA : vtyp G' A (sort s1) = and5_out2 lem];
Refine vcCons noccG welltypedA;
(* app *) 
intros; Refine vtyp_avtyp;
Refine vtApp; 
Refine +2 avtyp_vtyp; Refine +2 r_prem_ih;
Refine avtyp_vtyp; Refine l_prem_ih; Immed;
(* cnv *) 
intros; Refine vtyp_avtyp;
Refine vttCnv sc;
Refine +2 avtyp_vtyp; Refine +2 r_prem_ih;
Refine avtyp_vtyp; Refine l_prem_ih; Immed;
Save avtyp_thinning_lem;

Goal {G|Cxt}{M,A|Trm}{j:vtyp G M A}
     {G'|Cxt}{sub:subCxt G G'}{val:vcxt G'}
      vtyp G' M A;
intros; Refine avtyp_vtyp; Refine avtyp_thinning_lem;
Refine +1 vtyp_avtyp; Immed;
Save vtyp_thinning_lemma;

(* full weakening is now admissible *)
Goal {G|Cxt}{M,B|Trm}(vtyp G M B)->
      {p|PP}(is_ff (Poccur p G))->
      {A|Trm}{s|SS}(vtyp G A (sort s))->
        vtyp (CONS (Gb p A) G) M B;
intros;Refine vtyp_thinning_lemma;Immed;
Refine subCxt_hd;
Refine vcCons;Immed;
Save vtyp_weakening;

(* vtyp is complete for gts *)
%\VerbFileOpen gts_vtyp
Goal gts_vtyp: {G|Cxt}{M,A|Trm}(gts G M A)->(vtyp G M A);
%\VerbFileClos gts_vtyp
Refine gtsRec [G|Cxt][M,A|Trm][_:gts G M A]vtyp G M A;
(* ax *)
intros; Refine vtSort sc vcNil;
(* start *)
intros; Refine vtPar ? (vcCons noccG ih); Refine hd_GBoccur_lem;
(* vWeak *)
intros;
Refine vtyp_gen_par l_ih; intros B hypB; Refine snd hypB;
intros QDB; Qrepl QDB; Refine vtPar;
Refine snd (orr_character (GBeq (Gb n B) (Gb p A))
                          (GBoccur (Gb n B) G));
Refine inr; Refine fst hypB;
Refine vcCons; Immed;
intros exs; Refine exs; intros s hyps;
Refine vttCnv; Immed; Refine snd hyps;
Refine vtPar; Refine subCxt_hd|p|A|G; Refine fst hypB;
Refine vcCons;Refine +3 vtyp_weakening (fst hyps);Immed;
(* sWeak *)
intros;Refine vtyp_gen_sort l_ih; 
intros u hypu;Refine snd hypu;
intros QDu; Qrepl QDu; Refine vtSort; Refine fst hypu;
Refine vcCons; Immed;
intros exs; Refine exs; intros s hyps;
Refine vttCnv; Refine +2 snd hyps; Refine s1;
Refine vtSort; Refine fst hypu; 
Refine vcCons;Refine +3 vtyp_weakening (fst hyps);Immed;
(* pi *)
intros; Refine vtPi; Immed;
(* lda *)
intros; Refine vtLda; Immed;
(* app *)
intros; Refine vtApp; Immed;
(* cnv *)
intros; Refine vttCnv; Immed;
Save;

