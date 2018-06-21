Module tpts Import ots;

(* Bert's type system tpts *)

(* A syntax-directed system for ts1 *)
$[tpts:Cxt->Trm->Trm->Prop];

$[tpSrt:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           tpts G (sort s1) (sort s2)];

$[tpPar:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           tpts G (par p) A];

$[tpPi:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{p|PP}{n|VV}
         {sc:rl sA sB s}
         {noccB:is_ff (poccur p B)}
         {redX:par_bp_redn X (sort sA)}{redY:par_bp_redn Y (sort sB)}
         {l_prem:tpts G A X}
         {r_prem:tpts (CONS (Gb p A) G) (vsub (par p) n B) Y}
     (*****************************************)
           tpts G (pi n A B) (sort s)];

$[tpLda:{G|Cxt}{A,M,B|Trm}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {prem:tpts (CONS (Gb p A) G) (vsub (par p) n M)
                                     (vsub (par p) m B)}
     (*****************************************)
           tpts G (lda n A M) (pi m A B)];

$[tpApp:{G|Cxt}{a,b,A|Trm}{vcl:Vclosed b}
       {prem:tpts G a A}
     (*****************************************)
           tpts G (app a b) (app A b)];


$[tptsRec:{C:{G|Cxt}{M,A|Trm}(tpts G M A)->Prop}
      {AX:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           C (tpSrt wvalG sc)}
      {START:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           C (tpPar wvalG sc)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{p|PP}{n|VV}
         {sc:rl sA sB s}
         {noccB:is_ff (poccur p B)}
         {redX:par_bp_redn X (sort sA)}{redY:par_bp_redn Y (sort sB)}
         {l_prem:tpts G A X}
         {r_prem:tpts (CONS (Gb p A) G) (vsub (par p) n B) Y}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (tpPi sc noccB redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {prem:tpts (CONS (Gb p A) G) (vsub (par p) n M)
                                     (vsub (par p) m B)}
         {ih:C prem}
           C (tpLda noccM noccB prem)}
      {APP:{G|Cxt}{a,b,A|Trm}{vcl:Vclosed b}
           {prem:tpts G a A}{ih:C prem}
            C (tpApp vcl prem)}
      {G|Cxt}{M,A|Trm}{t:tpts G M A}C t];


Goal {G|Cxt}{M,A|Trm}(tpts G M A)->wValid G;
Refine tptsRec [G|Cxt][X,Y|Trm][_:tpts G X Y]wValid G;
(* ax *) 
intros; Immed;
(* start *) 
intros; Immed;
(* pi *) 
intros; Immed;
(* lda *) 
intros; Refine wValid_tail ih;
(* app *) 
intros; Immed;
Save tpts_wValid_lem;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->tpts G M A;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]tpts G M A;
(* ax *) 
intros; Refine tpSrt;Immed;
(* start *) 
intros; Refine tpPar;Immed;
(* pi *) 
intros; Refine tpPi;Immed;
(* lda *) 
intros; Refine tpLda;Immed;
(* app *) 
intros; Refine tpApp (fst (ots_Vclosed_lem r_prem));Immed;
Save ots_tpts;

Goal {G|Cxt}{M,A|Trm}(gts G M A)->Ex [A':Trm]and (conv_bp A A') (tpts G M A');
intros;Refine gts_ots_lem;Immed;
intros A' hyp;Refine ExIn A';Refine pair (fst hyp) (ots_tpts (snd hyp));
Save gts_tpts_lem;

Goal {G|Cxt}{M,A|Trm}(tpts G M A)->and (Vclosed M) (Vclosed A);
Refine tptsRec [G:Cxt][M,A:Trm][_:tpts G M A]and (Vclosed M) (Vclosed A);
(* ax *) intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *) intros;Refine pair;Refine Vclosed_par;
Refine and3_out3 (wValid_weak wvalG sc);
(* pi *) intros;Refine pair;
Refine Vclosed_pi (fst l_ih) (fst r_ih);
Refine Vclosed_sort;
(* lda *) intros;Refine pair;
[vclA = and4_out4 (wValid_gen (tpts_wValid_lem prem))];
Refine Vclosed_lda vclA (fst ih);
Refine Vclosed_pi vclA (snd ih);
(* app *) intros;Refine pair;
Refine Vclosed_app (fst ih) vcl;
Refine Vclosed_app (snd ih) vcl;
Save tpts_Vclosed_lem;

Goal {G|Cxt}(wValid G)->
     {s1,s2|SS}(ax s1 s2)->tpts G (sort s1) (sort s2);
Refine wValidRec ([G|Cxt][_:wValid G]
       {s1,s2:SS}(ax s1 s2)->tpts G (sort s1) (sort s2));
intros; Refine tpSrt wVnil H;
intros; Refine tpSrt (wVcons vclA sc_p sc_A prem) H;
Save tpsStartLem;

(* tpts generation lemmas *)
Goal {G|Cxt}{v|VV}{A|Trm}(tpts G (var v) A)->absurd;
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
                 (is_tt (Trm_eq M (var v)))->absurd;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save tpts_gen_var;

Goal {G|Cxt}{p|PP}{A|Trm}(tpts G (par p) A)->is_tt (GBoccur (Gb p A) G);
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
     (is_tt (Trm_eq M (par p)))->is_tt (GBoccur (Gb p A) G);
intros; Refine tt_not_ff (Q_sym H1);
intros; Qrepl Q_sym (PPdecide H1); Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save tpts_gen_par;

Goal {G|Cxt}{s|SS}{A|Trm}(tpts G (sort s) A)->
         Ex [s2:SS] and (Q A (sort s2)) (ax s s2);
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
     (is_tt (Trm_eq M (sort s)))->
         Ex [s2:SS] and (Q A (sort s2)) (ax s s2);
intros; Refine ExIn s2; Qrepl Q_sym (SSdecide H1);
    Refine pair (Q_refl (sort s2)) sc;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save tpts_gen_sort;

(* Tue Apr 6 15:23:32 BST 1993  *)
Goal {G|Cxt}{X,Y|Trm}(tpts G X Y)->
     {s,s'|SS}{is_sort:is_tt (Trm_eq X (sort s))}{redY:par_bp_redn Y (sort s')}
      ax s s';
intros;Refine tpts_gen_sort;
Refine +3 Q_subst (Trm_eq_subst is_sort) ([X:Trm]tpts ? X ?);Immed;
intros s'' hypS;Refine hypS;
intros eq axS;
Qrepl SSdecide (par_bp_redn_sort_character (Q_subst eq ([Y:Trm]par_bp_redn Y ?) redY));
Immed;
Save tpts_red_sort_lem;

Goal {G|Cxt}{v|VV}{D,B|Trm}{A|Trm}(tpts G (pi v D B) A)->
       Ex3[sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex[X:Trm] and (tpts G D X) (par_bp_redn X (sort sD)))
              (Ex2[p:PP][Y:Trm] and3 (tpts (CONS (Gb p D) G)
                                          (vsub (par p) v B) Y)
                                     (is_ff (poccur p B))
                                     (par_bp_redn Y (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
     (is_tt (Trm_eq M (pi v D B)))->
       Ex3[sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex[X:Trm] and (tpts G D X) (par_bp_redn X (sort sD)))
              (Ex2[p:PP][Y:Trm] and3 (tpts (CONS (Gb p D) G)
                                         (vsub (par p) v B) Y)
                                     (is_ff (poccur p B))
                                     (par_bp_redn Y (sort sB)))
              (is_tt (Trm_eq A (sort s)));Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex3In sA sB s; Refine Trm_eq_pi_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair4; Refine sc;
Refine ExIn X; Refine pair l_prem redX;
Refine Ex2In p Y; Refine pair3 r_prem noccB redY; Refine Trm_eq_refl;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Refine Trm_eq_refl;
Save tpts_gen_pi;

Goal {G|Cxt}{v|VV}{D,b|Trm}{A|Trm}(tpts G (lda v D b) A)->
      Ex3 [u:VV][p:PP][B:Trm]
      and (tpts (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
          (is_tt (Trm_eq A (pi u D B)));
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
     (is_tt (Trm_eq M (lda v D b)))->
       Ex3 [u:VV][p:PP][B:Trm]
       and (tpts (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
           (is_tt (Trm_eq A (pi u D B)));Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex3In m p B; Refine Trm_eq_lda_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair prem; Refine Trm_eq_refl;
intros; Refine tt_not_ff (Q_sym H1);
Refine Trm_eq_refl;
Save tpts_gen_lda;

Goal {G|Cxt}{a,b|Trm}{A|Trm}(tpts G (app a b) A)->
         Ex[D:Trm]and (tpts G a D)
                      (is_tt (Trm_eq A (app D b)));
intros;
Refine tptsRec [G|Cxt][M,A|Trm][_:tpts G M A]
       (is_tt (Trm_eq M (app a b)))->
         Ex[D:Trm]and (tpts G a D)
                      (is_tt (Trm_eq A (app D b))); Immed; 
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine ExIn A1; Refine Trm_eq_app_lem H1;
intros eqA eqB;
Qrepl Q_sym (Trm_eq_subst eqA); Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair prem;Refine Trm_eq_refl;
Refine Trm_eq_refl;
Save tpts_gen_app;

(* alternate tpts *)
$[atpts:Cxt->Trm->Trm->Prop];

$[atpSrt:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           atpts G (sort s1) (sort s2)];

$[atpPar:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           atpts G (par p) A];

$[atpPi:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{n,m|VV}
         {sc:rl sA sB s}
         {redX:par_bp_redn X (sort sA)}
         {redY:{p:PP}par_bp_redn (alpha p m Y) (sort sB)}
         {l_prem:atpts G A X}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       atpts (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y)}
     (*****************************************)
           atpts G (pi n A B) (sort s)];

$[atpLda:{G|Cxt}{A,M,B|Trm}{n,m|VV}
         {prem:{p|PP}{noccG:is_ff (Poccur p G)}
                     atpts (CONS (Gb p A) G) (vsub (par p) n M)
                                            (vsub (par p) m B)}
     (*****************************************)
           atpts G (lda n A M) (pi m A B)];

$[atpApp:{G|Cxt}{a,b,A|Trm}{vcl:Vclosed b}
       {prem:atpts G a A}
     (*****************************************)
           atpts G (app a b) (app A b)];


$[atptsRec:{C:{G|Cxt}{M,A|Trm}(atpts G M A)->Prop}
      {AX:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           C (atpSrt wvalG sc)}
      {START:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           C (atpPar wvalG sc)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{n,m|VV}
         {sc:rl sA sB s}
         {redX:par_bp_redn X (sort sA)}
         {redY:{p:PP}par_bp_redn (alpha p m Y) (sort sB)}
         {l_prem:atpts G A X}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       atpts (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y)}
         {l_ih:C l_prem}
         {r_ih:{p|PP}{noccG:is_ff (Poccur p G)}
                     C (r_prem noccG)}
           C (atpPi sc redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{n,m|VV}
         {prem:{p|PP}{noccG:is_ff (Poccur p G)}
                     atpts (CONS (Gb p A) G) (vsub (par p) n M)
                                            (vsub (par p) m B)}
         {ih:{p|PP}{noccG:is_ff (Poccur p G)}
                   C (prem noccG)}
           C (atpLda prem)}
      {APP:{G|Cxt}{a,b,A|Trm}{vcl:Vclosed b}
           {prem:atpts G a A}{ih:C prem}
            C (atpApp vcl prem)}
      {G|Cxt}{M,A|Trm}{t:atpts G M A}C t];


Goal {G|Cxt}(wValid G)->
     {s1,s2|SS}(ax s1 s2)->atpts G (sort s1) (sort s2);
Refine wValidRec ([G|Cxt][_:wValid G]
       {s1,s2|SS}(ax s1 s2)->atpts G (sort s1) (sort s2));
intros; Refine atpSrt wVnil H;
intros; Refine atpSrt (wVcons vclA sc_p sc_A prem) H;
Save atpsStartLem;

Goal {G|Cxt}{M,A|Trm}(atpts G M A)->tpts G M A;
Refine atptsRec [G:Cxt][M,A:Trm][_:atpts G M A]tpts G M A;
(* ax *) 
intros; Refine tpSrt; Immed;
(* start *) 
intros; Refine tpPar; Immed;
(* pi *)
intros;Refine fresh_params_lem2G G Y B;
intros p pFresh;Refine pFresh;
intros noccG noccY noccB;
Refine tpPi sc noccB redX (redY p) l_ih;
Refine r_ih noccG;
(* lda *) 
intros;Refine fresh_params_lem2G G M B;
intros p pFresh;Refine pFresh;
intros noccG noccM noccB;
Refine tpLda noccM noccB; Refine ih noccG;
(* app *) 
intros; Refine tpApp; Immed;
Save atpts_tpts;

Goal {G|Cxt}{M,A|Trm}(tpts G M A)->
     {rho:Renaming}
     [G' = renCxt rho G]
     {val:wValid G'}
      atpts G' (renTrm rho M) (renTrm rho A);
Refine tptsRec [G:Cxt][M,A:Trm][_:tpts G M A]
     {rho:Renaming}
     [G' = renCxt rho G]
     {val:wValid G'}
      atpts G' (renTrm rho M) (renTrm rho A);
(* sort *)
intros; Refine atpSrt; Immed;
(* par *)
intros;
Refine atpPar val (renaming_GBoccur sc rho);
(* pi *)
intros; Refine shape_lemma p Y;
intros m Y' Yspec;
[noccY : is_ff (poccur p Y') = snd Yspec];
[eqY : Q (alpha p m Y') Y = Q_sym (Trm_eq_subst (fst Yspec))];
Equiv atpts ? (pi n (renTrm rho A) (renTrm rho B)) (sort s);
Refine atpPi sc (renTrm_resp_par_bp_redn redX rho);
Refine renTrm rho Y';Refine m;

(* reduction {p|PP}par_bp_redn (alpha p m (renTrm rho Y')) (sort sB) *)
intros q; 
Claim ex [sigma:Renaming]
           and (Q (renPar sigma p) q)
               (Q (renTrm sigma Y') (renTrm rho Y'));
Refine ?+1;
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl alpha_renTrm_commutes sigma p m Y';
Equiv par_bp_redn ? (renTrm sigma (sort sB));
Refine renTrm_resp_par_bp_redn;
Qrepl eqY;Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma Y') (renTrm rho Y') *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccY; Refine Q_refl;

(* left premiss *)
Refine l_ih; Immed;
(* right premiss *)
intros q; intros;

(* specify a renaming to use with the right induction hyp *)
Claim ex [sigma:Renaming]
           and5 (Q (renPar sigma p) q)
                (Q (renTrm sigma B) (renTrm rho B))
                (Q (renTrm sigma A) (renTrm rho A))
                (Q (renCxt sigma G) (renCxt rho G))
                (Q (renTrm sigma Y') (renTrm rho Y'));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4 sigmaSpec5;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Qrepl Q_sym sigmaSpec5;
Equiv atpts (renCxt sigma (CONS (Gb p A) G)) ? ?;
Qrepl alpha_renTrm_commutes sigma p n B;
Qrepl alpha_renTrm_commutes sigma p m Y';
Qrepl eqY;
Refine r_ih sigma;

(* wValid G' *)
Equiv wValid (CONS (Gb (renPar sigma p) (renTrm sigma A))
                   (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec3;
Qrepl sigmaSpec4;
Refine wVcons ? noccG ? val; 
Refine renTrm_resp_Vclosed (fst (tpts_Vclosed_lem l_prem));
intros r occA;Refine renaming_poccur rho occA;
intros r' rHyp;Refine rHyp;
intros eqR poccA;Qrepl PPdecide eqR;Refine renaming_Poccur;
Refine and4_out2 (wValid_gen (tpts_wValid_lem r_prem));
Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair5; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(* Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
[lemA : is_ff (poccur p A)
      = and4_out3 (wValid_gen (tpts_wValid_lem r_prem))];
Qrepl triv_renTrm_lem rho q lemA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[lemG : is_ff (POCCUR p G)
      = wV_notPOCCURinTl (tpts_wValid_lem r_prem)];
Qrepl triv_renCxt_lem rho q lemG; Refine Q_refl;
(* Q (renTrm sigma Y') (renTrm rho Y') *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccY; Refine Q_refl;

(* lda *)
intros; Refine wValid_gen (tpts_wValid_lem prem);
intros _ wfA noccA vclA;
Equiv atpts ? (lda n (renTrm rho A) (renTrm rho M))
             (pi m (renTrm rho A) (renTrm rho B));
Refine atpLda; intros q; intros;
(* specify a renaming to use with the induction hyp *)
Claim ex [sigma:Renaming]
           and5 (Q (renPar sigma p) q)
                (Q (renTrm sigma B) (renTrm rho B))
                (Q (renTrm sigma A) (renTrm rho A))
                (Q (renCxt sigma G) (renCxt rho G))
                (Q (renTrm sigma M) (renTrm rho M));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4 sigmaSpec5;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Qrepl Q_sym sigmaSpec5;
Equiv atpts (renCxt sigma (CONS (Gb p A) G)) ? ?;
Qrepl alpha_renTrm_commutes sigma p m B;
Qrepl alpha_renTrm_commutes sigma p n M;
Refine ih sigma;

(* wValid G' *)
Equiv wValid (CONS (Gb (renPar sigma p) (renTrm sigma A))
                   (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec3;
Qrepl sigmaSpec4;
Refine wVcons;Immed;
Refine renTrm_resp_Vclosed vclA;
intros r occA;Refine renaming_poccur rho occA;
intros r' rHyp;Refine rHyp;
intros eqR poccA;Qrepl PPdecide eqR;Refine renaming_Poccur;Refine wfA;Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair5; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(* Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[NOCCG : is_ff (POCCUR p G)
       = wV_notPOCCURinTl (tpts_wValid_lem prem)];
Qrepl triv_renCxt_lem rho q NOCCG; Refine Q_refl;
(* Q (renTrm sigma M) (renTrm rho M) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccM; Refine Q_refl;

(* tpApp *)
intros;
Equiv atpts ? (app (renTrm rho a) (renTrm rho b))
             (app (renTrm rho A) (renTrm rho b));
Refine atpApp ? (ih rho val);
Refine renTrm_resp_Vclosed vcl;

Save tpts_atpts_lem;

Goal {G|Cxt}{M,A|Trm}(tpts G M A)->atpts G M A;
intros;
Qrepl renCxt_Id G;
Qrepl renTrm_Id M;
Qrepl renTrm_Id A;
Refine tpts_atpts_lem H;
Qrepl Q_sym (renCxt_Id G); 
Refine tpts_wValid_lem H;
Save tpts_atpts;

Goal {G|Cxt}{M,A|Trm}(tpts G M A)->{rho:Renaming}(wValid (renCxt rho G))->
      tpts (renCxt rho G) (renTrm rho M) (renTrm rho A);
intros;Refine atpts_tpts;Refine tpts_atpts_lem;Immed;
Save renTrm_resp_tpts;

Goal {G|Cxt}{a,A|Trm}(atpts G a A)->
     {GG|Cxt}(subCxt G GG)->(wValid GG)->
      atpts GG a A;
Refine atptsRec [G:Cxt][a,A:Trm][_:atpts G a A]
               {GG|Cxt}{sub:subCxt G GG}{wval:wValid GG}
                atpts GG a A;
(* sort *)
intros; Refine atpSrt; Immed;
(* par *)
intros; Refine atpPar; Refine +1 sub; Immed;
(* pi *)
intros; Refine atpPi; Immed;
Refine l_ih; Immed;
intros p noccGG; 
(* we now wish to use the premise ? : is_ff (Poccur p G) of the
   right induction hypothesis with the right premise to conclude
   wValid (CONS (Gb p A) G), and hence, by context extension,
   wValid (CONS (Gb p A) GG) *)
[noccG = Poccur_subCxt_lem sub noccGG];
Refine r_ih noccG;
Refine subCxt_extension sub;
Refine wValid_gen (tpts_wValid_lem (atpts_tpts (r_prem noccG)));
intros _ wfA noccA vclA;Refine wVcons vclA noccGG ? wval;
intros q occA;Refine subCxt_Poccur_lem sub;Refine wfA;Immed;
(* lda *)
intros; Refine atpLda;
intros p noccGG; 
[noccG : is_ff (Poccur p G) = Poccur_subCxt_lem sub noccGG];
Refine ih noccG;
Refine subCxt_extension sub; 
Refine wValid_gen (tpts_wValid_lem (atpts_tpts (prem noccG)));
intros _ wfA noccA vclA; Refine wVcons vclA noccGG ? wval;
intros q occA; Refine subCxt_Poccur_lem sub;Refine wfA;Immed;
(* app *)
intros; Refine atpApp; Immed;
Refine ih; Immed;
Save atpts_thinning;

Goal {G|Cxt}{a,A|Trm}(tpts G a A)->
     {GG|Cxt}(subCxt G GG)->(wValid GG)->
      tpts GG a A;
intros;Refine atpts_tpts;Refine atpts_thinning;Refine +1 tpts_atpts;Immed;
Save tpts_thinning;

Goal {G|Cxt}{a,A|Trm}(tpts G a A)->
     {p|PP}{B|Trm}(wValid (CONS (Gb p B) G))->
      tpts (CONS (Gb p B) G) a A;
intros;Refine tpts_thinning;Immed;
intros;Refine subCxt_hd;
Save tpts_weakening;

Goal {G|Cxt}{v|VV}{D,B|Trm}{A|Trm}(tpts G (pi v D B) A)->
       Ex3 [sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex [X:Trm] and (tpts G D X) (par_bp_redn X (sort sD)))
              (Ex2 [u:VV][Y:Trm]
               and ({p|PP}(is_ff (Poccur p G))->
                     tpts (CONS (Gb p D) G) (alpha p v B) (alpha p u Y))
                   ({p:PP}par_bp_redn (alpha p u Y) (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros;
Refine atptsRec [G|Cxt][M,A|Trm][_:atpts G M A]
     (is_tt (Trm_eq M (pi v D B)))->
       Ex3 [sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex [X:Trm] and (tpts G D X) (par_bp_redn X (sort sD)))
              (Ex2 [u:VV][Y:Trm]
               and ({p|PP}(is_ff (Poccur p G))->
                     tpts (CONS (Gb p D) G) (alpha p v B) (alpha p u Y))
                   ({p:PP}par_bp_redn (alpha p u Y) (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);

intros; Refine Ex3In sA sB s; Refine Trm_eq_pi_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine fresh_params_lem1G G1 Y;
intros q qFresh;Refine qFresh;
intros noccG noccY;Refine pair4 sc ? ? (Trm_eq_refl ?);
Refine ExIn X; Refine pair (atpts_tpts l_prem) redX;
Refine Ex2In m Y; Refine pair ? redY; 
intros;Refine atpts_tpts;Refine r_prem;Immed;

intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Refine +2 Trm_eq_refl;Refine tpts_atpts;Immed;
Save atpts_gen_pi;

Goal {G|Cxt}{v|VV}{D,b|Trm}{A|Trm}(tpts G (lda v D b) A)->
      Ex2 [u:VV][B:Trm]
      and ({p|PP}(is_ff (Poccur p G))->
           tpts (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
          (is_tt (Trm_eq A (pi u D B)));
intros;
Refine atptsRec [G|Cxt][M,A|Trm][_:atpts G M A]
     (is_tt (Trm_eq M (lda v D b)))->
       Ex2 [u:VV][B:Trm]
       and ({p|PP}(is_ff (Poccur p G))->
             tpts (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
           (is_tt (Trm_eq A (pi u D B)));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex2In m B; Refine Trm_eq_lda_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair;
intros;Refine atpts_tpts;Refine prem;Immed;
Refine Trm_eq_refl;
intros; Refine tt_not_ff (Q_sym H1);
Refine +2 Trm_eq_refl;Refine tpts_atpts;Immed;
Save atpts_gen_lda;
