Module EQV Import no_bp_red tpts KeyTheorem;

(*** now the \sim relation of Bert's draft, van Daalen's thesis ***)

$[EQV : Trm->Trm->Prop];
$[EQVrefl : refl EQV];
$[EQVs : {s1,s2:SS}EQV (sort s1) (sort s2)];
$[EQVpi : {a,b|Trm}{v,u|VV}
         {p|PP}{noccB:is_ff (poccur p a)}{noccB':is_ff (poccur p b)}
         {prem:EQV (vsub (par p) v a) (vsub (par p) u b)}
         {A:Trm}EQV (pi v A a) (pi u A b)];
$[EQVapp : {a,b|Trm}(EQV a b)->{c|Trm}{vcl:Vclosed c}EQV (app a c) (app b c)];
$[EQVrec : {C:{A,B|Trm}(EQV A B)->Prop}
     {EQVREFL:{A|Trm}C (EQVrefl A)}
     {EQVS:{s1,s2:SS}C (EQVs  s1 s2)}
     {EQVPI:{a,b|Trm}{v,u|VV}
            {p|PP}{noccB:is_ff (poccur p a)}{noccB':is_ff (poccur p b)}
            {prem:EQV (vsub (par p) v a) (vsub (par p) u b)}
            {ih:C prem}
            {A:Trm}C (EQVpi noccB noccB' prem A)}
     {EQVAPP:{a,b|Trm}
             {prem:EQV a b}
             {ih:C prem}
             {c|Trm}{vcl:Vclosed c}C (EQVapp prem vcl)}
     {A,B|Trm}{t:EQV A B}C t];


$[aEQV : Trm->Trm->Prop];
$[aEQVrefl : refl aEQV];
$[aEQVs : {s1,s2:SS}aEQV (sort s1) (sort s2)];
$[aEQVpi : {a,b|Trm}{v,u|VV}
          {prem:{p:PP}aEQV (vsub (par p) v a) (vsub (par p) u b)}
          {A:Trm}aEQV (pi v A a) (pi u A b)];
$[aEQVapp : {a,b|Trm}(aEQV a b)->{c|Trm}{vcl:Vclosed c}aEQV (app a c) (app b c)];
$[aEQVrec : {C:{A,B|Trm}(aEQV A B)->Prop}
     {aEQVREFL:{A|Trm}C (aEQVrefl A)}
     {aEQVS:{s1,s2:SS}C (aEQVs  s1 s2)}
     {aEQVPI:{a,b|Trm}{v,u|VV}
             {prem:{p:PP}aEQV (vsub (par p) v a) (vsub (par p) u b)}
             {ih:{p:PP}C (prem p)}
             {A:Trm}C (aEQVpi prem A)}
     {aEQVAPP:{a,b|Trm}
              {prem:aEQV a b}
              {ih:C prem}
              {c|Trm}{vcl:Vclosed c}C (aEQVapp prem vcl)}
     {A,B|Trm}{t:aEQV A B}C t];

Goal {A,B|Trm}(aEQV A B)->EQV A B;
Refine aEQVrec [A,B:Trm][_:aEQV A B]EQV A B;
intros;Refine EQVrefl;
intros;Refine EQVs;
intros;Refine fresh_params_lem2 a b;
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine EQVpi;Refine +3 ih;Immed;
intros;Refine EQVapp;Immed;
Save aEQV_EQV;

Goal {A,B|Trm}(EQV A B)->{rho:Renaming}aEQV (renTrm rho A) (renTrm rho B);
Refine EQVrec [A,B:Trm][_:EQV A B]
              {rho:Renaming}aEQV (renTrm rho A) (renTrm rho B);
intros;Refine aEQVrefl;
intros;Refine aEQVs;

intros;
Equiv aEQV (pi v (renTrm rho ?) (renTrm rho ?))
           (pi u (renTrm rho ?) (renTrm rho ?));
Refine aEQVpi;
intros q;
Claim Ex [sigma:Renaming]and3 (Q (renPar sigma p) q)
                              (Q (renTrm sigma a) (renTrm rho a))
                              (Q (renTrm sigma b) (renTrm rho b));
Refine ?+1;intros sigma sigmaSpec;
Qrepl Q_sym (and3_out1 sigmaSpec);
Qrepl Q_sym (and3_out2 sigmaSpec);
Qrepl Q_sym (and3_out3 sigmaSpec);
Qrepl alpha_renTrm_commutes sigma p v a;
Qrepl alpha_renTrm_commutes sigma p u b;
Immed;
[sigma = CONS (Pr p q) rho:Renaming];
Refine ExIn sigma;Refine pair3;
Equiv Q (if (PPeq p p) q ?) q;Qrepl PPrefl p;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB';Refine Q_refl;

intros;
Equiv aEQV (app (renTrm rho ?) (renTrm rho ?))
           (app (renTrm rho ?) (renTrm rho ?));
Refine aEQVapp;Refine +1 renTrm_resp_Vclosed;Immed;

Save EQV_aEQV_lem;

Goal {A,B|Trm}(EQV A B)->aEQV A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine EQV_aEQV_lem H renId;
Save EQV_aEQV;

Goal {A,B|Trm}(EQV A B)->{rho:Renaming}EQV (renTrm rho A) (renTrm rho B);
intros;Refine aEQV_EQV;Refine EQV_aEQV_lem;Immed;
Save renTrm_resp_EQV;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(EQV X Y)->EQV (psub N p X) (psub N p Y);
intros;
Refine aEQVrec [A,B:Trm][_:aEQV A B]EQV (psub N p A) (psub N p B);
intros;Refine EQVrefl;
intros;Refine EQVs;
intros;
Equiv EQV (pi ? (psub N p ?) (psub N p ?))
          (pi ? (psub N p ?) (psub N p ?));
Refine fresh_params_lem3p p N a b;
intros q qFresh;Refine qFresh;
intros neqPP noccN noccB noccB';
Refine EQVpi;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP u b);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP v a);
Refine ih;
intros;
Equiv EQV (app (psub N p ?) (psub N p ?))
          (app (psub N p ?) (psub N p ?));
Refine EQVapp;Refine +1 psub_resp_Vclosed;Immed;

Refine EQV_aEQV;Immed;
Save psub_resp_EQV;

Goal {X,Y|Trm}(EQV X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros ___;
Refine aEQVrec [A,B:Trm][_:aEQV A B]
               {p|PP}{occur:is_tt (poccur p B)}is_tt (poccur p A);
intros;Immed;
intros;Immed;

intros;Refine pocc_compound_lem occur;
intros occurA;Refine pocc_split_lem;Refine inl;Immed;
intros occurB;Refine pocc_split_lem;Refine inr;
Refine fresh_params_lem2p p a b;
intros q qFresh;Refine qFresh;
intros neqP noccB noccB';
Refine pocc_vsub_lem2 (ih q ?);
Refine +1 pocc_vsub_lem occurB;
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Immed;

intros;Refine pocc_compound_lem occur;
intros occurA;Refine pocc_split_lem;Refine inl;Refine ih;Immed;
intros occurB;Refine pocc_split_lem;Refine inr;Immed;

Refine EQV_aEQV;Immed;
Save EQV_refl_pocc;

Goal {X,Y|Trm}(EQV X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 EQV_refl_pocc;Immed;
Save not_pocc_resp_EQV;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}EQV (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (EQV_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Immed;
Save EQV_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}EQV (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 EQV_alpha_refl_pocc;Immed;
Save not_pocc_resp_EQV_alpha;

Goal {A,B|Trm}(EQV A B)->(Vclosed A)->Vclosed B;
Refine EQVrec [A,B:Trm][_:EQV A B]{vcl':Vclosed A}Vclosed B;
intros;Immed;
intros;Refine Vclosed_sort;
intros;Refine Vclosed_pi_lem vcl';
intros vclA vclB;Refine Vclosed_pi;Refine +2 ih;Immed;
intros;Refine Vclosed_app_lem vcl';
intros vclA vclB;Refine Vclosed_app;Refine ih;Immed;
Save Vclosed_resp_EQV;

Goal sym EQV;
Refine EQVrec [A,B:Trm][_:EQV A B]EQV B A;
intros;Refine EQVrefl;
intros;Refine EQVs;
intros;Refine EQVpi;Immed;
intros;Refine EQVapp;Immed;
Save EQVsym;

Goal {s|SS}{A|Trm}(EQV (sort s) A)-> Ex [s':SS]is_tt (Trm_eq A (sort s'));
intros;
Refine EQVrec [A,A'|Trm][_:EQV A A']{s|SS}{eq:is_tt (Trm_eq A (sort s))}
              Ex [s':SS]is_tt (Trm_eq A' (sort s'));Immed;
intros;Refine ExIn ?;Immed;
intros;Refine ExIn ?;Refine +1 SSrefl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine SSrefl;
Save EQV_sort_character;

Goal {u|VV}{A,B,C|Trm}(EQV (pi u C B) A)->
      Ex2 [v:VV][B':Trm]and (is_tt (Trm_eq A (pi v C B')))
                            ({q:PP}EQV (alpha q u B) (alpha q v B'));
intros;
Refine aEQVrec [A,A'|Trm][_:aEQV A A']
               {u|VV}{B,C|Trm}{eq:is_tt (Trm_eq A (pi u C B))}
               Ex2 [v:VV][B':Trm]
               and (is_tt (Trm_eq A' (pi v C B')))
                   ({q:PP}EQV (alpha q u B) (alpha q v B'));
intros;Refine Ex2In ? ?;Refine +2 pair eq ([q:PP]EQVrefl (alpha q ? ?));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Refine Ex2In u1 b;Refine pair;
Qrepl Trm_eq_subst eqA;Refine Trm_eq_refl;
intros;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine aEQV_EQV;Immed;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine EQV_aEQV;Immed;
Save EQV_pi_character;

Goal {u|VV}{A,B,C|Trm}(EQV (lda u C B) A)->is_tt (Trm_eq A (lda u C B));
intros;
Refine EQVrec [A,A'|Trm][_:EQV A A']
              {u|VV}{B,C|Trm}{eq:is_tt (Trm_eq A (lda u C B))}
               is_tt (Trm_eq A' (lda u C B));
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save EQV_lda_character;

Goal {A,B,C|Trm}(EQV (app B C) A)->
      Ex [B':Trm]and (is_tt (Trm_eq A (app B' C))) (EQV B B');
intros;
Refine EQVrec [A,A'|Trm][_:EQV A A']{eq:is_tt (Trm_eq A (app B C))}
               Ex [B':Trm]and (is_tt (Trm_eq A' (app B' C))) (EQV B B');

intros;Refine ExIn ?;Refine +1 pair eq (EQVrefl ?);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;
Refine ExIn b;Refine pair;
Qrepl Trm_eq_subst eqB;Refine Trm_eq_refl;
Qrepl Q_sym (Trm_eq_subst eqA);Immed;
Refine +2 Trm_eq_refl;Immed;
Save EQV_app_character;

Goal trans EQV;
Intros;
Refine EQVrec [A,C:Trm][_:EQV A C]{B|Trm}{eqv:EQV C B}EQV A B;Immed;
intros;Immed;
intros;Refine EQV_sort_character eqv;
intros s hypS;Qrepl Trm_eq_subst hypS;Refine EQVs;
intros;Refine EQV_pi_character eqv;
intros w b' hypB;Qrepl Trm_eq_subst (fst hypB);
Refine EQVpi noccB;
Refine not_pocc_resp_EQV_alpha (snd hypB) noccB'; 
Refine ih (snd hypB ?);
intros;Refine EQV_app_character eqv;
intros b' hypB;Qrepl Trm_eq_subst (fst hypB);
Refine EQVapp;Refine ih (snd hypB);Immed;
Save EQVtrans;

Goal {A,B|Trm}(EQV A B)->
     {A'|Trm}(no_bp_red1 A A')->
      Ex [B':Trm]and (no_bp_red1 B B') (EQV A' B');
Refine EQVrec [A,B|Trm][_:EQV A B]{A'|Trm}{redA:no_bp_red1 A A'}
               Ex [B':Trm]and (no_bp_red1 B B') (EQV A' B');
intros;Refine ExIn A';Refine pair redA (EQVrefl ?);
intros;Qrepl Trm_eq_subst (no_bp_red1_sort_character redA);
       Refine ExIn (sort s2);Refine pair (no_bp_red1_refl ?) (EQVs ? ?);
intros;Refine no_bp_red1_pi_character redA;
       intros w A'' B'' hyp;Qrepl Q_sym (Trm_eq_subst (and3_out3 hyp));
       [noccB'' = not_pocc_resp_no_bp_red1_alpha (and3_out2 hyp) noccB];
       Refine ih (and3_out2 hyp ?);
       intros B' hypB;Refine shape_lemma p B';
       intros x B''' shapeB;
       [eqB' = Q_sym (Trm_eq_subst (fst shapeB))][noccB''' = snd shapeB];
       Refine ExIn (pi x A'' B''');Refine pair;
       Refine no_bp_red1_pi;Refine and3_out1 hyp;
       Refine +4 EQVpi;Immed;
       Qrepl eqB';Refine fst hypB; 
       Qrepl eqB';Refine snd hypB; 
intros;Refine no_bp_red1_app_character redA;
       intros case;Refine case;
       intros a' c' hyp;Qrepl Q_sym (Trm_eq_subst (and3_out3 hyp));
       Refine ih (and3_out1 hyp);
       intros b' hypB;Refine ExIn (app b' c');Refine pair;
       Refine no_bp_red1_app (fst hypB) (and3_out2 hyp);
       Refine EQVapp (snd hypB);
       Refine Vclosed_resp_no_bp_red1 (and3_out2 hyp);Immed;
       intros case;Refine case;
       intros u U B hypB;Qrepl Q_sym (Trm_eq_subst (snd hypB));
       Refine EQV_pi_character (?:EQV (pi u U B) b);
       Qrepl Trm_eq_subst (fst hypB);Refine prem;
       intros v B' hypB';Refine ExIn (vsub c v B');Refine pair;
       Qrepl Trm_eq_subst (fst hypB');Refine no_bp_red1_pcon;
       Refine fresh_params_lem2 B B';
       intros q qFresh;Refine qFresh;
       intros noccB noccB';
       Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha c u noccB));
       Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha c v noccB'));
       Refine psub_resp_EQV q vcl;Refine snd hypB';
       intros case;Refine case;
       intros u U B hypB;Qrepl Q_sym (Trm_eq_subst (snd hypB));
       Claim EQV (lda u U B) b;
       Qrepl Trm_eq_subst (EQV_lda_character ?+1);
       Refine ExIn ?;Refine +1 pair;
       Refine +1 no_bp_red1_beta;Refine EQVrefl;
       Qrepl Trm_eq_subst (fst hypB);Refine prem;
Save EQV_no_bp_red1_character;

Goal {A,A'|Trm}(no_bp_redn A A')->
     {B|Trm}(EQV A B)->
      Ex [B':Trm]and (no_bp_redn B B') (EQV A' B');
Refine no_bp_rednRec [A,A'|Trm][_:no_bp_redn A A']{B|Trm}{eqv:EQV A B}
                      Ex [B':Trm]and (no_bp_redn B B') (EQV A' B');
intros;Refine EQV_no_bp_red1_character eqv r;
       intros B' hypB;Refine ExIn B';
       Refine pair (no_bp_redn_red1 (fst hypB)) (snd hypB);
intros;Refine lt_ih eqv;
       intros D' hypD;Refine rt_ih (snd hypD);
       intros B' hypB;Refine ExIn B';
       Refine pair (no_bp_redn_trans (fst hypD) (fst hypB)) (snd hypB);
Save EQV_no_bp_redn_character;

Goal {A,B|Trm}(EQV A B)->(Vclosed A)->
     {u|VV}{C,A'|Trm}(Vclosed (pi u C A'))->(conv_bp A (pi u C A'))->
      Ex2 [v:VV][B':Trm]conv_bp B (pi v C B');
intros;Refine conv_bpCR H3 H1 H2;
intros P hypP;Refine par_bp_redn_pi_character (snd hypP);
intros v C' A'' hypA';Refine EQV_no_bp_redn_character;
Refine +2 par_bp_no_bp_redn (fst hypP);Immed;
intros P' hypP';Refine EQV_pi_character (?:EQV (pi v C' A'') P');
Qrepl Trm_eq_subst (and3_out3 hypA');Refine snd hypP';
intros w B' hypB;Refine Ex2In w B';
Refine conv_bp_trans (conv_bp_redn (no_bp_par_bp_redn (fst hypP')));
Refine Vclosed_resp_no_bp_redn (fst hypP');Refine Vclosed_resp_EQV H H1;
Qrepl Trm_eq_subst (fst hypB);Refine PPinf (params B');
intros q noccB';Refine conv_bp_pi;Immed;
Refine conv_bp_sym (conv_bp_redn (and3_out1 hypA'));Refine conv_bp_refl;
Refine Vclosed_pi;Immed;Refine +2 Vclosed_pi;Immed;Refine +1 ?+3;
Refine Vclosed_resp_par_bp_redn (and3_out1 hypA') ?+1;
Refine fst (Vclosed_pi_lem H2);
Refine Vclosed_resp_EQV;Refine +1 snd hypB;
Refine Vclosed_resp_par_bp_redn;Refine +1 and3_out2 hypA';
Refine snd (Vclosed_pi_lem H2);
Save EQV_conv_bp_pi_character;

Goal {G|Cxt}{a,A|Trm}(tpts G a A)->{B|Trm}(tpts G a B)->EQV A B;
intros ____;
Refine atptsRec [G:Cxt][a,A:Trm][_:atpts G a A]
                {B|Trm}{tj:tpts G a B}EQV A B;
(* ax *) 
intros; Refine tpts_gen_sort tj; 
intros s hyp; Qrepl fst hyp; Refine EQVs;
(* par *) 
intros; 
Qrepl GBoccur_wValid_functional wvalG sc (tpts_gen_par tj);
Refine EQVrefl;
(* pi *) 
intros; Refine tpts_gen_pi tj; 
intros s1 s2 s3 hyp; Qrepl Trm_eq_subst (and4_out4 hyp);
Refine EQVs;
(* lda *) 
intros; Refine atpts_gen_lda tj; 
intros x B' hyp; Qrepl Trm_eq_subst (snd hyp);
Refine fresh_params_lem2G G1 B B';
intros q qFresh;Refine qFresh;
intros noccG noccB noccB';Refine EQVpi noccB noccB'; 
Refine ih noccG (fst hyp noccG);
(* app *) 
intros; Refine tpts_gen_app tj; 
intros A' hyp; Qrepl Trm_eq_subst (snd hyp);
Refine EQVapp (ih (fst hyp)) vcl;
Refine tpts_atpts;Immed;
Save tpts_EQV_lem;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->{B|Trm}(ots G a B)->EQV A B;
intros;Refine tpts_EQV_lem (ots_tpts H) (ots_tpts H1);
Save ots_EQV_lem;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->{B|Trm}(tpts G a B)->ots G a B;
intros ____;
Refine aotsRec [G|Cxt][a,A|Trm][_:aots G a A]{B|Trm}{tj:tpts G a B}ots G a B;
(* ax *) 
intros;Refine tpts_gen_sort tj; 
intros s hyp; Qrepl fst hyp; Refine oSrt wvalG (snd hyp);
(* par *) 
intros;Refine oPar;Immed;
Refine tpts_gen_par;Immed;
(* pi *) 
intros; Refine atpts_gen_pi tj; 
intros s1 s2 s3 hyp; Qrepl Trm_eq_subst (and4_out4 hyp);
Refine and4_out2 hyp;
intros X hypX;
Refine and4_out3 hyp;
intros w Y hypY;
Refine fresh_params_lem1G G1 B;
intros q qFresh;Refine qFresh;
intros noccG noccB;
Refine oPi (and4_out1 hyp) noccB (snd hypX) (snd hypY |?);
Refine +1 l_ih (fst hypX);
Refine +1 r_ih noccG (fst hypY noccG);
(* lda *) 
intros;Refine atpts_gen_lda tj; 
intros x B' hyp; Qrepl Trm_eq_subst (snd hyp);
Refine fresh_params_lem2G G1 M B';
intros q qFresh;Refine qFresh;
intros noccG noccM noccB'; 
Refine oLda noccM noccB' (ih noccG (fst hyp noccG));
(* app *) 
intros;Refine tpts_gen_app tj; 
intros B' hypB;Qrepl Trm_eq_subst (snd hypB);
Refine EQV_no_bp_redn_character (par_bp_no_bp_redn redA);
Refine +1 ots_EQV_lem (aots_ots l_prem) (l_ih (fst hypB));
intros P hypP;Refine EQV_pi_character (snd hypP);
intros w A' hypA;
Refine oApp (l_ih (fst hypB)) ? (aots_ots r_prem) redB;Immed;
Qrepl Q_sym (Trm_eq_subst (fst hypA));
Refine no_bp_par_bp_redn (fst hypP);

Refine +1 ots_aots;Immed;
Save tpts_ots_lem;

Goal {G|Cxt}{a,A|Trm}{j:gts G a A}{B|Trm}{tj:tpts G a B}
      or (conv_bp A B)
         (Ex3 [a0:Trm][s0:SS][BG:BindingCxt]KeyTheorem G a a0 B s0 BG);
intros;Refine gts_ots_lem j;
intros A' hypA;Refine hypA;
intros c oj;Refine ots_KeyTheorem;Refine +1 tpts_ots_lem;Immed;
Save tpts_KeyTheorem;

Goal {G|Cxt}{a,A|Trm}{j:gts G a A}
     {B|Trm}{tj:tpts G a B}{s|SS}{r:par_bp_redn B (sort s)}
      Ex [a0:Trm]and (gts G a0 (sort s)) (par_redn a a0);
intros;Refine gts_ots_lem j;
intros A' hypA;Refine hypA;
intros c oj;Refine ots_KeyTheorem_Corollary;Refine +3 tpts_ots_lem;Immed;
Save tpts_KeyTheorem_Corollary;

