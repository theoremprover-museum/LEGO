Module alpha_conversion 
Import conversion complete_development;

(* alpha conversion with atomic reflexivity *)

(******************************************************)

Inductive [alpha_conv : Trm->Trm->Prop] 

(*Relation*)

Constructors 
[alpha_conv_refl_sort : {s:SS} alpha_conv (sort s) (sort s)]
[alpha_conv_refl_par : {p:PP} alpha_conv (par p) (par p)]

[alpha_conv_pi:{A,A'|Trm}{premA:alpha_conv A A'} 
              {u,v|VV}{B,B'|Trm}{p|PP} 
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
              {premB:alpha_conv (alpha p u B) (alpha p v B')} 
               alpha_conv (pi u A B) (pi v A' B')]

[alpha_conv_lda:{A,A'|Trm}{premA:alpha_conv A A'} 
               {u,v|VV}{B,B'|Trm}{p|PP} 
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
               {premB:alpha_conv (alpha p u B) (alpha p v B')} 
                alpha_conv (lda u A B) (lda v A' B')]

[alpha_conv_app:{A,A'|Trm}{premA:alpha_conv A A'} 
                {B,B'|Trm}{premB:alpha_conv B B'} 
                 alpha_conv (app A B) (app A' B')];

(* introduce the non-dependent form - we could *)
(* do this with Relation, but we won't *)

Goal alpha_convRec : {C:{A,B:Trm}Prop} 

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {PI:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm}{p|PP} 
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                  {premB:alpha_conv (alpha p u B) (alpha p v B')}
 	          {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm}{p|PP} 
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                   {premB:alpha_conv (alpha p u B) (alpha p v B')}
		   {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:alpha_conv B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(alpha_conv A B) -> C A B;

intros;Refine alpha_conv_elim [A,B|Trm][_:alpha_conv A B]C A B;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;

Goal alpha_conv_par_red1: {A,B|Trm}(alpha_conv A B)->par_red1 A B;
Refine alpha_convRec [A,B:Trm]par_red1 A B;
intros; Refine par_red1_refl_sort;
intros; Refine par_red1_refl_par;
intros;Refine par_red1_pi;Immed;
intros;Refine par_red1_lda;Immed;
intros;Refine par_red1_app;Immed;
Save;

Goal alpha_conv_conv:
     {A,B|Trm}(alpha_conv A B)->conv A B;
intros; Refine conv_redn;
Refine par_redn_red1; Refine alpha_conv_par_red1; Immed;
Save;

Goal alpha_conv_Vclosed:
     {A,B|Trm}(alpha_conv A B)->and (Vclosed A) (Vclosed B);
intros; Refine par_red1_Vclosed; Refine alpha_conv_par_red1; Immed;
Save;

Goal alpha_conv_refl : {A|Trm}(Vclosed A)->alpha_conv A A;
intros;Refine aVclosedRec [A|Trm][_:aVclosed A]alpha_conv A A;
intros;Refine alpha_conv_refl_sort;
intros;Refine alpha_conv_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine alpha_conv_pi;Immed;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine alpha_conv_lda;Immed;
intros;Refine alpha_conv_app;Immed;
Refine Vclosed_aVclosed;Immed;
Save;

Goal {A,A'|Trm}(alpha_conv A A')->Q (isSrt A) (isSrt A');
Refine alpha_convRec [A,A'|Trm]Q (isSrt A) (isSrt A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save alpha_conv_shape_sort;

Goal {A,A'|Trm}(alpha_conv A A')->Q (isPar A) (isPar A');
Refine alpha_convRec [A,A'|Trm]Q (isPar A) (isPar A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save alpha_conv_shape_par;

Goal {A,A'|Trm}(alpha_conv A A')->Q (isPi A) (isPi A');
Refine alpha_convRec [A,A'|Trm]Q (isPi A) (isPi A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save alpha_conv_shape_pi;

Goal {A,A'|Trm}(alpha_conv A A')->Q (isLda A) (isLda A');
Refine alpha_convRec [A,A'|Trm]Q (isLda A) (isLda A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save alpha_conv_shape_lda;

Goal {A,A'|Trm}(alpha_conv A A')->Q (isApp A) (isApp A');
Refine alpha_convRec [A,A'|Trm]Q (isApp A) (isApp A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save alpha_conv_shape_app;

Goal alpha_conv_pres_lngth:
     {A,B|Trm}(alpha_conv A B)->Q (lngth A) (lngth B);
Refine alpha_conv_elim [A,B:Trm][_:alpha_conv A B]Q (lngth A) (lngth B);
(* refl *)
intros; Refine Q_refl;
intros; Refine Q_refl;
(* pi *)
intros;
Equiv Q (S (add (lngth ?) (lngth ?))) (S (add (lngth ?) (lngth ?)));
Qrepl Q_sym (alpha_preserves_lngth B p u);
Qrepl Q_sym (alpha_preserves_lngth B' p v);
Qrepl premA_ih; Qrepl premB_ih; Refine Q_refl;
(* lda *)
intros;
Equiv Q (S (add (lngth ?) (lngth ?))) (S (add (lngth ?) (lngth ?)));
Qrepl Q_sym (alpha_preserves_lngth B p u);
Qrepl Q_sym (alpha_preserves_lngth B' p v);
Qrepl premA_ih; Qrepl premB_ih; Refine Q_refl;
(* app *)
intros;
Equiv Q (S (add (lngth ?) (lngth ?))) (S (add (lngth ?) (lngth ?)));
Qrepl premA_ih; Qrepl premB_ih; Refine Q_refl;
Save;

Inductive [alpha_aconv : Trm->Trm->Prop] 

(*Relation*)

Constructors 
[alpha_aconv_refl_sort : {s:SS} alpha_aconv (sort s) (sort s)]
[alpha_aconv_refl_par : {p:PP} alpha_aconv (par p) (par p)]

[alpha_aconv_pi:{A,A'|Trm}{premA:alpha_aconv A A'} 
              {u,v|VV}{B,B'|Trm} 
              {premB:{p:PP}alpha_aconv (alpha p u B) (alpha p v B')} 
               alpha_aconv (pi u A B) (pi v A' B')]

[alpha_aconv_lda:{A,A'|Trm}{premA:alpha_aconv A A'} 
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}alpha_aconv (alpha p u B) (alpha p v B')} 
                alpha_aconv (lda u A B) (lda v A' B')]

[alpha_aconv_app:{A,A'|Trm}{premA:alpha_aconv A A'} 
                {B,B'|Trm}{premB:alpha_aconv B B'} 
                 alpha_aconv (app A B) (app A' B')]

NoReductions;


Goal {A,B|Trm}(alpha_aconv A B)->alpha_conv A B;
Refine alpha_aconv_elim [A,B:Trm][_:alpha_aconv A B]alpha_conv A B;
intros;Refine alpha_conv_refl_sort;
intros;Refine alpha_conv_refl_par;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine alpha_conv_pi;Refine +4 premB_ih;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine alpha_conv_lda;Refine +4 premB_ih;Immed;
intros;Refine alpha_conv_app;Immed;
Save alpha_aconv_conv;

Goal {A,B|Trm}(alpha_conv A B)->
     {rho:Renaming}alpha_aconv (renTrm rho A) (renTrm rho B);
Refine alpha_convRec [A,B:Trm]
                   {rho:Renaming}alpha_aconv (renTrm rho A) (renTrm rho B);
intros;Refine alpha_aconv_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine alpha_aconv_refl_par;

intros;
Equiv alpha_aconv (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine alpha_aconv_pi;Immed;
intros q;
Claim Ex [sigma:Renaming]and3 (Q (renPar sigma p) q)
                              (Q (renTrm sigma B) (renTrm rho B))
                              (Q (renTrm sigma B') (renTrm rho B'));
Refine ?+1;
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigma1 sigma2 sigma3;
Qrepl Q_sym sigma1;Qrepl Q_sym sigma2;Qrepl Q_sym sigma3;
Qrepl alpha_renTrm_commutes sigma p u B;
Qrepl alpha_renTrm_commutes sigma p v B';
Immed;
[sigma = CONS (Pr p q) rho:Renaming];
Refine ExIn sigma;Refine pair3;
Equiv Q (if (PPeq p p) q ?) q;Qrepl PPrefl p;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB';Refine Q_refl;

intros;
Equiv alpha_aconv (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine alpha_aconv_lda;Immed;
intros q;
Claim Ex [sigma:Renaming]and3 (Q (renPar sigma p) q)
                              (Q (renTrm sigma B) (renTrm rho B))
                              (Q (renTrm sigma B') (renTrm rho B'));
Refine ?+1;
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigma1 sigma2 sigma3;
Qrepl Q_sym sigma1;Qrepl Q_sym sigma2;Qrepl Q_sym sigma3;
Qrepl alpha_renTrm_commutes sigma p u B;
Qrepl alpha_renTrm_commutes sigma p v B';
Immed;
[sigma = CONS (Pr p q) rho:Renaming];
Refine ExIn sigma;Refine pair3;
Equiv Q (if (PPeq p p) q ?) q;Qrepl PPrefl p;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB';Refine Q_refl;

intros;
Equiv alpha_aconv (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine alpha_aconv_app;Immed;

Save alpha_conv_aconv_lem;

Goal {A,B|Trm}(alpha_conv A B)->alpha_aconv A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine alpha_conv_aconv_lem H renId;
Save alpha_conv_aconv;

Goal {A,B|Trm}(alpha_conv A B)->{rho:Renaming}alpha_conv (renTrm rho A) (renTrm rho B);
intros;Refine alpha_aconv_conv;Refine alpha_conv_aconv_lem;Immed;
Save renTrm_resp_alpha_conv;

(* introduce the non-dependent form - but this time, we don't appear *)
(* to be able to do this with Relation, because this really is a *)
(* complex derived notion *)

Goal alpha_aconvRec : {C:{A,B:Trm}Prop} 

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {PI:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm} 
                  {premB:{p:PP}alpha_conv (alpha p u B) (alpha p v B')}
 	          {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm} 
                   {premB:{p:PP}alpha_conv (alpha p u B) (alpha p v B')}
		   {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:alpha_conv A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:alpha_conv B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(alpha_conv A B) -> C A B;

intros;Refine alpha_aconv_elim[A,B|Trm][_:alpha_aconv A B]C A B;Immed;
intros;Refine PI;Immed;
       Refine alpha_aconv_conv premA;Refine [p:PP]alpha_aconv_conv (premB p);
intros;Refine LDA;Immed;
       Refine alpha_aconv_conv premA;Refine [p:PP]alpha_aconv_conv (premB p);
intros;Refine APP;Immed;
       Refine alpha_aconv_conv premA;Refine alpha_aconv_conv premB;
Refine alpha_conv_aconv;Immed;
Save;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(alpha_conv X Y)->alpha_conv (psub N p X) (psub N p Y);
intros ___;
Refine alpha_aconvRec [A,B:Trm]alpha_conv (psub N p A) (psub N p B);

intros;Refine alpha_conv_refl_sort;

intros;Equiv [M = if (PPeq p p1) N (par p1)]alpha_conv M M;
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Refine alpha_conv_refl;Immed;
intros neqP;Qrepl neqP;Refine alpha_conv_refl_par;

intros;
Equiv alpha_conv (pi u (psub N p A) (psub N p B))
               (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine alpha_conv_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv alpha_conv (lda u (psub N p A) (psub N p B))
               (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine alpha_conv_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv alpha_conv (app (psub N p A) (psub N p B))
               (app (psub N p A') (psub N p B'));
Refine alpha_conv_app;Immed;

Save psub_resp_alpha_conv;

Goal {X,Y|Trm}(alpha_conv X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);

Refine alpha_aconvRec [A,B:Trm]
                    {p|PP}{occ:is_tt (poccur p B)}is_tt (poccur p A);
intros;Immed;
intros;Immed;

intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine pocc_split_lem;Refine inr;
Refine fresh_params_lem2p p B B';
intros q qFresh;Refine qFresh;
intros neqP noccB noccB';
Refine pocc_vsub_lem2 (ihB q ?);
Refine +1 pocc_vsub_lem occB;
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;

intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine pocc_split_lem;Refine inr;
Refine fresh_params_lem2p p B B';
intros q qFresh;Refine qFresh;
intros neqP noccB noccB';
Refine pocc_vsub_lem2 (ihB q ?);
Refine +1 pocc_vsub_lem occB;
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;

intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine pocc_split_lem;Refine inr;Refine ihB;Immed;

Save alpha_conv_refl_pocc;

Goal {X,Y|Trm}(alpha_conv X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 alpha_conv_refl_pocc;Immed;
Save not_pocc_resp_alpha_conv;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}alpha_conv (alpha p u X) (alpha p v Y)}
     {p|PP}{occ:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (alpha_conv_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;
Save alpha_conv_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}alpha_conv (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 alpha_conv_alpha_refl_pocc;Immed;
Save not_pocc_resp_alpha_conv_alpha;

Goal {N,N'|Trm}{alpha_redN:alpha_conv N N'}{p:PP} 
      {M|Trm}(Vclosed M)->alpha_conv (psub N p M) (psub N' p M); 
 intros ______; 
 [vclN  = fst (alpha_conv_Vclosed alpha_redN): Vclosed N]; 
 [vclN' = snd (alpha_conv_Vclosed alpha_redN): Vclosed N']; 
 [subN = psub N p][subN' = psub N' p]; 

Refine aVclosedRec [A:Trm][_:aVclosed A]alpha_conv (subN A) (subN' A); 
 intros;Refine alpha_conv_refl_sort; 

intros;Equiv [M = if (PPeq p p1) N (par p1)] 
 	     [M' = if (PPeq p p1) N' (par p1)] 
 	      alpha_conv M M'; 
 Refine tt_or_ff (PPeq p p1); 
 intros eqP;Qrepl eqP;Immed; 
 intros neqP;Qrepl neqP;Refine alpha_conv_refl_par; 

intros;Equiv alpha_conv (pi n (subN A) (subN B)) (pi n (subN' A) (subN' B)); 
 Refine fresh_params_lem2p p N B; 
 intros q qFresh;Refine qFresh; 
 intros neqP noccN noccB;Refine alpha_conv_pi;Refine ihA; 
 Refine +1 not_pocc_psub_lem noccB noccN; 
 Refine not_pocc_psub_lem noccB (not_pocc_resp_alpha_conv alpha_redN noccN); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP n B); 
 Immed; 

intros;Equiv alpha_conv (lda n (subN A) (subN B)) (lda n (subN' A) (subN' B)); 
 Refine fresh_params_lem2p p N B; 
 intros q qFresh;Refine qFresh; 
 intros neqP noccN noccB;Refine alpha_conv_lda;Refine ihA; 
 Refine +1 not_pocc_psub_lem noccB noccN; 
 Refine not_pocc_psub_lem noccB (not_pocc_resp_alpha_conv alpha_redN noccN); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP n B); 
 Immed; 

intros;Equiv alpha_conv (app (subN A) (subN B)) (app (subN' A) (subN' B)); 
 Refine alpha_conv_app;Immed; 

Refine Vclosed_aVclosed;Immed; 
 Save alpha_conv_refl_psub_lem; 

Goal {N,N'|Trm}{alpha_redN:alpha_conv N N'}{p:PP}
     {X,X'|Trm}(alpha_conv X X')->alpha_conv (psub N p X) (psub N' p X');
intros ____;
[vclN  = fst (alpha_conv_Vclosed alpha_redN): Vclosed N];
[vclN' = snd (alpha_conv_Vclosed alpha_redN): Vclosed N'];
[subN = psub N p][subN' = psub N' p];

Refine alpha_aconvRec [M,M'|Trm]alpha_conv (subN M) (subN' M');

(* refl *)
intros;Refine alpha_conv_refl_sort;
intros;Equiv [M = if (PPeq p p1) N (par p1)]
	     [M' = if (PPeq p p1) N' (par p1)]
	      alpha_conv M M';
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Immed;
intros neqP;Qrepl neqP;Refine alpha_conv_refl_par;

(* pi *)
intros;
Equiv alpha_conv (pi u (subN A) (subN B)) (pi v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine alpha_conv_pi;
Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine ihB;
(* lda *)
intros;
Equiv alpha_conv (lda u (subN A) (subN B)) (lda v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine alpha_conv_lda;
Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine ihB;
(* app *)
intros;
Equiv alpha_conv (app (subN A) (subN B)) (app (subN' A') (subN' B'));
Refine alpha_conv_app;Immed;

Save alpha_conv_psub;

(* are these Vclosed hypotheses really needed? NO!!! *)
Goal {N,N'|Trm}(alpha_conv N N')->
     {u,v|VV}{X,X'|Trm}({q:PP}alpha_conv (alpha q u X) (alpha q v X'))->
      alpha_conv (vsub N u X) (vsub N' v X');
intros; Refine fresh_params_lem2 X X'; intros q qFresh;
Refine qFresh; intros noccX noccX';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N u noccX));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N' v noccX'));
Refine alpha_conv_psub;Immed;
Save alpha_conv_vsub;


(* characters and other general properties *)
(* Goal {s|SS}{A|Trm}{r:alpha_conv (sort s) A}is_tt (Trm_eq A (sort s)); *)
(* intros;Refine par_red1_sort_character;Refine alpha_conv_par_red1;Immed; *)
(* Save alpha_conv_sort_character; *)

(* (* Goal {v|VV}{A|Trm}{r:alpha_conv (var v) A}is_tt (Trm_eq A (var v)); *) *)
(* (* intros;Refine par_red1_var_character;Refine alpha_conv_par_red1;Immed; *) *)
(* (* Save alpha_conv_var_character; *) *)

(* Goal {p|PP}{A|Trm}{r:alpha_conv (par p) A}is_tt (Trm_eq A (par p)); *)
(* intros;Refine par_red1_par_character;Refine alpha_conv_par_red1;Immed; *)
(* Save alpha_conv_par_character; *)


Goal {s|SS}{A|Trm}{r:alpha_conv (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine alpha_convRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save alpha_conv_sort_character;

Goal {p|PP}{A|Trm}{r:alpha_conv (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine alpha_convRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save alpha_conv_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:alpha_conv (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (alpha_conv A A')
           ({p:PP}alpha_conv (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine alpha_aconvRec [P,P':Trm]{eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (alpha_conv A A')
                   ({p:PP}alpha_conv (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine premA;
intros;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save alpha_conv_pi_character;

Goal alpha_conv_pi_pi_character:
     {u,v|VV}{A,A',B,B'|Trm}{c:alpha_conv (pi u A B) (pi v A' B')}
     and (alpha_conv A A') ({q:PP}alpha_conv (alpha q u B) (alpha q v B'));
intros;
Refine alpha_aconvRec [X,Y:Trm]
     {u_,v_|VV}{A_,A'_,B_,B'_|Trm}(is_tt (Trm_eq X (pi u_ A_ B_)))->
                                  (is_tt (Trm_eq Y (pi v_ A'_ B'_)))->
     and (alpha_conv A_ A'_)
         ({q:PP}alpha_conv (alpha q u_ B_) (alpha q v_ B'_));Immed;
(* refl *)
intros;Refine tt_not_ff (Q_sym H);
intros;Refine tt_not_ff (Q_sym H);
(* pi *)
intros;
Refine Trm_eq_pi_lem H; intros; Refine Trm_eq_pi_lem H1; intros;
Refine pair;
Qrepl Q_sym (Trm_eq_subst H3); Qrepl Q_sym (Trm_eq_subst H6);Assumption;
Qrepl Q_sym (Trm_eq_subst H4); Qrepl Q_sym (Trm_eq_subst H7);
Qrepl Q_sym (VVdecide H2); Qrepl Q_sym (VVdecide H5);Assumption;
(* lda *)
intros; Refine tt_not_ff (Q_sym H);
(* app *)
intros; Refine tt_not_ff (Q_sym H);
(* bookkeeping *)
Refine Trm_eq_refl; Refine Trm_eq_refl;
Save;

Goal {w|VV}{A,B,X|Trm}{red_lda:alpha_conv (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (alpha_conv A A')
           ({p:PP}alpha_conv (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine alpha_aconvRec [L,L':Trm]
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (alpha_conv A A')
                   ({p:PP}alpha_conv (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine premA;
intros;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save alpha_conv_lda_character;

Goal {M,N,X|Trm}{red_app:alpha_conv (app M N) X}
      Ex2 [M',N':Trm]
          and3 (alpha_conv M M')
               (alpha_conv N N')
               (is_tt (Trm_eq (app M' N') X));

intros;Refine alpha_convRec [X,X':Trm]
              {eq:is_tt (Trm_eq (app M N) X)}
               Ex2 [M',N':Trm]
                   and3 (alpha_conv M M')
                        (alpha_conv N N')
                        (is_tt (Trm_eq (app M' N') X'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex2In A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Immed;
Save alpha_conv_app_character;

Goal alpha_conv_sym : sym alpha_conv;
Refine alpha_convRec [A,B:Trm]alpha_conv B A;
intros;Refine alpha_conv_refl_sort;
intros;Refine alpha_conv_refl_par;
intros;Refine alpha_conv_pi;Immed;
intros;Refine alpha_conv_lda;Immed;
intros;Refine alpha_conv_app;Immed;
Save;

%\VerbFileRecord alpha_conv_properties_verb
Goal alpha_conv_trans : trans alpha_conv;
%\VerbFileClos alpha_conv_properties_verb
Expand trans;intros;
Refine alpha_aconvRec [A,B:Trm]
         {C|Trm}{al:alpha_conv B C}alpha_conv A C;Immed;
(* refl *)
intros;Immed;
intros;Immed;
(* pi *)
intros;Refine alpha_conv_pi_character al;
intros w A'' B'' hyp;Refine hyp;
intros convA convB eq;Qrepl Q_sym (Trm_eq_subst eq);
Refine fresh_params_lem3 B B' B'';
intros q qFresh;Refine qFresh;
intros noccB noccB' noccB'';Refine alpha_conv_pi;
Refine ihA;Refine +4 ihB;Immed;
(* lda *)
intros;Refine alpha_conv_lda_character al;
intros w A'' B'' hyp;Refine hyp;
intros convA convB eq;Qrepl Q_sym (Trm_eq_subst eq);
Refine fresh_params_lem3 B B' B'';
intros q qFresh;Refine qFresh;
intros noccB noccB' noccB'';Refine alpha_conv_lda;
Refine ihA;Refine +4 ihB;Immed;
(* app *)
intros;Refine alpha_conv_app_character al;
intros A'' B'' hyp;Refine hyp;
intros convA convB eq;Qrepl Q_sym (Trm_eq_subst eq);
Refine alpha_conv_app;Refine ihA;Refine +1 ihB;Immed;
Save;

(********   some new stuff, very useful  ************)
(********   James, put it where you want it  *********)
Goal {X,Y|Trm}(alpha_conv X Y)->{s|SS}(is_tt (soccur s Y))->is_tt (soccur s X);
Refine alpha_convRec [A,B:Trm]
                    {s|SS}{occ:is_tt (soccur s B)}is_tt (soccur s A);
intros;Immed;
intros;Immed;

intros;Refine socc_compound_lem occ;
intros occA;Refine socc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine socc_split_lem;Refine inr;
            Refine socc_vsub_lem2 (ihB ?);
            Refine +1 socc_vsub_lem occB;
            intros abs;Refine tt_not_ff (Q_sym abs);
            intros;Immed;

intros;Refine socc_compound_lem occ;
intros occA;Refine socc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine socc_split_lem;Refine inr;
            Refine socc_vsub_lem2 (ihB ?);
            Refine +1 socc_vsub_lem occB;
            intros abs;Refine tt_not_ff (Q_sym abs);
            intros;Immed;

intros;Refine socc_compound_lem occ;
intros occA;Refine socc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine socc_split_lem;Refine inr;Refine ihB;Immed;

Save alpha_conv_refl_socc;

Goal {X|Trm}{s|SS}(alpha_conv X (sort s))->is_tt (soccur s X);
intros;Refine alpha_conv_refl_socc;Immed;
Qrepl socc_sort_lem s s;Refine SSrefl;
Save alpha_conv_sort_socc_lem;

(* alpha_conversion is decidable *)
%\VerbFileOpen decide_alpha_conv
Goal decide_alpha_conv:
     {A,B|Trm}(Vclosed A)->(Vclosed B)->decidable (alpha_conv A B);
%\VerbFileClos decide_alpha_conv
intros;
Claim {A|Trm}(aVclosed A)->{B|Trm}(aVclosed B)->
     or (alpha_conv A B) (not (alpha_conv A B));
Refine ?+1; Refine Vclosed_aVclosed; Refine +1 Vclosed_aVclosed; Immed;
Refine aVclosed_double_elim ([A:Trm][_:aVclosed A][B:Trm][_:aVclosed B]
     or (alpha_conv A B) (not (alpha_conv A B)));
(* sort-sort *)
intros; Refine tt_or_ff (SSeq s s');
intros eqss'; Refine inl; Qrepl SSdecide eqss'; Refine alpha_conv_refl_sort;
intros neqss'; Refine inr; Intros acss';
  Refine B_contradiction (alpha_conv_sort_character (alpha_conv_sym acss'));
  Immed;
(* par-sort *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_sort_character acps));
(* pi-sort *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_sort_character acps));
(* lda-sort *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_sort_character acps));
(* app-sort *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_sort_character acps));
(* sort-par *)
intros; Refine inr; Intros acsp;
Refine tt_not_ff (Q_sym (alpha_conv_par_character acsp));
(* par-par *)
intros; Refine tt_or_ff (PPeq p2' p2);
intros eqpp; Refine inl; Qrepl PPdecide eqpp; Refine alpha_conv_refl_par;
intros neqpp; Refine inr; Intros acpp; 
Refine B_contradiction (alpha_conv_par_character acpp);Immed;
(* pi-par *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_par_character acps));
(* lda-par *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_par_character acps));
(* app-par *)
intros; Refine inr; Intros acps;
Refine tt_not_ff (Q_sym (alpha_conv_par_character acps));
(* sort-pi *)
intros; Refine inr; Intros acps;
Refine alpha_conv_pi_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* par-pi *)
intros; Refine inr; Intros acps;
Refine alpha_conv_pi_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* pi-pi *)
intros; Refine premA2_ih premA2';
intros +1 nacA'A; Refine inr; Refine contrapos ? nacA'A; intros acpipi;
  Refine alpha_conv_pi_character acpipi; intros u C D hyp;
  Refine hyp; intros; Refine Trm_eq_pi_lem H4; intros;
  Qrepl Q_sym (Trm_eq_subst H6); Immed;
intros acA'A; Refine fresh_params_lem2 B2' B2; intros q qh;
  Refine qh; intros;  Refine premB2_ih q (premB2' q);
  intros +1 nacB'B; Refine inr; Refine contrapos ? nacB'B; intros acpipi;
    Refine alpha_conv_pi_character acpipi; intros u C D hyp;
    Refine hyp; intros; Refine Trm_eq_pi_lem H6; intros;
    Qrepl Q_sym (Trm_eq_subst H9); Qrepl Q_sym (VVdecide H7); Immed;
  intros acB'B; Refine inl; Refine alpha_conv_pi; Immed;
(* lda-pi *)
intros; Refine inr; Intros acps;
Refine alpha_conv_pi_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* app-pi *)
intros; Refine inr; Intros acps;
Refine alpha_conv_pi_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* sort-lda *)
intros; Refine inr; Intros acps;
Refine alpha_conv_lda_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* par-lda *)
intros; Refine inr; Intros acps;
Refine alpha_conv_lda_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* pi-lda *)
intros; Refine inr; Intros acps;
Refine alpha_conv_lda_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* lda-lda *)
intros; Refine premA1_ih premA1';
intros +1 nacA'A; Refine inr; Refine contrapos ? nacA'A; intros acldalda;
  Refine alpha_conv_lda_character acldalda; intros u C D hyp;
  Refine hyp; intros; Refine Trm_eq_lda_lem H4; intros;
  Qrepl Q_sym (Trm_eq_subst H6); Immed;
intros acA'A; Refine fresh_params_lem2 B1' B1; intros q qh;
  Refine qh; intros;  Refine premB1_ih q (premB1' q);
  intros +1 nacB'B; Refine inr; Refine contrapos ? nacB'B; intros acldalda;
    Refine alpha_conv_lda_character acldalda; intros u C D hyp;
    Refine hyp; intros; Refine Trm_eq_lda_lem H6; intros;
    Qrepl Q_sym (Trm_eq_subst H9); Qrepl Q_sym (VVdecide H7); Immed;
  intros acB'B; Refine inl; Refine alpha_conv_lda; Immed;
(* app-lda *)
intros; Refine inr; Intros acps;
Refine alpha_conv_lda_character acps; intros u C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* sort-app *)
intros; Refine inr; Intros acps;
Refine alpha_conv_app_character acps; intros C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* par-app *)
intros; Refine inr; Intros acps;
Refine alpha_conv_app_character acps; intros C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* pi-app *)
intros; Refine inr; Intros acps;
Refine alpha_conv_app_character acps; intros C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* lda-app *)
intros; Refine inr; Intros acps;
Refine alpha_conv_app_character acps; intros C D hyp;
  Refine hyp; intros; Refine tt_not_ff (Q_sym H4);
(* app-app *)
intros; Refine premA_ih premA';
intros +1 nacA'A; Refine inr; Refine contrapos ? nacA'A; intros acappapp;
  Refine alpha_conv_app_character acappapp; intros C D hyp;
  Refine hyp; intros; Refine Trm_eq_app_lem H4; intros;
  Qrepl Q_sym (Trm_eq_subst H5); Immed;
intros acA'A; Refine premB_ih premB';
  intros +1 nacB'B; Refine inr; Refine contrapos ? nacB'B; intros acappapp;
    Refine alpha_conv_app_character acappapp; intros C D hyp;
    Refine hyp; intros; Refine Trm_eq_app_lem H4; intros;
    Qrepl Q_sym (Trm_eq_subst H6); Immed;
  intros acB'B; Refine inl; Refine alpha_conv_app; Immed;
Save;

(* an illustration of the property: uniqueness of developments *)
Goal comp_dev_unique: 
     {M,M'|Trm}(comp_dev M M')-> 
     {M''|Trm}(comp_dev M M'')->alpha_conv M' M'';
intros;
Refine comp_devRec [M,M'|Trm]
                   {M''|Trm}{cd:comp_dev M M''}alpha_conv M' M'';
Immed;
(* sort *)
intros;Qrepl Trm_eq_subst (comp_dev_sort_character cd);
Refine alpha_conv_refl_sort;
(* par *)
intros;Qrepl Trm_eq_subst (comp_dev_par_character cd);
Refine alpha_conv_refl_par;
(* beta *)
intros;Refine comp_dev_app_character cd;
intros case_app;Refine case_app;
intros A'' B'' hyp;Refine hyp;
intros sc';Refine tt_not_ff sc';
intros case_beta;Refine case_beta;
intros u' v' U' B1 B'' A'' hyp;Refine hyp;
intros cdB1 cdA vclU eq1 eq2;Refine Trm_eq_lda_lem eq1;
intros eqV eqA eqB;Qrepl Q_sym (Trm_eq_subst eq2);
[cdB : {p:PP}comp_dev (alpha p u B) (alpha p v' B'')
     = Q_subst (VVdecide eqV)
               ([u:VV]{p:PP}comp_dev (alpha p u ?) (alpha p ? ?))
               (Q_subst (Trm_eq_subst eqB)
                        ([B:Trm]{p:PP}comp_dev (alpha p ? B) (alpha p ? ?))
                          cdB1)];
[noccB'' : is_ff (poccur p B'')
         = not_pocc_resp_comp_dev_alpha cdB noccB];
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A'' v' noccB''));
Refine alpha_conv_psub;
Refine ihA;Immed;
Refine ihB;Immed;
(* pi *)
intros;Refine comp_dev_pi_character cd;
intros w A'' B'' hyp;Refine hyp;
intros cdA cdB eq;Qrepl Q_sym (Trm_eq_subst eq);
[noccB'' : is_ff (poccur p B'')
         = not_pocc_resp_comp_dev_alpha cdB noccB];
Refine alpha_conv_pi;
Refine ihA; Immed; 
Refine ihB; Immed;
(* lda *)
intros;Refine comp_dev_lda_character cd;
intros w A'' B'' hyp;Refine hyp;
intros cdA cdB eq;Qrepl Q_sym (Trm_eq_subst eq);
[noccB'' : is_ff (poccur p B'')
         = not_pocc_resp_comp_dev_alpha cdB noccB];
Refine alpha_conv_lda;
Refine ihA; Immed; 
Refine ihB; Immed;
(* app *)
intros;Refine comp_dev_app_character cd;
intros case_app;Refine case_app;
intros A'' B'' hyp;Refine hyp;
intros sc' cdA cdB eq;Qrepl Q_sym (Trm_eq_subst eq);
Refine alpha_conv_app;
Refine ihA;Immed;
Refine ihB;Immed;
intros case_beta;Refine case_beta;
intros u v U X X' Y hyp;Refine B_contradiction;Immed;
Qrepl Q_sym (Trm_eq_subst (and5_out4 hyp));Refine Q_refl;
Save comp_dev_unique;

Goal comp_dev_ex_uni: 
     {M,M'|Trm}(alpha_conv M M')-> 
	Ex [M'':Trm]and (comp_dev M M'') (comp_dev M' M'');

intros;Refine alpha_convRec [M,M'|Trm]
	Ex [M'':Trm]and (comp_dev M M'') (comp_dev M' M'');Immed;
intros;Refine ExIn (* sort s *);Refine +1 pair;
	Refine +1 comp_dev_sort;Refine comp_dev_sort;  
intros;Refine ExIn (* par p *);Refine +1 pair;
	Refine +1 comp_dev_par; Refine comp_dev_par;

intros;Refine ihA;
intros A'' hypA;Refine hypA;
intros cdA cdA';Refine ihB;
intros B0;Refine shape_lemma p B0;
intros w B'' shapeB;Refine shapeB;
intros eqB noccB'';Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros cdB cdB';Refine ExIn (* pi w A'' B'' *);Refine +1 pair;
	Refine +1 comp_dev_pi;Refine +8 comp_dev_pi;Immed;
    
intros;Refine ihA;
intros A'' hypA;Refine hypA;
intros cdA cdA';Refine ihB;
intros B0;Refine shape_lemma p B0;
intros w B'' shapeB;Refine shapeB;
intros eqB noccB'';Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros cdB cdB';Refine ExIn (* lda w A'' B'' *);Refine +1 pair;
	Refine +1 comp_dev_lda;Refine +8 comp_dev_lda;Immed;
    
intros;Refine ihB;
intros B'' hypB;Refine hypB;
intros cdB cdB';Refine tt_or_ff (isLda A);

intros case_beta;Refine isLda_lem case_beta;
[case_beta' : is_tt (isLda A') = (Q_subst (alpha_conv_shape_lda premA)) is_tt case_beta];
intros u U X eqA;Refine isLda_lem case_beta';
intros u' U' X' eqA';Refine ihA;
Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqA';
intros L hypL;Refine hypL;
intros cdL cdL';Refine comp_dev_lda_character cdL;
intros v V Y hypL1;Refine hypL1; 
intros cdU cdX eqL1;Refine comp_dev_lda_character cdL';
intros v' V' Y';Qrepl Q_sym (Trm_eq_subst eqL1);
intros hypL2;Refine hypL2; 
intros cdU' cdX' eqL2;Refine Trm_eq_lda_lem eqL2;
intros eqv eqV eqY;Refine fresh_params_lem2 X X';
intros q qFresh;Refine qFresh;
intros noccX noccX';Refine ExIn (* vsub B'' v' Y' *);Refine +1 pair;
(**** do this step in future with Qnify ****)
Refine +1 comp_dev_beta (fst (comp_dev_Vclosed cdU)) cdB;
Refine +6 comp_dev_beta (fst (comp_dev_Vclosed cdU')) cdB';
Refine +8 ?+4;Refine +4 not_pocc_resp_comp_dev_alpha;Immed;
Qrepl VVdecide eqv;Qrepl Trm_eq_subst eqY;Immed;
(*******)

intros case_app;Refine ihA;
intros A'' hypA;Refine hypA;
intros cdA cdA';Refine ExIn (* app A'' B'' *);Refine +1 pair;
	Refine +1 comp_dev_app;Refine +5 comp_dev_app;Immed;
	Qrepl Q_sym (alpha_conv_shape_lda premA);Immed;
Save;
