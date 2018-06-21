Module par_red1
Import shape_lemma
       Vclosed
       renaming;

(* first, the parallel one-step reduction relation a la Tait, Martin-Lof *)

(******************************************************)

Inductive [par_red1 : Trm->Trm->Prop] 

(*Relation*)

Constructors 
[par_red1_refl_sort : {s:SS} par_red1 (sort s) (sort s)]
[par_red1_refl_par : {p:PP} par_red1 (par p) (par p)]

[par_red1_beta:{U|Trm}{vclU:Vclosed U}{A,A'|Trm}{premA:par_red1 A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:par_red1 (alpha p u B) (alpha p v B')}
                par_red1 (app (lda u U B) A) (vsub A' v B')]

[par_red1_pi:{A,A'|Trm}{premA:par_red1 A A'} 
              {u,v|VV}{B,B'|Trm}{p|PP} 
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
              {premB:par_red1 (alpha p u B) (alpha p v B')} 
               par_red1 (pi u A B) (pi v A' B')]

[par_red1_lda:{A,A'|Trm}{premA:par_red1 A A'} 
               {u,v|VV}{B,B'|Trm}{p|PP} 
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
               {premB:par_red1 (alpha p u B) (alpha p v B')} 
                par_red1 (lda u A B) (lda v A' B')]

[par_red1_app:{A,A'|Trm}{premA:par_red1 A A'} 
                {B,B'|Trm}{premB:par_red1 B B'} 
                 par_red1 (app A B) (app A' B')];

(* introduce the non-dependent form - we could *)
(* do this with Relation, but we won't *)

Goal par_red1Rec : {C:{A,B:Trm}Prop} 

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {BETA:{U|Trm}{vclU:Vclosed U}
		   {A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'}
                   {u,v|VV}{B,B'|Trm}{p|PP}
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                   {premB:par_red1 (alpha p u B) (alpha p v B')}
	           {ihB:C (alpha p u B) (alpha p v B')} 
 	            C (app (lda u U B) A) (vsub A' v B')}

	     {PI:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm}{p|PP} 
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                  {premB:par_red1 (alpha p u B) (alpha p v B')}
 	          {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm}{p|PP} 
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                   {premB:par_red1 (alpha p u B) (alpha p v B')}
		   {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:par_red1 B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(par_red1 A B) -> C A B;

intros;Refine par_red1_elim [A,B|Trm][_:par_red1 A B]C A B;Immed;
intros;Refine BETA;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;

Goal {A,B|Trm}(par_red1 A B)-> and (Vclosed A) (Vclosed B);
Refine par_red1Rec [A,B:Trm]and (Vclosed A) (Vclosed B);
intros;Refine pair;Refine ?+1;Refine Vclosed_sort;
intros;Refine pair;Refine ?+1;Refine Vclosed_par;
intros;Refine ihA;
	intros vclA vclA';Refine ihB;
	intros vclB vclB';
	Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
	Refine pair;Refine Vclosed_app;Refine Vclosed_lda;
	Refine +4 psub_resp_Vclosed;Immed;
intros;Refine ihA;
	intros vclA vclA';Refine ihB;
	intros vclB vclB';Refine pair;
	Refine Vclosed_pi;Refine +3 Vclosed_pi;Immed;
intros;Refine ihA;
	intros vclA vclA';Refine ihB;
	intros vclB vclB';Refine pair;
	Refine Vclosed_lda;Refine +3 Vclosed_lda;Immed;
intros;Refine ihA;
	intros vclA vclA';Refine ihB;
	intros vclB vclB';Refine pair;
	Refine Vclosed_app;Refine +2 Vclosed_app;Immed;
Save par_red1_Vclosed;

Goal par_red1_refl : {A|Trm}(Vclosed A)->par_red1 A A;
intros;Refine aVclosedRec [A|Trm][_:aVclosed A]par_red1 A A;
intros;Refine par_red1_refl_sort;
intros;Refine par_red1_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine par_red1_pi;Immed;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine par_red1_lda;Immed;
intros;Refine par_red1_app;Immed;
Refine Vclosed_aVclosed;Immed;
Save;

Inductive [par_ared1 : Trm->Trm->Prop] 

(*Relation*)

Constructors 
[par_ared1_refl_sort : {s:SS} par_ared1 (sort s) (sort s)]
[par_ared1_refl_par : {p:PP} par_ared1 (par p) (par p)]

[par_ared1_beta:{U|Trm}{vclU:Vclosed U}{A,A'|Trm}{premA:par_ared1 A A'}
                {u,v|VV}{B,B'|Trm}
                {premB:{p:PP}par_ared1 (alpha p u B) (alpha p v B')}
                 par_ared1 (app (lda u U B) A) (vsub A' v B')]

[par_ared1_pi:{A,A'|Trm}{premA:par_ared1 A A'} 
              {u,v|VV}{B,B'|Trm} 
              {premB:{p:PP}par_ared1 (alpha p u B) (alpha p v B')} 
               par_ared1 (pi u A B) (pi v A' B')]

[par_ared1_lda:{A,A'|Trm}{premA:par_ared1 A A'} 
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}par_ared1 (alpha p u B) (alpha p v B')} 
                par_ared1 (lda u A B) (lda v A' B')]

[par_ared1_app:{A,A'|Trm}{premA:par_ared1 A A'} 
                {B,B'|Trm}{premB:par_ared1 B B'} 
                 par_ared1 (app A B) (app A' B')]

NoReductions;


Goal {A,B|Trm}(par_ared1 A B)->par_red1 A B;
Refine par_ared1_elim [A,B:Trm][_:par_ared1 A B]par_red1 A B;
intros;Refine par_red1_refl_sort;
intros;Refine par_red1_refl_par;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_red1_beta;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_red1_pi;Refine +4 premB_ih;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_red1_lda;Refine +4 premB_ih;Immed;
intros;Refine par_red1_app;Immed;
Save par_ared1_red1;

Goal {A,B|Trm}(par_red1 A B)->{rho:Renaming}par_ared1 (renTrm rho A) (renTrm rho B);
Refine par_red1Rec [A,B:Trm]
                   {rho:Renaming}par_ared1 (renTrm rho A) (renTrm rho B);
intros;Refine par_ared1_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine par_ared1_refl_par;

intros;Equiv par_ared1 (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine par_ared1_beta;Refine renTrm_resp_Vclosed;Immed;
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
Equiv par_ared1 (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine par_ared1_pi;Immed;
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
Equiv par_ared1 (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine par_ared1_lda;Immed;
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
Equiv par_ared1 (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine par_ared1_app;Immed;

Save par_red1_ared1_lem;

Goal {A,B|Trm}(par_red1 A B)->par_ared1 A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine par_red1_ared1_lem H renId;
Save par_red1_ared1;

Goal {A,B|Trm}(par_red1 A B)->{rho:Renaming}par_red1 (renTrm rho A) (renTrm rho B);
intros;Refine par_ared1_red1;Refine par_red1_ared1_lem;Immed;
Save renTrm_resp_par_red1;

(* introduce the non-dependent form - but this time, we don't appear *)
(* to be able to do this with Relation, because this really is a *)
(* complex derived notion *)

Goal par_ared1Rec : {C:{A,B:Trm}Prop} 

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {BETA:{U|Trm}{vclU:Vclosed U}
		   {A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
	           {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	            C (app (lda u U B) A) (vsub A' v B')}

	     {PI:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm} 
                  {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
 	          {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm} 
                   {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
		   {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:par_red1 A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:par_red1 B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(par_red1 A B) -> C A B;

intros;Refine par_ared1_elim[A,B|Trm][_:par_ared1 A B]C A B;Immed;
intros;Refine BETA;Immed;
       Refine par_ared1_red1 premA;Refine [p:PP]par_ared1_red1 (premB p);
intros;Refine PI;Immed;
       Refine par_ared1_red1 premA;Refine [p:PP]par_ared1_red1 (premB p);
intros;Refine LDA;Immed;
       Refine par_ared1_red1 premA;Refine [p:PP]par_ared1_red1 (premB p);
intros;Refine APP;Immed;
       Refine par_ared1_red1 premA;Refine par_ared1_red1 premB;
Refine par_red1_ared1;Immed;
Save;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(par_red1 X Y)->par_red1 (psub N p X) (psub N p Y);
intros ___;
Refine par_ared1Rec [A,B:Trm]par_red1 (psub N p A) (psub N p B);

intros;Refine par_red1_refl_sort;

intros;Equiv [M = if (PPeq p p1) N (par p1)]par_red1 M M;
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Refine par_red1_refl;Immed;
intros neqP;Qrepl neqP;Refine par_red1_refl_par;

intros;
Equiv par_red1 (app (lda u (psub N p U) (psub N p B)) (psub N p A)) ?;
Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A' v B');
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine par_red1_beta;Refine psub_resp_Vclosed;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv par_red1 (pi u (psub N p A) (psub N p B))
               (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine par_red1_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv par_red1 (lda u (psub N p A) (psub N p B))
               (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine par_red1_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv par_red1 (app (psub N p A) (psub N p B))
               (app (psub N p A') (psub N p B'));
Refine par_red1_app;Immed;

Save psub_resp_par_red1;

Goal {X,Y|Trm}(par_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);

Refine par_ared1Rec [A,B:Trm]
                    {p|PP}{occ:is_tt (poccur p B)}is_tt (poccur p A);
intros;Immed;
intros;Immed;
intros;Refine pocc_vsub_lem2 occ;
intros occA;Refine pocc_split_lem;Refine inr;Refine ihA;Immed;
intros occB;Refine pocc_split_lem;Refine inl;
            Refine pocc_split_lem;Refine inr;
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

Save par_red1_refl_pocc;

Goal {X,Y|Trm}(par_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_red1_refl_pocc;Immed;
Save not_pocc_resp_par_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occ:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (par_red1_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;
Save par_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_par_red1_alpha;


Goal {N,N'|Trm}{par_redN:par_red1 N N'}{p:PP} 
      {M|Trm}(Vclosed M)->par_red1 (psub N p M) (psub N' p M); 
 intros ______; 
 [vclN  = fst (par_red1_Vclosed par_redN): Vclosed N]; 
 [vclN' = snd (par_red1_Vclosed par_redN): Vclosed N']; 
 [subN = psub N p][subN' = psub N' p]; 

Refine aVclosedRec [A:Trm][_:aVclosed A]par_red1 (subN A) (subN' A); 
 intros;Refine par_red1_refl_sort; 

intros;Equiv [M = if (PPeq p p1) N (par p1)] 
 	     [M' = if (PPeq p p1) N' (par p1)] 
 	      par_red1 M M'; 
 Refine tt_or_ff (PPeq p p1); 
 intros eqP;Qrepl eqP;Immed; 
 intros neqP;Qrepl neqP;Refine par_red1_refl_par; 

intros;Equiv par_red1 (pi n (subN A) (subN B)) (pi n (subN' A) (subN' B)); 
 Refine fresh_params_lem2p p N B; 
 intros q qFresh;Refine qFresh; 
 intros neqP noccN noccB;Refine par_red1_pi;Refine ihA; 
 Refine +1 not_pocc_psub_lem noccB noccN; 
 Refine not_pocc_psub_lem noccB (not_pocc_resp_par_red1 par_redN noccN); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP n B); 
 Immed; 

intros;Equiv par_red1 (lda n (subN A) (subN B)) (lda n (subN' A) (subN' B)); 
 Refine fresh_params_lem2p p N B; 
 intros q qFresh;Refine qFresh; 
 intros neqP noccN noccB;Refine par_red1_lda;Refine ihA; 
 Refine +1 not_pocc_psub_lem noccB noccN; 
 Refine not_pocc_psub_lem noccB (not_pocc_resp_par_red1 par_redN noccN); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); 
 Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP n B); 
 Immed; 

intros;Equiv par_red1 (app (subN A) (subN B)) (app (subN' A) (subN' B)); 
 Refine par_red1_app;Immed; 

Refine Vclosed_aVclosed;Immed; 
 Save par_red1_refl_psub_lem; 

Goal {N,N'|Trm}{par_redN:par_red1 N N'}{p:PP}
     {X,X'|Trm}(par_red1 X X')->par_red1 (psub N p X) (psub N' p X');
intros ____;
[vclN  = fst (par_red1_Vclosed par_redN): Vclosed N];
[vclN' = snd (par_red1_Vclosed par_redN): Vclosed N'];
[subN = psub N p][subN' = psub N' p];

Refine par_ared1Rec [M,M'|Trm]par_red1 (subN M) (subN' M');

(* refl *)
intros;Refine par_red1_refl_sort;
intros;Equiv [M = if (PPeq p p1) N (par p1)]
	     [M' = if (PPeq p p1) N' (par p1)]
	      par_red1 M M';
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Immed;
intros neqP;Qrepl neqP;Refine par_red1_refl_par;

(* beta *)
intros;Equiv par_red1 (app (lda u (subN U) (subN B)) (subN A)) ?;
Qrepl Trm_eq_subst (psub_vsub_commutes vclN' p A' v B');
Refine fresh_params_lem4p p N N' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';
Refine par_red1_beta;Refine psub_resp_Vclosed;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine ihB;

(* pi *)
intros;
Equiv par_red1 (pi u (subN A) (subN B)) (pi v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_red1_pi;
Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine ihB;
(* lda *)
intros;
Equiv par_red1 (lda u (subN A) (subN B)) (lda v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_red1_lda;
Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine ihB;
(* app *)
intros;
Equiv par_red1 (app (subN A) (subN B)) (app (subN' A') (subN' B'));
Refine par_red1_app;Immed;
Save par_red1_psub;

(* now the characters, for the Church-Rosser theorem *)
Goal {p|PP}{A|Trm}{r:par_red1 (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine par_red1Rec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save par_red1_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:par_red1 (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A A')
           ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine par_ared1Rec [P,P':Trm]{eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_red1 A A')
                   ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Refine tt_not_ff (Q_sym eq);
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
Save par_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:par_red1 (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A A')
           ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine par_ared1Rec [L,L':Trm]
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_red1 A A')
                   ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Refine tt_not_ff (Q_sym eq);
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
Save par_red1_lda_character;


Goal {M,N,X|Trm}{red_app:par_red1 (app M N) X}
      or (Ex2 [M',N':Trm]
          and3 (par_red1 M M')
               (par_red1 N N')
               (is_tt (Trm_eq (app M' N') X)))
         (Ex6 [u,v:VV][U,B,B',A':Trm]
          and5 ({p:PP}par_red1 (alpha p u B) (alpha p v B'))
               (par_red1 N A') (Vclosed U)
               (is_tt (Trm_eq (lda u U B) M))
               (is_tt (Trm_eq (vsub A' v B') X)));

intros;Refine par_ared1Rec [X,X':Trm]
              {eq:is_tt (Trm_eq (app M N) X)}
               or (Ex2 [M',N':Trm]
                   and3 (par_red1 M M')
                        (par_red1 N N')
                        (is_tt (Trm_eq (app M' N') X')))
                  (Ex6 [u,v:VV][U,B,B',A':Trm]
                   and5 ({p:PP}par_red1 (alpha p u B) (alpha p v B'))
                        (par_red1 N A') (Vclosed U)
                        (is_tt (Trm_eq (lda u U B) M))
                        (is_tt (Trm_eq (vsub A' v B') X')));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inr;Refine Trm_eq_app_lem eq;
intros eqM eqN;
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair5;Immed;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inl;Refine Trm_eq_app_lem eq;
intros eqM eqN;
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Immed;
Save par_red1_app_character;
