Module no_red
Import par_redn;

(* the non-overlapping one-step beta reduction relation *)

Inductive [no_red1 : Trm->Trm->Prop] NoReductions Constructors

[no_red1_refl_sort : {s:SS} no_red1 (sort s) (sort s)]
[no_red1_refl_par : {p:PP} no_red1 (par p) (par p)]

%\VerbFileOpen no_red1_beta
[no_red1_beta: {u|VV}{U,A,B|Trm}{vcl_redex:Vclosed (app (lda u U B) A)} 
		no_red1 (app (lda u U B) A) (vsub A u B)]
%\VerbFileClos no_red1_beta

[no_red1_pi:{A,A'|Trm}{u,v|VV}{B,B'|Trm}
            {premA:no_red1 A A'}
            {p|PP}{noccB:is_ff (poccur p B)}
            {noccB':is_ff (poccur p B')}
            {premB:no_red1 (alpha p u B) (alpha p v B')}
             no_red1 (pi u A B) (pi v A' B')]

[no_red1_lda:{A,A'|Trm}{u,v|VV}{B,B'|Trm}
             {premA:no_red1 A A'}
             {p|PP}{noccB:is_ff (poccur p B)}
             {noccB':is_ff (poccur p B')}
             {premB:no_red1 (alpha p u B) (alpha p v B')}
              no_red1 (lda u A B) (lda v A' B')]

[no_red1_app:{A,A'|Trm}{B,B'|Trm}
             {premA:no_red1 A A'}
             {premB:no_red1 B B'}
              no_red1 (app A B) (app A' B')];

Goal no_red1Rec : {C:{A,B:Trm}Prop}

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {BETA:{u|VV}{U,A,B|Trm}{vcl_redex:Vclosed (app (lda u U B) A)} 
 	            C (app (lda u U B) A) (vsub A u B)}

	     {PI:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm}{p|PP} 
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                  {premB:no_red1 (alpha p u B) (alpha p v B')}
 	          {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm}{p|PP} 
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')} 
                   {premB:no_red1 (alpha p u B) (alpha p v B')}
		   {ihB:C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:no_red1 B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(no_red1 A B) -> C A B;

intros;Refine no_red1_elim [A,B|Trm][_:no_red1 A B]C A B;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;

Goal no_red1_refl : {A|Trm}(Vclosed A)->no_red1 A A;
intros;Refine aVclosedRec [A|Trm][_:aVclosed A]no_red1 A A;
intros;Refine no_red1_refl_sort;
intros;Refine no_red1_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine no_red1_pi;Immed;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine no_red1_lda;Immed;
intros;Refine no_red1_app;Immed;
Refine Vclosed_aVclosed;Immed;
Save;


%\VerbFileOpen no_par_red1
Goal no_par_red1: {A,B|Trm}(no_red1 A B)->par_red1 A B;
%\VerbFileClos no_par_red1
Refine no_red1Rec [A,B:Trm]par_red1 A B;
intros;Refine par_red1_refl_sort;
intros;Refine par_red1_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine Vclosed_app_lem vcl_redex;
	intros vclL vclA;Refine Vclosed_lda_lem vclL;
	intros vclU vclB;Refine par_red1_beta;Immed;
	Refine par_red1_refl;Refine +1 par_red1_refl;Immed;
intros;Refine par_red1_pi;Immed;
intros;Refine par_red1_lda;Immed;
intros;Refine par_red1_app;Immed;
Save no_par_red1;

Goal {A,B|Trm}(no_red1 A B)-> and (Vclosed A) (Vclosed B);
intros;Refine par_red1_Vclosed;Refine no_par_red1;Immed;
Save no_red1_Vclosed;

Inductive [no_ared1 : Trm->Trm->Prop] Constructors

[no_ared1_refl_sort : {s:SS} no_ared1 (sort s) (sort s)]
[no_ared1_refl_par : {p:PP} no_ared1 (par p) (par p)]

[no_ared1_beta: {u|VV}{U,A,B|Trm}{vcl_redex:Vclosed (app (lda u U B) A)} 
		no_ared1 (app (lda u U B) A) (vsub A u B)]

[no_ared1_pi:{A,A'|Trm}{premA:no_ared1 A A'}
             {u,v|VV}{B,B'|Trm}
             {premB:{p:PP}no_ared1 (alpha p u B) (alpha p v B')}
              no_ared1 (pi u A B) (pi v A' B')]

[no_ared1_lda:{A,A'|Trm}{premA:no_ared1 A A'}
              {u,v|VV}{B,B'|Trm}
              {premB:{p:PP}no_ared1 (alpha p u B) (alpha p v B')}
               no_ared1 (lda u A B) (lda v A' B')]

[no_ared1_app:{A,A'|Trm}{premA:no_ared1 A A'}
              {B,B'|Trm}{premB:no_ared1 B B'}
               no_ared1 (app A B) (app A' B')]
NoReductions;

Goal {A,B|Trm}(no_ared1 A B)->no_red1 A B;
Refine no_ared1_elim [A,B:Trm][_:no_ared1 A B]no_red1 A B;
intros;Refine no_red1_refl_sort;
intros;Refine no_red1_refl_par;
intros;Refine no_red1_beta;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine no_red1_pi;Refine +4 premB_ih;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine no_red1_lda;Refine +4 premB_ih;Immed;
intros;Refine no_red1_app;Immed;
Save no_ared1_red1;

Goal {A,B|Trm}(no_red1 A B)->
     {rho:Renaming}no_ared1 (renTrm rho A) (renTrm rho B);
Refine no_red1Rec [A,B:Trm]
     {rho:Renaming}no_ared1 (renTrm rho A) (renTrm rho B);
intros;Refine no_ared1_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine no_ared1_refl_par;

intros;
Equiv no_ared1 (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A u B);Refine no_ared1_beta;
Equiv Vclosed (renTrm rho (app (lda ? ? ?) ?));
Refine renTrm_resp_Vclosed;Immed;

intros;
Equiv no_ared1 (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine no_ared1_pi;Immed;
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
Equiv no_ared1 (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine no_ared1_lda;Immed;
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
Equiv no_ared1 (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine no_ared1_app;Immed;

Save no_red1_ared1_lem;

Goal {A,B|Trm}(no_red1 A B)->no_ared1 A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine no_red1_ared1_lem H renId;
Save no_red1_ared1;

Goal {A,B|Trm}(no_red1 A B)->
     {rho:Renaming}no_red1 (renTrm rho A) (renTrm rho B);
intros;Refine no_ared1_red1;Refine no_red1_ared1_lem;Immed;
Save renTrm_resp_no_red1;

(* introduce the non-dependent form - but this time, we don't appear *)
(* to be able to do this with Relation, because this really is a *)
(* complex derived notion *)

Goal no_ared1Rec : {C:{A,B:Trm}Prop} 

 	     {REFL_SORT:{s:SS}C (sort s) (sort s)} 

 	     {REFL_PAR:{p:PP}C (par p) (par p)} 

 	     {BETA:{u|VV}{U,A,B|Trm}{vcl_redex:Vclosed (app (lda u U B) A)} 
 	            C (app (lda u U B) A) (vsub A u B)}

	     {PI:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                  {u,v|VV}{B,B'|Trm} 
                  {premB:{p:PP}no_red1 (alpha p u B) (alpha p v B')}
 	          {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (pi u A B) (pi v A' B')}

 	     {LDA:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                   {u,v|VV}{B,B'|Trm} 
                   {premB:{p:PP}no_red1 (alpha p u B) (alpha p v B')}
		   {ihB:{p:PP}C (alpha p u B) (alpha p v B')} 
 	           C (lda u A B) (lda v A' B')} 

 	     {APP:{A,A'|Trm}{premA:no_red1 A A'}{ihA:C A A'} 
                   {B,B'|Trm}{premB:no_red1 B B'}{ihB:C B B'} 
                    C (app A B) (app A' B')} 

 	     {A,B|Trm}(no_red1 A B) -> C A B;

intros;Refine no_ared1_elim[A,B|Trm][_:no_ared1 A B]C A B;Immed;
intros;Refine PI;Immed;
       Refine no_ared1_red1 premA;Refine [p:PP]no_ared1_red1 (premB p);
intros;Refine LDA;Immed;
       Refine no_ared1_red1 premA;Refine [p:PP]no_ared1_red1 (premB p);
intros;Refine APP;Immed;
       Refine no_ared1_red1 premA;Refine no_ared1_red1 premB;
Refine no_red1_ared1;Immed;
Save;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(no_red1 X Y)->no_red1 (psub N p X) (psub N p Y);
intros ___;
Refine no_ared1Rec [A,B:Trm]no_red1 (psub N p A) (psub N p B);

intros;Refine no_red1_refl_sort;

intros;Equiv [M = if (PPeq p p1) N (par p1)]no_red1 M M;
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Refine no_red1_refl;Immed;
intros neqP;Qrepl neqP;Refine no_red1_refl_par;

intros;
Equiv no_red1 (app (lda u (psub N p U) (psub N p B)) (psub N p A)) ?;
Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A u B);Refine no_red1_beta;
Equiv Vclosed (psub ? ? (app (lda ? ? ?) ?));
Refine psub_resp_Vclosed;Immed;

intros;
Equiv no_red1 (pi u (psub N p A) (psub N p B))
               (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine no_red1_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv no_red1 (lda u (psub N p A) (psub N p B))
               (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine no_red1_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv no_red1 (app (psub N p A) (psub N p B))
               (app (psub N p A') (psub N p B'));
Refine no_red1_app;Immed;

Save psub_resp_no_red1;

Goal {X,Y|Trm}(no_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros;Refine par_red1_refl_pocc;Refine +1 no_par_red1;Immed;
Save no_red1_refl_pocc;

Goal {X,Y|Trm}(no_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 no_red1_refl_pocc;Immed;
Save not_pocc_resp_no_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}no_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;Refine par_red1_alpha_refl_pocc;
intros +3 q;Refine no_par_red1;Immed;
Immed;
Save no_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}no_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 no_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_no_red1_alpha;

(* now take the transitive closure of no_red1 *)
(* and show it equivalent to redn              *)
%\VerbFileOpen no_redn
Inductive [no_redn: Trm->Trm->Prop]  NoReductions  Constructors
 [no_redn_red1: {A,B|Trm}(no_red1 A B)->no_redn A B]
 [no_redn_trans: {A,D,B|Trm}{lt_prem:no_redn A D}
		           {rt_prem:no_redn D B}no_redn A B];
%\VerbFileClos no_redn

Goal no_rednRec : {C:{A,B:Trm}Prop}
	 {NO_RED1:{A,B|Trm}{r:no_red1 A B}C A B}
	 {TRANS:{A,D,B|Trm}{lt_prem:no_redn A D}{lt_ih:C A D}
		           {rt_prem:no_redn D B}{rt_ih:C D B}
		 C A B}
	 {A,B|Trm}{r:no_redn A B}C A B;

intros;Refine no_redn_elim [A,B|Trm][_:no_redn A B]C A B;Immed;
intros;Refine TRANS;Immed;
Save;

Goal no_redn_refl : {A|Trm}(Vclosed A)->no_redn A A;
intros;Refine no_redn_red1;Refine no_red1_refl;Immed;
Save no_redn_refl;

Goal {A,B|Trm}(no_redn A B)->
     {rho:Renaming}no_redn (renTrm rho A) (renTrm rho B);
Refine no_rednRec [A,B:Trm]
     {rho:Renaming}no_redn (renTrm rho A) (renTrm rho B);
intros;Refine no_redn_red1;Refine renTrm_resp_no_red1;Immed;
intros;Refine no_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save renTrm_resp_no_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(no_redn A B)->no_redn (psub N p A) (psub N p B);
intros ___;
Refine no_rednRec [A,B:Trm]no_redn (psub N p A) (psub N p B);
intros;Refine no_redn_red1;Refine psub_resp_no_red1;Immed;
intros;Refine no_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save psub_resp_no_redn;

Goal {A,B|Trm}(no_redn A B)->
     {p|PP}(is_tt (poccur p B))->is_tt (poccur p A);
Refine no_rednRec [A,B:Trm]
     {p|PP}{pocc:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine no_red1_refl_pocc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save no_redn_refl_pocc;

Goal {A,B|Trm}(no_redn A B)->{p|PP}(is_ff (poccur p A))->is_ff (poccur p B);
intros;Refine B_contrapos;Refine +1 no_redn_refl_pocc;Immed;
Save not_pocc_resp_no_redn;

Goal {A,B|Trm}(no_redn A B)->and (Vclosed A) (Vclosed B);
Refine no_rednRec [A,B:Trm]and (Vclosed A) (Vclosed B);
intros;Refine no_red1_Vclosed;Immed;
intros;Refine rt_ih;
intros;Refine lt_ih;
intros;Refine pair;Immed;
Save no_redn_Vclosed;

(* introduce auxiliary relation which simplifies this: usual *-trick *)
Inductive [no_aredn:Trm->Trm->Prop] NoReductions Constructors 
[no_aredn_red1:{A,B|Trm}(no_red1 A B)->no_aredn A B]
[no_aredn_trans_red1 : {A,D,B|Trm}{lt_prem:no_red1 A D}
			{rt_prem:no_aredn D B}no_aredn A B];

Goal {A,B|Trm}(no_aredn A B)->no_redn A B;
Refine no_aredn_elim [A,B|Trm][_:no_aredn A B]no_redn A B;
intros;Refine no_redn_red1;Immed;
intros;Refine no_redn_trans;Refine +1 no_redn_red1;Immed;
Save no_aredn_redn;

Goal {A,D,B|Trm}{lt_prem:no_aredn A D}{rt_prem:no_aredn D B}no_aredn A B;
intros;
Refine no_aredn_elim [A,D|Trm][_:no_aredn A D]
                    {B|Trm}{rt_prem:no_aredn D B}no_aredn A B;Immed;
intros;Refine no_aredn_trans_red1;Immed;
intros;Refine no_aredn_trans_red1;Refine +2 rt_prem_ih;Immed;
Save no_aredn_trans;

Goal {A,B|Trm}(no_redn A B)->no_aredn A B;
Refine no_rednRec [A,B|Trm]no_aredn A B;
intros;Refine no_aredn_red1;Immed;
intros;Refine no_aredn_trans;Immed;
Save no_redn_aredn;

Goal no_arednRec:{C:{A,B:Trm}Prop}

	      {RED1:{A,B|Trm}{r:no_red1 A B}C A B} 

	      {TRANS_RED1:{A,D,B|Trm}
                          {lt_prem:no_red1 A D}
                          {rt_prem:no_redn D B}{rt_ih:C D B}
		           C A B}

	      {A,B|Trm}{r:no_redn A B}C A B;

intros;Refine no_aredn_elim [A,B|Trm][_:no_aredn A B]C A B;Immed;
intros;Refine TRANS_RED1;Refine +2 no_aredn_redn;Immed;
Refine no_redn_aredn;Immed;
Save;

(* now the characters, for the subject reduction theorem *)
Goal {s|SS}{A|Trm}{r:no_red1 (sort s) A}is_tt (Trm_eq A (sort s));
intros;Refine par_red1_sort_character;Refine no_par_red1;Immed;
Save no_red1_sort_character;

Goal {s|SS}{A|Trm}{r:no_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine no_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Refine no_red1_sort_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save no_redn_sort_character;

Goal {p|PP}{A|Trm}{r:no_red1 (par p) A}is_tt (Trm_eq A (par p));
intros;Refine par_red1_par_character;Refine no_par_red1;Immed;
Save no_red1_par_character;

Goal {p|PP}{A|Trm}{r:no_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine no_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine no_red1_par_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save no_redn_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:no_red1 (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (no_red1 A A')
           ({p:PP}no_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine no_ared1Rec [P,P':Trm]
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (no_red1 A A')
                   ({p:PP}no_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save no_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:no_red1 (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (no_red1 A A')
           ({p:PP}no_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine no_ared1Rec [L,L':Trm]
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (no_red1 A A')
                   ({p:PP}no_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save no_red1_lda_character;

Goal {M,N,X|Trm}{red_app:no_red1 (app M N) X}
      or (Ex2 [M',N':Trm]
          and3 (no_red1 M M')
               (no_red1 N N')
               (is_tt (Trm_eq (app M' N') X)))
         (Ex3 [u:VV][U,B:Trm]
          and (is_tt (Trm_eq (lda u U B) M))
              (is_tt (Trm_eq (vsub N u B) X)));

intros;Refine no_ared1Rec [X,X':Trm]
              {eq:is_tt (Trm_eq (app M N) X)}
               or (Ex2 [M',N':Trm]
                   and3 (no_red1 M M')
                        (no_red1 N N')
                        (is_tt (Trm_eq (app M' N') X')))
                  (Ex3 [u:VV][U,B:Trm]
                   and (is_tt (Trm_eq (lda u U B) M))
                       (is_tt (Trm_eq (vsub N u B) X')));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inr;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex3In u U B;Refine pair;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inl;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Immed;
Save no_red1_app_character;

%\VerbFileOpen no_par_redn
Goal no_par_redn: {A,B|Trm}(no_redn A B)->par_redn A B;
%\VerbFileNoRecord no_par_redn
Refine no_rednRec [A,B:Trm]par_redn A B;
intros;Refine par_redn_red1;Refine no_par_red1;Immed;
intros;Refine par_redn_trans lt_ih rt_ih;
Save no_par_redn;

(* need to show constructors are inherited by no_redn from no_red1 *)
Goal {q|PP}{v|VV}{B|Trm}{noccB:is_ff (poccur q B)}{vclB:Vclosed (alpha q v B)}
     {A,A'|Trm}(no_redn A A')->
     no_redn (pi v A B) (pi v A' B);
intros _____;
Refine no_rednRec [A,A'|Trm]
                    no_redn (pi v A B) (pi v A' B);
intros;Refine no_redn_red1;Refine no_red1_pi;Refine +4 no_red1_refl;Immed;
intros;Refine no_redn_trans;Immed;
Save no_redn_pi_l; 

Goal {q|PP}{v|VV}{B|Trm}{noccB:is_ff (poccur q B)}{vclB:Vclosed (alpha q v B)}
     {A,A'|Trm}(no_redn A A')->
     no_redn (lda v A B) (lda v A' B);
intros _____;
Refine no_rednRec [A,A'|Trm]
                    no_redn (lda v A B) (lda v A' B);
intros;Refine no_redn_red1;Refine no_red1_lda;Refine +4 no_red1_refl;Immed;
intros;Refine no_redn_trans;Immed;
Save no_redn_lda_l; 

Goal {N|Trm}{vclN:Vclosed N}{M,M'|Trm}(no_redn M M')->
     no_redn (app M N) (app M' N);
intros __;
Refine no_rednRec [M,M'|Trm]no_redn (app M N) (app M' N);
intros;Refine no_redn_red1;Refine no_red1_app r (no_red1_refl ?);Immed;
intros;Refine no_redn_trans;Immed;
Save no_redn_app_l;

Goal {M|Trm}{vclM:Vclosed M}{N,N'|Trm}(no_redn N N')->
     no_redn (app M N) (app M N');
intros __;
Refine no_rednRec [N,N'|Trm]no_redn (app M N) (app M N');
intros;Refine no_redn_red1;Refine no_red1_app (no_red1_refl ?) r;Immed;
intros;Refine no_redn_trans;Immed;
Save no_redn_app_r;

Goal {M,M',N,N'|Trm}(no_redn M M')->(no_redn N N')->
         no_redn (app M N) (app M' N');
intros;Refine no_redn_trans;
Refine +1 no_redn_app_l (fst (no_redn_Vclosed ?));
Refine +4 no_redn_app_r (snd (no_redn_Vclosed ?));Immed;
Save no_redn_app;

Goal {Y|Trm}{vclY:Vclosed Y}{X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:no_redn (alpha p u X) (alpha p v X')}
     no_redn (pi u Y X) (pi v Y X');
intros;
Refine no_rednRec [B,B'|Trm]{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                  no_redn (pi u Y X) (pi v Y X');Immed;
intros;Refine no_redn_red1;Refine no_red1_pi (no_red1_refl ?);Immed;
Qrepl Q_sym (Trm_eq_subst eqB);Qrepl Q_sym (Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine no_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save no_redn_pi_r;

Goal {Y|Trm}{vclY:Vclosed Y}{X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:no_redn (alpha p u X) (alpha p v X')}
     no_redn (lda u Y X) (lda v Y X');
intros;
Refine no_rednRec [B,B'|Trm]{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                  no_redn (lda u Y X) (lda v Y X');Immed;
intros;Refine no_redn_red1;Refine no_red1_lda (no_red1_refl ?);Immed;
Qrepl Q_sym (Trm_eq_subst eqB);Qrepl Q_sym (Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine no_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save no_redn_lda_r;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:no_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:no_redn (alpha p u B) (alpha p v B')}
      no_redn (pi u A B) (pi v A' B');
intros;Refine no_redn_trans;
Refine +1 no_redn_pi_l ? (fst (no_redn_Vclosed ?));
Refine +6 no_redn_pi_r (snd (no_redn_Vclosed ?));Immed;
Save no_redn_pi;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:no_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:no_redn (alpha p u B) (alpha p v B')}
      no_redn (lda u A B) (lda v A' B');
intros;Refine no_redn_trans;
Refine +1 no_redn_lda_l ? (fst (no_redn_Vclosed ?));
Refine +6 no_redn_lda_r (snd (no_redn_Vclosed ?));Immed;
Save no_redn_lda;

Goal {A,M,N,M',N'|Trm}{vcl:Vclosed A}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:no_redn (alpha p u M) (alpha p v M')}{redN:no_redn N N'}
      no_redn (app (lda u A M) N) (vsub N' v M');
intros;Refine no_redn_trans;Refine +2 no_redn_red1;Refine +2 no_red1_beta; 
Refine no_redn_app;Refine no_redn_lda_r;Immed;
Refine Vclosed_app ? (snd (no_redn_Vclosed redN));
Refine Vclosed_lda ? (snd (no_redn_Vclosed redM));
Immed;
Save no_redn_beta;

Goal {A,B|Trm}(par_red1 A B)->no_redn A B;
Refine par_red1Rec [A,B:Trm]no_redn A B;
intros;Refine no_redn_red1;Refine no_red1_refl_sort;
intros;Refine no_redn_red1;Refine no_red1_refl_par;
intros;Refine no_redn_beta;Immed;
intros;Refine no_redn_pi;Immed;
intros;Refine no_redn_lda;Immed;
intros;Refine no_redn_app;Immed;
Save par_red1_no_redn;


%\VerbFileRecord no_par_redn
Goal par_no_redn: {A,B|Trm}(par_redn A B)->no_redn A B;
%\VerbFileClos no_par_redn
Refine par_rednRec [A,B:Trm]no_redn A B;
intros;Refine par_red1_no_redn;Immed;
intros;Refine no_redn_trans lt_ih rt_ih;
Save par_no_redn;

