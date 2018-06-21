Module complete_development Import par_redn;

(* complete development as an inductive relation, cf. Takahashi *)

Inductive [comp_dev : Trm->Trm->Prop]

Constructors

[comp_dev_sort : {s:SS}comp_dev (sort s) (sort s)]

[comp_dev_par : {p:PP}comp_dev (par p) (par p)]

[comp_dev_beta:{U|Trm}{vclU:Vclosed U}{A,A'|Trm}{premA:comp_dev A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:comp_dev (alpha p u B) (alpha p v B')}
                comp_dev (app (lda u U B) A) (vsub A' v B')]

[comp_dev_pi:{A,A'|Trm}{premA:comp_dev A A'}
             {u,v|VV}{B,B'|Trm}{p|PP}
             {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
             {premB:comp_dev (alpha p u B) (alpha p v B')}
              comp_dev (pi u A B) (pi v A' B')]

[comp_dev_lda:{A,A'|Trm}{premA:comp_dev A A'}
              {u,v|VV}{B,B'|Trm}{p|PP}
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
              {premB:comp_dev (alpha p u B) (alpha p v B')}
               comp_dev (lda u A B) (lda v A' B')]

[comp_dev_app:{A,A'|Trm}{sc:is_ff (isLda A)}{premA:comp_dev A A'}
              {B,B'|Trm}{premB:comp_dev B B'}
               comp_dev (app A B) (app A' B')];

Goal comp_devRec:{C:{A,B:Trm}Prop}

	     {SORT:{s:SS}C (sort s) (sort s)}

	     {PAR:{p:PP}C (par p) (par p)}

	     {BETA:{U|Trm}{vclU:Vclosed U}
		   {A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                   {u,v|VV}{B,B'|Trm}{p|PP}
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                   {premB:comp_dev (alpha p u B) (alpha p v B')}
		   {ihB:C (alpha p u B) (alpha p v B')}
	            C (app (lda u U B) A) (vsub A' v B')}

	     {PI:{A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                 {u,v|VV}{B,B'|Trm}{p|PP}
                 {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                 {premB:comp_dev (alpha p u B) (alpha p v B')}
		 {ihB:C (alpha p u B) (alpha p v B')}
	          C (pi u A B) (pi v A' B')}

	     {LDA:{A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                  {u,v|VV}{B,B'|Trm}{p|PP}
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                  {premB:comp_dev (alpha p u B) (alpha p v B')}
		  {ihB:C (alpha p u B) (alpha p v B')}
	           C (lda u A B) (lda v A' B')}

	     {APP:{A,A'|Trm}{sc:is_ff (isLda A)}
		  {premA:comp_dev A A'}{ihA:C A A'}
                  {B,B'|Trm}{premB:comp_dev B B'}{ihB:C B B'}
                   C (app A B) (app A' B')}

	     {A,B|Trm}(comp_dev A B) -> C A B;

intros;Refine comp_dev_elim [A,B:Trm][_:comp_dev A B]C A B;Immed;
intros;Refine BETA;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;


Goal {M,M'|Trm}(comp_dev M M')->par_red1 M M';
Refine comp_dev_elim [M,M'|Trm][_:comp_dev M M']par_red1 M M';
intros;Refine par_red1_refl_sort;
intros;Refine par_red1_refl_par;
intros;Refine par_red1_beta;Immed;
intros;Refine par_red1_pi;Immed;
intros;Refine par_red1_lda;Immed;
intros;Refine par_red1_app;Immed;
Save comp_dev_par_red1;

Goal {X,Y|Trm}(comp_dev X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros;Refine par_red1_refl_pocc;Refine +1 comp_dev_par_red1;Immed;
Save comp_dev_refl_pocc;

Goal {X,Y|Trm}(comp_dev X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 comp_dev_refl_pocc;Immed;
Save not_pocc_resp_comp_dev;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}comp_dev (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;Refine par_red1_alpha_refl_pocc;
intros +3 q;Refine comp_dev_par_red1;Immed;
Immed;
Save comp_dev_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}comp_dev (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 comp_dev_alpha_refl_pocc;Immed;
Save not_pocc_resp_comp_dev_alpha;

Goal {A,B|Trm}(comp_dev A B)-> and (Vclosed A) (Vclosed B);
intros;Refine par_red1_Vclosed;Refine comp_dev_par_red1;Immed;
Save comp_dev_Vclosed;

Inductive [comp_adev : Trm->Trm->Prop]

NoReductions

Constructors

[comp_adev_sort : {s:SS}comp_adev (sort s) (sort s)]

[comp_adev_par : {p:PP}comp_adev (par p) (par p)]

[comp_adev_beta:{U|Trm}{vclU:Vclosed U}{A,A'|Trm}{premA:comp_adev A A'}
                {u,v|VV}{B,B'|Trm}
                {premB:{p:PP}comp_adev (alpha p u B) (alpha p v B')}
                 comp_adev (app (lda u U B) A) (vsub A' v B')]

[comp_adev_pi:{A,A'|Trm}{premA:comp_adev A A'}
              {u,v|VV}{B,B'|Trm}
              {premB:{p:PP}comp_adev (alpha p u B) (alpha p v B')}
               comp_adev (pi u A B) (pi v A' B')]

[comp_adev_lda:{A,A'|Trm}{premA:comp_adev A A'}
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}comp_adev (alpha p u B) (alpha p v B')}
                comp_adev (lda u A B) (lda v A' B')]

[comp_adev_app:{A,A'|Trm}{sc:is_ff (isLda A)}{premA:comp_adev A A'}
               {B,B'|Trm}{premB:comp_adev B B'}
                comp_adev (app A B) (app A' B')];

Goal {A,B|Trm}(comp_adev A B)->comp_dev A B;
Refine comp_adev_elim [A,B:Trm][_:comp_adev A B]comp_dev A B;
intros;Refine comp_dev_sort;
intros;Refine comp_dev_par;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_dev_beta;Refine +5 premB_ih;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_dev_pi;Refine +4 premB_ih;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_dev_lda;Refine +4 premB_ih;Immed;
intros;Refine comp_dev_app;Immed;
Save comp_adev_dev;

Goal {A,B|Trm}(comp_dev A B)->{rho:Renaming}comp_adev (renTrm rho A) (renTrm rho B);
Refine comp_devRec [A,B:Trm]
                   {rho:Renaming}comp_adev (renTrm rho A) (renTrm rho B);
intros;Refine comp_adev_sort;
intros;Refine comp_adev_par;

intros;
Equiv comp_adev (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine comp_adev_beta;Refine renTrm_resp_Vclosed;Immed;
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
Equiv comp_adev (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine comp_adev_pi;Immed;
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
Equiv comp_adev (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine comp_adev_lda;Immed;
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
Equiv comp_adev (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine comp_adev_app;
Qrepl renTrm_isLda rho A;
Immed;

Save comp_dev_adev_lem;

Goal {A,B|Trm}(comp_dev A B)->comp_adev A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine comp_dev_adev_lem H renId;
Save comp_dev_adev;

Goal {A,B|Trm}(comp_dev A B)->{rho:Renaming}comp_dev (renTrm rho A) (renTrm rho B);
intros;Refine comp_adev_dev;Refine comp_dev_adev_lem;Immed;
Save renTrm_resp_comp_dev;

Goal comp_adevRec:{C:{A,B:Trm}Prop}

	     {SORT:{s:SS}C (sort s) (sort s)}

	     {PAR:{p:PP}C (par p) (par p)}

	     {BETA:{U|Trm}{vclU:Vclosed U}
		   {A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}comp_dev (alpha p u B) (alpha p v B')}
		   {ihB:{p:PP}C (alpha p u B) (alpha p v B')}
	            C (app (lda u U B) A) (vsub A' v B')}

	     {PI:{A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                 {u,v|VV}{B,B'|Trm}
                 {premB:{p:PP}comp_dev (alpha p u B) (alpha p v B')}
		 {ihB:{p:PP}C (alpha p u B) (alpha p v B')}
	          C (pi u A B) (pi v A' B')}

	     {LDA:{A,A'|Trm}{premA:comp_dev A A'}{ihA:C A A'}
                  {u,v|VV}{B,B'|Trm}
                  {premB:{p:PP}comp_dev (alpha p u B) (alpha p v B')}
		  {ihB:{p:PP}C (alpha p u B) (alpha p v B')}
	           C (lda u A B) (lda v A' B')}

	     {APP:{A,A'|Trm}{sc:is_ff (isLda A)}
		  {premA:comp_dev A A'}{ihA:C A A'}
                  {B,B'|Trm}{premB:comp_dev B B'}{ihB:C B B'}
                   C (app A B) (app A' B')}

	     {A,B|Trm}(comp_dev A B) -> C A B;

intros;Refine comp_adev_elim [A,B:Trm][_:comp_adev A B]C A B;Immed;
intros;Refine BETA;Immed;
Refine comp_adev_dev premA;Refine [p:PP]comp_adev_dev (premB p);
intros;Refine PI;Immed;
Refine comp_adev_dev premA;Refine [p:PP]comp_adev_dev (premB p);
intros;Refine LDA;Immed;
Refine comp_adev_dev premA;Refine [p:PP]comp_adev_dev (premB p);
intros;Refine APP;Immed;
Refine comp_adev_dev premA;Refine comp_adev_dev premB;
Refine comp_dev_adev;Immed;
Save;

(* now the characters, for the Church-Rosser theorem *)
Goal {s|SS}{A|Trm}{r:comp_dev (sort s) A}is_tt (Trm_eq A (sort s));
intros;Refine par_red1_sort_character;Refine comp_dev_par_red1;Immed;
Save comp_dev_sort_character;

Goal {p|PP}{A|Trm}{r:comp_dev (par p) A}is_tt (Trm_eq A (par p));
intros;Refine par_red1_par_character;Refine comp_dev_par_red1;Immed;
Save comp_dev_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:comp_dev (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (comp_dev A A')
           ({p:PP}comp_dev (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine comp_adevRec [P,P':Trm]
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (comp_dev A A')
                   ({p:PP}comp_dev (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save comp_dev_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:comp_dev (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (comp_dev A A')
           ({p:PP}comp_dev (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine comp_adevRec [L,L':Trm]
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (comp_dev A A')
                   ({p:PP}comp_dev (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;Immed;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Immed;
Save comp_dev_lda_character;

Goal {M,N,X|Trm}{red_app:comp_dev (app M N) X}
      or (Ex2 [M',N':Trm]
          and4 (is_ff (isLda M))
               (comp_dev M M')
               (comp_dev N N')
               (is_tt (Trm_eq (app M' N') X)))
         (Ex6 [u,v:VV][U,B,B',A':Trm]
          and5 ({p:PP}comp_dev (alpha p u B) (alpha p v B'))
               (comp_dev N A') (Vclosed U)
               (is_tt (Trm_eq (lda u U B) M))
               (is_tt (Trm_eq (vsub A' v B') X)));

intros;Refine comp_adevRec [X,X':Trm]
              {eq:is_tt (Trm_eq (app M N) X)}
               or (Ex2 [M',N':Trm]
                   and4 (is_ff (isLda M))
                        (comp_dev M M')
                        (comp_dev N N')
                        (is_tt (Trm_eq (app M' N') X')))
                  (Ex6 [u,v:VV][U,B,B',A':Trm]
                   and5 ({p:PP}comp_dev (alpha p u B) (alpha p v B'))
                        (comp_dev N A') (Vclosed U)
                        (is_tt (Trm_eq (lda u U B) M))
                        (is_tt (Trm_eq (vsub A' v B') X')));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inr;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair5;Immed;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine inl;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair4;Immed;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Immed;
Save comp_dev_app_character;

Goal {M|Trm}(Vclosed M)->Ex [M':Trm]comp_dev M M';
intros;Refine aVclosedRec [M|Trm][_:aVclosed M]Ex [M':Trm]comp_dev M M';
intros;Refine ExIn (* sort s *);Refine +1 comp_dev_sort; 
intros;Refine ExIn (* par p *);Refine +1 comp_dev_par; 

intros;Refine fresh_params_lem1 B;
intros p noccB;Refine ihA;
intros A' cdA;Refine ihB p;
intros B1;Refine shape_lemma p B1;
intros u B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros cdB;Refine ExIn (* pi u A' B' *);Refine +1 comp_dev_pi;Immed;
    
intros;Refine fresh_params_lem1 B;
intros p noccB;Refine ihA;
intros A' cdA;Refine ihB p;
intros B1;Refine shape_lemma p B1;
intros u B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros cdB;Refine ExIn (* lda u A' B' *);Refine +1 comp_dev_lda;Immed;
    
intros;Refine ihB;
intros B' cdB;Refine tt_or_ff (isLda A);
intros case_lda;Refine isLda_lem case_lda;
intros u U X eqL;Refine ihA;Qrepl Trm_eq_subst eqL;
intros A' cdA;Refine comp_dev_lda_character cdA;
intros v V X' hypL;Refine hypL; 
intros cdU cdX eqL';Refine fresh_params_lem1 X;
intros q noccX;Refine ExIn (* vsub B' v X' *);
Refine +1 comp_dev_beta;Refine fst (comp_dev_Vclosed cdU);Immed;
Refine not_pocc_resp_comp_dev_alpha;Immed;
intros case_nlda;Refine ihA;
intros A' cdA;Refine ExIn (* app A' B' *);
Refine +1 comp_dev_app;Immed;

Refine Vclosed_aVclosed;Immed;
Save comp_dev_exists;

Goal {M,M''|Trm}(comp_dev M M'')->
     {M'|Trm}(par_red1 M M')->par_red1 M' M'';
Refine comp_devRec [M,M''|Trm]
                   {M'|Trm}{pr:par_red1 M M'}par_red1 M' M''; 
intros;Qrepl Trm_eq_subst (par_red1_sort_character pr);
Refine par_red1_refl_sort;

intros;Qrepl Trm_eq_subst (par_red1_par_character pr);
Refine par_red1_refl_par;

intros;Refine par_red1_app_character pr;

intros case_appPR;Refine case_appPR;
intros L A'' hypPR;Refine hypPR;
intros prL prA eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_red1_lda_character prL;
intros w W B'' hypPR';Refine hypPR';
intros prU prB eqL;Qrepl Q_sym (Trm_eq_subst eqL);
Refine par_red1_beta;Refine snd (par_red1_Vclosed prU);
Refine ihA;Immed;
Refine +1 ihB;Immed;
Refine not_pocc_resp_par_red1_alpha prB noccB;

intros case_betaPR;Refine case_betaPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' vclW eqL eqS;Refine Trm_eq_lda_lem eqL;
intros eqV eqA eqB;Qrepl Q_sym (Trm_eq_subst eqS);
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Claim is_ff (poccur p B''');
Qrepl  Q_sym (Trm_eq_subst (vsub_is_psub_alpha A'' w ?+1));
Refine par_red1_psub;
Refine ihA;Immed;
Refine ihB;
Qrepl Q_sym (VVdecide eqV);Qrepl Q_sym (Trm_eq_subst eqB);Refine prB';
Refine not_pocc_resp_par_red1_alpha prB';Qrepl Trm_eq_subst eqB;Refine noccB;

intros;Refine par_red1_pi_character pr; 
intros w A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_red1_pi;
Refine ihA;Immed;    
Refine not_pocc_resp_par_red1_alpha prB noccB;
Refine ihB;Immed;

intros;Refine par_red1_lda_character pr; 
intros w A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_red1_lda;
Refine ihA;Immed;    
Refine not_pocc_resp_par_red1_alpha prB noccB;
Refine ihB;Immed;    

intros;Refine par_red1_app_character pr;

intros case_appPR;Refine case_appPR;
intros A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_red1_app;
Refine ihA;Immed;
Refine ihB;Immed;

intros case_betaPR;Refine case_betaPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' vclW eqL eqS;Refine B_contradiction ? sc;
Qrepl Q_sym (Trm_eq_subst eqL);Refine Q_refl;

Save comp_dev_preCR;

Goal {M,M'|Trm}(comp_dev M M')->
     {N,N'|Trm}(par_red1 M N)->(comp_dev N N')->par_red1 M' N';
intros;Refine comp_dev_preCR;Refine +2 comp_dev_preCR;Immed;
Save comp_dev_red1_square;

Goal {M,M'|Trm}(comp_dev M M')->
     {N,N'|Trm}(par_redn M N)->(comp_dev N N')->par_redn M' N';
intros;Refine par_rednRec [M,N|Trm]
                          {M',N'|Trm}{c:comp_dev M M'}{c':comp_dev N N'}
                           par_redn M' N';Immed;
intros;Refine par_redn_red1;Refine comp_dev_red1_square;Immed;
intros;
[vclD : Vclosed D = snd (par_redn_Vclosed lt_prem)];
Refine comp_dev_exists vclD;
intros D' cD;Refine par_redn_trans;Refine +1 lt_ih;Refine +3 rt_ih;Immed;
Save comp_dev_redn_square;
