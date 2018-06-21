Module complete_bp_development Import par_bp_red;

(* complete beta-pi development as an inductive relation, cf. Takahashi *)

$[comp_bp_dev : Trm->Trm->Prop]

$[comp_bp_dev_sort : {s:SS}comp_bp_dev (sort s) (sort s)];

$[comp_bp_dev_par : {p:PP}comp_bp_dev (par p) (par p)];

$[comp_bp_dev_pcon:{U:Trm}{A,A'|Trm}{premA:comp_bp_dev A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:comp_bp_dev (alpha p u B) (alpha p v B')}
                comp_bp_dev (app (pi u U B) A) (vsub A' v B')];

$[comp_bp_dev_beta:{U:Trm}{A,A'|Trm}{premA:comp_bp_dev A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:comp_bp_dev (alpha p u B) (alpha p v B')}
                comp_bp_dev (app (lda u U B) A) (vsub A' v B')];

$[comp_bp_dev_pi:{A,A'|Trm}{premA:comp_bp_dev A A'}
             {u,v|VV}{B,B'|Trm}{p|PP}
             {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
             {premB:comp_bp_dev (alpha p u B) (alpha p v B')}
              comp_bp_dev (pi u A B) (pi v A' B')];

$[comp_bp_dev_lda:{A,A'|Trm}{premA:comp_bp_dev A A'}
              {u,v|VV}{B,B'|Trm}{p|PP}
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
              {premB:comp_bp_dev (alpha p u B) (alpha p v B')}
               comp_bp_dev (lda u A B) (lda v A' B')];

$[comp_bp_dev_app:{A,A'|Trm}{sc:is_ff (isPi A)}{sc':is_ff (isLda A)}
                        {premA:comp_bp_dev A A'}
              {B,B'|Trm}{premB:comp_bp_dev B B'}
               comp_bp_dev (app A B) (app A' B')];

$[comp_bp_devRec:{C:{A,B|Trm}(comp_bp_dev A B)->Prop}

	     {SORT:{s:SS}C (comp_bp_dev_sort s)}

	     {PAR:{p:PP}C (comp_bp_dev_par p)}

	     {PCON:{U:Trm}{A,A'|Trm}{premA:comp_bp_dev A A'}{ihA:C premA}
                   {u,v|VV}{B,B'|Trm}{p|PP}
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                   {premB:comp_bp_dev (alpha p u B) (alpha p v B')}{ihB:C premB}
	            C (comp_bp_dev_pcon U premA noccB noccB' premB)}

	     {BETA:{U:Trm}{A,A'|Trm}{premA:comp_bp_dev A A'}{ihA:C premA}
                   {u,v|VV}{B,B'|Trm}{p|PP}
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                   {premB:comp_bp_dev (alpha p u B) (alpha p v B')}{ihB:C premB}
	            C (comp_bp_dev_beta U premA noccB noccB' premB)}

	     {PI:{A,A'|Trm}{premA:comp_bp_dev A A'}{ihA:C premA}
                 {u,v|VV}{B,B'|Trm}{p|PP}
                 {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                 {premB:comp_bp_dev (alpha p u B) (alpha p v B')}{ihB:C premB}
	          C (comp_bp_dev_pi premA noccB noccB' premB)}

	     {LDA:{A,A'|Trm}{premA:comp_bp_dev A A'}{ihA:C premA}
                  {u,v|VV}{B,B'|Trm}{p|PP}
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                  {premB:comp_bp_dev (alpha p u B) (alpha p v B')}{ihB:C premB}
	           C (comp_bp_dev_lda premA noccB noccB' premB)}

	     {APP:{A,A'|Trm}{sc:is_ff (isPi A)}{sc':is_ff (isLda A)}
                            {premA:comp_bp_dev A A'}{ihA:C premA}
                  {B,B'|Trm}{premB:comp_bp_dev B B'}{ihB:C premB}
                   C (comp_bp_dev_app sc sc' premA premB)}

	     {A,B|Trm}{r:comp_bp_dev A B}C r];

$[comp_bp_adev : Trm->Trm->Prop]

$[comp_bp_adev_sort : {s:SS}comp_bp_adev (sort s) (sort s)];

$[comp_bp_adev_par : {p:PP}comp_bp_adev (par p) (par p)];

$[comp_bp_adev_pcon:{U:Trm}{A,A'|Trm}{premA:comp_bp_adev A A'}
                {u,v|VV}{B,B'|Trm}
                {premB:{p|PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                 comp_bp_adev (app (pi u U B) A) (vsub A' v B')];

$[comp_bp_adev_beta:{U:Trm}{A,A'|Trm}{premA:comp_bp_adev A A'}
                {u,v|VV}{B,B'|Trm}
                {premB:{p|PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                 comp_bp_adev (app (lda u U B) A) (vsub A' v B')];

$[comp_bp_adev_pi:{A,A'|Trm}{premA:comp_bp_adev A A'}
              {u,v|VV}{B,B'|Trm}
              {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
               comp_bp_adev (pi u A B) (pi v A' B')];
$[comp_bp_adev_lda:{A,A'|Trm}{premA:comp_bp_adev A A'}
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                comp_bp_adev (lda u A B) (lda v A' B')];

$[comp_bp_adev_app:{A,A'|Trm}{sc:is_ff (isPi A)}{sc':is_ff (isLda A)}
                         {premA:comp_bp_adev A A'}
               {B,B'|Trm}{premB:comp_bp_adev B B'}
                comp_bp_adev (app A B) (app A' B')];

$[comp_bp_adevRec:{C:{A,B|Trm}(comp_bp_adev A B)->Prop}

	      {SORT:{s:SS}C (comp_bp_adev_sort s)}

	      {PAR:{p:PP}C (comp_bp_adev_par p)}

	      {PCON:{U:Trm}{A,A'|Trm}{premA:comp_bp_adev A A'}{ihA:C premA}
                    {u,v|VV}{B,B'|Trm}
                    {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                    {ihB:{p:PP}C (premB p)}
	             C (comp_bp_adev_pcon U premA premB)}

	      {BETA:{U:Trm}{A,A'|Trm}{premA:comp_bp_adev A A'}{ihA:C premA}
                    {u,v|VV}{B,B'|Trm}
                    {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                    {ihB:{p:PP}C (premB p)}
	             C (comp_bp_adev_beta U premA premB)}

	      {PI:{A,A'|Trm}{premA:comp_bp_adev A A'}{ihA:C premA}
                  {u,v|VV}{B,B'|Trm}
                  {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                  {ihB:{p:PP}C (premB p)}
	           C (comp_bp_adev_pi premA premB)}

	      {LDA:{A,A'|Trm}{premA:comp_bp_adev A A'}{ihA:C premA}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}comp_bp_adev (alpha p u B) (alpha p v B')}
                   {ihB:{p:PP}C (premB p)}
	            C (comp_bp_adev_lda premA premB)}

	      {APP:{A,A'|Trm}{sc:is_ff (isPi A)}{sc':is_ff (isLda A)}
                             {premA:comp_bp_adev A A'}{ihA:C premA}
                   {B,B'|Trm}{premB:comp_bp_adev B B'}{ihB:C premB}
                    C (comp_bp_adev_app sc sc' premA premB)}

	      {A,B|Trm}{r:comp_bp_adev A B}C r];

Goal {M,M'|Trm}(comp_bp_dev M M')->par_bp_red1 M M';
Refine comp_bp_devRec [M,M'|Trm][_:comp_bp_dev M M']par_bp_red1 M M';
intros;Refine par_bp_red1_refl;
intros;Refine par_bp_red1_refl;
intros;Refine par_bp_red1_pcon;Immed;
intros;Refine par_bp_red1_beta;Immed;
intros;Refine par_bp_red1_pi;Immed;
intros;Refine par_bp_red1_lda;Immed;
intros;Refine par_bp_red1_app;Immed;
Save comp_bp_dev_par_bp_red1;

Goal {A,B|Trm}(comp_bp_adev A B)->comp_bp_dev A B;
Refine comp_bp_adevRec [A,B:Trm][_:comp_bp_adev A B]comp_bp_dev A B;
intros;Refine comp_bp_dev_sort;
intros;Refine comp_bp_dev_par;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_bp_dev_pcon;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_bp_dev_beta;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_bp_dev_pi;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine comp_bp_dev_lda;Refine +4 ihB;Immed;
intros;Refine comp_bp_dev_app;Immed;
Save comp_bp_adev_dev;

Goal {A,B|Trm}(comp_bp_dev A B)->
     {rho:Renaming}comp_bp_adev (renTrm rho A) (renTrm rho B);
Refine comp_bp_devRec [A,B:Trm][_:comp_bp_dev A B]
                   {rho:Renaming}comp_bp_adev (renTrm rho A) (renTrm rho B);
intros;Refine comp_bp_adev_sort;
intros;Refine comp_bp_adev_par;

intros;
Equiv comp_bp_adev (app (pi u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine comp_bp_adev_pcon;Immed;
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
Equiv comp_bp_adev (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine comp_bp_adev_beta;Immed;
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
Equiv comp_bp_adev (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine comp_bp_adev_pi;Immed;
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
Equiv comp_bp_adev (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine comp_bp_adev_lda;Immed;
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
Equiv comp_bp_adev (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine comp_bp_adev_app;
Qrepl renTrm_isPi rho A;Qrepl +1 renTrm_isLda rho A;
Immed;

Save comp_bp_dev_adev_lem;

Goal {A,B|Trm}(comp_bp_dev A B)->comp_bp_adev A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine comp_bp_dev_adev_lem H renId;
Save comp_bp_dev_adev;

Goal {A,B|Trm}(comp_bp_dev A B)->{rho:Renaming}comp_bp_dev (renTrm rho A) (renTrm rho B);
intros;Refine comp_bp_adev_dev;Refine comp_bp_dev_adev_lem;Immed;
Save renTrm_resp_comp_bp_dev;

Goal {X,Y|Trm}(comp_bp_dev X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros;Refine par_bp_red1_refl_pocc;Refine +1 comp_bp_dev_par_bp_red1;Immed;
Save comp_bp_dev_refl_pocc;

Goal {X,Y|Trm}(comp_bp_dev X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 comp_bp_dev_refl_pocc;Immed;
Save not_pocc_resp_comp_bp_dev;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}comp_bp_dev (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;Refine par_bp_red1_alpha_refl_pocc;
intros +3 q;Refine comp_bp_dev_par_bp_red1;Immed;
Immed;
Save comp_bp_dev_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}comp_bp_dev (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 comp_bp_dev_alpha_refl_pocc;Immed;
Save not_pocc_resp_comp_bp_dev_alpha;

Goal {A,B|Trm}(comp_bp_dev A B)->(Vclosed A)->Vclosed B;
intros;Refine Vclosed_resp_par_bp_red1;Refine +1 comp_bp_dev_par_bp_red1;Immed;
Save Vclosed_resp_comp_bp_dev;

(* now the characters, for the Church-Rosser theorem *)
Goal {s|SS}{A|Trm}{r:comp_bp_dev (sort s) A}is_tt (Trm_eq A (sort s));
intros;Refine par_bp_red1_sort_character;Refine comp_bp_dev_par_bp_red1;Immed;
Save comp_bp_dev_sort_character;

Goal {p|PP}{A|Trm}{r:comp_bp_dev (par p) A}is_tt (Trm_eq A (par p));
intros;Refine par_bp_red1_par_character;Refine comp_bp_dev_par_bp_red1;Immed;
Save comp_bp_dev_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:comp_bp_dev (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (comp_bp_dev A A')
           ({p:PP}comp_bp_dev (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine comp_bp_adevRec [P,P':Trm][_:comp_bp_adev P P']
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (comp_bp_dev A A')
                   ({p:PP}comp_bp_dev (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine comp_bp_adev_dev;Refine premA;
intros;Refine comp_bp_adev_dev;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine comp_bp_dev_adev;Immed;
Save comp_bp_dev_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:comp_bp_dev (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (comp_bp_dev A A')
           ({p:PP}comp_bp_dev (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine comp_bp_adevRec [L,L':Trm][_:comp_bp_adev L L']
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (comp_bp_dev A A')
                   ({p:PP}comp_bp_dev (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine comp_bp_adev_dev;Refine premA;
intros;Refine comp_bp_adev_dev;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine comp_bp_dev_adev;Immed;
Save comp_bp_dev_lda_character;

Goal {M,N,X|Trm}{red_app:comp_bp_dev (app M N) X}
      or3 (Ex2 [M',N':Trm]
           and5 (is_ff (isPi M))
                (is_ff (isLda M))
                (comp_bp_dev M M')
                (comp_bp_dev N N')
                (is_tt (Trm_eq (app M' N') X)))
          (Ex6 [u,v:VV][U,B,B',A':Trm]
           and4 ({p:PP}comp_bp_dev (alpha p u B) (alpha p v B'))
                (comp_bp_dev N A')
                (is_tt (Trm_eq (pi u U B) M))
                (is_tt (Trm_eq (vsub A' v B') X)))
          (Ex6 [u,v:VV][U,B,B',A':Trm]
           and4 ({p:PP}comp_bp_dev (alpha p u B) (alpha p v B'))
                (comp_bp_dev N A')
                (is_tt (Trm_eq (lda u U B) M))
                (is_tt (Trm_eq (vsub A' v B') X)));

intros;Refine comp_bp_adevRec [X,X':Trm][_:comp_bp_adev X X']
              {eq:is_tt (Trm_eq (app M N) X)}
               or3 (Ex2 [M',N':Trm]
                    and5 (is_ff (isPi M))
                         (is_ff (isLda M))
                         (comp_bp_dev M M')
                         (comp_bp_dev N N')
                         (is_tt (Trm_eq (app M' N') X')))
                   (Ex6 [u,v:VV][U,B,B',A':Trm]
                    and4 ({p:PP}comp_bp_dev (alpha p u B) (alpha p v B'))
                         (comp_bp_dev N A')
                         (is_tt (Trm_eq (pi u U B) M))
                         (is_tt (Trm_eq (vsub A' v B') X')))
                   (Ex6 [u,v:VV][U,B,B',A':Trm]
                    and4 ({p:PP}comp_bp_dev (alpha p u B) (alpha p v B'))
                         (comp_bp_dev N A')
                         (is_tt (Trm_eq (lda u U B) M))
                         (is_tt (Trm_eq (vsub A' v B') X')));

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine or3_in2;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair4;
intros;Refine comp_bp_adev_dev;Refine premB;
Refine comp_bp_adev_dev;Refine premA;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine or3_in3;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair4;
intros;Refine comp_bp_adev_dev;Refine premB;
Refine comp_bp_adev_dev;Refine premA;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine or3_in1;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair5 sc sc';
Refine comp_bp_adev_dev;Refine premA;
Refine comp_bp_adev_dev;Refine premB;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Refine comp_bp_dev_adev;Immed;
Save comp_bp_dev_app_character;

Goal {M|Trm}(Vclosed M)->Ex [M':Trm]comp_bp_dev M M';
intros;Refine aVclosedRec [M|Trm][_:aVclosed M]Ex [M':Trm]comp_bp_dev M M';

intros;Refine ExIn (sort s);Refine comp_bp_dev_sort; 
intros;Refine ExIn (par p);Refine comp_bp_dev_par; 

intros;Refine fresh_params_lem1 B;
intros p noccB;Refine ihA;
intros A' cdA;Refine ihB p;
intros B1;Refine shape_lemma p B1;
intros u B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros cdB;Refine ExIn (pi u A' B');Refine comp_bp_dev_pi;Immed;

intros;Refine fresh_params_lem1 B;
intros p noccB;Refine ihA;
intros A' cdA;Refine ihB p;
intros B1;Refine shape_lemma p B1;
intros u B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros cdB;Refine ExIn (lda u A' B');Refine comp_bp_dev_lda;Immed;

intros;Refine ihB;
intros B' cdB;Refine tt_or_ff (isPi A);
intros case_pi;Refine isPi_lem case_pi;
intros u U X eqL;Refine ihA;Qrepl Trm_eq_subst eqL;
intros A' cdA;Refine comp_bp_dev_pi_character cdA;
intros v V X' hypL;Refine hypL; 
intros cdU cdX eqL';Refine fresh_params_lem1 X;
intros q noccX;Refine ExIn (vsub B' v X');
Refine comp_bp_dev_pcon;Immed;
Refine not_pocc_resp_comp_bp_dev_alpha;Immed;
intros case_npi;Refine tt_or_ff (isLda A);
intros case_lda;Refine isLda_lem case_lda;
intros u U X eqL;Refine ihA;Qrepl Trm_eq_subst eqL;
intros A' cdA;Refine comp_bp_dev_lda_character cdA;
intros v V X' hypL;Refine hypL; 
intros cdU cdX eqL';Refine fresh_params_lem1 X;
intros q noccX;Refine ExIn (vsub B' v X');
Refine comp_bp_dev_beta;Immed;
Refine not_pocc_resp_comp_bp_dev_alpha;Immed;
intros case_nlda;Refine ihA;
intros A' cdA;Refine ExIn (app A' B');
Refine comp_bp_dev_app;Immed;

Refine Vclosed_aVclosed;Immed;

Save comp_bp_dev_exists;

Goal {M,M''|Trm}(comp_bp_dev M M'')->
     (Vclosed M)->{M'|Trm}(par_bp_red1 M M')->par_bp_red1 M' M'';
Refine comp_bp_devRec [M,M''|Trm][_:comp_bp_dev M M'']
                   {vcl:Vclosed M}{M'|Trm}{pr:par_bp_red1 M M'}par_bp_red1 M' M''; 
intros;Qrepl Trm_eq_subst (par_bp_red1_sort_character pr);
Refine par_bp_red1_refl;

intros;Qrepl  Trm_eq_subst (par_bp_red1_par_character pr);
Refine par_bp_red1_refl;

intros;Refine Vclosed_app_lem vcl;
intros vclP vclA;Refine Vclosed_pi_lem vclP;
intros vclU vclB;Refine par_bp_red1_app_character pr;

intros case_appPR;Refine case_appPR;
intros L A'' hypPR;Refine hypPR;
intros prL prA eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_bp_red1_pi_character prL;
intros w W B'' hypPR';Refine hypPR';
intros prU prB eqL;Qrepl Q_sym (Trm_eq_subst eqL);
Refine par_bp_red1_pcon;
Refine ihA;Immed;
Refine +1 ihB;Immed;
Refine not_pocc_resp_par_bp_red1_alpha prB noccB;

intros case_pconPR;Refine case_pconPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL eqS;Refine Trm_eq_lda_lem eqL;
intros eqV eqA eqB;Qrepl Q_sym (Trm_eq_subst eqS);
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Claim is_ff (poccur p B''');
Qrepl  Q_sym (Trm_eq_subst (vsub_is_psub_alpha A'' w ?+1));
Refine par_bp_red1_psub;
Refine ihA;Refine +2 Vclosed_resp_par_bp_red1 ?+1;Immed;
Refine ihB;Refine +2 Vclosed_resp_par_bp_red1 ?+1;Immed;
Qrepl Q_sym (VVdecide eqV);Qrepl Q_sym (Trm_eq_subst eqB);Refine prB';
Refine not_pocc_resp_par_bp_red1_alpha prB';Qrepl Trm_eq_subst eqB;Refine noccB;

intros case_betaPR;Refine case_betaPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL eqS;Refine tt_not_ff (Q_sym eqL);

intros;Refine Vclosed_app_lem vcl;
intros vclL vclA;Refine Vclosed_lda_lem vclL;
intros vclU vclB;Refine par_bp_red1_app_character pr;

intros case_appPR;Refine case_appPR;
intros L A'' hypPR;Refine hypPR;
intros prL prA eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_bp_red1_lda_character prL;
intros w W B'' hypPR';Refine hypPR';
intros prU prB eqL;Qrepl Q_sym (Trm_eq_subst eqL);
Refine par_bp_red1_beta;
Refine ihA;Immed;
Refine +1 ihB;Immed;
Refine not_pocc_resp_par_bp_red1_alpha prB noccB;

intros case_pconPR;Refine case_pconPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL eqS;Refine tt_not_ff (Q_sym eqL);

intros case_betaPR;Refine case_betaPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL eqS;Refine Trm_eq_lda_lem eqL;
intros eqV eqA eqB;Qrepl Q_sym (Trm_eq_subst eqS);
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Claim is_ff (poccur p B''');
Qrepl  Q_sym (Trm_eq_subst (vsub_is_psub_alpha A'' w ?+1));
Refine par_bp_red1_psub;
Refine ihA;Refine +2 Vclosed_resp_par_bp_red1 ?+1;Immed;
Refine ihB;Refine +2 Vclosed_resp_par_bp_red1 ?+1;Immed;
Qrepl Q_sym (VVdecide eqV);Qrepl Q_sym (Trm_eq_subst eqB);Refine prB';
Refine not_pocc_resp_par_bp_red1_alpha prB';Qrepl Trm_eq_subst eqB;Refine noccB;

intros;Refine Vclosed_pi_lem vcl;
intros vclA vclB;Refine par_bp_red1_pi_character pr; 
intros w A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_bp_red1_pi;
Refine ihA;Immed;    
Refine not_pocc_resp_par_bp_red1_alpha prB noccB;
Refine ihB;Immed;    

intros;Refine Vclosed_lda_lem vcl;
intros vclA vclB;Refine par_bp_red1_lda_character pr; 
intros w A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_bp_red1_lda;
Refine ihA;Immed;    
Refine not_pocc_resp_par_bp_red1_alpha prB noccB;
Refine ihB;Immed;    

intros;Refine Vclosed_app_lem vcl;
intros vclA vclB;Refine par_bp_red1_app_character pr;

intros case_appPR;Refine case_appPR;
intros A'' B'' hypPR;Refine hypPR;
intros prA prB eqPR;Qrepl Q_sym (Trm_eq_subst eqPR);
Refine par_bp_red1_app;
Refine ihA;Immed;
Refine ihB;Immed;

intros case_pconPR;Refine case_pconPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL;Refine B_contradiction ? sc;
Qrepl Q_sym (Trm_eq_subst eqL);Refine Q_refl;

intros case_betaPR;Refine case_betaPR;
intros w' w W B'' B''' A'' hypL;Refine hypL;
intros prB' prA' eqL;Refine B_contradiction ? sc';
Qrepl Q_sym (Trm_eq_subst eqL);Refine Q_refl;

Save comp_bp_dev_preCR;

