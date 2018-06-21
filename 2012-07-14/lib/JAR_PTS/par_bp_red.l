Module par_bp_red 
Import par_redn;

(* the parallel one-step pi-beta reduction relation *)

$[par_bp_red1 : Trm->Trm->Prop]

$[par_bp_red1_refl : refl par_bp_red1];

$[par_bp_red1_pcon:{U:Trm}{A,A'|Trm}{premA:par_bp_red1 A A'}
                  {u,v|VV}{B,B'|Trm}{p|PP}
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                  {premB:par_bp_red1 (alpha p u B) (alpha p v B')}
                   par_bp_red1 (app (pi u U B) A) (vsub A' v B')];

$[par_bp_red1_beta:{U:Trm}{A,A'|Trm}{premA:par_bp_red1 A A'}
                  {u,v|VV}{B,B'|Trm}{p|PP}
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                  {premB:par_bp_red1 (alpha p u B) (alpha p v B')}
                   par_bp_red1 (app (lda u U B) A) (vsub A' v B')];

$[par_bp_red1_pi:{A,A'|Trm}{premA:par_bp_red1 A A'}
                {u,v|VV}{B,B'|Trm}{p|PP}
                {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                {premB:par_bp_red1 (alpha p u B) (alpha p v B')}
                 par_bp_red1 (pi u A B) (pi v A' B')];

$[par_bp_red1_lda:{A,A'|Trm}{premA:par_bp_red1 A A'}
                 {u,v|VV}{B,B'|Trm}{p|PP}
                 {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                 {premB:par_bp_red1 (alpha p u B) (alpha p v B')}
                  par_bp_red1 (lda u A B) (lda v A' B')];

$[par_bp_red1_app:{A,A'|Trm}{premA:par_bp_red1 A A'}
                 {B,B'|Trm}{premB:par_bp_red1 B B'}
                  par_bp_red1 (app A B) (app A' B')];

$[par_bp_red1Rec:{C:{A,B|Trm}(par_bp_red1 A B)->Prop}

   	        {REFL:{A:Trm}C (par_bp_red1_refl A)}
   
   	        {PCON:{U:Trm}{A,A'|Trm}{premA:par_bp_red1 A A'}{ihA:C premA}
                      {u,v|VV}{B,B'|Trm}{p|PP}
                      {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                      {premB:par_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
   	               C (par_bp_red1_pcon U premA noccB noccB' premB)}
   
   	        {BETA:{U:Trm}{A,A'|Trm}{premA:par_bp_red1 A A'}{ihA:C premA}
                      {u,v|VV}{B,B'|Trm}{p|PP}
                      {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                      {premB:par_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
   	               C (par_bp_red1_beta U premA noccB noccB' premB)}
   
   	        {PI:{A,A'|Trm}{premA:par_bp_red1 A A'}{ihA:C premA}
                    {u,v|VV}{B,B'|Trm}{p|PP}
                    {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                    {premB:par_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
   	             C (par_bp_red1_pi premA noccB noccB' premB)}
   
   	        {LDA:{A,A'|Trm}{premA:par_bp_red1 A A'}{ihA:C premA}
                     {u,v|VV}{B,B'|Trm}{p|PP}
                     {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                     {premB:par_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
   	              C (par_bp_red1_lda premA noccB noccB' premB)}
   
   	        {APP:{A,A'|Trm}{premA:par_bp_red1 A A'}{ihA:C premA}
                     {B,B'|Trm}{premB:par_bp_red1 B B'}{ihB:C premB}
                      C (par_bp_red1_app premA premB)}
   
   	        {A,B|Trm}{r:par_bp_red1 A B}C r];

$[par_bp_ared1 : Trm->Trm->Prop]

$[par_bp_ared1_refl : refl par_bp_ared1];

$[par_bp_ared1_pcon:{U:Trm}{A,A'|Trm}{premA:par_bp_ared1 A A'}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                    par_bp_ared1 (app (pi u U B) A) (vsub A' v B')];

$[par_bp_ared1_beta:{U:Trm}{A,A'|Trm}{premA:par_bp_ared1 A A'}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                    par_bp_ared1 (app (lda u U B) A) (vsub A' v B')];

$[par_bp_ared1_pi:{A,A'|Trm}{premA:par_bp_ared1 A A'}
                 {u,v|VV}{B,B'|Trm}
                 {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                  par_bp_ared1 (pi u A B) (pi v A' B')];
$[par_bp_ared1_lda:{A,A'|Trm}{premA:par_bp_ared1 A A'}
                  {u,v|VV}{B,B'|Trm}
                  {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                   par_bp_ared1 (lda u A B) (lda v A' B')];

$[par_bp_ared1_app:{A,A'|Trm}{premA:par_bp_ared1 A A'}
                  {B,B'|Trm}{premB:par_bp_ared1 B B'}
                   par_bp_ared1 (app A B) (app A' B')];

$[par_bp_ared1Rec:{C:{A,B|Trm}(par_bp_ared1 A B)->Prop}

   	         {REFL:{A:Trm}C (par_bp_ared1_refl A)}
   
   	         {PCON:{U:Trm}{A,A'|Trm}{premA:par_bp_ared1 A A'}{ihA:C premA}
                       {u,v|VV}{B,B'|Trm}
                       {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                       {ihB:{p:PP}C (premB p)}
   	                C (par_bp_ared1_pcon U premA premB)}
   
   	     
   	         {BETA:{U:Trm}{A,A'|Trm}{premA:par_bp_ared1 A A'}{ihA:C premA}
                       {u,v|VV}{B,B'|Trm}
                       {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                       {ihB:{p:PP}C (premB p)}
   	                C (par_bp_ared1_beta U premA premB)}
   
   	     
   	         {PI:{A,A'|Trm}{premA:par_bp_ared1 A A'}{ihA:C premA}
                     {u,v|VV}{B,B'|Trm}
                     {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                     {ihB:{p:PP}C (premB p)}
   	              C (par_bp_ared1_pi premA premB)}
   
   	         {LDA:{A,A'|Trm}{premA:par_bp_ared1 A A'}{ihA:C premA}
                      {u,v|VV}{B,B'|Trm}
                      {premB:{p:PP}par_bp_ared1 (alpha p u B) (alpha p v B')}
                      {ihB:{p:PP}C (premB p)}
   	               C (par_bp_ared1_lda premA premB)}
   
   	         {APP:{A,A'|Trm}{premA:par_bp_ared1 A A'}{ihA:C premA}
                      {B,B'|Trm}{premB:par_bp_ared1 B B'}{ihB:C premB}
                       C (par_bp_ared1_app premA premB)}
   
   	         {A,B|Trm}{r:par_bp_ared1 A B}C r];

Goal {A,B|Trm}(par_red1 A B)->par_bp_red1 A B;
Refine par_red1Rec [A,B|Trm]par_bp_red1 A B;
intros;Refine par_bp_red1_refl;
intros;Refine par_bp_red1_refl;
intros;Refine par_bp_red1_beta;Immed;
intros;Refine par_bp_red1_pi;Immed;
intros;Refine par_bp_red1_lda;Immed;
intros;Refine par_bp_red1_app;Immed;
Save par_red1_bp_red1;

Goal {A,B|Trm}(par_bp_ared1 A B)->par_bp_red1 A B;
Refine par_bp_ared1Rec [A,B:Trm][_:par_bp_ared1 A B]par_bp_red1 A B;
intros;Refine par_bp_red1_refl;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_bp_red1_pcon;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_bp_red1_beta;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_bp_red1_pi;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine par_bp_red1_lda;Refine +4 ihB;Immed;
intros;Refine par_bp_red1_app;Immed;
Save par_bp_ared1_red1;

Goal {A,B|Trm}(par_bp_red1 A B)->
     {rho:Renaming}par_bp_ared1 (renTrm rho A) (renTrm rho B);
Refine par_bp_red1Rec [A,B:Trm][_:par_bp_red1 A B]
                   {rho:Renaming}par_bp_ared1 (renTrm rho A) (renTrm rho B);
intros;Refine par_bp_ared1_refl;

intros;
Equiv par_bp_ared1 (app (pi u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine par_bp_ared1_pcon;Immed;
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
Equiv par_bp_ared1 (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A' v B');
Refine par_bp_ared1_beta;Immed;
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
Equiv par_bp_ared1 (pi u (renTrm rho A) (renTrm rho B))
                   (pi v (renTrm rho A') (renTrm rho B'));
Refine par_bp_ared1_pi;Immed;
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
Equiv par_bp_ared1 (lda u (renTrm rho A) (renTrm rho B))
                   (lda v (renTrm rho A') (renTrm rho B'));
Refine par_bp_ared1_lda;Immed;
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
Equiv par_bp_ared1 (app (renTrm rho A) (renTrm rho B))
                   (app (renTrm rho A') (renTrm rho B'));
Refine par_bp_ared1_app;Immed;

Save par_bp_red1_ared1_lem;

Goal {A,B|Trm}(par_bp_red1 A B)->par_bp_ared1 A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine par_bp_red1_ared1_lem H renId;
Save par_bp_red1_ared1;

Goal {A,B|Trm}(par_bp_red1 A B)->
     {rho:Renaming}par_bp_red1 (renTrm rho A) (renTrm rho B);
intros;Refine par_bp_ared1_red1;Refine par_bp_red1_ared1_lem;Immed;
Save renTrm_resp_par_bp_red1;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(par_bp_red1 X Y)->par_bp_red1 (psub N p X) (psub N p Y);
intros;
Refine par_bp_ared1Rec
       [A,B:Trm][_:par_bp_ared1 A B]par_bp_red1 (psub N p A) (psub N p B);
intros;Refine par_bp_red1_refl;

intros;Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A' v B');
Equiv par_bp_red1 (app (pi u (psub N p U) (psub N p B)) (psub N p A)) ?;
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqPP noccN noccB noccB';
Refine par_bp_red1_pcon;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqPP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqPP v B');
Refine ihB;

intros;Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A' v B');
Equiv par_bp_red1 (app (lda u (psub N p U) (psub N p B)) (psub N p A)) ?;
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqPP noccN noccB noccB';
Refine par_bp_red1_beta;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqPP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqPP v B');
Refine ihB;

intros;
Equiv par_bp_red1 (pi u (psub N p A) (psub N p B))
                  (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine par_bp_red1_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv par_bp_red1 (lda u (psub N p A) (psub N p B))
                  (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine par_bp_red1_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine ihB;

intros;
Equiv par_bp_red1 (app (psub N p A) (psub N p B))
               (app (psub N p A') (psub N p B'));
Refine par_bp_red1_app;Immed;

Refine par_bp_red1_ared1;Immed;
Save psub_resp_par_bp_red1;

Goal {X,Y|Trm}(par_bp_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros ___;
Refine par_bp_ared1Rec [A,B:Trm][_:par_bp_ared1 A B]
                       {p|PP}{occ:is_tt (poccur p B)}is_tt (poccur p A);
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

Refine par_bp_red1_ared1;Immed;
Save par_bp_red1_refl_pocc;

Goal {X,Y|Trm}(par_bp_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_bp_red1_refl_pocc;Immed;
Save not_pocc_resp_par_bp_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_bp_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occ:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (par_bp_red1_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;
Save par_bp_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_bp_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_bp_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_par_bp_red1_alpha;

Goal {A,B|Trm}(par_bp_red1 A B)->(Vclosed A)->Vclosed B;
Refine par_bp_red1Rec [A,B:Trm][_:par_bp_red1 A B]{vcl:Vclosed A}Vclosed B;
(* refl *)
intros;Immed;
(* pi con  *)
intros;Refine Vclosed_app_lem vcl;
intros vclP vclA;Refine Vclosed_pi_lem vclP;
intros vclU vclB;Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Refine psub_resp_Vclosed;Refine ihA;Refine +1 ihB;Immed;
(* beta  *)
intros;Refine Vclosed_app_lem vcl;
intros vclL vclA;Refine Vclosed_lda_lem vclL;
intros vclU vclB;Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Refine psub_resp_Vclosed;Refine ihA;Refine +1 ihB;Immed;
(* pi *)
intros;Refine Vclosed_pi_lem vcl;
intros vclA vclB;Refine Vclosed_pi;Refine +1 ihA;Refine +2 ihB;Immed;
(* lda *)
intros;Refine Vclosed_lda_lem vcl;
intros vclA vclB;Refine Vclosed_lda;Refine +1 ihA;Refine +2 ihB;Immed;
(* app *)
intros;Refine Vclosed_app_lem vcl;
intros vclA vclB;Refine Vclosed_app;Refine ihA;Refine +1 ihB;Immed;
Save Vclosed_resp_par_bp_red1;

Goal {N,N'|Trm}{par_bp_redN:par_bp_red1 N N'}{vclN:Vclosed N}{p:PP}
     {M|Trm}(Vclosed M)->par_bp_red1 (psub N p M) (psub N' p M);
intros _______;[subN = psub N p][subN' = psub N' p];
[vclN' = Vclosed_resp_par_bp_red1 par_bp_redN vclN : Vclosed N'];
Refine aVclosedRec [A:Trm][_:aVclosed A]par_bp_red1 (subN A) (subN' A);
intros;Refine par_bp_red1_refl;

intros;Equiv par_bp_red1 (if ? ? ?) (if ? ? ?);
Refine tt_or_ff (PPeq p p1);
intros case;Qrepl case;Immed;
intros case;Qrepl case;Refine par_bp_red1_refl;

intros;Equiv par_bp_red1 (pi n (subN A) (subN B)) (pi n (subN' A) (subN' B));
Refine fresh_params_lem2p p N B;
intros q qFresh;Refine qFresh;
intros neqP noccN noccB;Refine par_bp_red1_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB (not_pocc_resp_par_bp_red1 par_bp_redN noccN);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP n B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP n B);
Immed;

intros;Equiv par_bp_red1 (lda n (subN A) (subN B)) (lda n (subN' A) (subN' B));
Refine fresh_params_lem2p p N B;
intros q qFresh;Refine qFresh;
intros neqP noccN noccB;Refine par_bp_red1_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB (not_pocc_resp_par_bp_red1 par_bp_redN noccN);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP n B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP n B);
Immed;

intros;Equiv par_bp_red1 (app (subN A) (subN B)) (app (subN' A) (subN' B));
Refine par_bp_red1_app;Immed;

Refine Vclosed_aVclosed;Immed;
Save par_bp_red1_refl_psub_lem;

Goal {N,N'|Trm}{par_bp_redN:par_bp_red1 N N'}{vclN:Vclosed N}{p|PP}
     {X,X'|Trm}(par_bp_red1 X X')->
               (Vclosed X)->par_bp_red1 (psub N p X) (psub N' p X');
intros ________;[subN = psub N p][subN' = psub N' p];
[vclN' = Vclosed_resp_par_bp_red1 par_bp_redN vclN : Vclosed N'];
Refine par_bp_ared1Rec [M,M'|Trm][_:par_bp_ared1 M M']
                       {vcl:Vclosed M}par_bp_red1 (subN M) (subN' M');

(* refl *)
intros;Refine par_bp_red1_refl_psub_lem;Immed;
(* pcon *)
intros;
[vclL = fst (Vclosed_app_lem vcl) : Vclosed (pi u U B)];
[vclU = fst (Vclosed_pi_lem vclL) : Vclosed U];
[vclB = snd (Vclosed_pi_lem vclL) : {p:PP}Vclosed (alpha p u B)];
[vclA = snd (Vclosed_app_lem vcl) : Vclosed A];
Qrepl Trm_eq_subst(psub_vsub_commutes vclN' p A' v B');
Equiv par_bp_red1 (app (pi u (subN U) (subN B)) (subN A)) ?;
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_bp_red1_pcon;
Refine ihA vclA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP v B');
Refine ihB;Refine vclB;
(* beta *)
intros;
[vclL = fst (Vclosed_app_lem vcl) : Vclosed (lda u U B)];
[vclU = fst (Vclosed_lda_lem vclL) : Vclosed U];
[vclB = snd (Vclosed_lda_lem vclL) : {p:PP}Vclosed (alpha p u B)];
[vclA = snd (Vclosed_app_lem vcl) : Vclosed A];
Qrepl Trm_eq_subst(psub_vsub_commutes vclN' p A' v B');
Equiv par_bp_red1 (app (lda u (subN U) (subN B)) (subN A)) ?;
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_bp_red1_beta;
Refine ihA vclA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP v B');
Refine ihB;Refine vclB;
(* pi *)
intros;
[vclA = fst (Vclosed_pi_lem vcl) : Vclosed A];
[vclB = snd (Vclosed_pi_lem vcl) : {p|PP}Vclosed (alpha p u B)];
Equiv par_bp_red1 (pi u (subN A) (subN B)) (pi v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_bp_red1_pi;
Refine ihA vclA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP v B');
Refine ihB;Refine vclB;
(* lda *)
intros;
[vclA = fst (Vclosed_lda_lem vcl) : Vclosed A];
[vclB = snd (Vclosed_lda_lem vcl) : {p|PP}Vclosed (alpha p u B)];
Equiv par_bp_red1 (lda u (subN A) (subN B)) (lda v (subN' A') (subN' B'));
Refine fresh_params_lem4p p N N' B B';intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';Refine par_bp_red1_lda;
Refine ihA vclA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN' neqP v B');
Refine ihB;Refine vclB;
(* app *)
intros;
[vclA = fst (Vclosed_app_lem vcl) : Vclosed A];
[vclB = snd (Vclosed_app_lem vcl) : Vclosed B];
Equiv par_bp_red1 (app (subN A) (subN B)) (app (subN' A') (subN' B'));
Refine par_bp_red1_app;
Refine ihA;Immed;
Refine ihB;Immed;

Refine par_bp_red1_ared1;Immed;
Save par_bp_red1_psub;

(* now the characters, for the Church-Rosser theorem *)
Goal {w|VV}{A,B,X|Trm}{red_pi:par_bp_red1 (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_bp_red1 A A')
           ({p:PP}par_bp_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine par_bp_ared1Rec [P,P':Trm][_:par_bp_ared1 P P']
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_bp_red1 A A')
                   ({p:PP}par_bp_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine Ex3In w A B;Refine pair3;
Refine par_bp_red1_refl;intros;Refine par_bp_red1_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine par_bp_ared1_red1;Refine premA;
intros;Refine par_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine par_bp_red1_ared1;Immed;
Save par_bp_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:par_bp_red1 (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_bp_red1 A A')
           ({p:PP}par_bp_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine par_bp_ared1Rec [L,L':Trm][_:par_bp_ared1 L L']
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_bp_red1 A A')
                   ({p:PP}par_bp_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine Ex3In w A B;Refine pair3;
Refine par_bp_red1_refl;intros;Refine par_bp_red1_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine par_bp_ared1_red1;Refine premA;
intros;Refine par_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine par_bp_red1_ared1;Immed;
Save par_bp_red1_lda_character;

Goal {M,N,X|Trm}{red_app:par_bp_red1 (app M N) X}
      or3 (Ex2 [M',N':Trm]
           and3 (par_bp_red1 M M')
                (par_bp_red1 N N')
                (is_tt (Trm_eq (app M' N') X)))
          (Ex6 [u,v:VV][U,B,B',A':Trm]
           and4 ({p:PP}par_bp_red1 (alpha p u B) (alpha p v B'))
                (par_bp_red1 N A')
                (is_tt (Trm_eq (pi u U B) M))
                (is_tt (Trm_eq (vsub A' v B') X)))
          (Ex6 [u,v:VV][U,B,B',A':Trm]
           and4 ({p:PP}par_bp_red1 (alpha p u B) (alpha p v B'))
                (par_bp_red1 N A')
                (is_tt (Trm_eq (lda u U B) M))
                (is_tt (Trm_eq (vsub A' v B') X)));

intros;Refine par_bp_ared1Rec [X,X':Trm][_:par_bp_ared1 X X']
              {eq:is_tt (Trm_eq (app M N) X)}
               or3 (Ex2 [M',N':Trm]
                    and3 (par_bp_red1 M M')
                         (par_bp_red1 N N')
                         (is_tt (Trm_eq (app M' N') X')))
                   (Ex6 [u,v:VV][U,B,B',A':Trm]
                    and4 ({p:PP}par_bp_red1 (alpha p u B) (alpha p v B'))
                         (par_bp_red1 N A')
                         (is_tt (Trm_eq (pi u U B) M))
                         (is_tt (Trm_eq (vsub A' v B') X')))
                   (Ex6 [u,v:VV][U,B,B',A':Trm]
                    and4 ({p:PP}par_bp_red1 (alpha p u B) (alpha p v B'))
                         (par_bp_red1 N A')
                         (is_tt (Trm_eq (lda u U B) M))
                         (is_tt (Trm_eq (vsub A' v B') X')));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine or3_in1;Refine Ex2In M N;Refine pair3;
Refine par_bp_red1_refl;Refine par_bp_red1_refl;Refine Trm_eq_refl;

intros;Refine or3_in2;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair4;
intros;Refine par_bp_ared1_red1;Refine premB;
Refine par_bp_ared1_red1;Refine premA;
Refine Trm_eq_refl;
Refine Trm_eq_refl;

intros;Refine or3_in3;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex6In u v U B B' A';Refine pair4;
intros;Refine par_bp_ared1_red1;Refine premB;
Refine par_bp_ared1_red1;Refine premA;
Refine Trm_eq_refl;
Refine Trm_eq_refl;

intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine or3_in1;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair3;
Refine par_bp_ared1_red1;Refine premA;
Refine par_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Refine par_bp_red1_ared1;Immed;
Save par_bp_red1_app_character;



(* now take the transitive closure of par_bp_red1 *)
(* and show it equivalent to redn              *)

$[par_bp_redn:Trm->Trm->Prop];
$[par_bp_redn_red1:{A,B|Trm}(par_bp_red1 A B)->par_bp_redn A B];
$[par_bp_redn_trans : trans par_bp_redn];

$[par_bp_rednRec:{C:{A,B|Trm}(par_bp_redn A B)->Prop}
	 {PAR_BP_RED1:{A,B|Trm}{r:par_bp_red1 A B}C  (par_bp_redn_red1 r)}
	 {TRANS:{A,D,B|Trm}{lt_prem:par_bp_redn A D}{lt_ih:C lt_prem}
		           {rt_prem:par_bp_redn D B}{rt_ih:C rt_prem}
		 C (par_bp_redn_trans lt_prem rt_prem)}
	 {A,B|Trm}{r:par_bp_redn A B}C r];

Goal refl par_bp_redn;
Intros;Refine par_bp_redn_red1;Refine par_bp_red1_refl;
Save par_bp_redn_refl;

Goal {A,B|Trm}(par_bp_redn A B)->{rho:Renaming}par_bp_redn (renTrm rho A) (renTrm rho B);
Refine par_bp_rednRec [A,B:Trm][_:par_bp_redn A B]
	{rho:Renaming}par_bp_redn (renTrm rho A) (renTrm rho B);
intros;Refine par_bp_redn_red1;Refine renTrm_resp_par_bp_red1;Immed;
intros;Refine par_bp_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save renTrm_resp_par_bp_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(par_bp_redn A B)->par_bp_redn (psub N p A) (psub N p B);
intros ___;
Refine par_bp_rednRec [A,B:Trm][_:par_bp_redn A B]par_bp_redn (psub N p A) (psub N p B);
intros;Refine par_bp_redn_red1;Refine psub_resp_par_bp_red1;Immed;
intros;Refine par_bp_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save psub_resp_par_bp_redn;

Goal {A,B|Trm}(par_bp_redn A B)->{p|PP}(is_tt (poccur p B))->is_tt (poccur p A);
Refine par_bp_rednRec [A,B:Trm][_:par_bp_redn A B]
                   {p|PP}{pocc:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine par_bp_red1_refl_pocc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save par_bp_redn_refl_pocc;

Goal {A,B|Trm}(par_bp_redn A B)->{p|PP}(is_ff (poccur p A))->is_ff (poccur p B);
intros;Refine B_contrapos;Refine +1 par_bp_redn_refl_pocc;Immed;
Save not_pocc_resp_par_bp_redn;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_bp_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (par_bp_redn_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Equiv (is_tt (orr (PPeq p q) ff))->is_tt ?;
Qrepl PPsym p q;Qrepl neqP;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Immed;
Save par_bp_redn_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_bp_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_bp_redn_alpha_refl_pocc;Immed;
Save not_pocc_resp_par_bp_redn_alpha;

Goal {A,B|Trm}(par_bp_redn A B)->(Vclosed A)->(Vclosed B);
Refine par_bp_rednRec [A,B:Trm][_:par_bp_redn A B](Vclosed A)->(Vclosed B);
intros;Refine Vclosed_resp_par_bp_red1;Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Save Vclosed_resp_par_bp_redn;

(* introduce auxiliary relation which simplifies this: usual *-trick *)
$[par_bp_aredn:Trm->Trm->Prop]; 
$[par_bp_aredn_red1:{A,B|Trm}(par_bp_red1 A B)->par_bp_aredn A B];
$[par_bp_aredn_trans_red1 : {A,D,B|Trm}(par_bp_red1 A D)->(par_bp_aredn D B)->par_bp_aredn A B];

$[par_bp_arednRec:{C:{A,B|Trm}(par_bp_aredn A B)->Prop}

	      {RED1:{A,B|Trm}{r:par_bp_red1 A B}C (par_bp_aredn_red1 r)} 

	      {TRANS_RED1:{A,D,B|Trm}
                          {lt_prem:par_bp_red1 A D}
                          {lt_ih:C  (par_bp_aredn_red1 lt_prem)}
		          {rt_prem:par_bp_aredn D B}{rt_ih:C rt_prem}
		           C (par_bp_aredn_trans_red1 lt_prem rt_prem)}

	      {A,B|Trm}{r:par_bp_aredn A B}C r];


Goal {A,B|Trm}(par_bp_aredn A B)->par_bp_redn A B;
Refine par_bp_arednRec [A,B|Trm][_:par_bp_aredn A B]par_bp_redn A B;
intros;Refine par_bp_redn_red1;Immed;
intros;Refine par_bp_redn_trans;Immed;
Save par_bp_aredn_redn;

Goal {A,D,B|Trm}{lt_prem:par_bp_aredn A D}{rt_prem:par_bp_aredn D B}par_bp_aredn A B;
intros;
Refine par_bp_arednRec [A,D|Trm][_:par_bp_aredn A D]
                    {B|Trm}{rt_prem:par_bp_aredn D B}par_bp_aredn A B;Immed;
intros;Refine par_bp_aredn_trans_red1;Immed;
intros;Refine par_bp_aredn_trans_red1;Refine +2 rt_ih;Immed;
Save par_bp_aredn_trans;

Goal {A,B|Trm}(par_bp_redn A B)->par_bp_aredn A B;
Refine par_bp_rednRec [A,B|Trm][_:par_bp_redn A B]par_bp_aredn A B;
intros;Refine par_bp_aredn_red1;Immed;
intros;Refine par_bp_aredn_trans;Immed;
Save par_bp_redn_aredn;

Goal {A,B|Trm}(par_redn A B)->par_bp_redn A B;
Refine par_rednRec [A,B|Trm]par_bp_redn A B;
intros;Refine par_bp_redn_red1;Refine par_red1_bp_red1;Immed;
intros;Refine par_bp_redn_trans;Immed;
Save par_redn_bp_redn;

(* need to show constructors are inherited by par_bp_redn from red1 *)
Goal {A,A'|Trm}(par_bp_redn A A')->
     {v:VV}{B:Trm}par_bp_redn (pi v A B) (pi v A' B);
Refine par_bp_rednRec [A,A'|Trm][_:par_bp_redn A A']
                   {v:VV}{B:Trm}par_bp_redn (pi v A B) (pi v A' B);
intros;Refine par_bp_redn_red1;Refine par_bp_ared1_red1;Refine par_bp_ared1_pi;
Refine par_bp_red1_ared1;Immed;
intros;Refine par_bp_ared1_refl;
intros;Refine par_bp_redn_trans;Immed;
Save par_bp_redn_pi_l;

Goal {A,A'|Trm}(par_bp_redn A A')->
     {v:VV}{B:Trm}par_bp_redn (lda v A B) (lda v A' B);
Refine par_bp_rednRec [A,A'|Trm][_:par_bp_redn A A']
                   {v:VV}{B:Trm}par_bp_redn (lda v A B) (lda v A' B);
intros;Refine par_bp_redn_red1;Refine par_bp_ared1_red1;Refine par_bp_ared1_lda;
Refine par_bp_red1_ared1;Immed;
intros;Refine par_bp_ared1_refl;
intros;Refine par_bp_redn_trans;Immed;
Save par_bp_redn_lda_l;

Goal {M,M'|Trm}(par_bp_redn M M')->{N:Trm}par_bp_redn (app M N) (app M' N);
Refine par_bp_rednRec [M,M'|Trm][_:par_bp_redn M M']
                                   {N:Trm}par_bp_redn (app M N) (app M' N);
intros;Refine par_bp_redn_red1;Refine par_bp_red1_app r (par_bp_red1_refl ?);
intros;Refine par_bp_redn_trans;Immed;
Save par_bp_redn_app_l;

Goal {N,N'|Trm}(par_bp_redn N N')->{M:Trm}par_bp_redn (app M N) (app M N');
Refine par_bp_rednRec [N,N'|Trm][_:par_bp_redn N N']{M:Trm}par_bp_redn (app M N) (app M N');
intros;Refine par_bp_redn_red1;Refine par_bp_red1_app (par_bp_red1_refl ?) r;
intros;Refine par_bp_redn_trans;Immed;
Save par_bp_redn_app_r;

Goal {M,M',N,N'|Trm}(par_bp_redn M M')->(par_bp_redn N N')->
         par_bp_redn (app M N) (app M' N');
intros;Refine par_bp_redn_trans;
Refine +1 par_bp_redn_app_l;Refine +2 par_bp_redn_app_r;Immed;
Save par_bp_redn_app;

Goal {X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:par_bp_redn (alpha p u X) (alpha p v X')}
     {Y:Trm}par_bp_redn (pi u Y X) (pi v Y X');
intros;
Refine par_bp_rednRec [B,B'|Trm][_:par_bp_redn B B']{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                 {A:Trm}par_bp_redn (pi u A X) (pi v A X');Immed;
intros;Refine par_bp_redn_red1;Refine par_bp_red1_pi (par_bp_red1_refl ?);Immed;
       Qrepl Q_sym(Trm_eq_subst eqB);Qrepl Q_sym(Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine par_bp_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;    

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save par_bp_redn_pi_r;

Goal {X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:par_bp_redn (alpha p u X) (alpha p v X')}
     {Y:Trm}par_bp_redn (lda u Y X) (lda v Y X');
intros;
Refine par_bp_rednRec [B,B'|Trm][_:par_bp_redn B B']{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                 {A:Trm}par_bp_redn (lda u A X) (lda v A X');Immed;
intros;Refine par_bp_redn_red1;Refine par_bp_red1_lda (par_bp_red1_refl ?);Immed;
       Qrepl Q_sym(Trm_eq_subst eqB);Qrepl Q_sym(Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine par_bp_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;    

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save par_bp_redn_lda_r;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:par_bp_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:par_bp_redn (alpha p u B) (alpha p v B')}
      par_bp_redn (pi u A B) (pi v A' B');
intros;Refine par_bp_redn_trans;
Refine +1 par_bp_redn_pi_l;Refine +2 par_bp_redn_pi_r;Immed;
Save par_bp_redn_pi;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:par_bp_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:par_bp_redn (alpha p u B) (alpha p v B')}
      par_bp_redn (lda u A B) (lda v A' B');
intros;Refine par_bp_redn_trans;
Refine +1 par_bp_redn_lda_l;Refine +2 par_bp_redn_lda_r;Immed;
Save par_bp_redn_lda;

Goal {A,M,N,M',N'|Trm}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:par_bp_redn (alpha p u M) (alpha p v M')}{redN:par_bp_redn N N'}
      par_bp_redn (app (pi u A M) N) (vsub N' v M');
intros;Refine par_bp_redn_trans;
       Refine +2 par_bp_redn_red1;Refine +2 par_bp_red1_pcon; 
Refine par_bp_redn_app;Refine par_bp_redn_pi;Refine par_bp_redn_refl;Immed;
Refine par_bp_red1_refl;Refine par_bp_red1_refl;
Save par_bp_redn_pcon;

Goal {A,M,N,M',N'|Trm}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:par_bp_redn (alpha p u M) (alpha p v M')}{redN:par_bp_redn N N'}
      par_bp_redn (app (lda u A M) N) (vsub N' v M');
intros;Refine par_bp_redn_trans;
       Refine +2 par_bp_redn_red1;Refine +2 par_bp_red1_beta; 
Refine par_bp_redn_app;Refine par_bp_redn_lda;Refine par_bp_redn_refl;Immed;
Refine par_bp_red1_refl;Refine par_bp_red1_refl;
Save par_bp_redn_beta;

Goal {p|PP}{M|Trm}(Vclosed M)->
     {N,N'|Trm}(par_bp_redn N N')->(Vclosed N)->
      par_bp_redn (psub N p M) (psub N' p M);
intros ___;
Refine par_bp_rednRec [N,N'|Trm][_:par_bp_redn N N']{vcl:Vclosed N}
                    par_bp_redn (psub N p M) (psub N' p M);
intros;Refine par_bp_redn_red1;Refine par_bp_red1_refl_psub_lem;Immed;
intros;[vclD = Vclosed_resp_par_bp_redn lt_prem vcl : Vclosed D];
Refine par_bp_redn_trans (lt_ih vcl) (rt_ih vclD);
Save par_bp_redn_refl_psub_lem;

Goal {p|PP}{M,M'|Trm}(par_bp_red1 M M')->(Vclosed M)->
     {N,N'|Trm}(par_bp_redn N N')->(Vclosed N)->
      par_bp_redn (psub N p M) (psub N' p M');
intros;
Refine par_bp_rednRec [N,N'|Trm][_:par_bp_redn N N']{vcl:Vclosed N}
                   {M,M'|Trm}{par_bp_redM:par_bp_red1 M M'}{vclM:Vclosed M}
                    par_bp_redn (psub N p M) (psub N' p M');Immed;
intros;Refine par_bp_redn_red1;Refine par_bp_red1_psub;Immed;
intros;
[vclD = Vclosed_resp_par_bp_redn lt_prem vcl : Vclosed D];
Refine par_bp_redn_trans (lt_ih vcl (par_bp_red1_refl ?) vclM)
                      (rt_ih vclD par_bp_redM vclM);
Save par_bp_redn_red1_psub_lem;

Goal {p|PP}{N,N'|Trm}(par_bp_redn N N')->(Vclosed N)->
     {X,X'|Trm}(par_bp_redn X X')->(Vclosed X)->par_bp_redn (psub N p X) (psub N' p X');
intros;
Refine par_bp_rednRec [M,M'|Trm][_:par_bp_redn M M']{vcl:Vclosed M}
                   {N,N'|Trm}{par_bp_redN:par_bp_redn N N'}{vclN:Vclosed N}
                    par_bp_redn (psub N p M) (psub N' p M');Immed;
intros;Refine par_bp_redn_red1_psub_lem;Immed;
intros;
[vclD = Vclosed_resp_par_bp_redn lt_prem vcl : Vclosed D];
Refine par_bp_redn_trans (lt_ih vcl (par_bp_redn_refl ?) vclN)
                      (rt_ih vclD par_bp_redN vclN);
Save par_bp_redn_psub;

Goal {s|SS}{A|Trm}{r:par_bp_red1 (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine par_bp_red1Rec [A,A'|Trm][_:par_bp_red1 A A']
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save par_bp_red1_sort_character;

Goal {s|SS}{A|Trm}{r:par_bp_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine par_bp_rednRec [A,A'|Trm][_:par_bp_redn A A']
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Refine par_bp_red1_sort_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save par_bp_redn_sort_character;

Goal {p|PP}{A|Trm}{r:par_bp_red1 (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine par_bp_red1Rec [A,A'|Trm][_:par_bp_red1 A A']
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save par_bp_red1_par_character;

Goal {p|PP}{A|Trm}{r:par_bp_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine par_bp_rednRec [A,A'|Trm][_:par_bp_redn A A']
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine par_bp_red1_par_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save par_bp_redn_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:par_bp_redn (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_bp_redn A A')
           ({p:PP}par_bp_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine par_bp_rednRec [P,P':Trm][_:par_bp_redn P P']
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_bp_redn A A')
                   ({p:PP}par_bp_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));Immed;

intros;Refine par_bp_red1_pi_character (?:par_bp_red1 (pi w1 A2 B2) B1);
Qrepl Trm_eq_subst eq;Refine r;
intros w' A' B' hyp;Refine Ex3In w' A' B';Refine pair3;
Refine par_bp_redn_red1 (and3_out1 hyp);
intros;Refine par_bp_redn_red1;Refine and3_out2 hyp;
Refine and3_out3 hyp;
intros;Refine lt_ih eq;
intros w' A' B' hyp;Refine rt_ih (and3_out3 hyp);
intros w'' A'' B'' hyp';Refine Ex3In w'' A'' B'';Refine pair3;
Refine par_bp_redn_trans (and3_out1 hyp) (and3_out1 hyp'); 
intros;
[redB = and3_out2 hyp][redB' = and3_out2 hyp'];
[noccB' = not_pocc_resp_par_bp_redn_alpha redB];
Refine par_bp_redn_trans;Immed;
Refine and3_out3 hyp';
Refine Trm_eq_refl;
Save par_bp_redn_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:par_bp_redn (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_bp_redn A A')
           ({p:PP}par_bp_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine par_bp_rednRec [P,P':Trm][_:par_bp_redn P P']
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq (lda w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_bp_redn A A')
                   ({p:PP}par_bp_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') P'));Immed;

intros;Refine par_bp_red1_lda_character (?:par_bp_red1 (lda w1 A2 B2) B1);
Qrepl Trm_eq_subst eq;Refine r;
intros w' A' B' hyp;Refine Ex3In w' A' B';Refine pair3;
Refine par_bp_redn_red1 (and3_out1 hyp);
intros;Refine par_bp_redn_red1;Refine and3_out2 hyp;
Refine and3_out3 hyp;
intros;Refine lt_ih eq;
intros w' A' B' hyp;Refine rt_ih (and3_out3 hyp);
intros w'' A'' B'' hyp';Refine Ex3In w'' A'' B'';Refine pair3;
Refine par_bp_redn_trans (and3_out1 hyp) (and3_out1 hyp'); 
intros;
[redB = and3_out2 hyp][redB' = and3_out2 hyp'];
[noccB' = not_pocc_resp_par_bp_redn_alpha redB];
Refine par_bp_redn_trans;Immed;
Refine and3_out3 hyp';
Refine Trm_eq_refl;
Save par_bp_redn_lda_character;
