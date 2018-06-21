Module ipar_red 
Import churchrosser
       wh_red;

(* the internal parallel one-step reduction relation,
   the inductive complement to weak-head reduction   *)

Inductive [ipar_red1 : Trm->Trm->Prop]

Constructors

[ipar_red1_refl_sort : {s:SS} ipar_red1 (sort s) (sort s)]
[ipar_red1_refl_par : {p:PP} ipar_red1 (par p) (par p)]

[ipar_red1_pi:{A,A'|Trm}{premA:par_red1 A A'}
              {u,v|VV}{B,B'|Trm}{p|PP}
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
              {premB:par_red1 (alpha p u B) (alpha p v B')}
               ipar_red1 (pi u A B) (pi v A' B')]

[ipar_red1_lda:{A,A'|Trm}{premA:par_red1 A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:par_red1 (alpha p u B) (alpha p v B')}
                ipar_red1 (lda u A B) (lda v A' B')]

[ipar_red1_app:{A,A'|Trm}{premA:ipar_red1 A A'}
               {B,B'|Trm}{premB:par_red1 B B'}
                ipar_red1 (app A B) (app A' B')];

Goal ipar_red1Rec:{C:{A,B:Trm}Prop}

	      {REFL_SORT:{s:SS}C (sort s) (sort s)}

	      {REFL_PAR:{p:PP}C (par p) (par p)}

	      {PI:{A,A'|Trm}{premA:par_red1 A A'}
                  {u,v|VV}{B,B'|Trm}{p|PP}
                  {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                  {premB:par_red1 (alpha p u B) (alpha p v B')}
	           C (pi u A B) (pi v A' B')}

	      {LDA:{A,A'|Trm}{premA:par_red1 A A'}
                   {u,v|VV}{B,B'|Trm}{p|PP}
                   {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                   {premB:par_red1 (alpha p u B) (alpha p v B')}
	            C (lda u A B) (lda v A' B')}

	      {APP:{A,A'|Trm}{premA:ipar_red1 A A'}{ihA:C A A'}
                   {B,B'|Trm}{premB:par_red1 B B'}
                    C (app A B) (app A' B')}

	      {A,B|Trm}{red:ipar_red1 A B}C A B;

intros;Refine ipar_red1_elim [A,B|Trm][_:ipar_red1 A B]C A B;Immed;
(* intros;Immed; *)
(* intros;Immed; *)
(* intros;Refine PI;Immed; *)
(* intros;Refine LDA;Immed; *)
intros;Refine APP;Immed;
Save;

Goal {A,A'|Trm}(ipar_red1 A A')->par_red1 A A';
Refine ipar_red1Rec [A,A':Trm]par_red1 A A';
intros;Refine par_red1_refl_sort;
intros;Refine par_red1_refl_par;
intros;Refine par_red1_pi;Immed;
intros;Refine par_red1_lda;Immed;
intros;Refine par_red1_app;Immed;
Save ipar_par_red1;

Goal {A,B|Trm}(ipar_red1 A B)-> and (Vclosed A) (Vclosed B);
intros;Refine par_red1_Vclosed;Refine ipar_par_red1;Immed;
Save ipar_red1_Vclosed;

Goal ipar_red1_refl : {A|Trm}(Vclosed A)->ipar_red1 A A;
intros;Refine aVclosedRec [A|Trm][_:aVclosed A]ipar_red1 A A;
intros;Refine ipar_red1_refl_sort;
intros;Refine ipar_red1_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine ipar_red1_pi;
	Refine par_red1_refl (aVclosed_Vclosed ?);
	Refine +4 par_red1_refl (aVclosed_Vclosed ?);Immed;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine ipar_red1_lda;
	Refine par_red1_refl (aVclosed_Vclosed ?);
	Refine +4 par_red1_refl (aVclosed_Vclosed ?);Immed;
intros;Refine ipar_red1_app;
	Refine +1 par_red1_refl (aVclosed_Vclosed ?);Immed;
Refine Vclosed_aVclosed;Immed;
Save;

Goal {A,A'|Trm}(ipar_red1 A A')->Q (isSrt A) (isSrt A');
Refine ipar_red1Rec [A,A'|Trm]Q (isSrt A) (isSrt A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save ipar_red1_shape_sort;

Goal {A,A'|Trm}(ipar_red1 A A')->Q (isPar A) (isPar A');
Refine ipar_red1Rec [A,A'|Trm]Q (isPar A) (isPar A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save ipar_red1_shape_par;

Goal {A,A'|Trm}(ipar_red1 A A')->Q (isPi A) (isPi A');
Refine ipar_red1Rec [A,A'|Trm]Q (isPi A) (isPi A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save ipar_red1_shape_pi;

Goal {A,A'|Trm}(ipar_red1 A A')->Q (isLda A) (isLda A');
Refine ipar_red1Rec [A,A'|Trm]Q (isLda A) (isLda A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save ipar_red1_shape_lda;

Goal {A,A'|Trm}(ipar_red1 A A')->Q (isApp A) (isApp A');
Refine ipar_red1Rec [A,A'|Trm]Q (isApp A) (isApp A');
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save ipar_red1_shape_app;

Inductive [ipar_ared1 : Trm->Trm->Prop]

Constructors

[ipar_ared1_refl_sort : {s:SS} ipar_ared1 (sort s) (sort s)]
[ipar_ared1_refl_par : {p:PP} ipar_ared1 (par p) (par p)]

[ipar_ared1_pi:{A,A'|Trm}{premA:par_red1 A A'}
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
                ipar_ared1 (pi u A B) (pi v A' B')]

[ipar_ared1_lda:{A,A'|Trm}{premA:par_red1 A A'}
                {u,v|VV}{B,B'|Trm}
                {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
                 ipar_ared1 (lda u A B) (lda v A' B')]

[ipar_ared1_app:{A,A'|Trm}{premA:ipar_ared1 A A'}
                {B,B'|Trm}{premB:par_red1 B B'}
                 ipar_ared1 (app A B) (app A' B')]

NoReductions;

Goal {A,B|Trm}(ipar_ared1 A B)->ipar_red1 A B;
Refine ipar_ared1_elim [A,B:Trm][_:ipar_ared1 A B]ipar_red1 A B;
intros;Refine ipar_red1_refl_sort;
intros;Refine ipar_red1_refl_par;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine ipar_red1_pi;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine ipar_red1_lda;Immed;
intros;Refine ipar_red1_app;Immed;
Save ipar_ared1_red1;

Goal {A,B|Trm}(ipar_red1 A B)->{rho:Renaming}ipar_ared1 (renTrm rho A) (renTrm rho B);
Refine ipar_red1Rec [A,B:Trm]
                   {rho:Renaming}ipar_ared1 (renTrm rho A) (renTrm rho B);
intros;Refine ipar_ared1_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine ipar_ared1_refl_par;

intros;
Equiv ipar_ared1 (pi u (renTrm rho A) (renTrm rho B))
                 (pi v (renTrm rho A') (renTrm rho B'));
Refine ipar_ared1_pi;Refine renTrm_resp_par_red1;Immed;
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
Refine renTrm_resp_par_red1;Immed;
[sigma = CONS (Pr p q) rho:Renaming];
Refine ExIn sigma;Refine pair3;
Equiv Q (if (PPeq p p) q ?) q;Qrepl PPrefl p;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB';Refine Q_refl;

intros;
Equiv ipar_ared1 (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine ipar_ared1_lda;Refine renTrm_resp_par_red1;Immed;
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
Refine renTrm_resp_par_red1;Immed;
[sigma = CONS (Pr p q) rho:Renaming];
Refine ExIn sigma;Refine pair3;
Equiv Q (if (PPeq p p) q ?) q;Qrepl PPrefl p;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
Qrepl triv_renTrm_lem rho q noccB';Refine Q_refl;

intros;
Equiv ipar_ared1 (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine ipar_ared1_app;Refine +1 renTrm_resp_par_red1;Immed;

Save ipar_red1_ared1_lem;

Goal {A,B|Trm}(ipar_red1 A B)->ipar_ared1 A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine ipar_red1_ared1_lem H renId;
Save ipar_red1_ared1;

Goal {A,B|Trm}(ipar_red1 A B)->{rho:Renaming}ipar_red1 (renTrm rho A) (renTrm rho B);
intros;Refine ipar_ared1_red1;Refine ipar_red1_ared1_lem;Immed;
Save renTrm_resp_ipar_red1;

Goal ipar_ared1Rec:{C:{A,B:Trm}Prop}

	      {REFL_SORT:{s:SS}C (sort s) (sort s)}

	      {REFL_PAR:{p:PP}C (par p) (par p)}

	      {PI:{A,A'|Trm}{premA:par_red1 A A'}
                   {u,v|VV}{B,B'|Trm}
                   {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
                    C (pi u A B) (pi v A' B')}

	       {LDA:{A,A'|Trm}{premA:par_red1 A A'}
                    {u,v|VV}{B,B'|Trm}
                    {premB:{p:PP}par_red1 (alpha p u B) (alpha p v B')}
                     C (lda u A B) (lda v A' B')}

	       {APP:{A,A'|Trm}{premA:ipar_red1 A A'}{ihA:C A A'}
                    {B,B'|Trm}{premB:par_red1 B B'}
                     C (app A B) (app A' B')}

	       {A,B|Trm}{red:ipar_red1 A B}C A B;

intros;Refine ipar_ared1_elim [A,B|Trm][_:ipar_ared1 A B]C A B;Immed;
(* intros;Refine PI;Immed; *)
(* intros;Refine LDA;Immed; *)
intros;Refine APP;Refine ipar_ared1_red1;Immed;
Refine ipar_red1_ared1;Immed;
Save;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(ipar_red1 X Y)->ipar_red1 (psub N p X) (psub N p Y);
intros ___;
Refine ipar_ared1Rec [A,B:Trm]ipar_red1 (psub N p A) (psub N p B);

intros;Refine ipar_red1_refl_sort;

intros;Equiv [M = if (PPeq p p1) N (par p1)]ipar_red1 M M;
Refine tt_or_ff (PPeq p p1);
intros eqP;Qrepl eqP;Refine ipar_red1_refl;Immed;
intros neqP;Qrepl neqP;Refine ipar_red1_refl_par;

intros;
Equiv ipar_red1 (pi u (psub N p A) (psub N p B))
                (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine ipar_red1_pi;Refine psub_resp_par_red1;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine psub_resp_par_red1;Immed;

intros;
Equiv ipar_red1 (lda u (psub N p A) (psub N p B))
                (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccB noccB';
Refine ipar_red1_lda;Refine psub_resp_par_red1;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqP v B');
Refine psub_resp_par_red1;Immed;

intros;
Equiv ipar_red1 (app (psub N p A) (psub N p B))
                (app (psub N p A') (psub N p B'));
Refine ipar_red1_app;Refine +1 psub_resp_par_red1;Immed;

Save psub_resp_ipar_red1;

Goal {X,Y|Trm}(ipar_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros;Refine par_red1_refl_pocc;Refine +1 ipar_par_red1;Immed;
Save ipar_red1_refl_pocc;

Goal {X,Y|Trm}(ipar_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 ipar_red1_refl_pocc;Immed;
Save not_pocc_resp_ipar_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}ipar_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;Refine par_red1_alpha_refl_pocc;
intros +3 q;Refine ipar_par_red1;Immed;
Immed;
Save ipar_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}ipar_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 ipar_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_ipar_red1_alpha;

(* Goal {N,N',N''|Trm} *)
(*      {par_redN:par_red1 N N''} *)
(*      {wh_redN:wh_redn N N'} *)
(*      {ipar_redN:ipar_red1 N' N''} *)
(*      {vclN:Vclosed N}{p:PP} *)
(*      {M|Trm}(Vclosed M)-> *)
(*       Ex [P:Trm]and (wh_redn (psub N p M) P) (ipar_red1 P (psub N'' p M)); *)
(* intros __________;[subN = psub N p][subN'' = psub N'' p]; *)
(* [vclN' = Vclosed_resp_wh_redn wh_redN vclN : Vclosed N']; *)
(* [vclN'' = snd (ipar_red1_Vclosed ipar_redN) : Vclosed N'']; *)
(* Refine aVclosedRec [A:Trm][_:aVclosed A] *)
(*       Ex [P:Trm]and (wh_redn (subN A) P) (ipar_red1 P (subN'' A)); *)
(* intros;Refine ExIn (sort s);Refine pair; *)
(* Refine wh_redn_refl;Refine ipar_red1_refl_sort; *)

(* intros;Equiv Ex [P:Trm]and (wh_redn (if ? ? ?) P) *)
(*                            (ipar_red1 P (if ? ? ?)); *)
(* Refine tt_or_ff (PPeq p p1); *)
(* intros case;Qrepl case;Refine ExIn N';Refine pair;Immed; *)
(* intros case;Qrepl case;Refine ExIn (par p1);Refine pair; *)
(* Refine wh_redn_refl;Refine ipar_red1_refl_par; *)

(* intros;Equiv Ex [P:Trm]and (wh_redn (pi n (subN A) (subN B)) P) *)
(*                            (ipar_red1 P (pi n (subN'' A) (subN'' B))); *)
(* Refine fresh_params_lem2p p N B; *)
(* intros q qFresh;Refine qFresh; *)
(* intros neqP noccN noccB; *)
(* Refine ExIn ?;Refine +1 pair (wh_redn_refl ?); *)
(* Refine ipar_red1_pi; *)
(* Refine par_red1_refl_psub_lem;Refine +1 aVclosed_Vclosed;Immed; *)
(* Refine not_pocc_psub_lem noccB noccN; *)
(* Refine not_pocc_psub_lem noccB (not_pocc_resp_par_red1 par_redN noccN); *)
(* Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); *)
(* Qrepl Trm_eq_subst (alpha_psub_commutes vclN'' neqP n B); *)
(* Refine par_red1_refl_psub_lem;Refine +1 aVclosed_Vclosed;Immed; *)

(* intros;Equiv Ex [P:Trm]and (wh_redn (lda n (subN A) (subN B)) P) *)
(*                            (ipar_red1 P (lda n (subN'' A) (subN'' B))); *)
(* Refine fresh_params_lem2p p N B; *)
(* intros q qFresh;Refine qFresh; *)
(* intros neqP noccN noccB; *)
(* Refine ExIn ?;Refine +1 pair (wh_redn_refl ?); *)
(* Refine ipar_red1_lda; *)
(* Refine par_red1_refl_psub_lem;Refine +1 aVclosed_Vclosed;Immed; *)
(* Refine not_pocc_psub_lem noccB noccN; *)
(* Refine not_pocc_psub_lem noccB (not_pocc_resp_par_red1 par_redN noccN); *)
(* Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B); *)
(* Qrepl Trm_eq_subst (alpha_psub_commutes vclN'' neqP n B); *)
(* Refine par_red1_refl_psub_lem;Refine +1 aVclosed_Vclosed;Immed; *)

(* intros;Equiv Ex [P:Trm]and (wh_redn (app (subN A) (subN B)) P) *)
(*                            (ipar_red1 P (app (subN'' A) (subN'' B))); *)
(* Refine ihA; *)
(* intros subNA hypA;Refine hypA; *)
(* intros wh_redA ipar_redA;Refine ExIn (app subNA (subN B));Refine pair; *)
(* Refine wh_redn_app;Refine +1 ipar_red1_app; *)
(* Refine +2 par_red1_refl_psub_lem;Refine +3 aVclosed_Vclosed;Immed; *)

(* Refine Vclosed_aVclosed;Immed; *)
(* Save wh_ipar_red1_refl_psub_lem; *)

(*******
Goal {N,N',N''|Trm}
     {par_redN:par_red1 N N''}
     {wh_redN:wh_redn N N'}
     {ipar_redN:ipar_red1 N' N''}
     {p:PP}
     {X,X'|Trm}(ipar_red1 X X')->
      Ex [P:Trm]and (wh_redn (psub N p X) P) (ipar_red1 P (psub N'' p X'));

intros _______;[subN = psub N p][subN'' = psub N'' p];
[vclN = fst (par_red1_Vclosed par_redN) : Vclosed N];
[vclN' = Vclosed_resp_wh_redn wh_redN vclN : Vclosed N'];
[vclN'' = snd (ipar_red1_Vclosed ipar_redN) : Vclosed N''];
Refine ipar_ared1Rec [M,M'|Trm]
       Ex [P:Trm]and (wh_redn (psub N p M) P) (ipar_red1 P (psub N'' p M'));

(* refl_sort *)
intros;Refine ExIn (sort s);Refine pair;
Refine wh_redn_refl;Refine ipar_red1_refl_sort;

(* refl_par *)
intros;Equiv Ex [P:Trm]and (wh_redn (if ? ? ?) P)
                           (ipar_red1 P (if ? ? ?));
Refine tt_or_ff (PPeq p p1);
intros case;Qrepl case;Refine ExIn N';Refine pair;Immed;
intros case;Qrepl case;Refine ExIn (par p1);Refine pair;
Refine wh_redn_refl;Refine ipar_red1_refl_par;

(* pi *)
intros;
Equiv Ex [P:Trm]and (wh_redn (pi u (subN A) (subN B)) P)
                    (ipar_red1 P (pi v (subN'' A') (subN'' B')));
Refine fresh_params_lem4p p N N'' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN'' noccB noccB';
Refine ExIn ?;Refine +1 pair (wh_redn_refl ?);
Refine ipar_red1_pi;
Refine par_red1_psub;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN'';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN'' neqP v B');
Refine par_red1_psub;Immed;

(* lda *)
intros;
Equiv Ex [P:Trm]and (wh_redn (lda u (subN A) (subN B)) P)
                    (ipar_red1 P (lda v (subN'' A') (subN'' B')));
Refine fresh_params_lem4p p N N'' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN'' noccB noccB';
Refine ExIn ?;Refine +1 pair (wh_redn_refl ?);
Refine ipar_red1_lda;
Refine par_red1_psub;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN'';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN'' neqP v B');
Refine par_red1_psub;Immed;

(* app *)
intros;
Equiv Ex [P:Trm]and (wh_redn (app (subN A) (subN B)) P)
                    (ipar_red1 P (app (subN'' A') (subN'' B')));
Refine ihA;
intros subNA hypA;Refine hypA;
intros wh_redA ipar_redA;Refine ExIn (app subNA (subN B));Refine pair;
Refine wh_redn_app;Refine +1 ipar_red1_app;
Refine +2 par_red1_psub;Immed;

Save wh_ipar_red1_psub;
*******)

(* now the characters *)
Goal {w|VV}{A,B,X|Trm}{red_pi:ipar_red1 (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A A')
           ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq X (pi w' A' B')));

intros;Refine ipar_ared1Rec [P,P':Trm]
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_red1 A A')
                   ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq P' (pi w' A' B')));

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
Save ipar_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:ipar_red1 (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A A')
           ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq X (lda w' A' B')));

intros;Refine ipar_ared1Rec [L,L':Trm]
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_red1 A A')
                   ({p:PP}par_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq L' (lda w' A' B')));

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
Save ipar_red1_lda_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:ipar_red1 X (pi w A B)}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A' A)
           ({p:PP}par_red1 (alpha p w' B') (alpha p w B))
           (is_tt (Trm_eq X (pi w' A' B')));
intros;Refine isPi_lem;
Refine +1 Q_subst (Q_sym (ipar_red1_shape_pi red_pi)) is_tt;Refine Q_refl;
intros w' A' B' eqX;Refine ipar_red1_pi_character (?:ipar_red1 (pi w' A' B') ?);
Qrepl +1 Q_sym (Trm_eq_subst eqX);Immed;
intros w1 A1 B1 hyp;Refine hyp;
intros rA rB eq;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;
Qrepl Trm_eq_subst eqA;
Qrepl Trm_eq_subst eqB;
Refine Ex3In;Refine +3 pair3;Immed;
Save ipar_red1_refl_pi;

Goal {w|VV}{A,B,X|Trm}{red_lda:ipar_red1 X (lda w A B)}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_red1 A' A)
           ({p:PP}par_red1 (alpha p w' B') (alpha p w B))
           (is_tt (Trm_eq X (lda w' A' B')));
intros;Refine isLda_lem;
Refine +1 Q_subst (Q_sym (ipar_red1_shape_lda red_lda)) is_tt;Refine Q_refl;
intros w' A' B' eqX;Refine ipar_red1_lda_character (?:ipar_red1 (lda w' A' B') ?);
Qrepl +1 Q_sym (Trm_eq_subst eqX);Immed;
intros w1 A1 B1 hyp;Refine hyp;
intros rA rB eq;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;
Qrepl Trm_eq_subst eqA;
Qrepl Trm_eq_subst eqB;
Refine Ex3In;Refine +3 pair3;Immed;
Save ipar_red1_refl_lda;

Goal {M,N,X|Trm}{red_app:ipar_red1 (app M N) X}
      Ex2 [M',N':Trm]
          and3 (ipar_red1 M M')
               (par_red1 N N')
               (is_tt (Trm_eq X (app M' N')));
intros;
Refine ipar_red1Rec [X,X'|Trm]
       {eq:is_tt (Trm_eq X (app M N))}
        Ex2 [M',N':Trm]
          and3 (ipar_red1 M M')
               (par_red1 N N')
               (is_tt (Trm_eq X' (app M' N')));Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;Qrepl Q_sym (Trm_eq_subst eqA);Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex2In;Refine +2 pair3 ? ? (Trm_eq_refl ?);Immed;
Refine Trm_eq_refl;
Save ipar_red1_app_character;

Goal {A,B,X|Trm}{red_app:ipar_red1 X (app A B)}
      Ex2 [A',B':Trm]
      and3 (ipar_red1 A' A)
           (par_red1 B' B)
           (is_tt (Trm_eq X (app A' B')));
intros;Refine isApp_lem;
Refine +1 Q_subst (Q_sym (ipar_red1_shape_app red_app)) is_tt;Refine Q_refl;
intros A' B' eqX;Refine ipar_red1_app_character (?:ipar_red1 (app A' B') ?);
Qrepl +1 Q_sym (Trm_eq_subst eqX);Immed;
intros A1 B1 hyp;Refine hyp;
intros rA rB eq;Refine Trm_eq_app_lem eq;
intros eqA eqB;
Qrepl Trm_eq_subst eqA;
Qrepl Trm_eq_subst eqB;
Refine Ex2In;Refine +2 pair3;Immed;
Save ipar_red1_refl_app;

(* now take the transitive closure of ipar_red1 *)
(* and show it equivalent to redn              *)

Inductive [ipar_redn:Trm->Trm->Prop]
Constructors
[ipar_redn_red1:{A,B|Trm}(ipar_red1 A B)->ipar_redn A B]
[ipar_redn_trans : {A,D,B|Trm}{lt_prem:ipar_redn A D}
		           {rt_prem:ipar_redn D B}ipar_redn A B];

Goal ipar_rednRec : {C:{A,B:Trm}Prop}
	 {IPAR_RED1:{A,B|Trm}{r:ipar_red1 A B}C A B}
	 {TRANS:{A,D,B|Trm}{lt_prem:ipar_redn A D}{lt_ih:C A D}
		           {rt_prem:ipar_redn D B}{rt_ih:C D B}
		 C A B}
	 {A,B|Trm}{r:ipar_redn A B}C A B;

intros;Refine ipar_redn_elim [A,B|Trm][_:ipar_redn A B]C A B;Immed;
intros;Refine TRANS;Immed;
Save;

Goal {A|Trm}(Vclosed A)->ipar_redn A A;
intros;Refine ipar_redn_red1;Refine ipar_red1_refl;Immed;
Save ipar_redn_refl;

Goal {A,A'|Trm}(ipar_redn A A')->Q (isSrt A) (isSrt A');
Refine ipar_rednRec [A,A'|Trm]Q (isSrt A) (isSrt A');
intros;Refine ipar_red1_shape_sort;Immed;
intros;Qrepl lt_ih;Qrepl rt_ih;Refine Q_refl;
Save ipar_redn_shape_sort;

Goal {A,A'|Trm}(ipar_redn A A')->Q (isPar A) (isPar A');
Refine ipar_rednRec [A,A'|Trm]Q (isPar A) (isPar A');
intros;Refine ipar_red1_shape_par;Immed;
intros;Qrepl lt_ih;Qrepl rt_ih;Refine Q_refl;
Save ipar_redn_shape_par;

Goal {A,A'|Trm}(ipar_redn A A')->Q (isPi A) (isPi A');
Refine ipar_rednRec [A,A'|Trm]Q (isPi A) (isPi A');
intros;Refine ipar_red1_shape_pi;Immed;
intros;Qrepl lt_ih;Qrepl rt_ih;Refine Q_refl;
Save ipar_redn_shape_pi;

Goal {A,A'|Trm}(ipar_redn A A')->Q (isLda A) (isLda A');
Refine ipar_rednRec [A,A'|Trm]Q (isLda A) (isLda A');
intros;Refine ipar_red1_shape_lda;Immed;
intros;Qrepl lt_ih;Qrepl rt_ih;Refine Q_refl;
Save ipar_redn_shape_lda;

Goal {A,A'|Trm}(ipar_redn A A')->Q (isApp A) (isApp A');
Refine ipar_rednRec [A,A'|Trm]Q (isApp A) (isApp A');
intros;Refine ipar_red1_shape_app;Immed;
intros;Qrepl lt_ih;Qrepl rt_ih;Refine Q_refl;
Save ipar_redn_shape_app;

Goal {A,B|Trm}(ipar_redn A B)->{rho:Renaming}ipar_redn (renTrm rho A) (renTrm rho B);
Refine ipar_rednRec [A,B:Trm]
	{rho:Renaming}ipar_redn (renTrm rho A) (renTrm rho B);
intros;Refine ipar_redn_red1;Refine renTrm_resp_ipar_red1;Immed;
intros;Refine ipar_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save renTrm_resp_ipar_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(ipar_redn A B)->ipar_redn (psub N p A) (psub N p B);
intros ___;
Refine ipar_rednRec [A,B:Trm]ipar_redn (psub N p A) (psub N p B);
intros;Refine ipar_redn_red1;Refine psub_resp_ipar_red1;Immed;
intros;Refine ipar_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save psub_resp_ipar_redn;

Goal {A,B|Trm}(ipar_redn A B)-> and (Vclosed A) (Vclosed B);
Refine ipar_rednRec [A,B:Trm]and (Vclosed A) (Vclosed B);
intros;Refine ipar_red1_Vclosed;Immed;
intros;Refine rt_ih;
intros;Refine lt_ih;
intros;Refine pair;Immed;
Save ipar_redn_Vclosed;

(* introduce auxiliary relation which simplifies this: usual *-trick *)
Inductive [ipar_aredn:Trm->Trm->Prop] NoReductions Constructors 
[ipar_aredn_red1:{A,B|Trm}(ipar_red1 A B)->ipar_aredn A B]
[ipar_aredn_trans_red1 : {A,D,B|Trm}{lt_prem:ipar_red1 A D}
			{rt_prem:ipar_aredn D B}ipar_aredn A B];

Goal {A,B|Trm}(ipar_aredn A B)->ipar_redn A B;
Refine ipar_aredn_elim [A,B|Trm][_:ipar_aredn A B]ipar_redn A B;
intros;Refine ipar_redn_red1;Immed;
intros;Refine ipar_redn_trans;Refine +1 ipar_redn_red1;Immed;
Save ipar_aredn_redn;

Goal {A,D,B|Trm}{lt_prem:ipar_aredn A D}{rt_prem:ipar_aredn D B}ipar_aredn A B;
intros;
Refine ipar_aredn_elim [A,D|Trm][_:ipar_aredn A D]
                    {B|Trm}{rt_prem:ipar_aredn D B}ipar_aredn A B;Immed;
intros;Refine ipar_aredn_trans_red1;Immed;
intros;Refine ipar_aredn_trans_red1;Refine +2 rt_prem_ih;Immed;
Save ipar_aredn_trans;

Goal {A,B|Trm}(ipar_redn A B)->ipar_aredn A B;
Refine ipar_rednRec [A,B|Trm]ipar_aredn A B;
intros;Refine ipar_aredn_red1;Immed;
intros;Refine ipar_aredn_trans;Immed;
Save ipar_redn_aredn;

Goal ipar_arednRec:{C:{A,B:Trm}Prop}

	      {RED1:{A,B|Trm}{r:ipar_red1 A B}C A B} 

	      {TRANS_RED1:{A,D,B|Trm}
                          {lt_prem:ipar_red1 A D}
                          {rt_prem:ipar_redn D B}{rt_ih:C D B}
		           C A B}

	      {A,B|Trm}{r:ipar_redn A B}C A B;

intros;Refine ipar_aredn_elim [A,B|Trm][_:ipar_aredn A B]C A B;Immed;
intros;Refine TRANS_RED1;Refine +2 ipar_aredn_redn;Immed;
Refine ipar_redn_aredn;Immed;
Save;


Goal {s|SS}{A|Trm}{r:ipar_red1 (sort s) A}is_tt (Trm_eq A (sort s));
intros;Refine par_red1_sort_character;Refine ipar_par_red1;Immed;
Save ipar_red1_sort_character;

Goal {s|SS}{A|Trm}{r:ipar_red1 A (sort s)}is_tt (Trm_eq A (sort s));
intros;Refine ipar_red1Rec [X,X'|Trm]
       {eq:is_tt (Trm_eq X' (sort s))}is_tt (Trm_eq X (sort s));Immed;
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save ipar_red1_refl_sort_lem;

Goal {s|SS}{A|Trm}{r:ipar_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine ipar_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Refine ipar_red1_sort_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save ipar_redn_sort_character;

Goal {s|SS}{A|Trm}{r:ipar_redn A (sort s)}is_tt (Trm_eq A (sort s));
intros;
Refine ipar_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A' (sort s))}is_tt (Trm_eq A (sort s));
Immed;
intros;Refine ipar_red1_refl_sort_lem;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Refine Trm_eq_refl;
Save ipar_redn_refl_sort_lem;

Goal {p|PP}{A|Trm}{r:ipar_red1 (par p) A}is_tt (Trm_eq A (par p));
intros;Refine par_red1_par_character;Refine ipar_par_red1;Immed;
Save ipar_red1_par_character;

Goal {p|PP}{A|Trm}{r:ipar_red1 A (par p)}is_tt (Trm_eq A (par p));
intros;Refine ipar_red1Rec [X,X'|Trm]
       {eq:is_tt (Trm_eq X' (par p))}is_tt (Trm_eq X (par p));Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save ipar_red1_refl_par_lem;

Goal {p|PP}{A|Trm}{r:ipar_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine ipar_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine ipar_red1_par_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save ipar_redn_par_character;

Goal {p|PP}{A|Trm}{r:ipar_redn A (par p)}is_tt (Trm_eq A (par p));
intros;
Refine ipar_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A' (par p))}is_tt (Trm_eq A (par p));
Immed;
intros;Refine ipar_red1_refl_par_lem;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Refine Trm_eq_refl;
Save ipar_redn_refl_par_lem;

Goal {X,Y|Trm}(ipar_redn X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
Refine ipar_rednRec [A,B:Trm]
                    {p|PP}{occur:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine ipar_red1_refl_pocc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save ipar_redn_refl_pocc;

Goal {X,Y|Trm}(ipar_redn X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 ipar_redn_refl_pocc;Immed;
Save not_pocc_resp_ipar_redn;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}ipar_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (ipar_redn_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;
Save ipar_redn_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}ipar_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 ipar_redn_alpha_refl_pocc;Immed;
Save not_pocc_resp_ipar_redn_alpha;

Goal {w|VV}{A,B,X|Trm}{red_pi:ipar_redn (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A A')
           ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq X (pi w' A' B')));

intros;Refine ipar_rednRec [P,P':Trm]
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq P (pi w A B))}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_redn A A')
                   ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq P' (pi w' A' B')));Immed;

intros;Refine ipar_red1_pi_character (?:ipar_red1 (pi w1 A2 B2) B1);
Qrepl Q_sym (Trm_eq_subst eq);Refine r;
intros w' A' B' hyp;Refine Ex3In w' A' B';Refine pair3;
Refine par_redn_red1 (and3_out1 hyp);
intros;Refine par_redn_red1;Refine and3_out2 hyp;
Refine and3_out3 hyp;
intros;Refine lt_ih eq;
intros w' A' B' hyp;Refine rt_ih (and3_out3 hyp);
intros w'' A'' B'' hyp';Refine Ex3In w'' A'' B'';Refine pair3;
Refine par_redn_trans (and3_out1 hyp) (and3_out1 hyp'); 
intros;
[redB = and3_out2 hyp][redB' = and3_out2 hyp'];
Refine par_redn_trans;Immed;
Refine and3_out3 hyp';
Refine Trm_eq_refl;
Save ipar_redn_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:ipar_redn (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A A')
           ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq X (lda w' A' B')));

intros;Refine ipar_rednRec [P,P':Trm]
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq P (lda w A B))}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_redn A A')
                   ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq P' (lda w' A' B')));Immed;

intros;Refine ipar_red1_lda_character (?:ipar_red1 (lda w1 A2 B2) B1);
Qrepl Q_sym (Trm_eq_subst eq);Refine r;
intros w' A' B' hyp;Refine Ex3In w' A' B';Refine pair3;
Refine par_redn_red1 (and3_out1 hyp);
intros;Refine par_redn_red1;Refine and3_out2 hyp;
Refine and3_out3 hyp;
intros;Refine lt_ih eq;
intros w' A' B' hyp;Refine rt_ih (and3_out3 hyp);
intros w'' A'' B'' hyp';Refine Ex3In w'' A'' B'';Refine pair3;
Refine par_redn_trans (and3_out1 hyp) (and3_out1 hyp'); 
intros;
[redB = and3_out2 hyp][redB' = and3_out2 hyp'];
Refine par_redn_trans;Immed;
Refine and3_out3 hyp';
Refine Trm_eq_refl;
Save ipar_redn_lda_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:ipar_redn X (pi w A B)}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A' A)
           ({p:PP}par_redn (alpha p w' B') (alpha p w B))
           (is_tt (Trm_eq X (pi w' A' B')));
intros;Refine isPi_lem;
Refine +1 Q_subst (Q_sym (ipar_redn_shape_pi red_pi)) is_tt;Refine Q_refl;
intros w' A' B' eqX;Refine ipar_redn_pi_character (?:ipar_redn (pi w' A' B') ?);
Qrepl +1 Q_sym (Trm_eq_subst eqX);Immed;
intros w1 A1 B1 hyp;Refine hyp;
intros rA rB eq;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;
Qrepl Trm_eq_subst eqA;
Qrepl Trm_eq_subst eqB;
Refine Ex3In;Refine +3 pair3;Immed;
Save ipar_redn_refl_pi;

Goal {w|VV}{A,B,X|Trm}{red_lda:ipar_redn X (lda w A B)}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A' A)
           ({p:PP}par_redn (alpha p w' B') (alpha p w B))
           (is_tt (Trm_eq X (lda w' A' B')));
intros;Refine isLda_lem;
Refine +1 Q_subst (Q_sym (ipar_redn_shape_lda red_lda)) is_tt;Refine Q_refl;
intros w' A' B' eqX;Refine ipar_redn_lda_character (?:ipar_redn (lda w' A' B') ?);
Qrepl +1 Q_sym (Trm_eq_subst eqX);Immed;
intros w1 A1 B1 hyp;Refine hyp;
intros rA rB eq;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;
Qrepl VVdecide eqV;
Qrepl Trm_eq_subst eqA;
Qrepl Trm_eq_subst eqB;
Refine Ex3In;Refine +3 pair3;Immed;
Save ipar_redn_refl_lda;

Goal {N,Nw,N'|Trm}
     {par_redN:par_red1 N N'}
     {wh_redN:wh_redn N Nw}
     {ipar_redN:ipar_red1 Nw N'}
     {p:PP}
     {X,X'|Trm}(ipar_red1 X X')->
      Ex [P:Trm]and (wh_redn (psub N p X) P) (ipar_red1 P (psub N' p X'));

intros _______;[subN = psub N p][subN' = psub N' p];
[vclN = fst (par_red1_Vclosed par_redN) : Vclosed N];
[vclNw = Vclosed_resp_wh_redn wh_redN vclN : Vclosed Nw];
[vclN' = snd (ipar_red1_Vclosed ipar_redN) : Vclosed N'];
Refine ipar_ared1Rec [M,M'|Trm]
       Ex [P:Trm]and (wh_redn (subN M) P) (ipar_red1 P (subN' M'));

(* refl_sort *)
intros;Refine ExIn (sort s);Refine pair;
Refine wh_redn_refl;Refine ipar_red1_refl_sort;

(* refl_par *)
intros;Equiv Ex [P:Trm]and (wh_redn (if ? ? ?) P)
                           (ipar_red1 P (if ? ? ?));
Refine tt_or_ff (PPeq p p1);
intros case;Qrepl case;Refine ExIn;Refine +1 pair;Immed;
intros case;Qrepl case;Refine ExIn (par p1);Refine pair;
Refine wh_redn_refl;Refine ipar_red1_refl_par;

(* pi *)
intros;
Equiv Ex [P:Trm]and (wh_redn (pi u (subN A) (subN B)) P)
                    (ipar_red1 P (pi v (subN' A') (subN' B')));
Refine fresh_params_lem4p p N N' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';
Refine ExIn ?;Refine +1 pair (wh_redn_refl ?);
Refine ipar_red1_pi;
Refine par_red1_psub;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine par_red1_psub;Immed;
(* lda *)
intros;
Equiv Ex [P:Trm]and (wh_redn (lda u (subN A) (subN B)) P)
                    (ipar_red1 P (lda v (subN' A') (subN' B')));
Refine fresh_params_lem4p p N N' B B';
intros q qFresh;Refine qFresh;
intros neqP noccN noccN' noccB noccB';
Refine ExIn ?;Refine +1 pair (wh_redn_refl ?);
Refine ipar_red1_lda;
Refine par_red1_psub;Immed;
Refine not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN';
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP u B);
Qrepl Trm_eq_subst (alpha_psub_commutes vclN' neqP v B');
Refine par_red1_psub;Immed;

(* app *)
intros;
Equiv Ex [P:Trm]and (wh_redn (app (subN A) (subN B)) P)
                    (ipar_red1 P (app (subN' A') (subN' B')));
Refine ihA;
intros NA hypNA;Refine hypNA;
intros wh_redNA ipar_redNA;Refine ExIn (app NA (subN B));Refine pair;
Refine wh_redn_app;Refine +1 ipar_red1_app;
Refine +2 par_red1_psub;Immed;

Save wh_ipar_red1_psub;

Goal {M,M'|Trm}(par_red1 M M')->
      Ex [N:Trm]and (wh_redn M N) (ipar_red1 N M');
Refine par_red1Rec [M,M'|Trm]
                    Ex [N:Trm]and (wh_redn M N) (ipar_red1 N M');

intros;Refine ExIn (* sort s *);Refine +1 pair;
Refine +1 wh_redn_refl;Refine ipar_red1_refl_sort;

intros;Refine ExIn (* par p *);Refine +1 pair;
Refine +1 wh_redn_refl;Refine ipar_red1_refl_par;

(* beta *)
intros;Refine ihA;
intros Aw hypA;Refine hypA;
intros wh_redA ipar_redA;Refine ihB;
intros B0;Refine shape_lemma p B0;
intros w Bw shapeB;Refine shapeB;
intros eqB noccBw;Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros wh_redB ipar_redB;

Refine wh_ipar_red1_psub
       premA wh_redA ipar_redA p ipar_redB;

intros BAw hypBAw;Refine hypBAw;
intros wh_redBAw ipar_redBAw;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A' v noccB'));
Refine ExIn (* BAw *);Refine +1 pair;Immed;
Refine wh_redn_trans ? wh_redBAw;Refine wh_redn_trans;
Refine +1 wh_redn_red1;Refine +1 wh_red1_beta;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A u noccB));
Refine psub_resp_wh_redn;Refine fst (par_red1_Vclosed premA);Immed;

(* pi *)
intros;Refine ihA;
intros Aw hypA;Refine hypA;
intros wh_redA ipar_redA;Refine ihB;
intros B0;Refine shape_lemma p B0;
intros w Bw shapeB;Refine shapeB;
intros eqB noccBw;Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ExIn (* pi u A B *);Refine +1 pair;
Refine +1 wh_redn_refl;Refine ipar_red1_pi;Immed;
(* lda *)
intros;Refine ihA;
intros Aw hypA;Refine hypA;
intros wh_redA ipar_redA;Refine ihB;
intros B0;Refine shape_lemma p B0;
intros w Bw shapeB;Refine shapeB;
intros eqB noccBw;Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ExIn (* lda u A B *);Refine +1 pair;
Refine +1 wh_redn_refl;Refine ipar_red1_lda;Immed;
(* app *)
intros;Refine ihA;
intros Aw hypA;Refine hypA;
intros wh_redA ipar_redA;Refine ihB;
intros Bw hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ExIn (* app Aw B *);Refine +1 pair;
Refine +1 wh_redn_app;Refine +2 ipar_red1_app;Immed;

Save par_red1_wh_redn_ipar_red1;

Goal {A,B|Trm}(ipar_red1 A B)->{C|Trm}(wh_red1 B C)->
      Ex [D:Trm]and (wh_redn A D) (ipar_red1 D C);
Refine ipar_red1Rec [A,B|Trm]
                    {C|Trm}{wh_red:wh_red1 B C}
                     Ex [D:Trm]and (wh_redn A D) (ipar_red1 D C);

intros;Refine wh_red1_sort_character wh_red;

intros;Refine wh_red1_par_character wh_red;

intros;Refine wh_red1_pi_character wh_red;

intros;Refine wh_red1_lda_character wh_red;

intros;Refine wh_ared1_app_character wh_red;
intros case;Refine case;
intros A'' hypA;Refine hypA;
intros is_not_ldaA wh_redA eq;Refine ihA wh_redA;
intros D hypD;Refine hypD;
intros wh_redD ipar_red1D;Qrepl Trm_eq_subst eq;
Refine ExIn (app D B);Refine pair;
Refine wh_redn_app;Refine +1 ipar_red1_app;Immed;

intros case;Refine case;
intros v V A'' hypL;Refine hypL;
intros eqA eqC;Qrepl Trm_eq_subst eqC;
Refine ipar_red1_refl_lda (?:ipar_red1 A (lda v V A''));
Qrepl Q_sym (Trm_eq_subst eqA);Refine premA;
intros u U A''' hypL';Refine hypL';
intros par_redU par_redA eq;Qrepl Trm_eq_subst eq;
Refine fresh_params_lem2 A'' A''';
intros q qFresh;Refine qFresh;
intros noccA'' noccA''';
Refine par_red1_wh_redn_ipar_red1;
Refine par_red1_beta (fst (par_red1_Vclosed par_redU));Immed;

Save ipar_wh_red1_commutes;

Goal {B,C|Trm}(wh_redn B C)->{A|Trm}(ipar_red1 A B)->
      Ex [D:Trm]and (wh_redn A D) (ipar_red1 D C);
Refine wh_rednRec [B,C|Trm]
                  {A|Trm}{ipar_red:ipar_red1 A B}
                   Ex [D:Trm]and (wh_redn A D) (ipar_red1 D C);
intros;Refine ExIn;Refine +1 pair (wh_redn_refl ?) ipar_red;

intros;Refine ipar_wh_red1_commutes ipar_red wh;
intros D1 hypD;Refine hypD;
intros wh_redD ipar_redD;
Refine ih ipar_redD;
intros B1 hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ExIn B1;Refine pair;
Refine wh_redn_trans;Immed;
Save ipar_red1_wh_redn_commutes;

Goal {A,B|Trm}(ipar_redn A B)->{C|Trm}(wh_redn B C)->
      Ex [D:Trm]and (wh_redn A D) (ipar_redn D C);
Refine ipar_rednRec [A,B|Trm]{C|Trm}{wh_red:wh_redn B C}
                     Ex [D:Trm]and (wh_redn A D) (ipar_redn D C);
intros;Refine ipar_red1_wh_redn_commutes;Immed;
intros C1 hypC;Refine hypC;
intros wh_redC ipar_redC;Refine ExIn C1;Refine pair wh_redC;
Refine ipar_redn_red1 ipar_redC;

intros;
Refine rt_ih wh_red;
intros D1 hypD;Refine hypD;
intros wh_redD ipar_redD;
Refine lt_ih wh_redD;
intros B1 hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ExIn B1;Refine pair;
Refine +1 ipar_redn_trans;Immed;
Save ipar_redn_wh_redn_commutes;

Goal {M,M'|Trm}(par_redn M M')->
      Ex [N:Trm]and (wh_redn M N) (ipar_redn N M');
Refine par_rednRec [M,M'|Trm]
                    Ex [N:Trm]and (wh_redn M N) (ipar_redn N M');

intros;Refine par_red1_wh_redn_ipar_red1;Immed;
intros C1 hypC;Refine hypC;
intros wh_redC ipar_redC;Refine ExIn C1;Refine pair wh_redC;
Refine ipar_redn_red1 ipar_redC;

intros;Refine lt_ih;
intros D1 hypD;Refine hypD;
intros wh_redD ipar_redD;Refine rt_ih;
intros B1 hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine ipar_redn_wh_redn_commutes ipar_redD wh_redB;
intros C1 hypC;Refine hypC;
intros wh_redC ipar_redC;
Refine ExIn C1;Refine pair;
Refine wh_redn_trans;Refine +3 ipar_redn_trans;Immed;
Save par_redn_wh_redn_ipar_redn;

Goal {A,B|Trm}(ipar_red1 A B)->(wh_nf A)->wh_nf B;
Refine ipar_red1Rec [A,B|Trm]{whnf:wh_nf A}wh_nf B;
intros;Refine wh_nf_sort;
intros;Refine wh_nf_par;
intros;Refine wh_nf_pi;
intros;Refine wh_nf_lda;
intros;Refine wh_nf_app_lem whnf;
intros sc whnfA;Refine wh_nf_app;
Qrepl Q_sym (ipar_red1_shape_lda premA);Refine +1 ihA;Immed;
Save ipar_red1_resp_wh_nf;

Goal {A,B|Trm}(ipar_red1 A B)->(wh_nf B)->wh_nf A;
Refine ipar_red1Rec [A,B|Trm]{whnf:wh_nf B}wh_nf A;
intros;Refine wh_nf_sort;
intros;Refine wh_nf_par;
intros;Refine wh_nf_pi;
intros;Refine wh_nf_lda;
intros;Refine wh_nf_app_lem whnf;
intros sc whnfA;Refine wh_nf_app;
Qrepl ipar_red1_shape_lda premA;Refine +1 ihA;Immed;
Save ipar_red1_refl_wh_nf;

Goal {A,B|Trm}(ipar_redn A B)->(wh_nf A)->wh_nf B;
Refine ipar_rednRec [A,B|Trm]{whnf:wh_nf A}wh_nf B;
intros;Refine ipar_red1_resp_wh_nf;Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Save ipar_redn_resp_wh_nf;

Goal {A,B|Trm}(ipar_redn A B)->(wh_nf B)->wh_nf A;
Refine ipar_rednRec [A,B|Trm]{whnf:wh_nf B}wh_nf A;
intros;Refine ipar_red1_refl_wh_nf;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save ipar_redn_refl_wh_nf;

Goal {M,M'|Trm}(par_redn M M')->(wh_nf M')->
      Ex [N:Trm]and3 (wh_redn M N) (wh_nf N) (ipar_redn N M');
intros;Refine par_redn_wh_redn_ipar_redn;Immed;
intros N hypN;Refine hypN;
intros wh_redN ipar_redN;Refine ExIn N;Refine pair3;
Refine +1 ipar_redn_refl_wh_nf;Immed;
Save wh_standardisation_lemma;

Goal {x|VV}{X,Y,M|Trm}(par_redn M (pi x X Y))->
      Ex3 [x':VV][X',Y':Trm]
      and3 (wh_redn M (pi x' X' Y'))
           (par_redn X' X)
           ({p:PP}par_redn (alpha p x' Y') (alpha p x Y));
intros;Refine wh_standardisation_lemma;Immed;Refine wh_nf_pi;
intros P hypP;Refine hypP;
intros whredP whnfP iredP;Refine ipar_redn_refl_pi iredP;
intros x' X' Y' hypP';Refine hypP';
intros redA' redB' eqP;Refine Ex3In;Refine +3 pair3;Immed;
Qrepl Q_sym (Trm_eq_subst eqP);Immed;
Save wh_standardisation_pi;

Goal {X,Y|Trm}(par_redn X Y)->
     {Xw|Trm}(wh_redn X Xw)->(wh_nf Xw)->
      Ex [Yw:Trm]and3 (wh_nf Yw) (ipar_redn Xw Yw) (wh_redn Y Yw);
intros;Refine par_redn_DP (wh_par_redn ? (fst (par_redn_Vclosed ?)));
Immed;
intros Y' hypY;Refine hypY;
intros rY rXw;Refine par_redn_wh_redn_ipar_redn rY;
intros W hypW;Refine hypW;
intros wW iW;Refine par_redn_wh_redn_ipar_redn rXw;
intros Yw hypYw;Refine hypYw;
intros wY iY;Refine par_redn_wh_redn_ipar_redn;
Refine +2 par_redn_trans ? 
       (wh_par_redn wY (fst (par_redn_Vclosed ?)));
Immed;
intros X' hypX;Refine hypX;
intros wX iX;Refine ExIn;Refine +1 pair3;Immed; 
Qrepl +1 Q_sym (Trm_eq_subst
         (wh_redn_to_wh_nf_unique wX H1 (ipar_redn_refl_wh_nf iX ?+0) H2));
Refine ipar_redn_refl_wh_nf iY;
Refine ipar_redn_resp_wh_nf iW;
Qrepl Q_sym (Trm_eq_subst (wh_nf_is_nf wW H2));
Immed;
Save par_redn_wh_nf_standardisation;

Goal {x|VV}{X,Y,A,B|Trm}(wh_redn X (pi x A B))->(par_redn X Y)->
      Ex3 [x':VV][A',B':Trm]
      and3 (par_redn A A')
           ({p:PP}par_redn (alpha p x B) (alpha p x' B'))
           (wh_redn Y (pi x' A' B'));
intros;Refine par_redn_wh_nf_standardisation;Immed;Refine wh_nf_pi;
intros Yw hypYw;Refine hypYw;
intros whnfY iY wY;Refine ipar_redn_pi_character iY;
intros x' A' B' hypY;Refine hypY;
intros rA rB eqY;Refine Ex3In;Refine +3 pair3;Immed;
Qrepl Q_sym (Trm_eq_subst eqY);Immed;
Save wh_nf_standardisation_pi;

(**********************************************************
***********************************************************)

