Module standard_mutual 
Import ipar_red;

Inductive [standard : Trm -> Trm -> Prop]
	 [istandard : Trm -> Trm -> Prop]

Constructors

[istandard_refl_sort : {s:SS} istandard (sort s) (sort s)]

[istandard_refl_par : {p:PP} istandard (par p) (par p)]

[istandard_pi:{A,A'|Trm}{premA:standard A A'}
              {u,v|VV}{B,B'|Trm}{p|PP}
              {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
              {premB:standard (alpha p u B) (alpha p v B')}
               istandard (pi u A B) (pi v A' B')]

[istandard_lda:{A,A'|Trm}{premA:standard A A'}
               {u,v|VV}{B,B'|Trm}{p|PP}
               {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
               {premB:standard (alpha p u B) (alpha p v B')}
                istandard (lda u A B) (lda v A' B')]

[istandard_app:{A,A'|Trm}{premA:istandard A A'}
               {B,B'|Trm}{premB:standard B B'}
                istandard (app A B) (app A' B')]

[standard_whi : {A,B,C|Trm}{wh_red:wh_redn A B}{prem:istandard B C}
	      standard A C]

(* Inversion *);

Goal standardRec:
	{R:Trm->Trm->Prop}{iR:Trm->Trm->Prop}
	
	{REFL_SORT:{s:SS}iR (sort s) (sort s)}

        {REFL_PAR:{p:PP}iR (par p) (par p)}

        {PI:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}{p|PP}
            {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
            {premB:standard (alpha p u B) (alpha p v B')}
            {ihB:R (alpha p u B) (alpha p v B')}
        	 iR (pi u A B) (pi v A' B')}

        {LDA:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}{p|PP}
            {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
            {premB:standard (alpha p u B) (alpha p v B')}
            {ihB:R (alpha p u B) (alpha p v B')}
         	iR (lda u A B) (lda v A' B')}

        {APP:{A,A'|Trm}{premA:istandard A A'}{ihA:iR A A'}
	     {B,B'|Trm}{premB:standard B B'}{ihB:R B B'}
                iR (app A B) (app A' B')}

        {WH:{A,B,C|Trm}{wh_red:wh_redn A B}
	    {prem:istandard B C}{ih:iR B C}
		R A C}

        {A,B|Trm}(standard A B)->R A B;

intros;Refine standard_elim 
	([A,B:Trm][_:standard A B]R A B)
	 [A,B:Trm][_:istandard A B]iR A B;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;

Goal istandardRec:
	{R:Trm->Trm->Prop}{iR:Trm->Trm->Prop}
	
	{REFL_SORT:{s:SS}iR (sort s) (sort s)}

        {REFL_PAR:{p:PP}iR (par p) (par p)}

        {PI:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}{p|PP}
            {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
            {premB:standard (alpha p u B) (alpha p v B')}
            {ihB:R (alpha p u B) (alpha p v B')}
        	 iR (pi u A B) (pi v A' B')}

        {LDA:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}{p|PP}
            {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
            {premB:standard (alpha p u B) (alpha p v B')}
            {ihB:R (alpha p u B) (alpha p v B')}
         	iR (lda u A B) (lda v A' B')}

        {APP:{A,A'|Trm}{premA:istandard A A'}{ihA:iR A A'}
	     {B,B'|Trm}{premB:standard B B'}{ihB:R B B'}
                iR (app A B) (app A' B')}

        {WH:{A,B,C|Trm}{wh_red:wh_redn A B}
	    {prem:istandard B C}{ih:iR B C}
		R A C}

        {A,B|Trm}(istandard A B)->iR A B;

intros;Refine istandard_elim 
	([A,B:Trm][_:standard A B]R A B)
	 [A,B:Trm][_:istandard A B]iR A B;Immed;
intros;Refine PI;Immed;
intros;Refine LDA;Immed;
intros;Refine APP;Immed;
Save;

Goal {A,B|Trm}(standard A B)->{C|Trm}(wh_redn C A)->standard C B;
Refine standard_elim 
	([A,B:Trm][_:standard A B]{C|Trm}(wh_redn C A)->standard C B)
	([A,B:Trm][_:istandard A B]{C|Trm}(wh_redn C A)->standard C B);
intros;Refine standard_whi;Refine +2 istandard_refl_sort;Immed;
intros;Refine standard_whi;Refine +2 istandard_refl_par;Immed;
intros;Refine standard_whi;Refine +2 istandard_pi;Immed;
intros;Refine standard_whi;Refine +2 istandard_lda;Immed;
intros;Refine standard_whi;Refine +2 istandard_app;Immed;
intros;Refine standard_whi;Refine +1 wh_redn_trans;Immed;
Save standard_wh_lem;

Goal {A,B,C|Trm}{wh_red:wh_redn A B}{prem:standard B C}
	      standard A C;
intros;Refine standard_wh_lem;Immed;
Save standard_wh;

Goal {A|Trm}(Vclosed A)->and (standard A A) (istandard A A);
intros;Refine aVclosedRec [A:Trm][_:aVclosed A]
		and (standard A A) (istandard A A);
intros;Refine pair;
Refine standard_whi (wh_redn_refl ?) ?+1;
Refine istandard_refl_sort;
intros;Refine pair;
Refine standard_whi (wh_redn_refl ?) ?+1;
Refine istandard_refl_par;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine ihA;
	intros AsA AisA;Refine ihB r;
	intros BsB BisB;Refine pair;
	Refine standard_whi (wh_redn_refl ?) ?+1;
	Refine istandard_pi;Immed;
intros;Refine fresh_params_lem1 B;
	intros r rFresh;Refine ihA;
	intros AsA AisA;Refine ihB r;
	intros BsB BisB;Refine pair;
	Refine standard_whi (wh_redn_refl ?) ?+1;
	Refine istandard_lda;Immed;
intros;Refine ihA;
	intros AsA AisA;Refine ihB;
	intros BsB BisB;Refine pair;
	Refine standard_whi (wh_redn_refl ?) ?+1;
	Refine istandard_app;Immed;
Refine Vclosed_aVclosed;Immed;
Save standard_refl;

Inductive [astandard : Trm -> Trm -> Prop]
	 [iastandard : Trm -> Trm -> Prop]

NoReductions

Constructors

[iastandard_refl_sort : {s:SS} iastandard (sort s) (sort s)]

[iastandard_refl_par : {p:PP} iastandard (par p) (par p)]

[iastandard_pi:{A,A'|Trm}{premA:astandard A A'}
              {u,v|VV}{B,B'|Trm}
              {premB:{p:PP}astandard (alpha p u B) (alpha p v B')}
               iastandard (pi u A B) (pi v A' B')]

[iastandard_lda:{A,A'|Trm}{premA:astandard A A'}
               {u,v|VV}{B,B'|Trm}
               {premB:{p:PP}astandard (alpha p u B) (alpha p v B')}
                iastandard (lda u A B) (lda v A' B')]

[iastandard_app:{A,A'|Trm}{premA:iastandard A A'}
               {B,B'|Trm}{premB:astandard B B'}
                iastandard (app A B) (app A' B')]

[astandard_whi : {A,B,C|Trm}{wh_red:wh_redn A B}{prem:iastandard B C}
	      astandard A C];

Goal {A,B|Trm}(astandard A B) -> standard A B;
Refine astandard_elim ([A,B|Trm][_:astandard A B]standard A B)
		       [A,B|Trm][_:iastandard A B]istandard A B;
intros;Refine istandard_refl_sort;
intros;Refine istandard_refl_par;
intros;Refine fresh_params_lem2 B B';
intros q qFresh;Refine qFresh;
intros noccB noccB';Refine istandard_pi;Immed;
intros;Refine fresh_params_lem2 B B';
intros q qFresh;Refine qFresh;
intros noccB noccB';Refine istandard_lda;Immed;
intros;Refine istandard_app;Immed;
intros;Refine standard_whi;Immed;
Save astandard_standard;

Goal {A,B|Trm}(iastandard A B) -> istandard A B;
Refine iastandard_elim ([A,B|Trm][_:astandard A B]standard A B)
		       [A,B|Trm][_:iastandard A B]istandard A B;
intros;Refine istandard_refl_sort;
intros;Refine istandard_refl_par;
intros;Refine fresh_params_lem2 B B';
intros q qFresh;Refine qFresh;
intros noccB noccB';Refine istandard_pi;Immed;
intros;Refine fresh_params_lem2 B B';
intros q qFresh;Refine qFresh;
intros noccB noccB';Refine istandard_lda;Immed;
intros;Refine istandard_app;Immed;
intros;Refine standard_whi;Immed;
Save iastandard_istandard;

Goal {A,B|Trm}(standard A B)->{rho:Renaming}astandard (renTrm rho A) (renTrm rho B);
Refine standard_elim ([A,B:Trm][_:standard A B]
                   {rho:Renaming}astandard (renTrm rho A) (renTrm rho B))
		 ([A,B:Trm][_:istandard A B]
                   {rho:Renaming}iastandard (renTrm rho A) (renTrm rho B));
intros;Refine iastandard_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine iastandard_refl_par;

intros;
Equiv iastandard (pi u (renTrm rho A) (renTrm rho B))
                 (pi v (renTrm rho A') (renTrm rho B'));
Refine iastandard_pi;Immed;
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
Equiv iastandard (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine iastandard_lda;Immed;
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
Equiv iastandard (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine iastandard_app;Immed;

intros;Refine astandard_whi;Refine +1 renTrm_resp_wh_redn;Immed;

Save standard_astandard_lem;

Goal {A,B|Trm}(istandard A B)->{rho:Renaming}iastandard (renTrm rho A) (renTrm rho B);
Refine istandard_elim ([A,B:Trm][_:standard A B]
                   {rho:Renaming}astandard (renTrm rho A) (renTrm rho B))
		 ([A,B:Trm][_:istandard A B]
                   {rho:Renaming}iastandard (renTrm rho A) (renTrm rho B));
intros;Refine iastandard_refl_sort;

intros;Refine isPar_lem;
Refine renTrm rho (par p);Qrepl renTrm_isPar rho (par p);Refine Q_refl;
intros q eqP;Qrepl Trm_eq_subst eqP;Refine iastandard_refl_par;

intros;
Equiv iastandard (pi u (renTrm rho A) (renTrm rho B))
                 (pi v (renTrm rho A') (renTrm rho B'));
Refine iastandard_pi;Immed;
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
Equiv iastandard (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine iastandard_lda;Immed;
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
Equiv iastandard (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine iastandard_app;Immed;

intros;Refine astandard_whi;Refine +1 renTrm_resp_wh_redn;Immed;

Save istandard_iastandard_lem;

Goal {A,B|Trm}(standard A B)->astandard A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine standard_astandard_lem H renId;
Save standard_astandard;

Goal {A,B|Trm}(standard A B)->{rho:Renaming}standard (renTrm rho A) (renTrm rho B);
intros;Refine astandard_standard;Refine standard_astandard_lem;Immed;
Save renTrm_resp_standard;

Goal {A,B|Trm}(istandard A B)->iastandard A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine istandard_iastandard_lem H renId;
Save istandard_iastandard;

Goal {A,B|Trm}(istandard A B)->{rho:Renaming}istandard (renTrm rho A) (renTrm rho B);
intros;Refine iastandard_istandard;Refine istandard_iastandard_lem;Immed;
Save renTrm_resp_istandard;

Goal astandardRec:
	{R:Trm->Trm->Prop}{iR:Trm->Trm->Prop}
	
	{REFL_SORT:{s:SS}iR (sort s) (sort s)}

        {REFL_PAR:{p:PP}iR (par p) (par p)}

        {PI:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}
            {premB:{p:PP}standard (alpha p u B) (alpha p v B')}
            {ihB:{p:PP}R (alpha p u B) (alpha p v B')}
        	 iR (pi u A B) (pi v A' B')}

        {LDA:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}
            {premB:{p:PP}standard (alpha p u B) (alpha p v B')}
            {ihB:{p:PP}R (alpha p u B) (alpha p v B')}
         	iR (lda u A B) (lda v A' B')}

        {APP:{A,A'|Trm}{premA:istandard A A'}{ihA:iR A A'}
	     {B,B'|Trm}{premB:standard B B'}{ihB:R B B'}
                iR (app A B) (app A' B')}

        {WH:{A,B,C|Trm}{wh_red:wh_redn A B}
	    {prem:istandard B C}{ih:iR B C}
		R A C}

        {A,B|Trm}(standard A B)->R A B;

intros;Refine astandard_elim 
	([A,B:Trm][_:astandard A B]R A B)
	 [A,B:Trm][_:iastandard A B]iR A B;Immed;
intros;Refine PI;Immed;
       Refine astandard_standard premA;
       Refine [p:PP]astandard_standard (premB p);
intros;Refine LDA;Immed;
       Refine astandard_standard premA;
       Refine [p:PP]astandard_standard (premB p);
intros;Refine APP;Immed;
       Refine iastandard_istandard premA;
       Refine astandard_standard premB;
intros;Refine WH;Immed;
       Refine iastandard_istandard prem;
Refine standard_astandard;Immed;
Save;

Goal iastandardRec:
	{R:Trm->Trm->Prop}{iR:Trm->Trm->Prop}
	
	{REFL_SORT:{s:SS}iR (sort s) (sort s)}

        {REFL_PAR:{p:PP}iR (par p) (par p)}

        {PI:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}
            {premB:{p:PP}standard (alpha p u B) (alpha p v B')}
            {ihB:{p:PP}R (alpha p u B) (alpha p v B')}
        	 iR (pi u A B) (pi v A' B')}

        {LDA:{A,A'|Trm}{premA:standard A A'}{ihA:R A A'}
	    {u,v|VV}{B,B'|Trm}
            {premB:{p:PP}standard (alpha p u B) (alpha p v B')}
            {ihB:{p:PP}R (alpha p u B) (alpha p v B')}
         	iR (lda u A B) (lda v A' B')}

        {APP:{A,A'|Trm}{premA:istandard A A'}{ihA:iR A A'}
	     {B,B'|Trm}{premB:standard B B'}{ihB:R B B'}
                iR (app A B) (app A' B')}

        {WH:{A,B,C|Trm}{wh_red:wh_redn A B}
	    {prem:istandard B C}{ih:iR B C}
		R A C}

        {A,B|Trm}(istandard A B)->iR A B;

intros;Refine iastandard_elim 
	([A,B:Trm][_:astandard A B]R A B)
	 [A,B:Trm][_:iastandard A B]iR A B;Immed;
intros;Refine PI;Immed;
       Refine astandard_standard premA;
       Refine [p:PP]astandard_standard (premB p);
intros;Refine LDA;Immed;
       Refine astandard_standard premA;
       Refine [p:PP]astandard_standard (premB p);
intros;Refine APP;Immed;
       Refine iastandard_istandard premA;
       Refine astandard_standard premB;
intros;Refine WH;Immed;
       Refine iastandard_istandard prem;
Refine istandard_iastandard;Immed;
Save;

Goal {A,B|Trm}(standard A B)->{C|Trm}(ipar_red1 C A)->standard C B;
Refine astandardRec
	([A,B:Trm]{C|Trm}(ipar_red1 C A)->standard C B)
	([A,B:Trm]{C|Trm}(ipar_red1 C A)->istandard C B);
(* sort *)
intros;Qrepl Trm_eq_subst (ipar_red1_refl_sort_lem H);
Refine istandard_refl_sort;
(* par *)
intros;Qrepl Trm_eq_subst (ipar_red1_refl_par_lem H);
Refine istandard_refl_par;
(* pi *)
intros;Refine ipar_red1_refl_pi H;
intros w A_c B_c hyp;Refine hyp;
intros redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine fresh_params_lem3 B B_c B';
intros q qFresh;Refine qFresh;
intros noccB noccB_c noccB';
Refine par_red1_wh_redn_ipar_red1 redA;
intros A_w hypA;Refine hypA;
intros wh_redA ipar_redA;Refine par_red1_wh_redn_ipar_red1 (redB q);
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_pi;Immed;
Refine standard_wh wh_redA (ihA ipar_redA);
Refine standard_wh wh_redB (ihB ? ipar_redB);
(* lda *)
intros;Refine ipar_red1_refl_lda H;
intros w A_c B_c hyp;Refine hyp;
intros redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine fresh_params_lem3 B B_c B';
intros q qFresh;Refine qFresh;
intros noccB noccB_c noccB';
Refine par_red1_wh_redn_ipar_red1 redA;
intros A_w hypA;Refine hypA;
intros wh_redA ipar_redA;Refine par_red1_wh_redn_ipar_red1 (redB q);
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_lda;Immed;
Refine standard_wh wh_redA (ihA ipar_redA);
Refine standard_wh wh_redB (ihB ? ipar_redB);
(* app *)
intros;Refine ipar_red1_refl_app H;
intros A_c B_c hyp;Refine hyp;
intros ipar_redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine par_red1_wh_redn_ipar_red1 redB;
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_app;
Refine ihA ipar_redA;
Refine standard_wh wh_redB (ihB ipar_redB);
(* wh *)
intros;Refine ipar_red1_wh_redn_commutes wh_red H;
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine standard_whi wh_redB (ih ipar_redB);
Save standard_absorbs_ipar_red1;

Goal {A,B|Trm}(istandard A B)->{C|Trm}(ipar_red1 C A)->istandard C B;
Refine iastandardRec
	([A,B:Trm]{C|Trm}(ipar_red1 C A)->standard C B)
	([A,B:Trm]{C|Trm}(ipar_red1 C A)->istandard C B);
(* sort *)
intros;Qrepl Trm_eq_subst (ipar_red1_refl_sort_lem H);
Refine istandard_refl_sort;
(* par *)
intros;Qrepl Trm_eq_subst (ipar_red1_refl_par_lem H);
Refine istandard_refl_par;
(* pi *)
intros;Refine ipar_red1_refl_pi H;
intros w A_c B_c hyp;Refine hyp;
intros redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine fresh_params_lem3 B B_c B';
intros q qFresh;Refine qFresh;
intros noccB noccB_c noccB';
Refine par_red1_wh_redn_ipar_red1 redA;
intros A_w hypA;Refine hypA;
intros wh_redA ipar_redA;Refine par_red1_wh_redn_ipar_red1 (redB q);
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_pi;Immed;
Refine standard_wh wh_redA (ihA ipar_redA);
Refine standard_wh wh_redB (ihB ? ipar_redB);
(* lda *)
intros;Refine ipar_red1_refl_lda H;
intros w A_c B_c hyp;Refine hyp;
intros redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine fresh_params_lem3 B B_c B';
intros q qFresh;Refine qFresh;
intros noccB noccB_c noccB';
Refine par_red1_wh_redn_ipar_red1 redA;
intros A_w hypA;Refine hypA;
intros wh_redA ipar_redA;Refine par_red1_wh_redn_ipar_red1 (redB q);
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_lda;Immed;
Refine standard_wh wh_redA (ihA ipar_redA);
Refine standard_wh wh_redB (ihB ? ipar_redB);
(* app *)
intros;Refine ipar_red1_refl_app H;
intros A_c B_c hyp;Refine hyp;
intros ipar_redA redB eqC;Qrepl Trm_eq_subst eqC;
Refine par_red1_wh_redn_ipar_red1 redB;
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;Refine istandard_app;
Refine ihA ipar_redA;
Refine standard_wh wh_redB (ihB ipar_redB);
(* wh *)
intros;Refine ipar_red1_wh_redn_commutes wh_red H;
intros B_w hypB;Refine hypB;
intros wh_redB ipar_redB;
Refine standard_whi wh_redB (ih ipar_redB);
Save istandard_absorbs_ipar_red1;

Goal {A,B|Trm}(standard A B)->{C|Trm}(par_red1 C A)->standard C B;
intros;Refine par_red1_wh_redn_ipar_red1 H1;
intros D hypD;Refine hypD;
intros wh_redD ipar_redD;Refine standard_wh;
Refine +2 standard_absorbs_ipar_red1;Immed;
Save standard_absorbs_par_red1;

Goal {A,B|Trm}(par_redn A B)->standard A B;
intros;Refine par_arednRec [A,B:Trm]standard A B;Immed;
intros;Refine standard_absorbs_par_red1;Refine +1 fst (standard_refl ?);
	Refine snd (par_red1_Vclosed ?+1);Immed;
intros;Refine standard_absorbs_par_red1;Immed;
Save standardisation_lem;
