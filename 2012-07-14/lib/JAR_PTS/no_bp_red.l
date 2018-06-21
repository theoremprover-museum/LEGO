Module no_bp_red Import par_bp_red;

(* the non-overlapping one-step beta-pi reduction relation *)

$[no_bp_red1 : Trm->Trm->Prop]

$[no_bp_red1_refl : refl no_bp_red1];

$[no_bp_red1_pcon:{u:VV}{U,A,B:Trm}no_bp_red1 (app (pi u U B) A) (vsub A u B)];

$[no_bp_red1_beta:{u:VV}{U,A,B:Trm}no_bp_red1 (app (lda u U B) A) (vsub A u B)];

$[no_bp_red1_pi:{A,A'|Trm}{premA:no_bp_red1 A A'}
            {u,v|VV}{B,B'|Trm}{p|PP}
            {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
            {premB:no_bp_red1 (alpha p u B) (alpha p v B')}
             no_bp_red1 (pi u A B) (pi v A' B')];

$[no_bp_red1_lda:{A,A'|Trm}{premA:no_bp_red1 A A'}
             {u,v|VV}{B,B'|Trm}{p|PP}
             {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
             {premB:no_bp_red1 (alpha p u B) (alpha p v B')}
              no_bp_red1 (lda u A B) (lda v A' B')];

$[no_bp_red1_app:{A,A'|Trm}{premA:no_bp_red1 A A'}
             {B,B'|Trm}{premB:no_bp_red1 B B'}
              no_bp_red1 (app A B) (app A' B')];

$[no_bp_red1Rec:{C:{A,B|Trm}(no_bp_red1 A B)->Prop}

	    {REFL:{A:Trm}C (no_bp_red1_refl A)}

	    {PCON:{u:VV}{U,A,B:Trm}C (no_bp_red1_pcon u U A B)}

	    {BETA:{u:VV}{U,A,B:Trm}C (no_bp_red1_beta u U A B)}

	    {PI:{A,A'|Trm}{premA:no_bp_red1 A A'}{ihA:C premA}
                {u,v|VV}{B,B'|Trm}{p|PP}
                {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                {premB:no_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
	         C (no_bp_red1_pi premA noccB noccB' premB)}

	    {LDA:{A,A'|Trm}{premA:no_bp_red1 A A'}{ihA:C premA}
                 {u,v|VV}{B,B'|Trm}{p|PP}
                 {noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
                 {premB:no_bp_red1 (alpha p u B) (alpha p v B')}{ihB:C premB}
	          C (no_bp_red1_lda premA noccB noccB' premB)}

	    {APP:{A,A'|Trm}{premA:no_bp_red1 A A'}{ihA:C premA}
                 {B,B'|Trm}{premB:no_bp_red1 B B'}{ihB:C premB}
                  C (no_bp_red1_app premA premB)}

	    {A,B|Trm}{r:no_bp_red1 A B}C r];

Goal {A,B|Trm}(no_bp_red1 A B)->par_bp_red1 A B;
Refine no_bp_red1Rec [A,B:Trm][_:no_bp_red1 A B]par_bp_red1 A B;
intros;Refine par_bp_red1_refl;
intros;Refine par_bp_ared1_red1;Refine par_bp_ared1_pcon;
       Refine par_bp_ared1_refl;intros;Refine par_bp_ared1_refl;
intros;Refine par_bp_ared1_red1;Refine par_bp_ared1_beta;
       Refine par_bp_ared1_refl;intros;Refine par_bp_ared1_refl;
intros;Refine par_bp_red1_pi;Immed;
intros;Refine par_bp_red1_lda;Immed;
intros;Refine par_bp_red1_app;Immed;
Save no_bp_par_bp_red1;

$[no_bp_ared1 : Trm->Trm->Prop]

$[no_bp_ared1_refl : refl no_bp_ared1];

$[no_bp_ared1_pcon:{u:VV}{U,A,B:Trm}no_bp_ared1 (app (pi u U B) A) (vsub A u B)];

$[no_bp_ared1_beta:{u:VV}{U,A,B:Trm}no_bp_ared1 (app (lda u U B) A) (vsub A u B)];

$[no_bp_ared1_pi:{A,A'|Trm}{premA:no_bp_ared1 A A'}
             {u,v|VV}{B,B'|Trm}
             {premB:{p:PP}no_bp_ared1 (alpha p u B) (alpha p v B')}
              no_bp_ared1 (pi u A B) (pi v A' B')];
$[no_bp_ared1_lda:{A,A'|Trm}{premA:no_bp_ared1 A A'}
              {u,v|VV}{B,B'|Trm}
              {premB:{p:PP}no_bp_ared1 (alpha p u B) (alpha p v B')}
               no_bp_ared1 (lda u A B) (lda v A' B')];

$[no_bp_ared1_app:{A,A'|Trm}{premA:no_bp_ared1 A A'}
              {B,B'|Trm}{premB:no_bp_ared1 B B'}
               no_bp_ared1 (app A B) (app A' B')];

$[no_bp_ared1Rec:{C:{A,B|Trm}(no_bp_ared1 A B)->Prop}

	     {REFL:{A:Trm}C (no_bp_ared1_refl A)}

	     {PCON:{u:VV}{U,A,B:Trm}C (no_bp_ared1_pcon u U A B)}
	     
	     {BETA:{u:VV}{U,A,B:Trm}C (no_bp_ared1_beta u U A B)}
	     
	     {PI:{A,A'|Trm}{premA:no_bp_ared1 A A'}{ihA:C premA}
                 {u,v|VV}{B,B'|Trm}
                 {premB:{p:PP}no_bp_ared1 (alpha p u B) (alpha p v B')}
                 {ihB:{p:PP}C (premB p)}
	          C (no_bp_ared1_pi premA premB)}

	     {LDA:{A,A'|Trm}{premA:no_bp_ared1 A A'}{ihA:C premA}
                  {u,v|VV}{B,B'|Trm}
                  {premB:{p:PP}no_bp_ared1 (alpha p u B) (alpha p v B')}
                  {ihB:{p:PP}C (premB p)}
	           C (no_bp_ared1_lda premA premB)}

	     {APP:{A,A'|Trm}{premA:no_bp_ared1 A A'}{ihA:C premA}
                  {B,B'|Trm}{premB:no_bp_ared1 B B'}{ihB:C premB}
                   C (no_bp_ared1_app premA premB)}

	     {A,B|Trm}{r:no_bp_ared1 A B}C r];

Goal {A,B|Trm}(no_bp_ared1 A B)->no_bp_red1 A B;
Refine no_bp_ared1Rec [A,B:Trm][_:no_bp_ared1 A B]no_bp_red1 A B;
intros;Refine no_bp_red1_refl;
intros;Refine no_bp_red1_pcon;
intros;Refine no_bp_red1_beta;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine no_bp_red1_pi;Refine +4 ihB;Immed;
intros;Refine fresh_params_lem2 B B';
intros r rFresh;Refine rFresh;
intros noccB noccB';Refine no_bp_red1_lda;Refine +4 ihB;Immed;
intros;Refine no_bp_red1_app;Immed;
Save no_bp_ared1_red1;

Goal {A,B|Trm}(no_bp_red1 A B)->{rho:Renaming}no_bp_ared1 (renTrm rho A) (renTrm rho B);
Refine no_bp_red1Rec [A,B:Trm][_:no_bp_red1 A B]
                   {rho:Renaming}no_bp_ared1 (renTrm rho A) (renTrm rho B);
intros;Refine no_bp_ared1_refl;

intros;
Equiv no_bp_ared1 (app (pi u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A u B);Refine no_bp_ared1_pcon;

intros;
Equiv no_bp_ared1 (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A u B);Refine no_bp_ared1_beta;

intros;
Equiv no_bp_ared1 (pi u (renTrm rho A) (renTrm rho B))
                (pi v (renTrm rho A') (renTrm rho B'));
Refine no_bp_ared1_pi;Immed;
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
Equiv no_bp_ared1 (lda u (renTrm rho A) (renTrm rho B))
                (lda v (renTrm rho A') (renTrm rho B'));
Refine no_bp_ared1_lda;Immed;
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
Equiv no_bp_ared1 (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B'));
Refine no_bp_ared1_app;Immed;

Save no_bp_red1_ared1_lem;

Goal {A,B|Trm}(no_bp_red1 A B)->no_bp_ared1 A B;
intros;Qrepl renTrm_Id A;Qrepl renTrm_Id B;
Refine no_bp_red1_ared1_lem H renId;
Save no_bp_red1_ared1;

Goal {A,B|Trm}(no_bp_red1 A B)->{rho:Renaming}no_bp_red1 (renTrm rho A) (renTrm rho B);
intros;Refine no_bp_ared1_red1;Refine no_bp_red1_ared1_lem;Immed;
Save renTrm_resp_no_bp_red1;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(no_bp_red1 X Y)->no_bp_red1 (psub N p X) (psub N p Y);
intros;
Refine no_bp_ared1Rec [A,B:Trm][_:no_bp_ared1 A B]no_bp_red1 (psub N p A) (psub N p B);
intros;Refine no_bp_red1_refl;

intros;
Equiv no_bp_red1 (app (pi u (psub N p U) (psub N p B)) (psub N p A)) ?;
Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A u B);Refine no_bp_red1_pcon;

intros;
Equiv no_bp_red1 (app (lda u (psub N p U) (psub N p B)) (psub N p A)) ?;
Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A u B);Refine no_bp_red1_beta;

intros;
Equiv no_bp_red1 (pi u (psub N p A) (psub N p B))
               (pi v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqPP noccN noccB noccB';
Refine no_bp_red1_pi;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP v B');
Refine ihB;

intros;
Equiv no_bp_red1 (lda u (psub N p A) (psub N p B))
               (lda v (psub N p A') (psub N p B'));
Refine fresh_params_lem3p p N B B';
intros q qFresh;Refine qFresh;
intros neqPP noccN noccB noccB';
Refine no_bp_red1_lda;Refine ihA;
Refine +1 not_pocc_psub_lem noccB noccN;
Refine not_pocc_psub_lem noccB' noccN;
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP u B);
Qrepl Trm_eq_subst(alpha_psub_commutes vclN neqPP v B');
Refine ihB;

intros;
Equiv no_bp_red1 (app (psub N p A) (psub N p B))
               (app (psub N p A') (psub N p B'));
Refine no_bp_red1_app;Immed;

Refine no_bp_red1_ared1;Immed;
Save psub_resp_no_bp_red1;

Goal {X,Y|Trm}(no_bp_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
intros;Refine par_bp_red1_refl_pocc;Refine +1 no_bp_par_bp_red1;Immed;
Save no_bp_red1_refl_pocc;

Goal {X,Y|Trm}(no_bp_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 no_bp_red1_refl_pocc;Immed;
Save not_pocc_resp_no_bp_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}no_bp_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;Refine par_bp_red1_alpha_refl_pocc;
intros +3 q;Refine no_bp_par_bp_red1;Immed;
Immed;
Save no_bp_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}no_bp_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 no_bp_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_no_bp_red1_alpha;

Goal {A,B|Trm}(no_bp_red1 A B)->(Vclosed A)->Vclosed B;
intros;Refine Vclosed_resp_par_bp_red1;Refine +1 no_bp_par_bp_red1;Immed;
Save Vclosed_resp_no_bp_red1;

(* now take the transitive closure of no_bp_red1 *)
(* and show it equivalent to redn              *)

$[no_bp_redn:Trm->Trm->Prop];
$[no_bp_redn_red1:{A,B|Trm}(no_bp_red1 A B)->no_bp_redn A B];
$[no_bp_redn_trans : trans no_bp_redn];

$[no_bp_rednRec:{C:{A,B|Trm}(no_bp_redn A B)->Prop}
	 {NO_BP_RED1:{A,B|Trm}{r:no_bp_red1 A B}C (no_bp_redn_red1 r)}
	 {TRANS:{A,D,B|Trm}{lt_prem:no_bp_redn A D}{lt_ih:C lt_prem}
		           {rt_prem:no_bp_redn D B}{rt_ih:C rt_prem}
		 C (no_bp_redn_trans lt_prem rt_prem)}
	 {A,B:Trm}{r:no_bp_redn A B}C r];

Goal refl no_bp_redn;
Intros;Refine no_bp_redn_red1;Refine no_bp_red1_refl;
Save no_bp_redn_refl;

Goal {A,B|Trm}(no_bp_redn A B)->{rho:Renaming}no_bp_redn (renTrm rho A) (renTrm rho B);
Refine no_bp_rednRec [A,B:Trm][_:no_bp_redn A B]
	{rho:Renaming}no_bp_redn (renTrm rho A) (renTrm rho B);
intros;Refine no_bp_redn_red1;Refine renTrm_resp_no_bp_red1;Immed;
intros;Refine no_bp_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save renTrm_resp_no_bp_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(no_bp_redn A B)->no_bp_redn (psub N p A) (psub N p B);
intros ___;
Refine no_bp_rednRec [A,B:Trm][_:no_bp_redn A B]no_bp_redn (psub N p A) (psub N p B);
intros;Refine no_bp_redn_red1;Refine psub_resp_no_bp_red1;Immed;
intros;Refine no_bp_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save psub_resp_no_bp_redn;

Goal {A,B|Trm}(no_bp_redn A B)->{p|PP}(is_tt (poccur p B))->is_tt (poccur p A);
Refine no_bp_rednRec [A,B:Trm][_:no_bp_redn A B]
                   {p|PP}{pocc:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine no_bp_red1_refl_pocc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save no_bp_redn_refl_pocc;

Goal {A,B|Trm}(no_bp_redn A B)->{p|PP}(is_ff (poccur p A))->is_ff (poccur p B);
intros;Refine B_contrapos;Refine +1 no_bp_redn_refl_pocc;Immed;
Save not_pocc_resp_no_bp_redn;

Goal {A,B|Trm}(no_bp_redn A B)->(Vclosed A)->(Vclosed B);
Refine no_bp_rednRec [A,B:Trm][_:no_bp_redn A B](Vclosed A)->(Vclosed B);
intros;Refine Vclosed_resp_no_bp_red1;Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Save Vclosed_resp_no_bp_redn;

(* introduce auxiliary relation which simplifies this: usual *-trick *)
$[no_bp_aredn:Trm->Trm->Prop]; 
$[no_bp_aredn_red1:{A,B|Trm}(no_bp_red1 A B)->no_bp_aredn A B];
$[no_bp_aredn_trans_red1 : {A,D,B|Trm}(no_bp_red1 A D)->(no_bp_aredn D B)->no_bp_aredn A B];

$[no_bp_arednRec:{C:{A,B|Trm}(no_bp_aredn A B)->Prop}

	      {RED1:{A,B|Trm}{r:no_bp_red1 A B}C (no_bp_aredn_red1 r)} 

	      {TRANS_RED1:{A,D,B|Trm}
                          {lt_prem:no_bp_red1 A D}
                          {lt_ih:C (no_bp_aredn_red1 lt_prem)}
		          {rt_prem:no_bp_aredn D B}{rt_ih:C rt_prem}
		           C (no_bp_aredn_trans_red1 lt_prem rt_prem)}

	      {A,B|Trm}{r:no_bp_aredn A B}C r];


Goal {A,B|Trm}(no_bp_aredn A B)->no_bp_redn A B;
Refine no_bp_arednRec [A,B|Trm][_:no_bp_aredn A B]no_bp_redn A B;
intros;Refine no_bp_redn_red1;Immed;
intros;Refine no_bp_redn_trans;Immed;
Save no_bp_aredn_redn;

Goal {A,D,B|Trm}{lt_prem:no_bp_aredn A D}{rt_prem:no_bp_aredn D B}no_bp_aredn A B;
intros;
Refine no_bp_arednRec [A,D|Trm][_:no_bp_aredn A D]
                    {B|Trm}{rt_prem:no_bp_aredn D B}no_bp_aredn A B;Immed;
intros;Refine no_bp_aredn_trans_red1;Immed;
intros;Refine no_bp_aredn_trans_red1;Refine +2 rt_ih;Immed;
Save no_bp_aredn_trans;

Goal {A,B|Trm}(no_bp_redn A B)->no_bp_aredn A B;
Refine no_bp_rednRec [A,B|Trm][_:no_bp_redn A B]no_bp_aredn A B;
intros;Refine no_bp_aredn_red1;Immed;
intros;Refine no_bp_aredn_trans;Immed;
Save no_bp_redn_aredn;

(* now the characters, for the subject reduction theorem *)
Goal {s|SS}{A|Trm}{r:no_bp_red1 (sort s) A}is_tt (Trm_eq A (sort s));
intros;Refine par_bp_red1_sort_character;Refine no_bp_par_bp_red1;Immed;
Save no_bp_red1_sort_character;

Goal {s|SS}{A|Trm}{r:no_bp_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine no_bp_rednRec [A,A'|Trm][_:no_bp_redn A A']
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Refine no_bp_red1_sort_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save no_bp_redn_sort_character;

Goal {p|PP}{A|Trm}{r:no_bp_red1 (par p) A}is_tt (Trm_eq A (par p));
intros;Refine par_bp_red1_par_character;Refine no_bp_par_bp_red1;Immed;
Save no_bp_red1_par_character;

Goal {p|PP}{A|Trm}{r:no_bp_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine no_bp_rednRec [A,A'|Trm][_:no_bp_redn A A']
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine no_bp_red1_par_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save no_bp_redn_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:no_bp_red1 (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (no_bp_red1 A A')
           ({p:PP}no_bp_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine no_bp_ared1Rec [P,P':Trm][_:no_bp_ared1 P P']
              {eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (no_bp_red1 A A')
                   ({p:PP}no_bp_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine Ex3In w A B;Refine pair3;
Refine no_bp_red1_refl;intros;Refine no_bp_red1_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine no_bp_ared1_red1;Refine premA;
intros;Refine no_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine no_bp_red1_ared1;Immed;
Save no_bp_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:no_bp_red1 (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (no_bp_red1 A A')
           ({p:PP}no_bp_red1 (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine no_bp_ared1Rec [L,L':Trm][_:no_bp_ared1 L L']
              {eq:is_tt (Trm_eq (lda w A B) L)}
              Ex3 [w':VV][A',B':Trm]
              and3 (no_bp_red1 A A')
                   ({p:PP}no_bp_red1 (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') L'));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine Ex3In w A B;Refine pair3;
Refine no_bp_red1_refl;intros;Refine no_bp_red1_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eq) : is_tt (VVeq w u)];
[eqA = and3_out2 (Trm_eq_pi_lem eq) : is_tt (Trm_eq A A1)];
[eqB = and3_out3 (Trm_eq_pi_lem eq) : is_tt (Trm_eq B B1)];
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqA;Qrepl Trm_eq_subst eqB;
Refine Ex3In v A' B';Refine pair3;
Refine no_bp_ared1_red1;Refine premA;
intros;Refine no_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine +2 Trm_eq_refl;Refine no_bp_red1_ared1;Immed;
Save no_bp_red1_lda_character;

Goal {M,N,X|Trm}{red_app:no_bp_red1 (app M N) X}
      or3 (Ex2 [M',N':Trm]
           and3 (no_bp_red1 M M')
                (no_bp_red1 N N')
                (is_tt (Trm_eq (app M' N') X)))
          (Ex3 [u:VV][U,B:Trm]
           and (is_tt (Trm_eq (pi u U B) M))
               (is_tt (Trm_eq (vsub N u B) X)))
          (Ex3 [u:VV][U,B:Trm]
           and (is_tt (Trm_eq (lda u U B) M))
               (is_tt (Trm_eq (vsub N u B) X)));

intros;Refine no_bp_ared1Rec [X,X':Trm][_:no_bp_ared1 X X']
              {eq:is_tt (Trm_eq (app M N) X)}
               or3 (Ex2 [M',N':Trm]
                    and3 (no_bp_red1 M M')
                         (no_bp_red1 N N')
                         (is_tt (Trm_eq (app M' N') X')))
                   (Ex3 [u:VV][U,B:Trm]
                    and (is_tt (Trm_eq (pi u U B) M))
                        (is_tt (Trm_eq (vsub N u B) X')))
                   (Ex3 [u:VV][U,B:Trm]
                    and (is_tt (Trm_eq (lda u U B) M))
                        (is_tt (Trm_eq (vsub N u B) X')));

intros;Qrepl Q_sym (Trm_eq_subst eq);Refine or3_in1;Refine Ex2In M N;Refine pair3;
Refine no_bp_red1_refl;Refine no_bp_red1_refl;Refine Trm_eq_refl;
intros;Refine or3_in2;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex3In u U B;Refine pair;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine or3_in3;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex3In u U B;Refine pair;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine or3_in1;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex2In A' B';Refine pair3;
Refine no_bp_ared1_red1;Refine premA;
Refine no_bp_ared1_red1;Refine premB;
Refine Trm_eq_refl;
Refine +2 Trm_eq_refl;Refine no_bp_red1_ared1;Immed;
Save no_bp_red1_app_character;

Goal {A,B|Trm}(no_bp_redn A B)->par_bp_redn A B;
Refine no_bp_rednRec [A,B:Trm][_:no_bp_redn A B]par_bp_redn A B;
intros;Refine par_bp_redn_red1;Refine no_bp_par_bp_red1;Immed;
intros;Refine par_bp_redn_trans lt_ih rt_ih;
Save no_bp_par_bp_redn;

(* need to show constructors are inherited by no_bp_redn from red1 *)
Goal {A,A'|Trm}(no_bp_redn A A')->{v:VV}{B:Trm}no_bp_redn (pi v A B) (pi v A' B);
Refine no_bp_rednRec [A,A'|Trm][_:no_bp_redn A A']
                   {v:VV}{B:Trm}no_bp_redn (pi v A B) (pi v A' B);
intros;Refine no_bp_redn_red1;Refine no_bp_ared1_red1;Refine no_bp_ared1_pi;
       Refine no_bp_red1_ared1;Immed;
       intros;Refine no_bp_ared1_refl;
intros;Refine no_bp_redn_trans;Immed;
Save no_bp_redn_pi_l;

Goal {X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:no_bp_redn (alpha p u X) (alpha p v X')}
     {Y:Trm}no_bp_redn (pi u Y X) (pi v Y X');
intros;
Refine no_bp_rednRec [B,B'|Trm][_:no_bp_redn B B']{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                 {A:Trm}no_bp_redn (pi u A X) (pi v A X');Immed;
intros;Refine no_bp_redn_red1;Refine no_bp_red1_pi (no_bp_red1_refl ?);Immed;
       Qrepl Q_sym(Trm_eq_subst eqB);Qrepl Q_sym(Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine no_bp_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;    

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save no_bp_redn_pi_r;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:no_bp_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:no_bp_redn (alpha p u B) (alpha p v B')}
      no_bp_redn (pi u A B) (pi v A' B');
intros;Refine no_bp_redn_trans;
Refine +1 no_bp_redn_pi_l;Refine +2 no_bp_redn_pi_r;Immed;
Save no_bp_redn_pi;

Goal {A,A'|Trm}(no_bp_redn A A')->{v:VV}{B:Trm}no_bp_redn (lda v A B) (lda v A' B);
Refine no_bp_rednRec [A,A'|Trm][_:no_bp_redn A A']
                   {v:VV}{B:Trm}no_bp_redn (lda v A B) (lda v A' B);
intros;Refine no_bp_redn_red1;Refine no_bp_ared1_red1;Refine no_bp_ared1_lda;
       Refine no_bp_red1_ared1;Immed;
       intros;Refine no_bp_ared1_refl;
intros;Refine no_bp_redn_trans;Immed;
Save no_bp_redn_lda_l;

Goal {X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:no_bp_redn (alpha p u X) (alpha p v X')}
     {Y:Trm}no_bp_redn (lda u Y X) (lda v Y X');
intros;
Refine no_bp_rednRec [B,B'|Trm][_:no_bp_redn B B']{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                 {A:Trm}no_bp_redn (lda u A X) (lda v A X');Immed;
intros;Refine no_bp_redn_red1;Refine no_bp_red1_lda (no_bp_red1_refl ?);Immed;
       Qrepl Q_sym(Trm_eq_subst eqB);Qrepl Q_sym(Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine no_bp_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;    

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save no_bp_redn_lda_r;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:no_bp_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:no_bp_redn (alpha p u B) (alpha p v B')}
      no_bp_redn (lda u A B) (lda v A' B');
intros;Refine no_bp_redn_trans;
Refine +1 no_bp_redn_lda_l;Refine +2 no_bp_redn_lda_r;Immed;
Save no_bp_redn_lda;

Goal {M,M'|Trm}(no_bp_redn M M')->{N:Trm}no_bp_redn (app M N) (app M' N);
Refine no_bp_rednRec [M,M'|Trm][_:no_bp_redn M M']{N:Trm}no_bp_redn (app M N) (app M' N);
intros;Refine no_bp_redn_red1;Refine no_bp_red1_app r (no_bp_red1_refl ?);
intros;Refine no_bp_redn_trans;Immed;
Save no_bp_redn_app_l;

Goal {N,N'|Trm}(no_bp_redn N N')->{M:Trm}no_bp_redn (app M N) (app M N');
Refine no_bp_rednRec [N,N'|Trm][_:no_bp_redn N N']{M:Trm}no_bp_redn (app M N) (app M N');
intros;Refine no_bp_redn_red1;Refine no_bp_red1_app (no_bp_red1_refl ?) r;
intros;Refine no_bp_redn_trans;Immed;
Save no_bp_redn_app_r;

Goal {M,M',N,N'|Trm}(no_bp_redn M M')->(no_bp_redn N N')->
         no_bp_redn (app M N) (app M' N');
intros;Refine no_bp_redn_trans;
Refine +1 no_bp_redn_app_l;Refine +2 no_bp_redn_app_r;Immed;
Save no_bp_redn_app;

Goal {A,M,N,M',N'|Trm}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:no_bp_redn (alpha p u M) (alpha p v M')}{redN:no_bp_redn N N'}
      no_bp_redn (app (pi u A M) N) (vsub N' v M');
intros;Refine no_bp_redn_trans;Refine +2 no_bp_redn_red1;Refine +2 no_bp_red1_pcon; 
Refine no_bp_redn_app;Refine no_bp_redn_pi;Refine no_bp_redn_refl;Immed;
Save no_bp_redn_pcon;

Goal {A,M,N,M',N'|Trm}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:no_bp_redn (alpha p u M) (alpha p v M')}{redN:no_bp_redn N N'}
      no_bp_redn (app (lda u A M) N) (vsub N' v M');
intros;Refine no_bp_redn_trans;Refine +2 no_bp_redn_red1;Refine +2 no_bp_red1_beta; 
Refine no_bp_redn_app;Refine no_bp_redn_lda;Refine no_bp_redn_refl;Immed;
Save no_bp_redn_beta;

Goal {A,B|Trm}(par_bp_red1 A B)->no_bp_redn A B;
Refine par_bp_red1Rec [A,B:Trm][_:par_bp_red1 A B]no_bp_redn A B;
intros;Refine no_bp_redn_refl;
intros;Refine no_bp_redn_pcon;Immed;
intros;Refine no_bp_redn_beta;Immed;
intros;Refine no_bp_redn_pi;Immed;
intros;Refine no_bp_redn_lda;Immed;
intros;Refine no_bp_redn_app;Immed;
Save par_bp_red1_no_bp_redn;

Goal {A,B|Trm}(par_bp_redn A B)->no_bp_redn A B;
Refine par_bp_rednRec [A,B:Trm][_:par_bp_redn A B]no_bp_redn A B;
intros;Refine par_bp_red1_no_bp_redn;Immed;
intros;Refine no_bp_redn_trans lt_ih rt_ih;
Save par_bp_no_bp_redn;

