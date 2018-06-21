Module par_redn
Import par_red1;

(* now take the transitive closure of par_red1 *)
(* and show it equivalent to redn              *)
Inductive [par_redn:Trm->Trm->Prop]
Constructors
[par_redn_red1:{A,B|Trm}(par_red1 A B)->par_redn A B]
[par_redn_trans : {A,D,B|Trm}{lt_prem:par_redn A D}
		           {rt_prem:par_redn D B}par_redn A B];

Goal par_rednRec : {C:{A,B:Trm}Prop}
	 {PAR_RED1:{A,B|Trm}{r:par_red1 A B}C A B}
	 {TRANS:{A,D,B|Trm}{lt_prem:par_redn A D}{lt_ih:C A D}
		           {rt_prem:par_redn D B}{rt_ih:C D B}
		 C A B}
	 {A,B|Trm}{r:par_redn A B}C A B;

intros;Refine par_redn_elim [A,B|Trm][_:par_redn A B]C A B;Immed;
intros;Refine TRANS;Immed;
Save;

Goal par_redn_refl : {A|Trm}(Vclosed A)->par_redn A A;
intros;Refine par_redn_red1;Refine par_red1_refl;Immed;
Save par_redn_refl;

Goal {A,B|Trm}(par_redn A B)-> and (Vclosed A) (Vclosed B);
Refine par_rednRec [A,B:Trm]and (Vclosed A) (Vclosed B);
intros;Refine par_red1_Vclosed;Immed;
intros;Refine rt_ih;
intros;Refine lt_ih;
intros;Refine pair;Immed;
Save par_redn_Vclosed;

Goal {A,B|Trm}(par_redn A B)->{rho:Renaming}par_redn (renTrm rho A) (renTrm rho B);
Refine par_rednRec [A,B:Trm]
	{rho:Renaming}par_redn (renTrm rho A) (renTrm rho B);
intros;Refine par_redn_red1;Refine renTrm_resp_par_red1;Immed;
intros;Refine par_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save renTrm_resp_par_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(par_redn A B)->par_redn (psub N p A) (psub N p B);
intros ___;
Refine par_rednRec [A,B:Trm]par_redn (psub N p A) (psub N p B);
intros;Refine par_redn_red1;Refine psub_resp_par_red1;Immed;
intros;Refine par_redn_trans;Refine +1 lt_ih;Refine rt_ih;
Save psub_resp_par_redn;

(* introduce auxiliary relation which simplifies this: usual *-trick *)
Inductive [par_aredn:Trm->Trm->Prop] NoReductions Constructors 
[par_aredn_red1:{A,B|Trm}(par_red1 A B)->par_aredn A B]
[par_aredn_trans_red1 : {A,D,B|Trm}{lt_prem:par_red1 A D}
			{rt_prem:par_aredn D B}par_aredn A B];

Goal {A,B|Trm}(par_aredn A B)->par_redn A B;
Refine par_aredn_elim [A,B|Trm][_:par_aredn A B]par_redn A B;
intros;Refine par_redn_red1;Immed;
intros;Refine par_redn_trans;Refine +1 par_redn_red1;Immed;
Save par_aredn_redn;

Goal {A,D,B|Trm}{lt_prem:par_aredn A D}{rt_prem:par_aredn D B}par_aredn A B;
intros;
Refine par_aredn_elim [A,D|Trm][_:par_aredn A D]
                    {B|Trm}{rt_prem:par_aredn D B}par_aredn A B;Immed;
intros;Refine par_aredn_trans_red1;Immed;
intros;Refine par_aredn_trans_red1;Refine +2 rt_prem_ih;Immed;
Save par_aredn_trans;

Goal {A,B|Trm}(par_redn A B)->par_aredn A B;
Refine par_rednRec [A,B|Trm]par_aredn A B;
intros;Refine par_aredn_red1;Immed;
intros;Refine par_aredn_trans;Immed;
Save par_redn_aredn;

Goal par_arednRec:{C:{A,B:Trm}Prop}

	      {RED1:{A,B|Trm}{r:par_red1 A B}C A B} 

	      {TRANS_RED1:{A,D,B|Trm}
                          {lt_prem:par_red1 A D}
                          {rt_prem:par_redn D B}{rt_ih:C D B}
		           C A B}

	      {A,B|Trm}{r:par_redn A B}C A B;

intros;Refine par_aredn_elim [A,B|Trm][_:par_aredn A B]C A B;Immed;
intros;Refine TRANS_RED1;Refine +2 par_aredn_redn;Immed;
Refine par_redn_aredn;Immed;
Save;

(* need to show constructors are inherited by par_redn from red1 *)
Goal {q|PP}{v|VV}{B|Trm}{vclB:Vclosed (alpha q v B)}
     {A,A'|Trm}(par_redn A A')->
     par_redn (pi v A B) (pi v A' B);
intros ____;
Refine par_rednRec [A,A'|Trm]par_redn (pi v A B) (pi v A' B);
intros;Refine par_redn_red1; Refine par_ared1_red1;Refine par_ared1_pi;
  Refine par_red1_ared1; Immed;
  intros; Refine par_red1_ared1; Refine par_red1_refl;
  Refine aVclosed_Vclosed; Refine aVclosed_alpha;
  Refine +1 (Vclosed_aVclosed vclB);
intros;Refine par_redn_trans;Immed;
Save par_redn_pi_l; 

Goal {q|PP}{v|VV}{B|Trm}{vclB:Vclosed (alpha q v B)}
     {A,A'|Trm}(par_redn A A')->
     par_redn (lda v A B) (lda v A' B);
intros ____;
Refine par_rednRec [A,A'|Trm]par_redn (lda v A B) (lda v A' B);
intros;Refine par_redn_red1; Refine par_ared1_red1;Refine par_ared1_lda;
  Refine par_red1_ared1; Immed;
  intros; Refine par_red1_ared1; Refine par_red1_refl;
  Refine aVclosed_Vclosed; Refine aVclosed_alpha;
  Refine +1 (Vclosed_aVclosed vclB);
intros;Refine par_redn_trans;Immed;
Save par_redn_lda_l; 

Goal {N|Trm}{vclN:Vclosed N}{M,M'|Trm}(par_redn M M')->
     par_redn (app M N) (app M' N);
intros __;
Refine par_rednRec [M,M'|Trm]par_redn (app M N) (app M' N);
intros;Refine par_redn_red1;Refine par_red1_app r (par_red1_refl ?);Immed;
intros;Refine par_redn_trans;Immed;
Save par_redn_app_l;

Goal {M|Trm}{vclM:Vclosed M}{N,N'|Trm}(par_redn N N')->
     par_redn (app M N) (app M N');
intros __;
Refine par_rednRec [N,N'|Trm]par_redn (app M N) (app M N');
intros;Refine par_redn_red1;Refine par_red1_app (par_red1_refl ?) r;Immed;
intros;Refine par_redn_trans;Immed;
Save par_redn_app_r;

Goal {M,M',N,N'|Trm}(par_redn M M')->(par_redn N N')->
         par_redn (app M N) (app M' N');
intros;Refine par_redn_trans;
Refine +1 par_redn_app_l (fst (par_redn_Vclosed ?));
Refine +4 par_redn_app_r (snd (par_redn_Vclosed ?));Immed;
Save par_redn_app;

Goal {Y|Trm}{vclY:Vclosed Y}{X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:par_redn (alpha p u X) (alpha p v X')}
     par_redn (pi u Y X) (pi v Y X');
intros;
Refine par_rednRec [B,B'|Trm]{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                  par_redn (pi u Y X) (pi v Y X');Immed;
intros;Refine par_redn_red1;Refine par_red1_pi (par_red1_refl ?);Immed;
Qrepl Q_sym (Trm_eq_subst eqB);Qrepl Q_sym (Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine par_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save par_redn_pi_r;

Goal {Y|Trm}{vclY:Vclosed Y}{X,X'|Trm}{u,v|VV}
     {p|PP}(is_ff (poccur p X))->(is_ff (poccur p X'))->
     {redX:par_redn (alpha p u X) (alpha p v X')}
     par_redn (lda u Y X) (lda v Y X');
intros;
Refine par_rednRec [B,B'|Trm]{X,X'|Trm}{u,v|VV}
                 {noccX:is_ff (poccur p X)}{noccX':is_ff (poccur p X')}
                 {eqB:is_tt (Trm_eq B (alpha p u X))}
                 {eqB':is_tt (Trm_eq B' (alpha p v X'))}
                  par_redn (lda u Y X) (lda v Y X');Immed;
intros;Refine par_redn_red1;Refine par_red1_lda (par_red1_refl ?);Immed;
Qrepl Q_sym (Trm_eq_subst eqB);Qrepl Q_sym (Trm_eq_subst eqB');Immed;

intros;Refine shape_lemma p D;
intros w D' hypD;
[eqD = fst hypD][noccD = snd hypD];
Refine par_redn_trans;Refine +1 lt_ih;Refine +6 rt_ih;Immed;

Refine Trm_eq_refl;Refine Trm_eq_refl;
Save par_redn_lda_r;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:par_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:par_redn (alpha p u B) (alpha p v B')}
      par_redn (pi u A B) (pi v A' B');
intros;Refine par_redn_trans;
Refine +1 par_redn_pi_l (fst (par_redn_Vclosed ?));
Refine +5 par_redn_pi_r (snd (par_redn_Vclosed ?));Immed;
Save par_redn_pi;

Goal {u,v|VV}{A,A',B,B'|Trm}{redA:par_redn A A'}
     {p|PP}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {redB:par_redn (alpha p u B) (alpha p v B')}
      par_redn (lda u A B) (lda v A' B');
intros;Refine par_redn_trans;
Refine +1 par_redn_lda_l (fst (par_redn_Vclosed ?));
Refine +5 par_redn_lda_r (snd (par_redn_Vclosed ?));Immed;
Save par_redn_lda;

Goal {A,M,N,M',N'|Trm}{vcl:Vclosed A}{u,v|VV}
     {p|PP}{noccM:is_ff (poccur p M)}{noccM':is_ff (poccur p M')}
     {redM:par_redn (alpha p u M) (alpha p v M')}{redN:par_redn N N'}
      par_redn (app (lda u A M) N) (vsub N' v M');
intros;Refine par_redn_trans;Refine +2 par_redn_red1;Refine +2 par_red1_beta; 
Refine par_redn_app;Refine par_redn_lda_r;Immed;
Refine par_red1_refl (snd (par_redn_Vclosed redN));
Refine par_red1_refl (snd (par_redn_Vclosed redM));
Save par_redn_beta;

Goal {s|SS}{A|Trm}{r:par_red1 (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine par_red1Rec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save par_red1_sort_character;

Goal {s|SS}{A|Trm}{r:par_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine par_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Refine par_red1_sort_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save par_redn_sort_character;

Goal not_par_redn_sort_pi:
     {v|VV}{A,B|Trm}{s|SS}not (par_redn (sort s) (pi v A B));
Expand not; intros; Refine tt_not_ff (Q_sym (par_redn_sort_character H));
Save;
 
Goal {p|PP}{A|Trm}{r:par_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine par_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Refine par_red1_par_character;Qrepl Q_sym (Trm_eq_subst eq);Immed;
intros;Refine rt_ih;Refine lt_ih;Immed;
Refine Trm_eq_refl;
Save par_redn_par_character;

Goal {X,Y|Trm}(par_redn X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
Refine par_rednRec [A,B:Trm]
                    {p|PP}{occ:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine par_red1_refl_pocc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save par_redn_refl_pocc;

Goal {X,Y|Trm}(par_redn X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_redn_refl_pocc;Immed;
Save not_pocc_resp_par_redn;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{occ:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (par_redn_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Equiv (is_tt (orr (PPeq p q) ff))->is_tt ?;
Qrepl PPsym p q;Qrepl neqP;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Immed;
Save par_redn_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}par_redn (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 par_redn_alpha_refl_pocc;Immed;
Save not_pocc_resp_par_redn_alpha;

Goal {w|VV}{A,B,X|Trm}{red_pi:par_redn (pi w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A A')
           ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (pi w' A' B') X));

intros;Refine par_rednRec [P,P':Trm]
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq (pi w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_redn A A')
                   ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (pi w' A' B') P'));Immed;

intros;Refine par_red1_pi_character (?:par_red1 (pi w1 A2 B2) B1);
Qrepl Trm_eq_subst eq;Refine r;
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
Save par_redn_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_lda:par_redn (lda w A B) X}
      Ex3 [w':VV][A',B':Trm]
      and3 (par_redn A A')
           ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
           (is_tt (Trm_eq (lda w' A' B') X));

intros;Refine par_rednRec [P,P':Trm]
              {w|VV}{A,B|Trm}{eq:is_tt (Trm_eq (lda w A B) P)}
              Ex3 [w':VV][A',B':Trm]
              and3 (par_redn A A')
                   ({p:PP}par_redn (alpha p w B) (alpha p w' B'))
                   (is_tt (Trm_eq (lda w' A' B') P'));Immed;

intros;Refine par_red1_lda_character (?:par_red1 (lda w1 A2 B2) B1);
Qrepl Trm_eq_subst eq;Refine r;
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
Save par_redn_lda_character;

Goal {p|PP}{M|Trm}(Vclosed M)->
     {N,N'|Trm}(par_redn N N')->
      par_redn (psub N p M) (psub N' p M);
intros ___;
Refine par_rednRec [N,N'|Trm]
                    par_redn (psub N p M) (psub N' p M);
intros;Refine par_redn_red1;Refine par_red1_refl_psub_lem;Immed;
intros;Refine par_redn_trans;Immed;
Save par_redn_refl_psub_lem;

Goal {p|PP}{M,M'|Trm}(par_red1 M M')->
     {N,N'|Trm}(par_redn N N')->
      par_redn (psub N p M) (psub N' p M');
intros;
Refine par_rednRec [N,N'|Trm]
                   {M,M'|Trm}{par_redM:par_red1 M M'}
                    par_redn (psub N p M) (psub N' p M');Immed;
intros;Refine par_redn_red1;Refine par_red1_psub;Immed;
intros;Refine par_redn_trans (lt_ih ?) (rt_ih ?);Immed;
Refine par_red1_refl;Refine fst (par_red1_Vclosed par_redM);
Save par_redn_red1_psub_lem;

Goal {p|PP}{N,N'|Trm}(par_redn N N')->
     {X,X'|Trm}(par_redn X X')->par_redn (psub N p X) (psub N' p X');
intros;
Refine par_rednRec [M,M'|Trm]
                   {N,N'|Trm}{par_redN:par_redn N N'}
                    par_redn (psub N p M) (psub N' p M');Immed;
intros;Refine par_redn_red1_psub_lem;Immed;
intros;Refine par_redn_trans (lt_ih ?) (rt_ih ?);Immed;
Refine par_redn_refl;Refine fst (par_redn_Vclosed par_redN);
Save par_redn_psub;

Goal {N,N'|Trm}(par_redn N N')->
     {u,v:VV}{X,X'|Trm}({q:PP}par_redn (alpha q u X) (alpha q v X'))->
      par_redn (vsub N u X) (vsub N' v X');
intros;Refine fresh_params_lem2 X X';
intros q qFresh;Refine qFresh;
intros noccX noccX';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N u noccX));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N' v noccX'));
Refine par_redn_psub;Immed;
Save par_redn_vsub;

(********   some new stuff, very useful  ************)
(********   James, put it where you want it  *********)
Goal {X,Y|Trm}(par_red1 X Y)->{s|SS}(is_tt (soccur s Y))->is_tt (soccur s X);
Refine par_red1Rec [A,B:Trm]
                    {s|SS}{occ:is_tt (soccur s B)}is_tt (soccur s A);
intros;Immed;
intros;Immed;

intros;Refine socc_vsub_lem2 occ;
intros occA;Refine socc_split_lem;Refine inr;Refine ihA;Immed;
intros occB;Refine socc_split_lem;Refine inl;
            Refine socc_split_lem;Refine inr;
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
intros occB;Refine socc_split_lem;Refine inr;
            Refine socc_vsub_lem2 (ihB ?);
            Refine +1 socc_vsub_lem occB;
            intros abs;Refine tt_not_ff (Q_sym abs);
            intros;Immed;

intros;Refine socc_compound_lem occ;
intros occA;Refine socc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine socc_split_lem;Refine inr;Refine ihB;Immed;

Save par_red1_refl_socc;

Goal {X|Trm}{s|SS}(par_red1 X (sort s))->is_tt (soccur s X);
intros;Refine par_red1_refl_socc;Immed;
Qrepl socc_sort_lem s s;Refine SSrefl;
Save par_red1_sort_socc_lem;

Goal {X,Y|Trm}(par_redn X Y)->{s|SS}(is_tt (soccur s Y))->is_tt (soccur s X);
Refine par_rednRec [A,B:Trm]
                    {s|SS}{occ:is_tt (soccur s B)}is_tt (soccur s A);
intros;Refine par_red1_refl_socc;Immed;
intros;Refine lt_ih;Refine rt_ih;Immed;
Save par_redn_refl_socc;

Goal {X|Trm}{s|SS}(par_redn X (sort s))->is_tt (soccur s X);
intros;Refine par_redn_refl_socc;Immed;
Qrepl socc_sort_lem s s;Refine SSrefl;
Save par_redn_sort_socc_lem;
