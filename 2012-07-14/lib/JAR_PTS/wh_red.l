Module wh_red 
Import alpha_conversion no_red;

(* weak-head reduction and weak-head-normal forms NEW *)


Inductive [wh_red1 : Trm->Trm->Prop]
Constructors 

[wh_red1_beta:{u:VV}{U,A,B:Trm}wh_red1 (app (lda u U B) A) (vsub A u B)]

[wh_red1_app:{A,A'|Trm}{premA:wh_red1 A A'}
             {B:Trm}wh_red1 (app A B) (app A' B)];


Goal wh_red1Rec:{C:{A,B:Trm}Prop}

	    {BETA:{u:VV}{U,A,B:Trm}C (app (lda u U B) A) (vsub A u B)}

	    {APP:{A,A'|Trm}{premA:wh_red1 A A'}{ihA:C A A'}
                 {B:Trm}C (app A B) (app A' B)}

	    {A,B|Trm}{red:wh_red1 A B}C A B;

intros;Refine wh_red1_elim [A,B|Trm][_:wh_red1 A B]C A B;
intros;Refine BETA;
intros;Refine APP;Immed;
Immed;
Save;

Goal wh_no_red1:
     {A,B|Trm}(wh_red1 A B)->(Vclosed A)->no_red1 A B;
Refine wh_red1Rec [A,B:Trm](Vclosed A)->no_red1 A B;
intros;Refine no_red1_beta; Immed;
intros; Refine aVclosed_app_gen (Vclosed_aVclosed H); 
intros; Refine no_red1_app; Refine ihA; Refine aVclosed_Vclosed;
Refine +1 no_red1_refl; Refine +1 aVclosed_Vclosed; Immed;
Save;

Goal {A,B|Trm}(wh_red1 A B)->
     {rho:Renaming}wh_red1 (renTrm rho A) (renTrm rho B);
Refine wh_red1Rec [A,B:Trm]
     {rho:Renaming}wh_red1 (renTrm rho A) (renTrm rho B);
intros;
Equiv wh_red1 (app (lda u (renTrm rho U) (renTrm rho B)) (renTrm rho A)) ?;
Qrepl Q_sym (vsub_renTrm_commutes rho A u B);
Refine wh_red1_beta;
intros;
Equiv wh_red1 (app (renTrm rho A) (renTrm rho B))
                (app (renTrm rho A') (renTrm rho B));
Refine wh_red1_app; Immed;
Save renTrm_resp_wh_red1;

Goal {X,Y|Trm}(wh_red1 X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
Refine wh_red1Rec [A,B:Trm]
		  {p|PP}{occ:is_tt (poccur p B)}is_tt (poccur p A);
intros;Refine pocc_vsub_lem2 occ;
intros occA;Refine pocc_split_lem;Refine inr;Immed;
intros occB;Refine pocc_split_lem;Refine inl;
            Refine pocc_split_lem;Refine inr;Immed;
intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_split_lem;Refine inl;Refine ihA;Immed;
intros occB;Refine pocc_split_lem;Refine inr;Immed;
Save wh_red1_refl_pocc;

Goal {X,Y|Trm}(wh_red1 X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 wh_red1_refl_pocc;Immed;
Save not_pocc_resp_wh_red1;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}wh_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{occur:is_tt (poccur p Y)}is_tt (poccur p X);
intros;
Refine fresh_params_lem2p p X Y;
intros q qFresh;Refine qFresh;
intros neqP noccX noccY;
Refine pocc_vsub_lem2 (wh_red1_refl_pocc (ih q) ?);
Refine +1 pocc_vsub_lem;Immed; 
Qrepl pocc_par_lem p q;Qrepl PPsym p q;Qrepl neqP;
intros abs;Refine tt_not_ff (Q_sym abs);
intros;Immed;
Save wh_red1_alpha_refl_pocc;

Goal {X,Y|Trm}{u,v|VV}
     {ih:{p:PP}wh_red1 (alpha p u X) (alpha p v Y)}
     {p|PP}{nocc:is_ff (poccur p X)}is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 wh_red1_alpha_refl_pocc;Immed;
Save not_pocc_resp_wh_red1_alpha;

Goal {A,B|Trm}(wh_red1 A B)->(Vclosed A)->Vclosed B;
Refine wh_red1Rec [A,B:Trm]{vcl:Vclosed A}Vclosed B;
intros;Refine Vclosed_app_lem vcl;
intros vclL vclA;Refine Vclosed_lda_lem vclL;
intros vclU vclB;Refine fresh_params_lem1 B;
intros q noccB;Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha A u noccB));
Refine psub_resp_Vclosed;Immed;
intros;Refine Vclosed_app_lem vcl;
intros vclA vclB;Refine Vclosed_app;Refine ihA;Immed;
Save Vclosed_resp_wh_red1;

Goal {s|SS}{A|Trm}{r:wh_red1 (sort s) A}absurd;
intros;
Refine wh_red1Rec [A,A'|Trm]{eq:is_tt (Trm_eq A (sort s))}absurd;
Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save wh_red1_sort_character;

Goal {p|PP}{A|Trm}{r:wh_red1 (par p) A}absurd;
intros;
Refine wh_red1Rec [A,A'|Trm]{eq:is_tt (Trm_eq A (par p))}absurd;
Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save wh_red1_par_character;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {X,Y|Trm}(wh_red1 X Y)->wh_red1 (psub N p X) (psub N p Y);
intros ___;
Refine wh_red1Rec [A,B:Trm]wh_red1 (psub N p A) (psub N p B);

intros;Qrepl Trm_eq_subst (psub_vsub_commutes vclN p A u B);
Equiv wh_red1 (app (lda u (psub N p U) (psub N p B)) (psub N p A)) ?;
Refine wh_red1_beta;

intros;
Equiv wh_red1 (app (psub N p A) (psub N p B)) (app (psub N p A') (psub N p B));
Refine wh_red1_app;Immed;
Save psub_resp_wh_red1;

Goal {w|VV}{A,B,X|Trm}{red_pi:wh_red1 (pi w A B) X}absurd;
intros;Refine wh_red1Rec [P,P':Trm]
              {eq:is_tt (Trm_eq (pi w A B) P)}absurd;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save wh_red1_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:wh_red1 (lda w A B) X}absurd;
intros;Refine wh_red1Rec [P,P':Trm]
              {eq:is_tt (Trm_eq (lda w A B) P)}absurd;Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Refine Trm_eq_refl;
Save wh_red1_lda_character;

Goal wh_red1_not_lda: {A,B|Trm}(wh_red1 A B)->is_ff (isLda A);
intros; Refine tt_or_ff (isLda A);
intros isLdaA; Refine isLda_lem isLdaA; intros v X Y h;
  Refine wh_red1_lda_character|v|X|Y|B; Qrepl Q_sym (Trm_eq_subst h); Immed;
intros; Immed;
Save;

Goal {M,N,X|Trm}{red_app:wh_red1 (app M N) X}
      or (Ex [M':Trm]and (wh_red1 M M') (is_tt (Trm_eq X (app M' N))))
         (Ex3 [u:VV][U,B:Trm]and (is_tt (Trm_eq M (lda u U B)))
                                 (is_tt (Trm_eq X (vsub N u B))));
intros;
Refine wh_red1Rec [X,X':Trm]{eq:is_tt (Trm_eq (app M N) X)}
      or (Ex [M':Trm]and (wh_red1 M M') (is_tt (Trm_eq X' (app M' N))))
         (Ex3 [u:VV][U,B:Trm]and (is_tt (Trm_eq M (lda u U B)))
                                 (is_tt (Trm_eq X' (vsub N u B))));
Immed;
(* beta *)
intros;Refine inr;
Refine Trm_eq_app_lem eq; intros eqM eqN;
Qrepl Trm_eq_subst eqM; Qrepl Trm_eq_subst eqN;
Refine Ex3In u U B; Refine pair;
Refine Trm_eq_refl; Refine Trm_eq_refl;
(* app *)
intros;Refine inl;
Refine Trm_eq_app_lem eq; intros eqM eqN;
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine ExIn A'; Refine pair premA; Refine Trm_eq_refl;
Refine Trm_eq_refl;
Save wh_red1_app_character;

Inductive [wh_ared1 : Trm->Trm->Prop]

Constructors 

[wh_ared1_beta:{u:VV}{U,A,B:Trm}wh_ared1 (app (lda u U B) A) (vsub A u B)]

[wh_ared1_app:{A,A'|Trm}{sc:is_ff (isLda A)}
             {premA:wh_ared1 A A'}
             {B:Trm}wh_ared1 (app A B) (app A' B)];

Goal wh_ared1_red1 : {A,B|Trm}(wh_ared1 A B) -> wh_red1 A B;
Refine wh_ared1_elim [A,B|Trm][_:wh_ared1 A B]wh_red1 A B;
intros;Refine wh_red1_beta;
intros;Refine wh_red1_app;Immed;
Save;

Goal wh_red1_ared1 : {A,B|Trm}(wh_red1 A B) -> wh_ared1 A B;
Refine wh_red1_elim [A,B|Trm][_:wh_red1 A B]wh_ared1 A B;
intros;Refine wh_ared1_beta;
intros L;Refine tt_or_ff (isLda L);
intros is_lda;Refine isLda_lem is_lda;
intros u U B eqL L';Qrepl (Trm_eq_subst eqL);
intros premL;Refine wh_red1_lda_character premL;
intros is_not_lda ____;Refine wh_ared1_app;Immed;
Save;

Goal wh_ared1Rec:{C:{A,B:Trm}Prop}

	    {BETA:{u:VV}{U,A,B:Trm}C (app (lda u U B) A) (vsub A u B)}

	    {APP:{A,A'|Trm}{sc:is_ff (isLda A)}
                 {premA:wh_red1 A A'}{ihA:C A A'}
                 {B:Trm}C (app A B) (app A' B)}

	    {A,B|Trm}{red:wh_red1 A B}C A B;

intros;Refine wh_ared1_elim [A,B|Trm][_:wh_ared1 A B]C A B;Immed;
intros;Refine APP;Refine +1 wh_ared1_red1;Immed;
Refine wh_red1_ared1;Immed;
Save;

Goal {M,N,X|Trm}{red_app:wh_red1 (app M N) X}
      or (Ex [M':Trm]
          and3 (is_ff (isLda M)) (wh_red1 M M')
              (is_tt (Trm_eq X (app M' N))))
         (Ex3 [u:VV][U,B:Trm]
          and (is_tt (Trm_eq M (lda u U B)))
              (is_tt (Trm_eq X (vsub N u B))));

intros;Refine wh_ared1Rec [X,X':Trm]
              {eq:is_tt (Trm_eq (app M N) X)}
               or (Ex [M':Trm]
                   and3 (is_ff (isLda M)) (wh_red1 M M')
                       (is_tt (Trm_eq X' (app M' N))))
                  (Ex3 [u:VV][U,B:Trm]
                   and (is_tt (Trm_eq M (lda u U B)))
                       (is_tt (Trm_eq X' (vsub N u B))));Immed;

intros;Refine inr;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine Ex3In u U B;Refine pair;
Refine Trm_eq_refl;
Refine Trm_eq_refl;
intros;Refine inl;
[eqM = fst (Trm_eq_app_lem eq)][eqN = snd (Trm_eq_app_lem eq)];
Qrepl Trm_eq_subst eqM;Qrepl Trm_eq_subst eqN;
Refine ExIn A';Refine pair3 sc premA;Refine Trm_eq_refl;
Refine Trm_eq_refl;
Save wh_ared1_app_character;

(* wh_red1 is deterministic *)
Goal wh_red1_determin: {A,B|Trm}(wh_red1 A B)->{C|Trm}(wh_red1 A C)->Q B C;
(* Refine wh_red1Rec [A,B|Trm]{C|Trm}(wh_red1 A C)->Q B C; *)
(* (* beta *) *)
(* intros; Refine wh_red1_app_character H; *)
(*   intros; Refine H1; intros; Refine H2; intros; *)
(*     Refine wh_red1_lda_character H3; *)
(*   intros; Refine H1; intros; Refine H2; intros; *)
(*     Qrepl Trm_eq_subst H4; Refine Trm_eq_lda_lem H3; intros; *)
(*     Qrepl VVdecide H5; Qrepl Trm_eq_subst H7; Refine Q_refl; *)
(* (* app head *) *)
(* intros; Refine wh_red1_app_character H; *)
(*   intros; Refine H1; intros; Refine H2; intros; Qrepl Trm_eq_subst H4; *)
(*     Qrepl ihA H3; Refine Q_refl; *)
(*   intros; Refine H1; intros; Refine H2; intros; *)
(*     Refine wh_red1_lda_character (?:wh_red1 (lda t s u) A'); *)
(*     Qrepl Q_sym (Trm_eq_subst H3); Immed; *)
Refine wh_ared1Rec [A,B|Trm]{C|Trm}(wh_red1 A C)->Q B C;
(* beta *)
intros; Refine wh_ared1_app_character H;
  intros; Refine H1; intros; Refine H2; intros;
    Refine tt_not_ff;Immed;
  intros; Refine H1; intros; Refine H2; intros;
    Qrepl Trm_eq_subst H4; Refine Trm_eq_lda_lem H3; intros;
    Qrepl VVdecide H5; Qrepl Trm_eq_subst H7; Refine Q_refl;
(* app head *)
intros; Refine wh_ared1_app_character H;
  intros; Refine H1; intros; Refine H2; intros; Qrepl Trm_eq_subst H5;
    Qrepl ihA H4; Refine Q_refl;
  intros; Refine H1; intros; Refine H2; intros;
    Refine B_contradiction ? sc;
    Qrepl Trm_eq_subst H3; Refine Q_refl;
Save;

(* now take the transitive closure of wh_red1 *)

Inductive [wh_redn:Trm->Trm->Prop] Constructors
 [wh_redn_refl:{A:Trm}wh_redn A A]
 [wh_redn_red1_trans:{A,D,B|Trm}{wh:wh_red1 A D}{prem:wh_redn D B}wh_redn A B];

Goal wh_rednRec:{C:{A,B:Trm}Prop}
	 {REFL:{A:Trm}C A A}
         {TRANS:{A,D,B|Trm}{wh:wh_red1 A D}{prem:wh_redn D B}{ih:C D B}
		 C A B}
	 {A,B|Trm}{r:wh_redn A B}C A B;

intros;Refine wh_redn_elim [A,B|Trm][_:wh_redn A B]C A B;Immed;
Save;

Goal {A,B|Trm}(wh_red1 A B)->wh_redn A B;
intros;Refine wh_redn_red1_trans;Refine +2 wh_redn_refl;Immed;
Save wh_redn_red1;

Goal trans wh_redn;
Expand trans;intros;
Refine wh_rednRec [A,D|Trm]
                  {B|Trm}{rt_prem:wh_redn D B}wh_redn A B;Immed;
intros;Immed;
intros;Refine wh_redn_red1_trans;Refine +2 ih;Immed;
Save wh_redn_trans;

Goal wh_no_redn:
     {A,B|Trm}(wh_redn A B)->(Vclosed A)->no_redn A B;
Refine wh_rednRec [A,B:Trm](Vclosed A)->no_redn A B;
intros;Refine no_redn_refl;Immed;
intros;Refine no_redn_trans;
  Refine +1 no_redn_red1;Refine +1 wh_no_red1;Immed;
Refine ih; Refine Vclosed_resp_wh_red1 wh H;
Save;

Goal {A,B|Trm}(wh_redn A B)->{rho:Renaming}wh_redn (renTrm rho A) (renTrm rho B);
Refine wh_rednRec [A,B:Trm]
	          {rho:Renaming}wh_redn (renTrm rho A) (renTrm rho B);
intros;Refine wh_redn_refl;
intros;Refine wh_redn_red1_trans;Refine +1 renTrm_resp_wh_red1;Immed;
Save renTrm_resp_wh_redn;

Goal {p:PP}{N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(wh_redn A B)->wh_redn (psub N p A) (psub N p B);
intros ___;
Refine wh_rednRec [A,B:Trm]wh_redn (psub N p A) (psub N p B);
intros;Refine wh_redn_refl;
intros;Refine wh_redn_red1_trans;Refine +1 psub_resp_wh_red1;Immed;
Save psub_resp_wh_redn;

Goal {A,B|Trm}(wh_redn A B)->(Vclosed A)->(Vclosed B);
Refine wh_rednRec [A,B:Trm](Vclosed A)->(Vclosed B);
intros;Immed;
intros;Refine ih;Refine Vclosed_resp_wh_red1;Immed;
Save Vclosed_resp_wh_redn;

Goal {X,Y|Trm}(wh_redn X Y)->{p|PP}(is_tt (poccur p Y))->is_tt (poccur p X);
Refine wh_rednRec [A,B:Trm]
                  {p|PP}{occur:is_tt (poccur p B)}is_tt (poccur p A);
intros;Immed;
intros;Refine wh_red1_refl_pocc;Refine +2 ih;Immed;
Save wh_redn_refl_pocc;

Goal {X,Y|Trm}(wh_redn X Y)->{p|PP}(is_ff (poccur p X))->is_ff (poccur p Y);
intros;Refine B_contrapos;Refine +1 wh_redn_refl_pocc;Immed;
Save not_pocc_resp_wh_redn;

Goal {s|SS}{A|Trm}{r:wh_redn (sort s) A}is_tt (Trm_eq A (sort s));
intros;
Refine wh_rednRec [A,A'|Trm]
                  {eq:is_tt (Trm_eq A (sort s))}is_tt (Trm_eq A' (sort s));
Immed;
intros;Immed;
intros;Refine wh_red1_sort_character
             (Q_subst (Trm_eq_subst eq) ([Y:Trm]wh_red1 Y ?) ?);Immed;
Refine Trm_eq_refl;
Save wh_redn_sort_character;

Goal {p|PP}{A|Trm}{r:wh_redn (par p) A}is_tt (Trm_eq A (par p));
intros;
Refine wh_rednRec [A,A'|Trm]
                   {eq:is_tt (Trm_eq A (par p))}is_tt (Trm_eq A' (par p));
Immed;
intros;Immed;
intros;Refine wh_red1_par_character
             (Q_subst (Trm_eq_subst eq) ([Y:Trm]wh_red1 Y ?) ?);Immed;
Refine Trm_eq_refl;
Save wh_redn_par_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:wh_redn (pi w A B) X}
      is_tt (Trm_eq X (pi w A B));
intros;Refine wh_rednRec [P,P':Trm]
              {eq:is_tt (Trm_eq P (pi w A B))}
               is_tt (Trm_eq P' (pi w A B));Immed;
intros;Immed;
intros;Refine wh_red1_pi_character
             (Q_subst (Trm_eq_subst eq) ([Y:Trm]wh_red1 Y ?) ?);Immed;
Refine Trm_eq_refl;
Save wh_redn_pi_character;

Goal {w|VV}{A,B,X|Trm}{red_pi:wh_redn (lda w A B) X}
      is_tt (Trm_eq X (lda w A B));

intros;Refine wh_rednRec [P,P':Trm]
              {eq:is_tt (Trm_eq P (lda w A B))}
               is_tt (Trm_eq P' (lda w A B));Immed;

intros;Immed;
intros;Refine wh_red1_lda_character
             (Q_subst (Trm_eq_subst eq) ([Y:Trm]wh_red1 Y ?) ?);Immed;
Refine Trm_eq_refl;
Save wh_redn_lda_character;

Goal {A,A'|Trm}(wh_redn A A')->
     {B:Trm}wh_redn (app A B) (app A' B);
Refine wh_rednRec [A,A'|Trm]
                  {B:Trm}wh_redn (app A B) (app A' B);
intros;Refine wh_redn_refl;
intros;(* Refine tt_or_ff (isLda A); *)
(* intros is_lda;Refine isLda_lem is_lda; *)
(* intros x X Y eq;Refine wh_red1_lda_character *)
(*              (Q_subst (Trm_eq_subst eq) ([Y:Trm]wh_red1 Y ?) ?);Immed; *)
(* intros is_not_lda; *)Refine wh_redn_red1_trans;Refine +1 wh_red1_app;Immed;
Save wh_redn_app;

Goal {X,Y|Trm}(wh_red1 X Y) -> (Vclosed X) -> par_red1 X Y;
Refine wh_red1Rec [X,Y:Trm]{vcl:Vclosed X}par_red1 X Y;
intros;Refine Vclosed_app_lem vcl;
intros vclL vclA;Refine Vclosed_lda_lem vclL;
intros vclU vclB;Refine fresh_params_lem1 B;
intros p noccB;Refine par_red1_beta;Immed;
Refine par_red1_refl vclA;
Refine par_red1_refl (vclB p);
intros;Refine Vclosed_app_lem vcl;
intros vclA vclB;Refine par_red1_app (ihA vclA);
Refine par_red1_refl vclB;
Save wh_par_red1;

Goal {X,Y|Trm}(wh_redn X Y) -> (Vclosed X) -> par_redn X Y;
Refine wh_rednRec [X,Y:Trm]{vcl:Vclosed X}par_redn X Y;
intros;Refine par_redn_refl;Immed;
intros;Refine par_redn_trans;
Refine +1 par_redn_red1;Refine +1 wh_par_red1;Immed;
Refine ih (Vclosed_resp_wh_red1 wh vcl);
Save wh_par_redn;

(* an inductive characterisation of the weak-head-normal terms *)
Inductive [wh_nf:Trm->Prop]  Constructors
[wh_nf_sort:{s:SS}wh_nf (sort s)]
[wh_nf_par:{p:PP}wh_nf (par p)]
[wh_nf_pi:{n:VV}{A,B:Trm}wh_nf (pi n A B)]
[wh_nf_lda:{n:VV}{A,B:Trm}wh_nf (lda n A B)]
[wh_nf_app:{A|Trm}{sc:is_ff (isLda A)}{premA:wh_nf A}{B:Trm}wh_nf (app A B)];

Goal wh_nfRec:{C:{A:Trm}Prop}
            {WHNFSORT:{s:SS}C (sort s)}
            {WHNFPAR:{p:PP}C (par p)}
            {WHNFPI:{n:VV}{A,B:Trm}C (pi n A B)}
            {WHNFLDA:{n:VV}{A,B:Trm}C (lda n A B)}
            {WHNFAPP:{A|Trm}{sc:is_ff (isLda A)}{premA:wh_nf A}{ihA:C A}
                     {B:Trm}C (app A B)}
            {A|Trm}{whnf:wh_nf A}C A;

intros;Refine wh_nf_elim [A|Trm][_:wh_nf A]C A;Immed;
intros;Refine WHNFAPP;Immed;
Save;

Goal {A|Trm}(wh_nf A)->{rho:Renaming}wh_nf (renTrm rho A);
Refine wh_nfRec [A:Trm]{rho:Renaming}wh_nf (renTrm rho A);
intros;Refine wh_nf_sort;
intros;Refine wh_nf_par;
intros;Refine wh_nf_pi;
intros;Refine wh_nf_lda;
intros;Equiv wh_nf (app (renTrm rho A) (renTrm rho B));
       Refine wh_nf_app;Qrepl renTrm_isLda rho A;Immed;
Save renTrm_resp_wh_nf;

Goal {A,B|Trm}(wh_nf (app A B))->and (is_ff (isLda A)) (wh_nf A);
intros;
Refine wh_nfRec [M|Trm]{eq:is_tt (Trm_eq (app A B) M)}
                    and (is_ff (isLda A)) (wh_nf A);Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;Qrepl Trm_eq_subst eqA;Refine pair;Immed;
Refine Trm_eq_refl;
Save wh_nf_app_lem;

Goal {A,B|Trm}(wh_red1 A B)->(wh_nf A)->absurd;
Refine wh_red1Rec [A,B|Trm]{whnf:wh_nf A}absurd;
intros;Refine tt_not_ff (fst (wh_nf_app_lem whnf));
intros;Refine ihA (snd (wh_nf_app_lem whnf));
Save wh_nf_is_nf1;

Goal {A,B|Trm}(wh_redn A B)->(wh_nf A)->is_tt (Trm_eq A B);
Refine wh_rednRec [A,B|Trm]{whnf:wh_nf A}is_tt (Trm_eq A B);
intros;Refine Trm_eq_refl;
intros;Refine wh_nf_is_nf1;Immed;
Save wh_nf_is_nf;

Goal {u|VV}{U,A,B,Xw|Trm}(wh_redn (app (lda u U B) A) Xw)->(wh_nf Xw)->
      wh_redn (vsub A u B) Xw;
intros;Refine wh_rednRec [X,Y|Trm]
              {eq:is_tt (Trm_eq X (app (lda u U B) A))}{whnf:wh_nf Y}
               wh_redn (vsub A u B) Y;Immed;
intros __;Qrepl Trm_eq_subst eq;
intros;Refine tt_not_ff (fst (wh_nf_app_lem whnf));
intros;(* Refine wh_red1_app_character (?:wh_red1 (app (lda u U B) A) ?); *)
(* Qrepl +1 Q_sym (Trm_eq_subst eq);Immed; *)
(* intros case_app;Refine case_app; *)
(* intros X hypX; Refine wh_red1_lda_character (fst hypX); *)
Refine wh_ared1_app_character (?:wh_red1 (app (lda u U B) A) ?);
Qrepl +1 Q_sym (Trm_eq_subst eq);Immed;
intros case_app;Refine case_app;
intros X hypX;Refine tt_not_ff (and3_out1 hypX);
intros case_beta;Refine case_beta;
intros x X Y hypX;Refine hypX;
intros eqLda eqD;Refine Trm_eq_lda_lem eqLda;
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqB;Qrepl Q_sym (Trm_eq_subst eqD);
Immed;
Refine Trm_eq_refl;
Save wh_redn_beta_whnf;

Goal {A,B,Xw|Trm}(wh_redn (app A B) Xw)->(is_ff (isLda A))->(wh_nf Xw)->
      Ex [Aw:Trm]and3 (wh_nf Aw) (wh_redn A Aw) (wh_redn (app Aw B) Xw);
intros;Refine wh_rednRec [X,Y|Trm]{A,B|Trm}{sc:is_ff (isLda A)}
              {eq:is_tt (Trm_eq X (app A B))}{whnf:wh_nf Y}
            Ex [Aw:Trm]and3 (wh_nf Aw) (wh_redn A Aw) (wh_redn (app Aw B) Y);
Immed;
(* beta *)
intros _____;Qrepl Trm_eq_subst eq;
intros;Refine wh_nf_app_lem whnf;
intros is_not_lda whnfA;Refine ExIn;Refine +1 pair3;Immed;
Refine wh_redn_refl;Refine wh_redn_refl;
intros;Refine wh_ared1_app_character (?:wh_red1 (app A2 B2) ?);
Qrepl +1 Q_sym (Trm_eq_subst eq);Immed;
(* app *)
intros case_app;Refine case_app;
intros X hypX;Refine hypX;
intros is_not_lda whA eqD;Refine tt_or_ff (isLda X);
intros is_lda;Refine isLda_lem is_lda;

intros x' X' Y' eqX;Refine ExIn X;Refine pair3;
Qrepl Trm_eq_subst eqX;Refine wh_nf_lda;
Refine wh_redn_red1;Immed;
Qrepl Q_sym (Trm_eq_subst eqD);Immed;
intros is_not_lda';Refine ih is_not_lda';Immed;
intros Aw hypAw;Refine hypAw;
intros whnfA whX whAw;Refine ExIn;
Refine +1 pair3;Refine +2 wh_redn_red1_trans;Immed;

intros case_beta;Refine case_beta;
intros x X Y hypX;
Refine tt_not_ff (Q_subst (Trm_eq_subst (fst hypX))
			  ([X:Trm]is_ff (isLda X)) sc);

Refine Trm_eq_refl;
Save wh_redn_app_whnf;

Goal {A,B|Trm}(wh_red1 A B)->{Aw|Trm}(wh_redn A Aw)->(wh_nf Aw)->wh_redn B Aw;
Refine wh_ared1Rec [A,B|Trm]
                  {Aw|Trm}{wh:wh_redn A Aw}{whnf:wh_nf Aw}wh_redn B Aw;
intros;Refine wh_redn_beta_whnf;Immed;
intros;Refine wh_redn_app_whnf;Immed;
intros X hypX;Refine hypX;
intros whnfX whA whX;Refine wh_redn_trans;
Refine +1 wh_redn_app;Refine +1 ihA;Immed;
Save wh_nf_is_wh_redn_extremal1;

Goal {A,B|Trm}(wh_redn A B)->{Aw|Trm}(wh_redn A Aw)->(wh_nf Aw)->wh_redn B Aw;
Refine wh_rednRec [A,B|Trm]
                  {Aw|Trm}(wh_redn A Aw)->(wh_nf Aw)->wh_redn B Aw;
intros;Immed;
intros;Refine ih;Refine wh_nf_is_wh_redn_extremal1;Immed;
Save wh_nf_is_wh_redn_extremal;

Goal {A,Aw,Aw'|Trm}(wh_redn A Aw)->(wh_redn A Aw')->(wh_nf Aw)->(wh_nf Aw')->
      is_tt (Trm_eq Aw Aw');
intros;Refine wh_nf_is_nf;Refine wh_nf_is_wh_redn_extremal;Immed;
Save wh_redn_to_wh_nf_unique;



(** alpha_conv and wh_red **)
Goal alpha_conv_resp_wh_nf:
     {A|Trm}(wh_nf A)->{B|Trm}(alpha_conv A B)->wh_nf B;
Refine wh_nfRec [A:Trm]{B|Trm}(alpha_conv A B)->wh_nf B;
(* sort *)
intros; Qrepl Trm_eq_subst (alpha_conv_sort_character H); Refine wh_nf_sort;
(* par *)
intros; Qrepl Trm_eq_subst (alpha_conv_par_character H); Refine wh_nf_par;
(* pi *)
intros; Refine alpha_conv_pi_character H; intros nn AA CC hyp;
Refine hyp; intros; Qrepl Q_sym (Trm_eq_subst H3); Refine wh_nf_pi;
(* lda *)
intros; Refine alpha_conv_lda_character H; intros nn AA CC hyp;
Refine hyp; intros; Qrepl Q_sym (Trm_eq_subst H3); Refine wh_nf_lda;
(* app *)
intros; Refine alpha_conv_app_character H; intros AA CC hyp;
Refine hyp; intros; Qrepl Q_sym (Trm_eq_subst H3); Refine wh_nf_app;
Refine tt_or_ff (isLda AA);
  intros isLdaAA; Refine isLda_lem isLdaAA; intros v XX YY hh;
    Refine alpha_conv_lda_character (?:alpha_conv (lda v XX YY) A);
    Qrepl Q_sym (Trm_eq_subst hh); Refine alpha_conv_sym H1;
    intros u X Y gg; Refine gg; intros;
    Refine tt_not_ff; Qrepl Q_sym sc; Qrepl Q_sym (Trm_eq_subst H6);
    Refine Q_refl;
  intros; Immed;
Refine ihA; Immed;
Save;

Goal wh_red1_commute_alpha_conv:
     {A,B|Trm}(alpha_conv A B)->{AA|Trm}(wh_red1 A AA)->
     Ex [BB:Trm]and (wh_red1 B BB) (alpha_conv AA BB);
intros;
Claim {A,AA|Trm}{whA:wh_red1 A AA}{B|Trm}{acAB:alpha_conv A B}
     Ex [BB:Trm]and (wh_red1 B BB) (alpha_conv AA BB);
Refine ?+1; Immed;
Refine wh_red1Rec [A,AA|Trm]{B|Trm}{acAB:alpha_conv A B}
     Ex [BB:Trm]and (wh_red1 B BB) (alpha_conv AA BB);
(* beta *)
intros; Refine alpha_conv_app_character acAB; intros lda' A1' hyp;
Refine hyp; intros;
Refine alpha_conv_lda_character H2; intros u_ U_ B1_ gyp;
Refine gyp; intros; Refine ExIn (vsub A1' u_ B1_); Refine pair;
Qrepl Q_sym (Trm_eq_subst H4); Qrepl Q_sym (Trm_eq_subst H7); 
Refine wh_red1_beta;
Refine alpha_conv_vsub; Immed;
(* app *)
intros; Refine alpha_conv_app_character acAB; intros A1' B1' hyp;
Refine hyp; intros;
Refine ihA H2; intros X h; Refine h; intros;
Refine ExIn (app X B1'); Refine pair;
Qrepl Q_sym (Trm_eq_subst H4); Refine wh_red1_app H5;
Refine alpha_conv_app; Immed;
Save;

Goal wh_redn_commute_alpha_conv:
     {A,B|Trm}(alpha_conv A B)->{AA|Trm}(wh_redn A AA)->
     Ex [BB:Trm]and (wh_redn B BB) (alpha_conv AA BB);
intros;
Claim {A,AA|Trm}{whA:wh_redn A AA}{B|Trm}{acAB:alpha_conv A B}
     Ex [BB:Trm]and (wh_redn B BB) (alpha_conv AA BB);
Refine ?+1; Immed;
Refine wh_rednRec [A,AA|Trm]{B|Trm}{acAB:alpha_conv A B}
     Ex [BB:Trm]and (wh_redn B BB) (alpha_conv AA BB);
(* refl *)
intros; Refine ExIn B1; Refine pair (wh_redn_refl ?) acAB;
(* trans *)
intros; Refine wh_red1_commute_alpha_conv acAB wh; intros DD DDh;
Refine DDh; intros;
Refine ih  H3; intros EE EEh;
Refine EEh; intros;
Refine ExIn EE; Refine pair (wh_redn_red1_trans ??); Immed;
Save;


Goal alpha_conv_wh_redn_wh_nf_lem:
     {A,C|Trm}{acAC:alpha_conv A C}
     {AA|Trm}{whA:wh_redn A AA}{wnAA:wh_nf AA}
     {CC|Trm}{whC:wh_redn C CC}{wnCC:wh_nf CC}
     alpha_conv AA CC;
intros;
Refine wh_redn_commute_alpha_conv acAC whA; intros XX XXh;
Refine XXh; intros;
Refine wh_redn_commute_alpha_conv (alpha_conv_sym acAC) whC;
intros YY YYh; Refine YYh; intros;
Claim Q AA YY; Qrepl ?+1; Refine alpha_conv_sym H3;
Refine Trm_eq_subst (wh_redn_to_wh_nf_unique whA H2 wnAA ?);
Refine alpha_conv_resp_wh_nf wnCC H3;
Save;

(* wh_red1 is really right! *)
Inductive [Wh_red1: Trm->Trm->Prop] Inversion
Constructors 
[Wh_red1_beta: {u:VV}{U,A,B:Trm}Wh_red1 (app (lda u U B) A) (vsub A u B)]

[Wh_red1_app: {A,A'|Trm}      {sc:is_ff (isLda A)} 
              {premA:Wh_red1 A A'}
              {B:Trm}Wh_red1 (app A B) (app A' B)];

Goal {A,B|Trm}(Wh_red1 A B)->wh_red1 A B;
Refine Wh_red1_elim [A,B:Trm][_:Wh_red1 A B]wh_red1 A B;
intros; Refine wh_red1_beta;
intros; Refine wh_red1_app; Immed;

Goal {A,B|Trm}(wh_red1 A B)->Wh_red1 A B;
Refine wh_red1_elim [A,B:Trm][_:wh_red1 A B]Wh_red1 A B;
intros; Refine Wh_red1_beta;
intros; Refine Wh_red1_app; Refine wh_red1_not_lda; Immed;

(****************************************************
*****************************************************)
