Module beta_normal Import alpha_conversion;

%\VerbFileOpen beta_norm
Inductive [beta_norm:Trm->Prop]  NoReductions  Constructors
[bn_sort:{s:SS}beta_norm (sort s)]

[bn_par:{p:PP}beta_norm (par p)]

[bn_pi:{A,B|Trm}{v|VV}
      {lprem:beta_norm A}
      {rprem:{p:PP}beta_norm (alpha p v B)}
    (***************************************)
          beta_norm (pi v A B)]

[bn_lda:{A,B|Trm}{v|VV}
      {lprem:beta_norm A}
      {rprem:{p:PP}beta_norm (alpha p v B)}
    (***************************************)
          beta_norm (lda v A B)]

[bn_app:{A,B|Trm}{sc:is_ff (isLda A)}
      {lprem:beta_norm A}
      {rprem:beta_norm B}
    (***************************************)
          beta_norm (app A B)];
%\VerbFileClos beta_norm


%\VerbFileOpen beta_norm_Vclosed
Goal beta_norm_Vclosed: {A|Trm}(beta_norm A)->Vclosed A;
%\VerbFileClos beta_norm_Vclosed
intros; Refine aVclosed_Vclosed; 
Refine beta_norm_elim [A:Trm][_:beta_norm A]aVclosed A;
intros; Refine aVclosed_sort;
intros; Refine aVclosed_par;
intros; Refine aVclosed_pi; Immed;
intros; Refine aVclosed_lda; Immed;
intros; Refine aVclosed_app; Immed;
Immed;
Save;

Goal beta_norm_gen_pi:
     {A,B|Trm}{v|VV}(beta_norm (pi v A B))->
     and (beta_norm A) ({p:PP}beta_norm (alpha p v B));
intros;
Refine beta_norm_elim [X:Trm][_:beta_norm X](is_tt (Trm_eq X (pi v A B)))->
     and (beta_norm A) ({p:PP}beta_norm (alpha p v B));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Trm_eq_pi_lem H1; intros v1v A1A B1B;
Qrepl Q_sym (VVdecide v1v); 
Qrepl Q_sym (Trm_eq_subst A1A); Qrepl Q_sym (Trm_eq_subst B1B);
Refine pair; Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save;

Goal beta_norm_gen_lda:
     {A,B|Trm}{v|VV}(beta_norm (lda v A B))->
     and (beta_norm A) ({p:PP}beta_norm (alpha p v B));
intros;
Refine beta_norm_elim [X:Trm][_:beta_norm X](is_tt (Trm_eq X (lda v A B)))->
     and (beta_norm A) ({p:PP}beta_norm (alpha p v B));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Trm_eq_lda_lem H1; intros v1v A1A B1B;
Qrepl Q_sym (VVdecide v1v); 
Qrepl Q_sym (Trm_eq_subst A1A); Qrepl Q_sym (Trm_eq_subst B1B);
Refine pair; Immed;
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save;

Goal beta_norm_gen_app:
     {A,B|Trm}(beta_norm (app A B))->
     and3 (beta_norm A) (beta_norm B) (is_ff (isLda A));
intros;
Refine beta_norm_elim [X:Trm][_:beta_norm X](is_tt (Trm_eq X (app A B)))->
     and3 (beta_norm A) (beta_norm B) (is_ff (isLda A));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Trm_eq_app_lem H1; intros eqA1A eqB1B;
Qrepl Q_sym (Trm_eq_subst eqA1A); Qrepl Q_sym (Trm_eq_subst eqB1B);
Refine pair3; Immed;
Immed; Refine Trm_eq_refl;
Save;

Goal par_red1_bnorm_is_alpha_conv:
     {A,B|Trm}(par_red1 A B)->(beta_norm A)->alpha_conv A B;
Refine par_red1Rec [A,B:Trm](beta_norm A)->alpha_conv A B;
(* sort *)
intros; Refine alpha_conv_refl_sort;
(* par *)
intros; Refine alpha_conv_refl_par;
(* beta: cannot happen *)
intros; Refine tt_not_ff (and3_out3 (beta_norm_gen_app H));
(* pi *)
intros; Refine alpha_conv_pi; Immed;
Refine ihA; Refine fst (beta_norm_gen_pi H);
Refine ihB; Refine snd (beta_norm_gen_pi H);
(* lda *)
intros; Refine alpha_conv_lda; Immed;
Refine ihA; Refine fst (beta_norm_gen_lda H);
Refine ihB; Refine snd (beta_norm_gen_lda H);
(* app *)
intros; Refine alpha_conv_app;
Refine ihA; Refine and3_out1 (beta_norm_gen_app H);
Refine ihB; Refine and3_out2 (beta_norm_gen_app H);
Save;

Goal par_red1_bnorm_is_bnorm:
     {A,B|Trm}(par_red1 A B)->(beta_norm A)->beta_norm B;
intros;
Refine par_ared1Rec [A,B:Trm](beta_norm A)->beta_norm B;
(* sort *)
intros; Immed;
(* par *)
intros; Immed;
(* beta: cannot happen *)
intros; Refine tt_not_ff (and3_out3 (beta_norm_gen_app H2));
(* pi *)
intros; Refine beta_norm_gen_pi H2; intros bnA bnB;
Refine bn_pi; Refine ihA bnA; intros q; Refine ihB ? (bnB ?);
(* lda *)
intros; Refine beta_norm_gen_lda H2; intros bnA bnB;
Refine bn_lda; Refine ihA bnA; intros q; Refine ihB ? (bnB ?);
(* app *)
intros; Refine beta_norm_gen_app H2; intros bnA bnB nlda;
Refine bn_app; 
[acA1A' : alpha_conv A1 A'
        = par_red1_bnorm_is_alpha_conv premA bnA];
Refine tt_or_ff (isLda A');
intros ldaA; Refine isLda_lem ldaA; intros v X Y h;
Refine alpha_conv_lda_character (?:alpha_conv (lda v X Y) A1);
Qrepl Q_sym (Trm_eq_subst h); Refine alpha_conv_sym acA1A';
intros; Refine H3; intros; Refine tt_not_ff;
Qrepl Q_sym nlda; Qrepl Q_sym (Trm_eq_subst H6); Refine Q_refl;
intros; Immed;
Refine ihA bnA; Refine ihB bnB;
Immed;
Save;

%\VerbFileOpen par_redn_bnorm_is_bnorm
Goal par_redn_bnorm_is_bnorm:
     {A,B|Trm}(par_redn A B)->(beta_norm A)->beta_norm B;
%\VerbFileClos par_redn_bnorm_is_bnorm
Refine par_rednRec [A,B:Trm](beta_norm A)->beta_norm B;
intros; Refine par_red1_bnorm_is_bnorm; Immed;
intros; Refine rt_ih (lt_ih H);
Save;

(************  not in use ******
Goal par_redn_lngth: {A,B|Trm}(par_redn A B)->NN;
Refine par_rednRec [A,B:Trm][_:par_redn A B]NN;
intros; Refine one;
intros; Refine S (add lt_ih rt_ih);
Save;

Goal par_redn_WF_ind:
     {f:{A,B|Trm}{R:par_redn A B}NN}
     {C:{A,B|Trm}{R:par_redn A B}Prop}
     {wf_ih:{A,B|Trm}{R:par_redn A B}
            {ih:{a,b|Trm}{r:par_redn a b}(Lt (f r) (f R))->C r}C R}
     {A,B|Trm}{R:par_redn A B}C R;
intros;
Refine complete_induction [n:NN]{A,B:Trm}{R:par_redn A B}(Q n (f R))->C R;
intros; Refine wf_ih;
intros; Refine H; Refine f r; Qrepl H1; Refine H2; Refine Q_refl;
Refine +1 Q_refl;
Save;
**********************************)


%\VerbFileOpen par_redn_bnorm_is_alpha_conv
Goal par_redn_bnorm_is_alpha_conv:
     {A,B|Trm}(par_redn A B)->(beta_norm A)->alpha_conv A B;
%\VerbFileClos par_redn_bnorm_is_alpha_conv
Refine par_rednRec [A,B:Trm](beta_norm A)->alpha_conv A B;
(* red1 *)
intros; Refine par_red1_bnorm_is_alpha_conv; Immed;
(* trans *)
intros; Refine alpha_conv_trans (lt_ih ?) (rt_ih ?);
Refine +1 par_redn_bnorm_is_bnorm lt_prem H; Immed;
Save;


(* normal forms and normalizing terms *)
%\VerbFileOpen normalizing
[normal_form [N,A:Trm] = and (beta_norm N) (par_redn A N)];
[normalizing [A:Trm] = Ex [B:Trm] normal_form B A];
%\VerbFileClos normalizing

Goal normalizing_red_normalizing:
     {A|Trm}(normalizing A)->{B|Trm}(par_redn A B)->normalizing B;
intros; Refine H; intros AA h; Refine h; intros bnAA redAAA;
Refine par_redn_DP H1 redAAA; intros X g; Refine g; intros;
Refine ExIn X; Refine pair; Refine par_redn_bnorm_is_bnorm; Immed;
Save;

%\VerbFileOpen nf_unique
Goal nf_unique:
     {A|Trm}{M,N|Trm}(normal_form M A)->(normal_form N A)->alpha_conv M N;
%\VerbFileClos nf_unique
intros ___ nfMA nfNA; Refine nfMA; intros; Refine nfNA; intros;
Refine par_redn_DP H1 H3; intros X Xh; Refine Xh; intros;
Refine alpha_conv_trans;
Refine +2 alpha_conv_sym; Refine +2 par_redn_bnorm_is_alpha_conv;
Refine +1 par_redn_bnorm_is_alpha_conv;
Immed;
Save;


%\VerbFileOpen nf_alpha_class
Goal nf_alpha_class:
     {A|Trm}{M,N|Trm}(normal_form M A)->(alpha_conv M N)->normal_form N A;
%\VerbFileClos nf_alpha_class
intros ___ nfMA alpMN; Refine nfMA; intros; Refine pair;
Refine par_red1_bnorm_is_bnorm ? H;
Refine +1 par_redn_trans H1 (par_redn_red1 ?+0);
Refine alpha_conv_par_red1 alpMN;
Save;

Goal normalizing_pi_subterms_normalizing:
     {A,B|Trm}{v|VV}(normalizing (pi v A B))->
     and (normalizing A) ({p:PP}normalizing (alpha p v B));
intros; Refine H; intros X nfX; Refine nfX; intros bnX redPiX;
Refine par_redn_pi_character redPiX; intros v' A' B' h;
    Refine h; intros redA redB eqPi;
Refine beta_norm_gen_pi|A'|B'|v'; Qrepl (Trm_eq_subst eqPi); Immed;
intros bnA' bnB'; Refine pair;
Refine ExIn A'; Refine pair; Immed;
intros p; Refine ExIn (alpha p v' B'); Refine pair; Immed;
Save;

(* this lemma used for typ_syn *)
Goal red_normalizing_pi_subterms_normalizing:
     {X|Trm}(normalizing X)->
     {A,B|Trm}{v|VV}(par_redn X (pi v A B))->
     and (normalizing A) ({p:PP}normalizing (alpha p v B));
intros; Refine normalizing_pi_subterms_normalizing;
Refine normalizing_red_normalizing; Immed;
Save;


(* some decidability results *)

%\VerbFileOpen RedToSortPi
[RedToSort [A:Trm] = Ex [s:SS] par_redn A (sort s)];
[RedToPi [A:Trm] = Ex3 [X,Y:Trm][v:VV] par_redn A (pi v X Y)];
%\VerbFileClos RedToSortPi

(* The 'Vclosed' assumptions are apparently needed because these
 * are essentially church-rosser arguments
 *)
%\VerbFileOpen normalizing_decides
Goal normalizing_decides_RedToSort:
     {A|Trm}(normalizing A)->decidable (RedToSort A);
%\VerbFileNoRecord normalizing_decides
intros A nlzA; Refine nlzA; intros nA nAh;
Refine nAh; intros bnnA redAnA;
[vclnA : Vclosed nA = beta_norm_Vclosed bnnA];
Refine decide_IsSrt nA;
intros isnA; Refine inl; Refine isnA; intros s eqnAs; Refine ExIn s;
  Qrepl Q_sym (Trm_eq_subst eqnAs); Immed;
intros nisnA; Refine inr; Refine contrapos ? nisnA;
  intros rtsA; Refine rtsA; intros s As; Refine ExIn s;
  Refine par_redn_DP redAnA As; intros D Dh; Refine Dh; intros nAD sD;
  Refine alpha_conv_sort_character; Refine alpha_conv_sym;
  Qrepl Q_sym (Trm_eq_subst (par_redn_sort_character sD)); 
  Refine par_redn_bnorm_is_alpha_conv nAD bnnA;
Save;

(* this proof can be simplified as above !! *)
%\VerbFileRecord normalizing_decides
Goal normalizing_decides_RedToPi:
     {A|Trm}(normalizing A)->decidable (RedToPi A);
%\VerbFileClos normalizing_decides
intros A nlzA; Refine nlzA; intros nA nAh;
Refine nAh; intros bnnA redAnA;
Refine beta_norm_elim [X:Trm][_:beta_norm X]
       {eq:Q nA X}(par_redn A X)->or (RedToPi A) (not (RedToPi A));
(* sort *)
intros; Refine inr; Intros RTSA; Refine RTSA; intros X Y u redApi;
Refine convCR_pi_character (conv_redn H) redApi; intros vv XX YY hh;
Refine hh; intros redspi __;
Refine tt_not_ff (Q_sym (par_redn_sort_character redspi));
(* par *)
intros; Refine inr; Intros RTSA; Refine RTSA; intros X Y u redApi;
Refine convCR_pi_character (conv_redn H) redApi; intros vv XX YY hh;
Refine hh; intros redppi __;
Refine tt_not_ff (Q_sym (par_redn_par_character redppi));
(* pi *)
intros; Refine inl; Refine Ex3In A1 B v; Immed;
(* lda *)
intros; Refine inr; Intros RTSA; Refine RTSA; intros X Y u redApi;
Refine convCR_pi_character (conv_redn H) redApi; intros vv XX YY hh;
Refine hh; intros redldapi __;
Refine par_redn_lda_character redldapi;
intros ___ gg; Refine gg; intros __ jj; Refine tt_not_ff (Q_sym jj);
(* app *)
intros; Refine inr; Intros RTSA; Refine RTSA; intros X Y u redApi;
Refine convCR_pi_character (conv_redn H) redApi; intros vv XX YY hh;
Refine hh; intros redapppi __;
Refine tt_not_ff;
Claim conv (pi u X Y) nA;
Refine conv_pi_character ?+1; intros XX YY uu kk;
Refine kk; intros rednapi __;
Refine alpha_conv_pi_character
       (alpha_conv_sym (par_redn_bnorm_is_alpha_conv rednapi bnnA));
intros uuu XXX YYY jj; Refine jj; intros __ eqpi;
Qrepl Q_sym eqpi;
Qrepl eq; Refine Q_refl;
Refine conv_trans (conv_sym (conv_redn redApi))
                  (conv_redn redAnA);
Immed; Refine Q_refl;
Save;


%\VerbFileOpen normalizing_decides_conv
Goal normalizing_decides_conv:
     {A,B|Trm}(normalizing A)->(normalizing B)->decidable (conv A B);
%\VerbFileClos normalizing_decides_conv
intros A B nlzA nlzB;
Refine nlzA; intros nA nAh; Refine nAh; intros bnnA redAnA;
Refine nlzB; intros nB nBh; Refine nBh; intros bnnB redBnB;
[vclnA : Vclosed nA = beta_norm_Vclosed bnnA];
[vclnB : Vclosed nB = beta_norm_Vclosed bnnB];
Refine decide_alpha_conv vclnA vclnB;
intros acnAnB; Refine inl;
  Refine conv_trans (conv_redn redAnA)
                    (conv_trans (alpha_conv_conv acnAnB)
                                (conv_sym (conv_redn redBnB)));
intros nacnAnB; Refine inr; Refine contrapos ? nacnAnB; intros cnvAB;
Refine convCR (?:conv nA nB);
Refine conv_trans (conv_sym (conv_redn redAnA))
                  (conv_trans cnvAB (conv_redn redBnB));
intros D Dh; Refine Dh; intros nAD nBD;
Refine alpha_conv_trans ? (alpha_conv_sym ?);
Refine +1 par_redn_bnorm_is_alpha_conv nAD;
Refine +1 par_redn_bnorm_is_alpha_conv nBD; Immed;
Save;
