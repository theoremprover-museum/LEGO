Module conversion 
Import churchrosser;

(* finally, the conversion relation *)
Inductive [conv : Trm->Trm->Prop]

Constructors 

[conv_redn:{A,B|Trm}{red:par_redn A B} conv A B]

[conv_sym : {A,B|Trm}{prem:conv A B} conv B A] 

[conv_trans : {A,D,B|Trm}{lt_prem:conv A D}{rt_prem:conv D B} conv A B]; 

Goal convRec:{C:{A,B:Trm}Prop}
	 {REDN:{A,B|Trm}{r:par_redn A B}C A B}
	 {SYM:{A,B|Trm}{s_prem:conv A B}{s_ih:C A B}C B A}
	 {TRANS:{A,D,B|Trm}{lt_prem:conv A D}{lt_ih:C A D}
		           {rt_prem:conv D B}{rt_ih:C D B}
		 C A B}
	 {A,B|Trm}(conv A B)->C A B;

intros;Refine conv_elim [A,B|Trm][_:conv A B]C A B;
intros;Refine REDN;Immed;
intros;Refine SYM;Immed;
intros;Refine TRANS;Immed;
Immed;
Save;

Goal {A|Trm}(Vclosed A)->conv A A;
intros;Refine conv_redn; 
Refine par_redn_red1; Refine par_red1_refl;Immed;
Save conv_refl;

Goal {A,B|Trm}(conv A B)->{rho:Renaming}conv (renTrm rho A) (renTrm rho B);
Refine convRec [A,B:Trm]
	{rho:Renaming}conv (renTrm rho A) (renTrm rho B);
intros;Refine conv_redn;Refine renTrm_resp_par_redn;Immed;
intros;Refine conv_sym;Immed;
intros;Refine conv_trans;Immed;
Save renTrm_resp_conv;

Goal {A,B|Trm}(conv A B)-> and (Vclosed A) (Vclosed B);
Refine convRec [A,B:Trm]and (Vclosed A) (Vclosed B);
intros;Refine par_redn_Vclosed;Immed;
intros;Refine s_ih;
intros vclA vclB;Refine pair;Immed;
intros;Refine lt_ih;
intros vclA _;Refine rt_ih;
intros _ vclB;Refine pair;Immed;
Save conv_Vclosed;

Goal {N|Trm}{vclN:Vclosed N}
     {A,B|Trm}(conv A B)->{p:PP}conv (psub N p A) (psub N p B);
intros ___;
Refine convRec [A,B:Trm]{p:PP}conv (psub N p A) (psub N p B);
intros;Refine conv_redn;Refine psub_resp_par_redn;Immed;
intros;Refine conv_sym;Immed;
intros;Refine conv_trans;Immed;
Save psub_resp_conv;

Goal {A,B|Trm}(conv A B)->
      Ex [C:Trm]and (par_redn A C) (par_redn B C);
Refine convRec [A,B|Trm]Ex [C:Trm]and (par_redn A C) (par_redn B C);

intros;Refine ExIn (* B *);Refine +1 pair r;
Refine par_redn_refl (snd (par_redn_Vclosed r));

intros;Refine s_ih;
intros C hypC;Refine ExIn (* C *);Refine +1 pair (snd hypC) (fst hypC);

intros;Refine lt_ih;
intros C1 hypC1;Refine rt_ih;
intros C2 hypC2;Refine par_redn_DP (snd hypC1) (fst hypC2);
intros C hypC;Refine ExIn (* C *);Refine +1 pair;
Refine +1 par_redn_trans (fst hypC1) (fst hypC);
Refine par_redn_trans (snd hypC2) (snd hypC);

Save convCR;

Goal {s|SS}{A|Trm}{c:conv (sort s) A}par_redn A (sort s);
intros;Refine convCR c;
intros C hyp;Refine hyp; 
intros h1 h2;
Qrepl Q_sym (Trm_eq_subst (par_redn_sort_character h1));
Immed;
Save conv_sort_character;

Goal {s,t|SS}(conv (sort s) (sort t))->is_tt (SSeq s t);
intros;Refine par_redn_sort_character (conv_sort_character H);
Save conv_sort_sort_lem;

Goal {X,Y|Trm}{convXY:conv X Y}
     {s|SS}{redXs:par_redn X (sort s)}par_redn Y (sort s);
intros;Refine convCR convXY;
intros S hypS;Refine par_redn_trans (snd hypS);
Refine par_rednCR_sort_character (fst hypS) redXs; 
Save convCR_sort_character;

Goal {p|PP}{A|Trm}{c:conv (par p) A}par_redn A (par p);
intros;
Refine convCR c; intros C hyp; Refine hyp; intros h1 h2;
Qrepl Q_sym (Trm_eq_subst (par_redn_par_character h1));
Immed;
Save conv_par_character;

Goal {p,q|PP}(conv (par p) (par q))->is_tt (PPeq p q);
intros; Refine par_redn_par_character (conv_par_character H);
Save conv_par_par_lem;

Goal {X,Y|Trm}{convXY:conv X Y}
     {p|PP}{redXp:par_redn X (par p)}par_redn Y (par p);
intros;Refine convCR convXY;
intros P hypP;Refine par_redn_trans (snd hypP);
Refine par_rednCR_par_character (fst hypP) redXp;
Save convCR_par_character;

Goal {A,A'|Trm}{convA:conv A A'}
     {u,v|VV}{p|PP}
     {B,B'|Trm}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {convB:conv (alpha p u B) (alpha p v B')}
      conv (pi u A B) (pi v A' B');
intros;Refine convCR convA;
intros A0 hypA;Refine hypA;
intros redA redA';Refine convCR convB;
intros B0;Refine shape_lemma p B0;
intros w B1 shapeB;Refine shapeB;
intros eqB1 noccB1;Qrepl Trm_eq_subst eqB1;
intros hypB;Refine hypB;
intros redB redB';
Refine conv_trans 
       (conv_redn (par_redn_pi redA noccB noccB1 redB))
       (conv_sym (conv_redn (par_redn_pi redA' noccB' noccB1 redB')));

Save conv_pi;

Goal {A,A'|Trm}{convA:conv A A'}
     {u,v|VV}{p|PP}
     {B,B'|Trm}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {convB:conv (alpha p u B) (alpha p v B')}
      conv (lda u A B) (lda v A' B');
intros;Refine convCR convA;
intros A0 hypA;Refine hypA;
intros redA redA';Refine convCR convB;
intros B0;Refine shape_lemma p B0;
intros w B1 shapeB;Refine shapeB;
intros eqB1 noccB1;Qrepl Trm_eq_subst eqB1;
intros hypB;Refine hypB;
intros redB redB';
Refine conv_trans 
       (conv_redn (par_redn_lda redA noccB noccB1 redB))
       (conv_sym (conv_redn (par_redn_lda redA' noccB' noccB1 redB')));

Save conv_lda;

Goal {A,A'|Trm}{convA:conv A A'}
     {B,B'|Trm}{convB:conv B B'}
      conv (app A B) (app A' B');
intros;Refine convCR convA;
intros A0 hypA;Refine hypA;
intros redA redA';Refine convCR convB;
intros B0 hypB;Refine hypB;
intros redB redB';
Refine conv_trans 
       (conv_redn (par_redn_app redA redB))
       (conv_sym (conv_redn (par_redn_app (snd hypA) (snd hypB))));

Save conv_app;

Goal {u|VV}{A,B,X|Trm}{c:conv (pi u A B) X}
      Ex3 [A',B':Trm][v:VV]
      and3 (par_redn X (pi v A' B'))
           (par_redn A A')
           ({q:PP}par_redn (alpha q u B) (alpha q v B'));
intros;Refine convCR c;
intros C hypC;Refine par_redn_pi_character (fst hypC);
intros v A' B' hyp;
[redA = and3_out1 hyp];
[redB = and3_out2 hyp];
[eqP = Trm_eq_subst (and3_out3 hyp)];
Refine Ex3In A' B' v;Qrepl eqP;Refine pair3;
(* par_redn X (pi v A' B') *) Refine snd hypC;
(* par_redn A A' *) Refine redA;
(* {q:PP}par_redn (alpha q u B) (alpha q v B') *) Refine redB;

Save conv_pi_character;

Goal {X,Y|Trm}{convXY:conv X Y}
     {u|VV}{A,B|Trm}{redXpi:par_redn X (pi u A B)}
      Ex3 [v:VV][A',B':Trm]
      and3 (par_redn Y (pi v A' B'))
           (par_redn A A')
           ({q:PP}par_redn (alpha q u B) (alpha q v B'));
intros;Refine convCR convXY;
intros X' hypX;Refine par_rednCR_pi_character (fst hypX) redXpi;
intros v A' B' hypP;Refine Ex3In v A' B';
Refine pair3 (par_redn_trans (snd hypX) (and3_out1 hypP))
             (and3_out2 hypP) (and3_out3 hypP); 
Save convCR_pi_character;

Goal {u,v|VV}{A,A',B,B'|Trm}{c:conv (pi u A B) (pi v A' B')}
      and (conv A A') ({q:PP}conv (alpha q u B) (alpha q v B'));
intros;Refine convCR c;
intros X hypX;Refine par_redn_pi_character (fst hypX);
intros x Ac Bc hypL;
[redAlc = and3_out1 hypL][redBlc = and3_out2 hypL];
[eqL = Trm_eq_subst (and3_out3 hypL)];
Refine par_redn_pi_character (snd hypX);
intros x' Ac' Bc' hypR;
[redArc = and3_out1 hypR][redBrc = and3_out2 hypR];
[eqR = Trm_eq_subst (and3_out3 hypR)];
Refine Trm_eq_pi_lem (?:is_tt (Trm_eq (pi x Ac Bc) (pi x' Ac' Bc')));
Qrepl eqL;Qrepl eqR;Refine Trm_eq_refl;
intros eqV eqA eqB;
Refine pair;
(* conv A A' *)
Refine conv_trans (conv_redn redAlc);
Qrepl Trm_eq_subst eqA;
Refine (conv_sym (conv_redn redArc));
(* conv (alpha q u B) (alpha q v B') *)
intros;Refine fresh_params_lem4 B B' Bc Bc';
intros r rFresh;Refine rFresh;
intros noccB noccB' noccBc noccBc';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) u noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) v noccB'));
Refine psub_resp_conv (Vclosed_par ?); 
Refine conv_trans (conv_redn ?) (conv_sym (conv_redn ?));
Refine +1 redBlc; 
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqB;
Refine redBrc;

Save convCR_pi_lem;

Goal {u|VV}{A,B,X|Trm}{c:conv (lda u A B) X}
      Ex3 [A',B':Trm][v:VV]
      and3 (par_redn X (lda v A' B'))
           (par_redn A A')
           ({q:PP}par_redn (alpha q u B) (alpha q v B'));
intros;Refine convCR c;
intros C hypC;Refine par_redn_lda_character (fst hypC);
intros v A' B' hyp;
[redA = and3_out1 hyp];
[redB = and3_out2 hyp];
[eqP = Trm_eq_subst (and3_out3 hyp)];
Refine Ex3In A' B' v;Qrepl eqP;Refine pair3;
(* par_redn X (lda v A' B') *) Refine snd hypC;
(* par_redn A A' *) Refine redA;
(* {q:PP}par_redn (alpha q u B) (alpha q v B') *) Refine redB;

Save conv_lda_character;

Goal {u,v|VV}{A,A',B,B'|Trm}{c:conv (lda u A B) (lda v A' B')}
      and (conv A A') ({q:PP}conv (alpha q u B) (alpha q v B'));
intros;Refine convCR c;
intros X hypX;Refine par_redn_lda_character (fst hypX);
intros x Ac Bc hypL;
[redAlc = and3_out1 hypL][redBlc = and3_out2 hypL];
[eqL = Trm_eq_subst (and3_out3 hypL)];
Refine par_redn_lda_character (snd hypX);
intros x' Ac' Bc' hypR;
[redArc = and3_out1 hypR][redBrc = and3_out2 hypR];
[eqR = Trm_eq_subst (and3_out3 hypR)];
Refine Trm_eq_lda_lem (?:is_tt (Trm_eq (lda x Ac Bc) (lda x' Ac' Bc')));
Qrepl eqL;Qrepl eqR;Refine Trm_eq_refl;
intros eqV eqA eqB;
Refine pair;
(* conv A A' *)
Refine conv_trans (conv_redn redAlc);
Qrepl Trm_eq_subst eqA;
Refine (conv_sym (conv_redn redArc));
(* conv (alpha q u B) (alpha q v B') *)
intros;Refine fresh_params_lem4 B B' Bc Bc';
intros r rFresh;Refine rFresh;
intros noccB noccB' noccBc noccBc';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) u noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) v noccB'));
Refine psub_resp_conv (Vclosed_par ?); 
Refine conv_trans (conv_redn ?) (conv_sym (conv_redn ?));
Refine +1 redBlc; 
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqB;
Refine redBrc;

Save convCR_lda_lem;

Goal {p|PP}{M|Trm}(Vclosed M)->
     {N,N'|Trm}(conv N N')-> conv (psub N p M) (psub N' p M);
intros ___;
Refine convRec [N,N'|Trm]conv (psub N p M) (psub N' p M);
intros;Refine conv_redn;Refine par_redn_refl_psub_lem;Immed;
intros;Refine conv_sym;Immed;
intros;Refine conv_trans;Immed;
Save conv_refl_psub_lem;

Goal {p|PP}{M,M'|Trm}{redM:par_redn M M'}
     {N,N'|Trm}{cNN:conv N N'}
      conv (psub N p M) (psub N' p M');
intros;Refine convCR cNN;
intros N0 hyp;Refine hyp;
intros redN redN';Refine conv_trans;
Refine +2 conv_sym;Refine +2 conv_redn;
Refine +2 par_redn_refl_psub_lem;Refine +1 snd (par_redn_Vclosed redM);
Refine conv_redn;Refine par_redn_psub;Immed;
Save conv_redn_psub_lem;

Goal {N,N'|Trm}(conv N N')->
     {X,X'|Trm}(conv X X')->
     {p:PP} conv (psub N p X) (psub N' p X');
intros;
Refine convRec [M,M'|Trm]
               {N,N'|Trm}{c:conv N N'}
                conv (psub N p M) (psub N' p M');Immed;
intros;Refine conv_redn_psub_lem;Immed;
intros;Refine conv_sym;Refine s_ih;Refine conv_sym;Immed;
intros;Refine conv_trans;Refine +1 lt_ih;Refine +2 rt_ih;
       Refine +1 conv_refl;Refine fst (conv_Vclosed ?);Immed;
Save conv_psub;

Goal {N,N'|Trm}(conv N N')->
     {u,v:VV}{X,X'|Trm}({q:PP}conv (alpha q u X) (alpha q v X'))->
      conv (vsub N u X) (vsub N' v X');
intros;Refine fresh_params_lem2 X X';
intros q qFresh;Refine qFresh;
intros noccX noccX';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N u noccX));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N' v noccX'));
Refine conv_psub;Immed;
Save conv_vsub;

Goal {N,N'|Trm}(conv N N')->
     {u|VV}{X|Trm}({q:PP}Vclosed (alpha q u X))->
     conv (vsub N u X) (vsub N' u X);
intros; Refine fresh_params_lem1 X; intros q noccX;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N u noccX));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N' u noccX));
Refine conv_psub; Refine +1 conv_refl; Immed;
Save special_conv_vsub;

Goal {v|VV}{A,B|Trm}{s|SS}not (conv (sort s) (pi v A B));
Expand not; intros;
Refine par_redn_pi_character (conv_sort_character H);
intros u X Y hyp;
Refine tt_not_ff (Q_sym (and3_out3 hyp));
Save not_conv_sort_pi;

Goal decide_conv_sorts: {s,t:SS}decidable (conv (sort s) (sort t));
intros; Refine tt_or_ff (SSeq s t);
intros eqst; Qrepl SSdecide eqst; Refine inl (conv_refl (Vclosed_sort ?));
intros nest; Refine inr; Intros cst; Refine tt_not_ff;
  Qrepl Q_sym (conv_sort_sort_lem cst);
  Qrepl Q_sym nest; Refine Q_refl;
Save;
