Module conversion_bp Import conversion churchrosser_bp;

(* the beta-pi conversion relation *)
$[conv_bp : Trm->Trm->Prop]
$[conv_bp_refl : refl conv_bp];
$[conv_bp_sym : sym conv_bp];
$[conv_bp_trans :
         {A,D,B|Trm}(conv_bp A D)->(Vclosed D)->(conv_bp D B)->conv_bp A B];
$[conv_bp_redn:{A,B|Trm}(par_bp_redn A B)->conv_bp A B];
$[conv_bpRec:{C:{A,B|Trm}(conv_bp A B)->Prop}
	 {REFL:{A:Trm}C (conv_bp_refl A)}
	 {SYM:{A,B|Trm}{s_prem:conv_bp A B}{s_ih:C s_prem}C (conv_bp_sym s_prem)}
	 {TRANS:{A,D,B|Trm}{lt_prem:conv_bp A D}{lt_ih:C lt_prem}{vclD:Vclosed D}
		           {rt_prem:conv_bp D B}{rt_ih:C rt_prem}
		 C (conv_bp_trans lt_prem vclD rt_prem)}
	 {REDN:{A,B|Trm}{r:par_bp_redn A B}C (conv_bp_redn r)}
	 {A,B|Trm}{c:conv_bp A B}C c];

Goal {A,B|Trm}(conv A B)->conv_bp A B;
Refine convRec [A,B|Trm]conv_bp A B;
intros;Refine conv_bp_redn;Refine par_redn_bp_redn;Immed;
intros;Refine conv_bp_sym;Immed;
intros;Refine conv_Vclosed lt_prem; intros;
   Refine conv_bp_trans;Immed;
Save conv_conv_bp;

Goal {A,B|Trm}(conv_bp A B)->
     {rho:Renaming}conv_bp (renTrm rho A) (renTrm rho B);
Refine conv_bpRec [A,B:Trm][_:conv_bp A B]
     {rho:Renaming}conv_bp (renTrm rho A) (renTrm rho B);
intros;Refine conv_bp_refl;
intros;Refine conv_bp_sym;Immed;
intros;Refine conv_bp_trans;Refine +2 renTrm_resp_Vclosed;Immed;
intros; Refine conv_bp_redn;Refine renTrm_resp_par_bp_redn;Immed;
Save renTrm_resp_conv_bp;

Goal {N|Trm}{vclN:Vclosed N}{p:PP}
     {A,B|Trm}(conv_bp A B)->conv_bp (psub N p A) (psub N p B);
intros ___;
Refine conv_bpRec [A,B:Trm][_:conv_bp A B]conv_bp (psub N p A) (psub N p B);
intros;Refine conv_bp_refl;
intros;Refine conv_bp_sym;Refine s_ih;
intros;Refine conv_bp_trans;Refine +2 psub_resp_Vclosed;Immed;
intros;Refine conv_bp_redn;Refine psub_resp_par_bp_redn;Immed;
Save psub_resp_conv_bp;

Goal {A,B|Trm}(conv_bp A B)->(Vclosed A)->(Vclosed B)->
      Ex [C:Trm]and (par_bp_redn A C) (par_bp_redn B C);
Refine conv_bpRec [A,B|Trm][_:conv_bp A B]{vclL:Vclosed A}{vclR:Vclosed B}
                 Ex [C:Trm]and (par_bp_redn A C) (par_bp_redn B C);

intros;Refine ExIn A;Refine pair;Refine par_bp_redn_refl;Refine par_bp_redn_refl;

intros;Refine s_ih vclR vclL;
intros C hypC;Refine ExIn C;Refine pair (snd hypC) (fst hypC);

intros;Refine lt_ih vclL vclD;
intros C1 hypC1;Refine rt_ih vclD vclR;
intros C2 hypC2;Refine par_bp_redn_DP vclD (snd hypC1) (fst hypC2);
intros C hypC;Refine ExIn C;Refine pair;
Refine par_bp_redn_trans (fst hypC1) (fst hypC);
Refine par_bp_redn_trans (snd hypC2) (snd hypC);

intros;Refine ExIn B;Refine pair r (par_bp_redn_refl ?);

Save conv_bpCR;

Goal {s|SS}{A|Trm}{c:conv_bp (sort s) A}{vclA:Vclosed A}par_bp_redn A (sort s);
intros;Refine conv_bpCR c (Vclosed_sort s) vclA;
intros C hyp;
Qrepl Q_sym (Trm_eq_subst (par_bp_redn_sort_character (fst hyp)));
Refine snd hyp;
Save conv_bp_sort_character;

Goal {s,t|SS}(conv_bp (sort s) (sort t))->is_tt (SSeq s t);
intros;
Refine par_bp_redn_sort_character (conv_bp_sort_character H (Vclosed_sort ?));
Save conv_bp_sort_sort_lem;

Goal {X,Y|Trm}{conv_bpXY:conv_bp X Y}{vclX:Vclosed X}{vclY:Vclosed Y}
     {s|SS}{redXs:par_bp_redn X (sort s)}par_bp_redn Y (sort s);
intros;Refine conv_bpCR conv_bpXY vclX vclY;
intros S hypS;Refine par_bp_redn_trans (snd hypS);
Refine redn_bpCR_sort_character vclX (fst hypS) redXs;
Save conv_bpCR_sort_character;

Goal {X,Y|Trm}{conv_bpXY:conv_bp X Y}{vclX:Vclosed X}{vclY:Vclosed Y}
     {p|PP}{redXp:par_bp_redn X (par p)}par_bp_redn Y (par p);
intros;Refine conv_bpCR conv_bpXY vclX vclY;
intros P hypP;Refine par_bp_redn_trans (snd hypP);
Refine redn_bpCR_par_character vclX (fst hypP) redXp;
Save conv_bpCR_par_character;

Goal {A,A'|Trm}{conv_bpA:conv_bp A A'}
     {u,v|VV}{p|PP}
     {B,B'|Trm}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {conv_bpB:conv_bp (alpha p u B) (alpha p v B')}
     {vclP:Vclosed (pi u A B)}{vclP':Vclosed (pi v A' B')}
      conv_bp (pi u A B) (pi v A' B');
intros;
[vclA = fst (Vclosed_pi_lem vclP)];
[vclA' = fst (Vclosed_pi_lem vclP')];
[vclB = snd (Vclosed_pi_lem vclP) p];
[vclB' = snd (Vclosed_pi_lem vclP') p];
Refine conv_bpCR conv_bpA vclA vclA';
intros A0 hypA;Refine hypA;
intros redA redA';Refine conv_bpCR conv_bpB vclB vclB';
intros B0;Refine shape_lemma p B0;
intros w B1 shapeB;Refine shapeB;
intros eqB1 noccB1;Qrepl Trm_eq_subst eqB1;
intros hypB;Refine hypB;
intros redB redB';
Refine conv_bp_trans 
       (conv_bp_redn (par_bp_redn_pi redA noccB noccB1 redB))
       (Vclosed_pi (Vclosed_resp_par_bp_redn redA vclA)
                   (Vclosed_resp_par_bp_redn redB vclB))
       (conv_bp_sym (conv_bp_redn (par_bp_redn_pi redA' noccB' noccB1 redB')));
Save conv_bp_pi;

Goal {A,A'|Trm}{conv_bpA:conv_bp A A'}
     {u,v|VV}{p|PP}
     {B,B'|Trm}{noccB:is_ff (poccur p B)}{noccB':is_ff (poccur p B')}
     {conv_bpB:conv_bp (alpha p u B) (alpha p v B')}
     {vclP:Vclosed (lda u A B)}{vclP':Vclosed (lda v A' B')}
      conv_bp (lda u A B) (lda v A' B');
intros;
[vclA = fst (Vclosed_lda_lem vclP)];
[vclA' = fst (Vclosed_lda_lem vclP')];
[vclB = snd (Vclosed_lda_lem vclP) p];
[vclB' = snd (Vclosed_lda_lem vclP') p];
Refine conv_bpCR conv_bpA vclA vclA';
intros A0 hypA;Refine hypA;
intros redA redA';Refine conv_bpCR conv_bpB vclB vclB';
intros B0;Refine shape_lemma p B0;
intros w B1 shapeB;Refine shapeB;
intros eqB1 noccB1;Qrepl Trm_eq_subst eqB1;
intros hypB;Refine hypB;
intros redB redB';
Refine conv_bp_trans 
       (conv_bp_redn (par_bp_redn_lda redA noccB noccB1 redB))
       (Vclosed_lda (Vclosed_resp_par_bp_redn redA vclA)
                   (Vclosed_resp_par_bp_redn redB vclB))
       (conv_bp_sym (conv_bp_redn (par_bp_redn_lda redA' noccB' noccB1 redB')));

Save conv_bp_lda;

Goal {A,A'|Trm}{vclA:Vclosed A}{vclA':Vclosed A'}{conv_bpA:conv_bp A A'}
     {B,B'|Trm}{vclB:Vclosed B}{vclB':Vclosed B'}{conv_bpB:conv_bp B B'}
      conv_bp (app A B) (app A' B');
intros;Refine conv_bpCR conv_bpA vclA vclA';
intros A0 hypA;Refine hypA;
intros redA redA';Refine conv_bpCR conv_bpB vclB vclB';
intros B0 hypB;Refine hypB;
intros redB redB';
Refine conv_bp_trans 
       (conv_bp_redn (par_bp_redn_app redA redB))
       (Vclosed_app (Vclosed_resp_par_bp_redn redA vclA)
                    (Vclosed_resp_par_bp_redn redB vclB))
       (conv_bp_sym (conv_bp_redn (par_bp_redn_app (snd hypA) (snd hypB))));

Save conv_bp_app;

Goal {u|VV}{A,B,X|Trm}{c:conv_bp (pi u A B) X}
     {vclP:Vclosed (pi u A B)}{vclX:Vclosed X}
      Ex3 [A',B':Trm][v:VV]
      and3 (par_bp_redn X (pi v A' B'))
           (par_bp_redn A A')
           ({q:PP}par_bp_redn (alpha q u B) (alpha q v B'));
intros;Refine conv_bpCR c vclP vclX;
intros C hypC;Refine par_bp_redn_pi_character (fst hypC);
intros v A' B' hyp;
[redA = and3_out1 hyp];
[redB = and3_out2 hyp];
[eqP = Trm_eq_subst (and3_out3 hyp)];
Refine Ex3In A' B' v;Qrepl eqP;Refine pair3;
(* par_bp_redn X (pi v A' B') *) Refine snd hypC;
(* par_bp_redn A A' *) Refine redA;
(* {q:PP}par_bp_redn (alpha q u B) (alpha q v B') *) Refine redB;

Save conv_bp_pi_character;

Goal {X,Y|Trm}{conv_bpXY:conv_bp X Y}{vclX:Vclosed X}{vclY:Vclosed Y}
     {u|VV}{A,B|Trm}{redXpi:par_bp_redn X (pi u A B)}
      Ex3 [v:VV][A',B':Trm]
      and3 (par_bp_redn Y (pi v A' B'))
           (par_bp_redn A A')
           ({q:PP}par_bp_redn (alpha q u B) (alpha q v B'));
intros;Refine conv_bpCR conv_bpXY vclX vclY;
intros X' hypX;Refine redn_bpCR_pi_character vclX (fst hypX) redXpi;
intros v A' B' hypP;Refine Ex3In v A' B';
Refine pair3 (par_bp_redn_trans (snd hypX) (and3_out1 hypP))
             (and3_out2 hypP) (and3_out3 hypP); 
Save conv_bpCR_pi_character;

Goal {u,v|VV}{A,A',B,B'|Trm}{c:conv_bp (pi u A B) (pi v A' B')}
     {vclP:Vclosed (pi u A B)}{vclP':Vclosed (pi v A' B')}
      and (conv_bp A A') ({q:PP}conv_bp (alpha q u B) (alpha q v B'));
intros;Refine conv_bpCR c vclP vclP';
intros X hypX;Refine par_bp_redn_pi_character (fst hypX);
intros x Ac Bc hypL;
[redAlc = and3_out1 hypL][redBlc = and3_out2 hypL];
[vclAc = Vclosed_resp_par_bp_redn redAlc (fst (Vclosed_pi_lem vclP))];
[eqL = Trm_eq_subst (and3_out3 hypL)];
Refine par_bp_redn_pi_character (snd hypX);
intros x' Ac' Bc' hypR;
[redArc = and3_out1 hypR][redBrc = and3_out2 hypR];
[vclAc' = Vclosed_resp_par_bp_redn redArc (fst (Vclosed_pi_lem vclP'))];
[eqR = Trm_eq_subst (and3_out3 hypR)];
Refine Trm_eq_pi_lem (?:is_tt (Trm_eq (pi x Ac Bc) (pi x' Ac' Bc')));
Qrepl eqL;Qrepl eqR;Refine Trm_eq_refl;
intros eqV eqA eqB;
Refine pair;
(* conv_bp A A' *)
Refine conv_bp_trans (conv_bp_redn redAlc) vclAc;Qrepl Trm_eq_subst eqA;
Refine (conv_bp_sym (conv_bp_redn redArc));
(* conv_bp (alpha q u B) (alpha q v B') *)
intros;Refine fresh_params_lem4 B B' Bc Bc';
intros r rFresh;Refine rFresh;
intros noccB noccB' noccBc noccBc';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) u noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) v noccB'));
Refine psub_resp_conv_bp (Vclosed_par ?); 
Refine conv_bp_trans (conv_bp_redn ?) ? (conv_bp_sym (conv_bp_redn ?));
Refine +2 Vclosed_resp_par_bp_redn ?+1 (snd (Vclosed_pi_lem vclP) |?);
Refine +1 redBlc; 
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqB;
Refine redBrc;

Save conv_bpCR_pi_lem;

Goal {u|VV}{A,B,X|Trm}{c:conv_bp (lda u A B) X}
     {vclP:Vclosed (lda u A B)}{vclX:Vclosed X}
      Ex3 [A',B':Trm][v:VV]
      and3 (par_bp_redn X (lda v A' B'))
           (par_bp_redn A A')
           ({q:PP}par_bp_redn (alpha q u B) (alpha q v B'));
intros;Refine conv_bpCR c vclP vclX;
intros C hypC;Refine par_bp_redn_lda_character (fst hypC);
intros v A' B' hyp;
[redA = and3_out1 hyp];
[redB = and3_out2 hyp];
[eqP = Trm_eq_subst (and3_out3 hyp)];
Refine Ex3In A' B' v;Qrepl eqP;Refine pair3;
(* par_bp_redn X (lda v A' B') *) Refine snd hypC;
(* par_bp_redn A A' *) Refine redA;
(* {q:PP}par_bp_redn (alpha q u B) (alpha q v B') *) Refine redB;

Save conv_bp_lda_character;

Goal {u,v|VV}{A,A',B,B'|Trm}{c:conv_bp (lda u A B) (lda v A' B')}
     {vclP:Vclosed (lda u A B)}{vclP':Vclosed (lda v A' B')}
      and (conv_bp A A') ({q:PP}conv_bp (alpha q u B) (alpha q v B'));
intros;Refine conv_bpCR c vclP vclP';
intros X hypX;Refine par_bp_redn_lda_character (fst hypX);
intros x Ac Bc hypL;
[redAlc = and3_out1 hypL][redBlc = and3_out2 hypL];
[vclAc = Vclosed_resp_par_bp_redn redAlc (fst (Vclosed_lda_lem vclP))];
[eqL = Trm_eq_subst (and3_out3 hypL)];
Refine par_bp_redn_lda_character (snd hypX);
intros x' Ac' Bc' hypR;
[redArc = and3_out1 hypR][redBrc = and3_out2 hypR];
[vclAc' = Vclosed_resp_par_bp_redn redArc (fst (Vclosed_lda_lem vclP'))];
[eqR = Trm_eq_subst (and3_out3 hypR)];
Refine Trm_eq_lda_lem (?:is_tt (Trm_eq (lda x Ac Bc) (lda x' Ac' Bc')));
Qrepl eqL;Qrepl eqR;Refine Trm_eq_refl;
intros eqV eqA eqB;
Refine pair;
(* conv_bp A A' *)
Refine conv_bp_trans (conv_bp_redn redAlc) vclAc;Qrepl Trm_eq_subst eqA;
Refine (conv_bp_sym (conv_bp_redn redArc));
(* conv_bp (alpha q u B) (alpha q v B') *)
intros;Refine fresh_params_lem4 B B' Bc Bc';
intros r rFresh;Refine rFresh;
intros noccB noccB' noccBc noccBc';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) u noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha (par q) v noccB'));
Refine psub_resp_conv_bp (Vclosed_par ?); 
Refine conv_bp_trans (conv_bp_redn ?) ? (conv_bp_sym (conv_bp_redn ?));
Refine +2 Vclosed_resp_par_bp_redn ?+1 (snd (Vclosed_lda_lem vclP) |?);
Refine +1 redBlc; 
Qrepl VVdecide eqV;Qrepl Trm_eq_subst eqB;
Refine redBrc;

Save conv_bpCR_lda_lem;

Goal {p|PP}{M|Trm}(Vclosed M)->
     {N,N'|Trm}(conv_bp N N')->(Vclosed N)->(Vclosed N')->
      conv_bp (psub N p M) (psub N' p M);
intros ___;
Refine conv_bpRec [N,N'|Trm][_:conv_bp N N']
               {vcl:Vclosed N}{vcl':Vclosed N'}
                conv_bp (psub N p M) (psub N' p M);
intros;Refine conv_bp_refl;
intros;Refine conv_bp_sym;Refine s_ih;Immed;
intros;Refine conv_bp_trans;Refine +1 lt_ih;Refine +3 rt_ih;
       Refine +2 psub_resp_Vclosed;Immed;
intros;Refine conv_bp_redn;Refine par_bp_redn_refl_psub_lem;Immed;
Save conv_bp_refl_psub_lem;

Goal {p|PP}{M,M'|Trm}{redM:par_bp_redn M M'}{vclM:Vclosed M}
     {N,N'|Trm}{cNN:conv_bp N N'}{vclN:Vclosed N}{vclN':Vclosed N'}
      conv_bp (psub N p M) (psub N' p M');
intros;Refine conv_bpCR cNN vclN vclN';
intros N0 hyp;Refine hyp;
intros redN redN';
[vclM' = Vclosed_resp_par_bp_redn redM vclM];
[vclN0 = Vclosed_resp_par_bp_redn redN vclN];
Refine conv_bp_trans;
Refine +3 conv_bp_sym;Refine +3 conv_bp_redn;Refine +3 par_bp_redn_refl_psub_lem;
Refine conv_bp_redn;Refine par_bp_redn_psub;Refine +4 psub_resp_Vclosed;Immed;
Save conv_bp_redn_psub_lem;

Goal {N,N'|Trm}(conv_bp N N')->(Vclosed N)->(Vclosed N')->
     {X,X'|Trm}(conv_bp X X')->(Vclosed X)->(Vclosed X')->
     {p:PP} conv_bp (psub N p X) (psub N' p X');
intros;
Refine conv_bpRec [M,M'|Trm][_:conv_bp M M']{vcl:Vclosed M}{vcl':Vclosed M'}
               {N,N'|Trm}{c:conv_bp N N'}{vclN:Vclosed N}{vclN':Vclosed N'}
                conv_bp (psub N p M) (psub N' p M');Immed;
intros;Refine conv_bp_refl_psub_lem;Immed;
intros;Refine conv_bp_sym;Refine s_ih;Refine +2 conv_bp_sym;Immed;
intros;Refine conv_bp_trans;Refine +1 lt_ih;Refine +3 conv_bp_refl;
       Refine +5 rt_ih;Refine +4 psub_resp_Vclosed;Immed;
intros;Refine conv_bp_redn_psub_lem;Immed;
Save conv_bp_psub;

Goal {N,N'|Trm}(conv_bp N N')->(Vclosed N)->(Vclosed N')->
     {u,v:VV}{X,X'|Trm}({q:PP}conv_bp (alpha q u X) (alpha q v X'))->
     ({q:PP}Vclosed (alpha q u X))->({q:PP}Vclosed (alpha q v X'))->
      conv_bp (vsub N u X) (vsub N' v X');
intros;Refine fresh_params_lem2 X X';
intros q qFresh;Refine qFresh;
intros noccX noccX';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N u noccX));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N' v noccX'));
Refine conv_bp_psub;Immed;
Save conv_bp_vsub;
