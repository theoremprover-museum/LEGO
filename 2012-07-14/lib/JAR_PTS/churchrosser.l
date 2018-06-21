Module churchrosser 
Import complete_development;

(* Church Rosser theorem, using complete developments *)

[CommonReduct [t|Type][R,S:t->t->Prop] = [b,c:t]Ex [d:t]and (S b d) (R c d)];

[DiamondProperty' [t|Type][R:t->t->Prop]
                = {a,b,c|t}(R a b)->(R a c)->CommonReduct R R b c];

[StripLemma' [t|Type][R,S:t->t->Prop]
           = {a,b,c|t}(R a b)->(S a c)->CommonReduct R S b c];


Goal DiamondProperty' par_red1;
Expand DiamondProperty';
intros;Refine comp_dev_exists (fst (par_red1_Vclosed H));
intros d cd;Refine ExIn d;Refine pair;
Refine comp_dev_preCR;Immed;
Refine comp_dev_preCR;Immed;
Save par_red1_DP;

Goal StripLemma' par_redn par_red1;
Expand StripLemma';
intros;[CR = CommonReduct par_redn par_red1];
Refine par_rednRec [X,Xl:Trm]
                     {Xr|Trm}{redR:par_red1 X Xr}CR Xl Xr;
Immed;

intros A Al redL Ar redR;Refine par_red1_DP redL redR;
intros Ac hypA;Refine ExIn Ac;Refine pair;
Refine fst hypA;Refine par_redn_red1;Refine snd hypA;

intros _______ Ar redA;Refine lt_ih redA;
intros Dr hypD;Refine rt_ih (fst hypD);
intros Br hypB;Refine ExIn Br;Refine pair;
Refine fst hypB;Refine par_redn_trans;Refine +1 snd hypD;Refine snd hypB;

Save par_redn_red1_SL;

Goal DiamondProperty' par_redn;
Expand DiamondProperty';
intros;[CR = CommonReduct par_redn par_redn];
Refine par_rednRec [X,Xl:Trm]
                     {Xr|Trm}{redR:par_redn X Xr}CR Xl Xr;
Immed;

intros A Al redL Ar redR;Refine par_redn_red1_SL;Immed;
intros Ac hypA;Refine ExIn Ac;Refine pair;
Refine snd hypA;Refine par_redn_red1;Refine fst hypA;

intros _______ Ar redA;Refine lt_ih redA;
intros Dr hypD;Refine rt_ih (fst hypD);
intros Br hypB;Refine ExIn Br;Refine pair;
Refine fst hypB;Refine par_redn_trans;Refine +1 snd hypD;Refine snd hypB;

Save par_redn_DP;

Goal {X,Y|Trm}{redXY:par_redn X Y}
     {s|SS}{redXs:par_redn X (sort s)}par_redn Y (sort s);
intros;Refine par_redn_DP redXY redXs;
intros S hypS;
Qrepl Q_sym (Trm_eq_subst (par_redn_sort_character (snd hypS)));
Refine fst hypS;
Save par_rednCR_sort_character;

Goal {X,Y|Trm}{redXY:par_redn X Y}
     {p|PP}{redXp:par_redn X (par p)}par_redn Y (par p);
intros;Refine par_redn_DP redXY redXp;
intros P hypP;
Qrepl Q_sym (Trm_eq_subst (par_redn_par_character (snd hypP)));
Refine fst hypP;
Save par_rednCR_par_character;

Goal {X,Y|Trm}{redXY:par_redn X Y}
     {u|VV}{A,B|Trm}{redXpi:par_redn X (pi u A B)}
      Ex3 [v:VV][A',B':Trm]
      and3 (par_redn Y (pi v A' B'))
           (par_redn A A')
           ({q:PP}par_redn (alpha q u B) (alpha q v B'));
intros;Refine par_redn_DP redXY redXpi;
intros P hypP;Refine par_redn_pi_character (snd hypP);
intros v A' B' hyp;Refine Ex3In v A' B';
Qrepl Trm_eq_subst (and3_out3 hyp);
Refine pair3 (fst hypP) (and3_out1 hyp) (and3_out2 hyp); 
Save par_rednCR_pi_character;
