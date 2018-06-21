Module churchrosser_bp Import churchrosser par_bp_red complete_bp_development;

(* Church Rosser theorem for pi-beta *)

[DiamondProperty [R:Trm->Trm->Prop]
    = {a,b,c|Trm}(Vclosed a)->(R a b)->(R a c)->CommonReduct R R b c];
[StripLemma [R,S:Trm->Trm->Prop]
    = {a,b,c|Trm}(Vclosed a)->(R a b)->(S a c)->CommonReduct R S b c];

Goal DiamondProperty par_bp_red1;
Expand DiamondProperty;
intros;Refine comp_bp_dev_exists;Immed;
intros d cd;Refine ExIn d;Refine pair;
Refine comp_bp_dev_preCR;Immed;
Refine comp_bp_dev_preCR;Immed;
Save comp_bp_dev_par_bp_red1_DP;

Goal StripLemma par_bp_redn par_bp_red1;
Expand StripLemma;
intros;[CR = CommonReduct par_bp_redn par_bp_red1];
Refine par_bp_rednRec [X,Xl:Trm][_:par_bp_redn X Xl]
                   {vcl:Vclosed X}{Xr|Trm}{redR:par_bp_red1 X Xr}CR Xl Xr;
Immed;

intros A Al redL vclA Ar redR;Refine comp_bp_dev_par_bp_red1_DP vclA redL redR;
intros Ac hypA;Refine ExIn Ac;Refine pair;
Refine fst hypA;Refine par_bp_redn_red1;Refine snd hypA;

intros _______ vclA Ar redA;Refine lt_ih vclA redA;
intros Dr hypD;Refine rt_ih (Vclosed_resp_par_bp_redn lt_prem vclA) (fst hypD);
intros Br hypB;Refine ExIn Br;Refine pair;
Refine fst hypB;Refine par_bp_redn_trans;Refine +1 snd hypD;Refine snd hypB;

Save par_bp_redn_red1_SL;

Goal DiamondProperty par_bp_redn;
Expand DiamondProperty;
intros;[CR = CommonReduct par_bp_redn par_bp_redn];
Refine par_bp_rednRec [X,Xl:Trm][_:par_bp_redn X Xl]
                   {vcl:Vclosed X}{Xr|Trm}{redR:par_bp_redn X Xr}CR Xl Xr;
Immed;

intros A Al redL vclA Ar redR;Refine par_bp_redn_red1_SL;Immed;
intros Ac hypA;Refine ExIn Ac;Refine pair;
Refine snd hypA;Refine par_bp_redn_red1;Refine fst hypA;

intros _______ vclA Ar redA;Refine lt_ih vclA redA;
intros Dr hypD;Refine rt_ih (Vclosed_resp_par_bp_redn lt_prem vclA) (fst hypD);
intros Br hypB;Refine ExIn Br;Refine pair;
Refine fst hypB;Refine par_bp_redn_trans;Refine +1 snd hypD;Refine snd hypB;

Save par_bp_redn_DP;

Goal {X,Y|Trm}{vclX:Vclosed X}{redXY:par_bp_redn X Y}
     {s|SS}{redXs:par_bp_redn X (sort s)}par_bp_redn Y (sort s);
intros;Refine par_bp_redn_DP vclX redXY redXs;
intros S hypS;
Qrepl Q_sym (Trm_eq_subst (par_bp_redn_sort_character (snd hypS)));
Refine fst hypS;
Save redn_bpCR_sort_character;

Goal {X,Y|Trm}{vclX:Vclosed X}{redXY:par_bp_redn X Y}
     {p|PP}{redXs:par_bp_redn X (par p)}par_bp_redn Y (par p);
intros;Refine par_bp_redn_DP vclX redXY redXs;
intros P hypP;
Qrepl Q_sym (Trm_eq_subst (par_bp_redn_par_character (snd hypP)));
Refine fst hypP;
Save redn_bpCR_par_character;

Goal {X,Y|Trm}{vclX:Vclosed X}{redXY:par_bp_redn X Y}
     {u|VV}{A,B|Trm}{redXpi:par_bp_redn X (pi u A B)}
      Ex3 [v:VV][A',B':Trm]
      and3 (par_bp_redn Y (pi v A' B'))
           (par_bp_redn A A')
           ({q:PP}par_bp_redn (alpha q u B) (alpha q v B'));
intros;Refine par_bp_redn_DP vclX redXY redXpi;
intros P hypP;Refine par_bp_redn_pi_character (snd hypP);
intros v A' B' hyp;Refine Ex3In v A' B';
Qrepl Trm_eq_subst (and3_out3 hyp);
Refine pair3 (fst hypP) (and3_out1 hyp) (and3_out2 hyp); 
Save redn_bpCR_pi_character;

