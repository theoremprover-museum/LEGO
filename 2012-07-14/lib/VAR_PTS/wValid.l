Module wValid 
Import context
       Vclosed;

(* Vclosed Context *)
Inductive [VclCxt: Cxt->Prop] Inversion
Constructors
[VCnil: VclCxt nilCxt]
[VCcons: {G|Cxt}{A|Trm}{vclA:Vclosed A}
         {prem:VclCxt G}
     (************************************)
         {p:PP}VclCxt (CONS (Gb p A) G)];


(* weak validity of contexts *)
%\VerbFileOpen wValid_verb
Inductive [wValid: Cxt->Prop] Inversion
Constructors
[wVnil: wValid nilCxt]
[wVcons: {G|Cxt}{p|PP}{A|Trm}                                {vclA:Vclosed A}
                                                    {sc_p:is_ff (Poccur p G)}
                        {sc_A:{q|PP}(is_tt (poccur q A))->is_tt (Poccur q G)}
          {prem:wValid G}
     (************************************)
           wValid (CONS (Gb p A) G)];
%\VerbFileClos wValid_verb

[wValidRec = wValid_elim
  : {C:{G|Cxt}(wValid G)->Prop}
    {WVNIL:C wVnil}
    {WVCONS:{G|Cxt}{p|PP}{A|Trm}{vclA:Vclosed A}
            {sc_p:is_ff (Poccur p G)}
            {sc_A:{q|PP}(is_tt (poccur q A))->is_tt (Poccur q G)}
            {prem:wValid G}
            {ih:C prem}
              C (wVcons vclA sc_p sc_A prem)}
    {G|Cxt}{t:wValid G}C t];

Goal wValid_VclCxt: {G|Cxt}(wValid G)->VclCxt G;
Refine wValidRec [G:Cxt][_:wValid G]VclCxt G;
Refine VCnil;
intros; Refine VCcons; Immed;
Save;

%\VerbFileOpen wValid_tail
Goal wValid_tail : {G|Cxt}(wValid G)->wValid (tl G);
%\VerbFileClos wValid_tail
Refine wValidRec [G:Cxt][_:wValid G]wValid (tl G);
Refine wVnil;
intros; Immed;
Save;

%\VerbFileOpen wValid_gen
Goal wValid_gen :
     {p|PP}{A|Trm}{G|Cxt}(wValid (CONS (Gb p A) G))->
     and4 (is_ff (Poccur p G))
          ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
%\VerbFileClos wValid_gen
intros;
Refine wValidRec [GG|Cxt][_:wValid GG]
     (is_tt (Cxt_eq GG (CONS (Gb p A) G)))->
     and4 (is_ff (Poccur p G))
          ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros;Refine new_eqCxtLem (Cxt_eq_subst H1);
intros eqP eqA eqG;
Qrepl Q_sym eqP;
Qrepl Q_sym eqA;
Qrepl Q_sym eqG;
Refine pair4 sc_p sc_A ? vclA;
Refine tt_or_ff (poccur p1 A1);
intros istt; Refine tt_not_ff;
   Qrepl Q_sym sc_p; Qrepl Q_sym (sc_A istt); Refine Q_refl;
intros; Immed;
Refine Cxt_eq_refl;
Save;

Goal {p|PP}{A|Trm}{G,K|Cxt}(wValid (append K (CONS (Gb p A) G)))->
     and4 (is_ff (Poccur p G))
          ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
intros;
Refine LLrec [K|Cxt]{wval:wValid (append K (CONS (Gb p A) G))}
     and4 (is_ff (Poccur p G))
          ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
Immed;
intros;Refine wValid_gen;Immed;
intros;Refine LLih (wValid_tail wval);
Save wValid_gen_append;

Goal {G|Cxt}(wValid G)->
     {p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
     and3 ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
Refine wValidRec [G|Cxt][_:wValid G]
     {p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
     and3 ({q|PP}(is_tt (poccur q A))->is_tt (Poccur q G))
          (is_ff (poccur p A))
          (Vclosed A);
intros; Refine tt_not_ff (Q_sym H);
intros; Refine fst (orr_character ? (GBoccur (Gb p1 A1) G)) H;
intros eq;
[lem : and (Q p1 p) (Q A1 A)
     = Q_resp_bnd_proj (GBeq_subst eq)];
Qrepl fst lem; Qrepl snd lem; Refine pair3 ? ? vclA;
intros; Refine snd (orr_character ? (Poccur ? G));
Refine inr; Refine sc_A; Immed;
Refine tt_or_ff (poccur p A);
intros istt; Refine tt_not_ff;
   Qrepl Q_sym sc_p; Qrepl Q_sym (sc_A istt); Refine Q_refl;
intros; Immed;
intros inC; Refine ih inC;
intros poccG noccA vclA';
Refine pair3 ? noccA vclA';
intros; Refine snd (orr_character ? (Poccur q G));
Refine inr; Refine poccG; Immed;
Save wValid_weak;

Goal {G|Cxt}(wValid G)->
     {p|PP}{A,B|Trm}
     (is_tt (GBoccur (Gb p A) G))->(is_tt(GBoccur (Gb p B) G))->
          Q A B;
Refine wValidRec [G:Cxt][_:wValid G]
     {p|PP}{A,B|Trm}
     (is_tt (GBoccur (Gb p A) G))->(is_tt(GBoccur (Gb p B) G))->
          Q A B;
intros; Refine tt_not_ff (Q_sym H);
intros; Refine tt_or_ff (PPeq p1 p);
intros eqp1p;
Refine fst (orr_character ? (GBoccur (Gb p1 A1) G)) H;
Refine fst (orr_character ? (GBoccur (Gb p1 B) G)) H1;
intros; Qrepl snd (Q_resp_bnd_proj (GBeq_subst H2));
Qrepl snd (Q_resp_bnd_proj (GBeq_subst H3)); Refine Q_refl;
Qrepl PPdecide eqp1p; intros; Refine tt_not_ff; Qrepl Q_sym sc_p;
Qrepl GBoccur_Poccur_lem H2; Refine Q_refl;

Refine fst (orr_character ? (GBoccur (Gb p1 B) G)) H1;
Qrepl PPdecide eqp1p; intros; Refine tt_not_ff; Qrepl Q_sym sc_p;
Qrepl GBoccur_Poccur_lem H3; Refine Q_refl;
intros; Refine ih H3 H2;

intros neqp1p;
Refine fst (orr_character ? (GBoccur (Gb p1 A1) G)) H;
intros; Refine tt_not_ff; Qrepl Q_sym neqp1p;
Qrepl fst (Q_resp_bnd_proj (GBeq_subst H2)); Qrepl PPrefl p;
Refine Q_refl;

Refine fst (orr_character ? (GBoccur (Gb p1 B) G)) H1;
intros; Refine tt_not_ff; Qrepl Q_sym neqp1p;
Qrepl fst (Q_resp_bnd_proj (GBeq_subst H2)); Qrepl PPrefl p;
Refine Q_refl;

intros; Refine ih H3 H2;
Save GBoccur_wValid_functional;

Goal {G|Cxt}(wValid G)->
     {p|PP}(is_ff (Poccur p G))->is_ff (POCCUR p G);
Refine wValidRec [G:Cxt][_:wValid G]
     {p|PP}(is_ff (Poccur p G))->is_ff (POCCUR p G);
intros; Refine Q_refl;
intros;
[lem : and (is_ff (PPeq p1 p)) (is_ff (Poccur p1 G))
     = fst (deMorgan ? (Poccur ? ?)) H];
Refine snd (deMorgan (PPeq p1 p)
                     (member PPeq p1 (append (params A) (freeNames G))));
Refine pair (fst lem) ?;
Qrepl member_append_lem PPeq p1 (params A) (freeNames G);
Refine snd (deMorgan ? ?); Refine pair;
Refine tt_or_ff (poccur p1 A);
intros h; Refine tt_not_ff; Qrepl Q_sym (sc_A h); Refine snd lem;
intros; Immed;
Refine ih (snd lem);
Save wV_Poccur_POCCUR_lem;

Goal {b|GB}{G|Cxt}(wValid (CONS b G))->is_ff (POCCUR (namOf b) G);
intros;
Refine wValidRec [J:Cxt][_:wValid J]
      (is_tt (Cxt_eq J (CONS b G)))->is_ff (POCCUR (namOf b) G);
Immed;
intros h; Refine tt_not_ff (Q_sym h);
intros;
[lem : and3 (Q p (namOf b)) (Q A (typOf b)) (Q G1 G)
     = new_eqCxtLem (Cxt_eq_subst H1)];
Refine wV_Poccur_POCCUR_lem (wValid_tail H);
Qrepl Q_sym (and3_out1 lem); Qrepl Q_sym (and3_out3 lem); Refine sc_p;
Refine Cxt_eq_refl;
Save wV_notPOCCURinTl;

Goal {G|Cxt}(wValid G)->
     {p|PP}{nocc:is_ff (Poccur p G)}
     {N:Trm}is_tt (Cxt_eq (map (GBsub N p) G) G);
Refine wValidRec [G|Cxt][_:wValid G]{p|PP}{nocc:is_ff (Poccur p G)}
                 {N:Trm}is_tt (Cxt_eq (map (GBsub N p) G) G);
intros;Refine Cxt_eq_refl;
intros;Refine Poccur_CONS_lem nocc;
intros neqP noccG;
Refine snd (andd_character ? (Cxt_eq (map (GBsub N p1) G) G));
Refine pair;Refine +1 ih;Immed;
Equiv is_tt (GBeq (Gb p (psub ? ? ?)) ?);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem (B_contrapos (sc_A|?) noccG) N);
Refine GBeq_refl;
Save wValid_GBsub_lem;

Goal {a|Trm}{vcl:Vclosed a}
     {Gamma|Cxt}{wf:{q|PP}{occ:is_tt (poccur q a)}is_tt (Poccur q Gamma)}
     {p:PP}[subGB = GBsub a p]
     {A|Trm}{G|Cxt}{prem:wValid G}
     {Delta:Cxt}
     {eqCxt:is_tt (Cxt_eq G (append Delta (CONS (Gb p A) Gamma)))}
      wValid (append (map subGB Delta) Gamma);
intros _______;
Refine wValidRec [G|Cxt][_:wValid G]{Delta:Cxt}
       {eqCxt:is_tt (Cxt_eq G (append Delta (CONS (Gb p A) Gamma)))}
        wValid (append (map subGB Delta) Gamma);
intros;Refine NIL_not_append_CONS ? ? ? (Cxt_eq_subst eqCxt);
intros;Refine LLrec [Delta:Cxt]
                    {eqCxt':is_tt (Cxt_eq (CONS (Gb p1 A1) G)
                                  (append Delta (CONS (Gb p A) Gamma)))}
                     wValid (append (map subGB Delta) Gamma);Immed;
(* Delta NIL *)
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt');
intros eqP eqA eqG;
Qrepl Q_sym eqG;Immed;
(* Delta CONS *)
intros pA Delta' __;Refine new_eqCxtLem (Cxt_eq_subst eqCxt');
intros eqP eqA eqG;
Refine Poccur_compound_lem (Q_subst eqG ([G:Cxt]is_ff (Poccur p1 G)) sc_p);
intros noccurDelta neqP noccurGamma;  
[p2 = namOf pA][A2 = typOf pA];
Equiv wValid (CONS (Gb p2 (psub a p A2)) (append (map subGB Delta') Gamma));
Qrepl Q_sym eqP;Qrepl Q_sym eqA;
Refine wVcons (psub_resp_Vclosed vcl p vclA) ? ? (ih Delta' ?);

Refine Pocc_split_lem2;Qrepl GBsub_Poccur_lem a p p1 Delta';Immed;

intros;Refine Pocc_split_lem;
Qrepl GBsub_Poccur_lem a p q Delta';
Refine pocc_psub_lem H;
intros case;Refine inr;Refine wf (fst case);
intros case;Equiv or ? (is_tt (orr ff (Poccur ? ?)));
Refine fst (orr_character ? ?);Qrepl Q_sym (snd case);
Qrepl Q_sym (member_append_lem PPeq q (globalNames Delta')
                                      (globalNames (CONS (Gb p A) Gamma)));
Qrepl Q_sym (globalNames_append_lem Delta' (CONS (Gb p A) Gamma));
Qrepl Q_sym eqG;Refine sc_A (fst case);

Qrepl eqG;Refine Cxt_eq_refl;

Save psub_resp_wValid;
