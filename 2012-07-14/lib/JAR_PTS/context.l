Module context Import terms occurrence substitution;

(* global bindings and contexts *)
%\VerbFileOpen GB_verb
[GB : Prop = PROD|PP|Trm];
[Gb : PP->Trm->GB = Pr|PP|Trm];
%\VerbFileNoRecord GB_verb
[GBrec : {C:GB->Prop}({a:PP}{b:Trm}C (Pr a b))->{g:GB}C g = PRODrec|PP|Trm];
%\VerbFileRecord GB_verb
[namOf : GB->PP = Fst|PP|Trm];
[typOf : GB->Trm = Snd|PP|Trm];
[GBeq [b,c:GB] = andd (PPeq (namOf b) (namOf c))
                      (Trm_eq (typOf b) (typOf c))];
%\VerbFileClos GB_verb

(* namOf and typOf are proper destructors *)
Goal {b:GB}Q b (Gb (namOf b) (typOf b));
Refine PROD_surj_pair;
Save GB_surj_pair;

Goal {p,q|PP}(Q p q)->{A,B|Trm}(Q A B)->Q (Gb p A) (Gb q B);
intros; Qrepl H; Qrepl H1; Refine Q_refl;
Save Q_resp_Gb;

Goal {b:GB}is_tt (GBeq b b);
Refine GBrec [b:GB]is_tt (GBeq b b);
intros; Refine snd (andd_character ? ?); Refine pair;
Refine PPrefl; Refine Trm_eq_refl;
Save GBeq_refl;

(* equality and global bindings *)
Goal {b,c|GB}(is_tt (GBeq b c))->Q b c;
intros;
[lem1:and (is_tt (PPeq (namOf b) (namOf c)))
          (is_tt (Trm_eq (typOf b) (typOf c)))
     = fst (andd_character ? ?) H];
Qrepl GB_surj_pair b; Qrepl GB_surj_pair c;
Qrepl PPdecide (fst lem1); Qrepl Trm_eq_subst (snd lem1);
Refine Q_refl;
Save GBeq_subst;

Goal {u,v|GB}(Q u v)->(and (Q (namOf u) (namOf v)) (Q (typOf u) (typOf v)));
Refine Q_resp_proj;
Save Q_resp_bnd_proj;

(* contexts are just lists of bindings *)
%\VerbFileOpen Cxt_verb
[Cxt = LL|GB];
[nilCxt = NIL|GB];
%\VerbFileClos Cxt_verb

Goal {b,b'|GB}{G,G'|Cxt}
     (Q (CONS b G) (CONS b' G'))->
     and3 (Q (namOf b) (namOf b')) (Q (typOf b) (typOf b')) (Q G G');
intros; Refine pair3;
Refine fst (Q_resp_bnd_proj (Q_resp_hd H));
Refine snd (Q_resp_bnd_proj (Q_resp_hd H));
Refine Q_resp_tl H;
Save new_eqCxtLem;

(* decidable context equality *)
[Cxt_eq : Cxt->Cxt->BB = list_eq GBeq];
[Cxt_eq_refl : {G:Cxt}is_tt (Cxt_eq G G)
             = list_eq_refl GBeq_refl];
[Cxt_eq_subst : {G,K|Cxt}(is_tt (Cxt_eq G K))->Q G K
              = list_eq_subst GBeq_subst];


(* context manipulation *)
%\VerbFileOpen GBoccur_verb
[GBoccur [b:GB][G:Cxt] : BB = member GBeq b G];
%\VerbFileClos GBoccur_verb

Goal {b:GB}{G:Cxt}is_tt (GBoccur b (CONS b G));
intros; Refine snd (orr_character ? (GBoccur ? ?));
Refine inl; Refine GBeq_refl;
Save hd_GBoccur_lem;

Goal {G,K|Cxt}{b,b'|GB}(is_tt (GBoccur b (append K (CONS b' G))))->
      or3 (is_tt (GBoccur b K)) (is_tt (GBeq b b')) (is_tt (GBoccur b G));
intros ____;
Qrepl member_append_lem GBeq b K (CONS b' G);
intros occ;Refine fst (orr_character ? ?) occ;
intros case;Refine or3_in1;Immed;
Qrepl member_append_lem GBeq b  (CONS b' nilCxt) G;
intros occ';Refine fst (orr_character ? ?) occ';
intros case;Refine or3_in2;Qrepl Q_sym (ff_orr_unit (GBeq b b'));Immed;
intros case;Refine or3_in3;Immed;
Save GBoccur_split_lem;

Goal {G,K|Cxt}{b|GB}is_tt (GBoccur b (append K (CONS b G)));
intros;Refine LLrec [K|Cxt]is_tt (GBoccur b (append K (CONS b G)));
Refine hd_GBoccur_lem;
intros;Refine snd (orr_character ? ?);Refine inr;Immed;
Save GBoccur_compound_lem;

[N:Trm][p:PP];

[GBsub [pA:GB] = Gb (namOf pA) (psub N p (typOf pA))];

Goal {G|Cxt}{q|PP}{A|Trm}(is_tt (GBoccur (Gb q A) G))->
       is_tt (GBoccur (Gb q (psub N p A)) (map GBsub G));
Refine LLrec [G:Cxt]{q|PP}{A|Trm}{occ:is_tt (GBoccur (Gb q A) G)}
              is_tt (GBoccur (Gb q (psub N p A)) (map GBsub G));
intros; Refine tt_not_ff (Q_sym occ);
intros;
Refine snd (orr_character ? (GBoccur (Gb ? (psub ? ? ?)) (map GBsub ?)));
Refine fst (orr_character ? (GBoccur (Gb q A) prem)) occ;
intros eq; Refine inl;
[lem : and (is_tt (PPeq q (namOf b))) (is_tt (Trm_eq A (typOf b)))
     = fst (andd_character ? ?) eq];
Qrepl GB_surj_pair b;Qrepl PPdecide (fst lem);Qrepl Trm_eq_subst (snd lem);
Refine GBeq_refl;
intros inC; Refine inr; Refine LLih inC;
Save GBsub_GBoccur;

Goal {G|Cxt}{q|PP}{A|Trm}(is_tt (GBoccur (Gb q A) (map GBsub G)))->
      Ex [B:Trm]and (is_tt (GBoccur (Gb q B) G))
                    (is_tt (Trm_eq A (psub N p B)));
Refine LLrec [G:Cxt]{q|PP}{A|Trm}{occ:is_tt (GBoccur (Gb q A) (map GBsub G))}
              Ex [B:Trm]and (is_tt (GBoccur (Gb q B) G))
                            (is_tt (Trm_eq A (psub N p B)));
intros; Refine tt_not_ff (Q_sym occ);
intros;
Refine fst (orr_character ? (GBoccur (Gb ? ?) (map GBsub ?))) occ;
intros eq;
[lem : and (is_tt (PPeq q (namOf b))) (is_tt (Trm_eq A (psub N p (typOf b))))
     = fst (andd_character ? ?) eq];
Refine ExIn (typOf b);Refine pair ? (snd lem);
Qrepl GB_surj_pair b;Qrepl PPdecide (fst lem);
Refine snd (orr_character ? (GBoccur ? prem));Refine inl;
Refine GBeq_refl;
intros inC;Refine LLih inC;
intros B hypB;Refine ExIn B;Refine pair ? (snd hypB);
Refine snd (orr_character ? (GBoccur ? prem));Refine inr;Refine fst hypB;
Save GBoccur_GBsub;

Discharge N;

(* names with binding instances in a context *)

%\VerbFileOpen globalNames_verb
[globalNames : Cxt->PPs = map namOf];
%\VerbFileNoRecord globalNames_verb
[globalNames_append_lem = map_append_lem namOf];

(* globalNames only examines left objects of pairs *)

Goal {f|(GB)->GB}({x:GB}Q (namOf (f x)) (namOf x))->
      {G:Cxt}Q (globalNames (map f G)) (globalNames G);
intros f hyp;
Refine LLrec [G:Cxt]Q (globalNames (map f G)) (globalNames G);
intros; Refine Q_refl;
intros;
Equiv Q (CONS (namOf (f b)) (globalNames (map f prem)))
        (CONS (namOf b) (globalNames prem));
Qrepl hyp b; Qrepl LLih; Refine Q_refl;
Save globalNames_map_lem;

(* occurrence of a binding instance *)
%\VerbFileRecord globalNames_verb
[Poccur [p:PP][G:Cxt] : BB = member PPeq p (globalNames G)];
%\VerbFileClos globalNames_verb

Goal {N:Trm}{p,q:PP}{G:Cxt}Q (Poccur q (map (GBsub N p) G)) (Poccur q G);
intros;Expand Poccur;
Qrepl globalNames_map_lem ([x:GB]Q_refl (namOf (GBsub N p x))) G;
Refine Q_refl;
Save GBsub_Poccur_lem;

Goal {G|Cxt}{b|GB}(is_tt (GBoccur b G))->is_tt (Poccur (namOf b) G);
Refine LLrec [G:Cxt]{b|GB}(is_tt (GBoccur b G))->
                is_tt (Poccur (namOf b) G);
intros; Immed;
intros;
Refine fst (orr_character ? (GBoccur b1 prem)) H;
intros eq; Qrepl GBeq_subst eq;
Refine snd (orr_character ? (Poccur ? ?));
Refine inl; Refine PPrefl;
intros inprem;
Refine snd (orr_character ? (Poccur ? ?));
Refine inr; Refine LLih inprem;
Save GBoccur_Poccur_lem;

Goal {G|Cxt}{p|PP}(is_tt (Poccur p G))->Ex [A:Trm]is_tt (GBoccur (Gb p A) G);
Refine LLrec [G:Cxt]{p|PP}{occ:is_tt (Poccur p G)}
              Ex [A:Trm]is_tt (GBoccur (Gb p A) G);
intros;Refine tt_not_ff (Q_sym occ);
intros;Refine fst (orr_character ? (Poccur p prem)) occ;
intros eq;Refine ExIn (typOf b);
          Refine snd (orr_character ? (GBoccur ? ?));
          Refine inl;Refine snd (andd_character ? ?);
          Refine pair eq (Trm_eq_refl ?);
intros inprem;Refine LLih inprem;
          intros A occA;Refine ExIn A;
          Refine snd (orr_character ? (GBoccur ? ?));
          Refine inr occA; 
Save Poccur_GBoccur_lem;

Goal {p|PP}{G,H|Cxt}(or (is_tt (Poccur p G)) (is_tt (Poccur p H)))->
      is_tt (Poccur p (append G H));
intros;Expand Poccur;Qrepl globalNames_append_lem G H;
Qrepl member_append_lem PPeq p (globalNames G) (globalNames H);
Refine snd (orr_character (Poccur ? ?) (Poccur ? ?));Immed;
Save Pocc_split_lem;

Goal {p|PP}{G,H|Cxt}(is_tt (Poccur p (append G H)))->
      or (is_tt (Poccur p G)) (is_tt (Poccur p H));
intros;Refine fst (orr_character (Poccur p G) (Poccur p H));
Qrepl Q_sym (member_append_lem PPeq p (globalNames G) (globalNames H));
Qrepl Q_sym (globalNames_append_lem G H);Immed;
Save Pocc_compound_lem;

Goal {p|PP}{G,H|Cxt}(is_ff (Poccur p (append G H)))->
      and (is_ff (Poccur p G)) (is_ff (Poccur p H));
intros;Refine fst (deMorgan (Poccur p G) (Poccur p H));
Qrepl Q_sym (member_append_lem PPeq p (globalNames G) (globalNames H));
Qrepl Q_sym (globalNames_append_lem G H);Immed;
Save Pocc_combine_lem;

Goal {p|PP}{G,H|Cxt}(is_ff (Poccur p G))->(is_ff (Poccur p H))->
      is_ff (Poccur p (append G H));
intros;Expand Poccur;Qrepl globalNames_append_lem G H;
Qrepl member_append_lem PPeq p (globalNames G) (globalNames H);
Refine snd (deMorgan (Poccur p G) (Poccur p H));Refine pair;Immed;
Save Pocc_split_lem2;

Goal {G|Cxt}{p|PP}{b|GB}(is_ff (Poccur p (CONS b G)))->
               and (is_ff (PPeq p (namOf b))) (is_ff (Poccur p G));
intros; Refine fst (deMorgan ? (Poccur ? ?)) H;
Save Poccur_CONS_lem;

Goal {G|Cxt}{p|PP}{b|GB}(is_ff (PPeq p (namOf b)))->(is_ff (Poccur p G))->
       is_ff (Poccur p (CONS b G));
intros;Refine snd (deMorgan ? (Poccur ? ?));
Refine pair;Immed;
Save CONS_Poccur_lem;

Goal {G|Cxt}{p,q|PP}{B|Trm}(is_tt (Poccur p (CONS (Gb q B) G)))->
               (or (is_tt (PPeq p q)) (is_tt (Poccur p G)));
intros ____; Refine fst (orr_character ? ?);
Save mlc1;

Goal {G|Cxt}{p,q|PP}{B|Trm}(or (is_tt (PPeq p q)) (is_tt (Poccur p G)))->
                 (is_tt (Poccur p (CONS (Gb q B) G)));
intros ____; Refine snd (orr_character ? ?);
Save mlc2;

Goal {G,H|Cxt}{p,q|PP}{A|Trm}
       (is_ff (Poccur p (append G (CONS (Gb q A) H))))->
        and3 (is_ff (Poccur p G))
             (is_ff (PPeq p q))
             (is_ff (Poccur p H));
intros;Refine Pocc_combine_lem;Immed;
intros noccG noccqAH;Refine Poccur_CONS_lem noccqAH;
intros neqP noccH;Refine pair3;Immed;
Save Poccur_compound_lem;

(* some lemmas to simplify choosing fresh enough parameters *)
[p:PP][G:Cxt][M,M',M'',M''':Trm];

Goal ex [q:PP]and (is_ff (Poccur q G)) (is_ff (poccur q M));
intros;Refine PPinf (append (globalNames G) (params M));
intros q qFresh;
[qFresh1 : and (is_ff (Poccur q G))
               (is_ff (poccur q M))
         = fst (deMorgan (Poccur q G) (poccur q M))
               (member_append_lem' PPeq q qFresh)];
[noccG = fst qFresh1][noccM = snd qFresh1];
Refine ExIn q;Refine pair;Immed;
Save fresh_params_lem1G;

Goal ex [q:PP]and3 (is_ff (Poccur q G))
                   (is_ff (poccur q M)) (is_ff (poccur q M'));
intros;Refine PPinf (append (globalNames G) (append (params M) (params M')));
intros q qFresh;
[qFresh0 : and (is_ff (Poccur q G))
               (is_ff (member PPeq q (append (params M) (params M'))))
         = fst (deMorgan (Poccur q G)
                         (member PPeq q (append (params M) (params M'))))
               (member_append_lem' PPeq q qFresh)];
[qFresh1 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem (snd qFresh0)];
[noccG = fst qFresh0];
[noccM = fst qFresh1][noccM' = snd qFresh1];
Refine ExIn q;Refine pair3;Immed;
Save fresh_params_lem2G;

Goal ex [q:PP]and4 (is_ff (Poccur q G))
                   (is_ff (poccur q M))
                   (is_ff (poccur q M'))
                   (is_ff (poccur q M''));
intros;Refine PPinf (append (globalNames G)
                    (append (params M) (append (params M') (params M''))));
intros q qFresh;
[qFresh0 : and (is_ff (Poccur q G))
               (is_ff (member PPeq q (append (params M)
                                     (append (params M') (params M'')))))
         = fst (deMorgan (Poccur q G)
                         (member PPeq q (append (params M)
                                        (append (params M') (params M'')))))
               (member_append_lem' PPeq q qFresh)];
[qFresh1 : and (is_ff (poccur q M))
               (is_ff (member PPeq q (append (params M') (params M''))))
         = fst (deMorgan (poccur q M)
                         (member PPeq q (append (params M') (params M''))))
               (member_append_lem' PPeq q (snd qFresh0))];
[qFresh2 : and (is_ff (poccur q M')) (is_ff (poccur q M''))
         = pocc_combine_lem (snd qFresh1)];
[noccG = fst qFresh0];
[noccM = fst qFresh1][noccM' = fst qFresh2][noccM'' = snd qFresh2];
Refine ExIn q;Refine pair4;Immed;
Save fresh_params_lem3G;

Goal ex [q:PP]and5 (is_ff (Poccur q G))
                   (is_ff (poccur q M)) (is_ff (poccur q M'))
                   (is_ff (poccur q M'')) (is_ff (poccur q M'''));
intros;Refine PPinf (append (globalNames G)
                            (append (append (params M) (params M'))
                                    (append (params M'') (params M'''))));
intros q qFresh;
[qFresh0 : and (is_ff (Poccur q G))
               (is_ff (member PPeq q (append (append (params M) (params M'))
                                             (append (params M'') (params M''')))))
         = fst (deMorgan (Poccur q G)
                         (member PPeq q (append (append (params M) (params M'))
                                          (append (params M'') (params M''')))))
               (member_append_lem' PPeq q qFresh)];
[qFresh1 : and (is_ff (member PPeq q (append (params M) (params M'))))
               (is_ff (member PPeq q (append (params M'') (params M'''))))
         = fst (deMorgan (member PPeq q (append (params M) (params M')))
                         (member PPeq q (append (params M'') (params M'''))))
               (member_append_lem' PPeq q (snd qFresh0))];
[qFresh2 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem (fst qFresh1)];
[qFresh3 : and (is_ff (poccur q M'')) (is_ff (poccur q M'''))
         = pocc_combine_lem (snd qFresh1)];
[noccG = fst qFresh0];
[noccM = fst qFresh2][noccM' = snd qFresh2];
[noccM'' = fst qFresh3][noccM''' = snd qFresh3];
Refine ExIn q;Refine pair5;Immed;
Save fresh_params_lem4G;

Discharge p;

(* names with any instances in a context *)
[freeNames : Cxt->PPs
            = LLrec ([_:Cxt]PPs)
                    (NIL|PP)
                    ([b:GB][_:Cxt][rest:PPs]
                          CONS (namOf b) (append (params (typOf b)) rest))];

[POCCUR [p:PP][G:Cxt] : BB = member PPeq p (freeNames G)];

Goal {p|PP}{G|Cxt}(is_tt (Poccur p G))->is_tt (POCCUR p G);
intros _;
Refine LLrec [G:Cxt]{occ:is_tt (Poccur p G)}is_tt (POCCUR p G);
intros;Immed;
intros;Refine fst (orr_character (PPeq ? ?) (Poccur ? ?)) occ;
intros;Refine snd (orr_character (PPeq ? ?) (member ? ? (append ? (freeNames ?))));
       Refine inl;Immed;
intros;Refine snd (orr_character (PPeq ? ?) ?);Refine inr;
       Qrepl member_append_lem PPeq p (params (typOf b)) (freeNames prem);
       Refine snd (orr_character (poccur ? ?) (POCCUR ? ?));Refine inr;
       Refine LLih;Immed;
Save Poccur_POCCUR;

Goal {p|PP}{G|Cxt}{nocc:is_ff (POCCUR p G)}is_ff (Poccur p G);
intros;Refine B_contrapos ? nocc;Refine Poccur_POCCUR;
Save POCCUR_Poccur;

Goal {G|Cxt}{p,q|PP}{B|Trm}(is_tt (POCCUR p (CONS (Gb q B) G)))->
               (or3 (is_tt (PPeq p q)) (is_tt (poccur p B)) (is_tt (POCCUR p G)));
intros;Refine fst (orr_character ? ?);Immed;
intros;Refine or3_in1;Immed;
Qrepl member_append_lem PPeq p (params B) (freeNames G);
intros;Refine fst (orr_character (poccur ? ?) (POCCUR ? ?));Immed;
intros;Refine or3_in2;Immed;
intros;Refine or3_in3;Immed;
Save MLC1;

Goal {G|Cxt}{p,q|PP}{B|Trm}
     (or3 (is_tt (PPeq p q)) (is_tt (poccur p B)) (is_tt (POCCUR p G)))->
      is_tt (POCCUR p (CONS (Gb q B) G));
intros;Refine snd (orr_character ? ?);
Qrepl member_append_lem PPeq p (params B) (freeNames G);
Refine H;
intros;Refine inl;Immed;
intros;Refine inr;Refine snd (orr_character ? ?);Refine inl;Immed;
intros;Refine inr;Refine snd (orr_character ? ?);Refine inr;Immed;
Save MLC2;

Goal {G|Cxt}{p|PP}{b|GB}(is_ff (POCCUR p (CONS b G)))->
           and3 (is_ff (PPeq p (namOf b)))
                (is_ff (poccur p (typOf b)))
                (is_ff (POCCUR p G));
intros;
[lem : and (is_ff (PPeq p (namOf b)))
           (is_ff (member PPeq p (append (params (typOf b))
                                         (freeNames G))))
     = fst (deMorgan ? ?) H];
[lem2 : and (is_ff (poccur p (typOf b))) (is_ff (POCCUR p G))
      = fst (deMorgan ? ?) (member_append_lem' PPeq p (snd lem))];
Refine pair3 (fst lem) (fst lem2) (snd lem2);
Save POCCUR_CONS_lem;

Goal {G|Cxt}{p|PP}{b|GB}(is_ff (PPeq p (namOf b)))->
      (is_ff (poccur p (typOf b)))->(is_ff (POCCUR p G))->
       is_ff (POCCUR p (CONS b G));
intros;Refine snd (deMorgan ? (member PPeq p (append (params ?) (freeNames ?))));
Refine pair;Immed;
Qrepl member_append_lem PPeq p (params (typOf b)) (freeNames G);
Refine snd (deMorgan (poccur ? ?) (POCCUR ? ?));
Refine pair;Immed;
Save CONS_POCCUR_lem;

(* inclusion of contexts: why not make this a decidable relation? *)
%\VerbFileOpen subCxt_verb
[subCxt [G,H:Cxt] = {b:GB}(is_tt (GBoccur b G))->is_tt (GBoccur b H)];
%\VerbFileClos subCxt_verb

Goal {G:Cxt}subCxt G G;
Intros;Immed;
Save subCxt_refl;

Goal {G,G'|Cxt}(subCxt G G')->
         {p:PP}{A:Trm}subCxt (CONS (Gb p A) G) (CONS (Gb p A) G');
intros;Expand subCxt; 
intros b bMem;
Refine fst (orr_character ? ?) bMem;
intros beqp;
Refine snd (orr_character ? ?);
Refine inl;Immed;
intros bMemG;
Refine snd (orr_character ? ?);
Refine inr;Refine H;Immed;
Save subCxt_extension;

Goal {G,K:Cxt}subCxt K (append K G);
Intros;Qrepl member_append_lem GBeq b K G;
Refine snd (orr_character ? ?);Refine inl;Immed;
Save subCxt_l;

Goal {G,K:Cxt}subCxt G (append K G);
Intros;Qrepl member_append_lem GBeq b K G;
Refine snd (orr_character ? ?);Refine inr;Immed;
Save subCxt_r;

Goal {G,H,K|Cxt}(subCxt G K)->(subCxt H K)->subCxt (append H G) K;
Intros ______;Qrepl member_append_lem GBeq b H G;intros;
Refine fst (orr_character ? ?) H3;
intros;Refine H2;Immed;
intros;Refine H1;Immed;
Save subCxt_append;

Goal {p|PP}{A|Trm}{G|Cxt}subCxt G (CONS (Gb p A) G);
Intros;Refine snd (orr_character ? ?);Refine inr;Immed;
Save subCxt_hd;

Goal {p|PP}{A|Trm}{G,G'|Cxt}(subCxt (CONS (Gb p A) G) G')->subCxt G G';
Intros;Refine H;Refine snd (orr_character ? ?);Refine inr;Immed;
Save subCxt_tail;

Goal {G1,G2,G3|Cxt}(subCxt G1 G2)->(subCxt G2 G3)->subCxt G1 G3;
Expand subCxt; intros;
Refine H1; Refine H; Immed;
Save subCxt_trans;

Goal {G,G'|Cxt}(subCxt G G')->{b|GB}(is_tt (GBoccur b G))->
         is_tt (GBoccur b G');
Refine LLrec [G:Cxt]{G'|Cxt}(subCxt G G')->{b|GB}(is_tt (GBoccur b G))->
         is_tt (GBoccur b G');
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine H; Immed;
Save subCxt_GBoccur_lem;

Goal {G,G'|Cxt}(subCxt G G')->{b|GB}(is_ff (GBoccur b G'))->
         is_ff (GBoccur b G);
intros ____; Refine B_contrapos; Refine subCxt_GBoccur_lem; Immed;
Save GBoccur_subCxt_lem;

Goal {G,G'|Cxt}{sub:subCxt G G'}
     {p|PP}(is_tt (Poccur p G))->
            is_tt (Poccur p G');
Refine LLrec [G:Cxt]{G'|Cxt}{sub:subCxt G G'}
     {p|PP}(is_tt (Poccur p G))->
            is_tt (Poccur p G');
intros; Refine tt_not_ff (Q_sym H);
intros;Refine fst (orr_character ? (Poccur p prem)) H;
intros eq; Qrepl (PPdecide eq); Refine GBoccur_Poccur_lem;
Refine sub b;
Refine snd (orr_character ? (GBoccur ? ?));
Refine inl; Refine GBeq_refl;
intros inPrem; Refine LLih;
Expand subCxt; intros; Refine sub;
Refine snd (orr_character ? (GBoccur ? ?));
Refine inr; Immed; Immed;
Save subCxt_Poccur_lem;

Goal {G,G'|Cxt}{sub:subCxt G G'}
     {p|PP}(is_ff (Poccur p G'))->
            is_ff (Poccur p G);
intros ____; Refine B_contrapos; Refine subCxt_Poccur_lem; Immed;
Save Poccur_subCxt_lem;

