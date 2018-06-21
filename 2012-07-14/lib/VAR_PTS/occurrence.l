Module occurrence Import terms;

(* occurrence lemmas *)

[params : Trm->PPs =
  Trec ([_:Trm]PPs)
       ([_:SS]NIL|PP)
       ([_:VV]NIL|PP)
       ([p:PP]unit p)
       ([_:VV][_,_:Trm][l,r:PPs]append l r)
       ([_:VV][_,_:Trm][l,r:PPs]append l r)
       ([_,_:Trm][l,r:PPs]append l r)];

[poccur [p:PP][A:Trm] : BB = member PPeq p (params A)];

[sorts : Trm->SSs =
  Trec ([_:Trm]SSs)
       ([s:SS]unit s)
       ([_:VV]NIL|SS)
       ([_:PP]NIL|SS)
       ([_:VV][_,_:Trm][l,r:SSs]append l r)
       ([_:VV][_,_:Trm][l,r:SSs]append l r)
       ([_,_:Trm][l,r:SSs]append l r)];

[soccur [s:SS][A:Trm] : BB = member SSeq s (sorts A)];

Goal pocc_par_lem: {p,q:PP}Q (poccur p (par q)) (PPeq p q);
intros; Qrepl ff_orr_unit (PPeq p q); Refine Q_refl;
Save;

Goal {s,t:SS}Q (soccur s (sort t)) (SSeq s t);
intros; Qrepl ff_orr_unit (SSeq s t); Refine Q_refl;
Save socc_sort_lem;

Goal isSrt_socc_equal:
     {A|Trm}(is_tt (isSrt A))->{s|SS}(is_tt (soccur s A))->Q A (sort s);
intros _ srtA _ sinA; Refine isSrt_lem srtA; intros t teqA;
Qrepl Trm_eq_subst teqA; Refine Q_resp; Refine Q_sym; Refine SSdecide;
Qrepl Q_sym (socc_sort_lem s t); Qrepl Q_sym (Trm_eq_subst teqA); Immed;
Save;

Goal pocc_split_lem:
     {p|PP}{A,B|Trm}(or (is_tt (poccur p A)) (is_tt (poccur p B)))->
              is_tt (member PPeq p (append (params A) (params B)));
intros;
Qrepl member_append_lem PPeq p (params A) (params B);
Refine snd (orr_character (poccur ? ?) (poccur ? ?)); Immed;
Save pocc_split_lem;


Goal {s:SS}{A,B:Trm}Q (orr (soccur s A) (soccur s B))
                      (member SSeq s (append (sorts A) (sorts B)));
intros; Qrepl member_append_lem SSeq s (sorts A) (sorts B); Refine Q_refl;
Save socc_split;

Goal {s|SS}{A,B|Trm}(or (is_tt (soccur s A)) (is_tt (soccur s B)))->
              is_tt (member SSeq s (append (sorts A) (sorts B)));
intros;
Qrepl member_append_lem SSeq s (sorts A) (sorts B);
Refine snd (orr_character (soccur ? ?) (soccur ? ?)); Immed;
Save socc_split_lem;

Goal pocc_compound_lem:
     {p|PP}{A,B|Trm}
       (is_tt (member PPeq p (append (params A) (params B))))->
         or (is_tt (poccur p A)) (is_tt (poccur p B));
intros;
Refine fst (orr_character (poccur ? ?) (poccur ? ?));
Qrepl Q_sym (member_append_lem PPeq p (params A) (params B));
Immed;
Save pocc_compound_lem;

Goal {s|SS}{A,B|Trm}
       (is_tt (member SSeq s (append (sorts A) (sorts B))))->
         or (is_tt (soccur s A)) (is_tt (soccur s B));
intros;
Refine fst (orr_character (soccur ? ?) (soccur ? ?));
Qrepl Q_sym (member_append_lem SSeq s (sorts A) (sorts B));
Immed;
Save socc_compound_lem;

(* this is really a general deMorgan lemma *)
Goal {p|PP}{A,B|Trm}(is_ff (member PPeq p (append (params A) (params B))))->
         and (is_ff (poccur p A)) (is_ff (poccur p B));
intros;
Refine fst (deMorgan (poccur ? ?) (poccur ? ?));
Qrepl Q_sym (member_append_lem PPeq p (params A) (params B));
Immed;
Save pocc_combine_lem;

Goal {s|SS}{A,B|Trm}(is_ff (member SSeq s (append (sorts A) (sorts B))))->
         and (is_ff (soccur s A)) (is_ff (soccur s B));
intros;
Refine fst (deMorgan (soccur ? ?) (soccur ? ?));
Qrepl Q_sym (member_append_lem SSeq s (sorts A) (sorts B));
Immed;
Save socc_combine_lem;

Goal {p|PP}{A,B|Trm}(is_ff (member PPeq p (append (params A) (params B))))->
         is_ff (orr (poccur p A) (poccur p B));
intros;
Qrepl Q_sym (member_append_lem PPeq p (params A) (params B));
Immed;
Save pocc_combine_lem2;

Goal {s|SS}{A,B|Trm}(is_ff (member SSeq s (append (sorts A) (sorts B))))->
         is_ff (orr (soccur s A) (soccur s B));
intros;
Qrepl Q_sym (member_append_lem SSeq s (sorts A) (sorts B));
Immed;
Save socc_combine_lem2;

Goal {p|PP}{A|Trm}(is_ff (poccur p A))->{B|Trm}(is_ff (poccur p B))->
         is_ff (member PPeq p (append (params A) (params B)));
intros;
Qrepl member_append_lem PPeq p (params A) (params B);
Refine snd (deMorgan (poccur ? ?) (poccur ? ?)); Refine pair; Immed;
Save pocc_split_lem2;

Goal {s|SS}{A|Trm}(is_ff (soccur s A))->{B|Trm}(is_ff (soccur s B))->
         is_ff (member SSeq s (append (sorts A) (sorts B)));
intros;
Qrepl member_append_lem SSeq s (sorts A) (sorts B);
Refine snd (deMorgan (soccur ? ?) (soccur ? ?)); Refine pair; Immed;
Save socc_split_lem2;

(* some derived induction principles for occurrence checks *)

[C:PP->Trm->Prop][p|PP];
[D:SS->Trm->Prop][s|SS];

Goal {pocc_par:{n|PP}{neqP:is_tt (PPeq p n)}C p (par n)}
     {pocc_piA:{n:VV}{A,B|Trm}{occA:is_tt (poccur p A)}{ihA:C p A}
                             {ihB:{occB:is_tt (poccur p B)}C p B}
               C p (pi n A B)}
     {pocc_piB:{n:VV}{A,B|Trm}{ihA:{occA:is_tt (poccur p A)}C p A}
                             {occB:is_tt (poccur p B)}{ihB:C p B}
               C p (pi n A B)}
     {pocc_ldaA:{n:VV}{A,B|Trm}{occA:is_tt (poccur p A)}{ihA:C p A}
                              {ihB:{occB:is_tt (poccur p B)}C p B}
                C p (lda n A B)}
     {pocc_ldaB:{n:VV}{A,B|Trm}{ihA:{occA:is_tt (poccur p A)}C p A}
                              {occB:is_tt (poccur p B)}{ihB:C p B}
                C p (lda n A B)}
     {pocc_appA:{A,B|Trm}{occA:is_tt (poccur p A)}{ihA:C p A}
                        {ihB:{occB:is_tt (poccur p B)}C p B}
                C p (app A B)}
     {pocc_appB:{A,B|Trm}{ihA:{occA:is_tt (poccur p A)}C p A}
                        {occB:is_tt (poccur p B)}{ihB:C p B}
                C p (app A B)}
     {M|Trm}(is_tt (poccur p M)) -> C p M;

intros;Refine Trec [M|Trm]{occ:is_tt (poccur p M)}C p M;Immed;
intros;Refine tt_not_ff (Q_sym occ);
intros;Refine tt_not_ff (Q_sym occ);
intros;Refine pocc_par;Qrepl Q_sym (pocc_par_lem p n);Immed;
intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_piA;Refine +1 ihA;Immed;
intros occB;Refine pocc_piB;Refine +2 ihB;Immed;
intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_ldaA;Refine +1 ihA;Immed;
intros occB;Refine pocc_ldaB;Refine +2 ihB;Immed;
intros;Refine pocc_compound_lem occ;
intros occA;Refine pocc_appA;Refine +1 ihA;Immed;
intros occB;Refine pocc_appB;Refine +2 ihB;Immed;
Save pocc_Trec;

Goal {socc_sort:{t|SS}{neqS:is_tt (SSeq s t)}D s (sort t)}
     {socc_piA:{n:VV}{A,B|Trm}{occA:is_tt (soccur s A)}{ihA:D s A}
                             {ihB:{occB:is_tt (soccur s B)}D s B}
               D s (pi n A B)}
     {socc_piB:{n:VV}{A,B|Trm}{ihA:{occA:is_tt (soccur s A)}D s A}
                             {occB:is_tt (soccur s B)}{ihB:D s B}
               D s (pi n A B)}
     {socc_ldaA:{n:VV}{A,B|Trm}{occA:is_tt (soccur s A)}{ihA:D s A}
                              {ihB:{occB:is_tt (soccur s B)}D s B}
                D s (lda n A B)}
     {socc_ldaB:{n:VV}{A,B|Trm}{ihA:{occA:is_tt (soccur s A)}D s A}
                              {occB:is_tt (soccur s B)}{ihB:D s B}
                D s (lda n A B)}
     {socc_appA:{A,B|Trm}{occA:is_tt (soccur s A)}{ihA:D s A}
                        {ihB:{occB:is_tt (soccur s B)}D s B}
                D s (app A B)}
     {socc_appB:{A,B|Trm}{ihA:{occA:is_tt (soccur s A)}D s A}
                        {occB:is_tt (soccur s B)}{ihB:D s B}
                D s (app A B)}
     {M|Trm}(is_tt (soccur s M)) -> D s M;

intros;Refine Trec [M|Trm]{occ:is_tt (soccur s M)}D s M;Immed;
intros;Refine socc_sort;Qrepl Q_sym (socc_sort_lem s s1);Immed;
intros;Refine tt_not_ff (Q_sym occ);
intros;Refine tt_not_ff (Q_sym occ);
intros;Refine socc_compound_lem occ;
intros occA;Refine socc_piA;Refine +1 ihA;Immed;
intros occB;Refine socc_piB;Refine +2 ihB;Immed;
intros;Refine socc_compound_lem occ;
intros occA;Refine socc_ldaA;Refine +1 ihA;Immed;
intros occB;Refine socc_ldaB;Refine +2 ihB;Immed;
intros;Refine socc_compound_lem occ;
intros occA;Refine socc_appA;Refine +1 ihA;Immed;
intros occB;Refine socc_appB;Refine +2 ihB;Immed;
Save socc_Trec;

Goal {nocc_sort:{s:SS}C p (sort s)}
     {nocc_var:{n:VV}C p (var n)}
     {nocc_par:{n|PP}{noccP:is_ff (PPeq p n)}C p (par n)}
     {nocc_pi:{n:VV}{A,B|Trm}{noccA:is_ff (poccur p A)}{ihA:C p A}
                             {noccB:is_ff (poccur p B)}{ihB:C p B}
               C p (pi n A B)}
     {nocc_lda:{n:VV}{A,B|Trm}{noccA:is_ff (poccur p A)}{ihA:C p A}
                              {noccB:is_ff (poccur p B)}{ihB:C p B}
                C p (lda n A B)}
     {nocc_app:{A,B|Trm}{noccA:is_ff (poccur p A)}{ihA:C p A}
                        {noccB:is_ff (poccur p B)}{ihB:C p B}
                C p (app A B)}
     {M|Trm}(is_ff (poccur p M)) -> C p M;

intros;Refine Trec [M|Trm]{nocc:is_ff (poccur p M)}C p M;Immed;
intros;Immed;
intros;Immed;
intros;Refine nocc_par;Qrepl Q_sym (pocc_par_lem p n);Immed;
intros;Refine pocc_combine_lem nocc;
intros noccA noccB;Refine nocc_pi;Refine +1 ihA;Refine +3 ihB;Immed;
intros;Refine pocc_combine_lem nocc;
intros noccA noccB;Refine nocc_lda;Refine +1 ihA;Refine +3 ihB;Immed;
intros;Refine pocc_combine_lem nocc;
intros noccA noccB;Refine nocc_app;Refine +1 ihA;Refine +3 ihB;Immed;
Save not_pocc_Trec;

Goal {nocc_sort:{t|SS}{noccS:is_ff (SSeq s t)}D s (sort t)}
     {nocc_var:{n:VV}D s (var n)}
     {nocc_par:{n:PP}D s (par n)}
     {nocc_pi:{n:VV}{A,B|Trm}{noccA:is_ff (soccur s A)}{ihA:D s A}
                             {noccB:is_ff (soccur s B)}{ihB:D s B}
               D s (pi n A B)}
     {nocc_lda:{n:VV}{A,B|Trm}{noccA:is_ff (soccur s A)}{ihA:D s A}
                              {noccB:is_ff (soccur s B)}{ihB:D s B}
                D s (lda n A B)}
     {nocc_app:{A,B|Trm}{noccA:is_ff (soccur s A)}{ihA:D s A}
                        {noccB:is_ff (soccur s B)}{ihB:D s B}
                D s (app A B)}
     {M|Trm}(is_ff (soccur s M)) -> D s M;

intros;Refine Trec [M|Trm]{nocc:is_ff (soccur s M)}D s M;Immed;
intros;Refine nocc_sort;Qrepl Q_sym (socc_sort_lem s s1);Immed;
intros;Immed;
intros;Immed;
intros;Refine socc_combine_lem nocc;
intros noccA noccB;Refine nocc_pi;Refine +1 ihA;Refine +3 ihB;Immed;
intros;Refine socc_combine_lem nocc;
intros noccA noccB;Refine nocc_lda;Refine +1 ihA;Refine +3 ihB;Immed;
intros;Refine socc_combine_lem nocc;
intros noccA noccB;Refine nocc_app;Refine +1 ihA;Refine +3 ihB;Immed;
Save not_socc_Trec;

Discharge C;

(* some easy warm-up examples *)

Goal {p|PP}{B|Trm}(is_ff (poccur p B))->is_ff (Trm_eq B (par p));
intros;Refine not_pocc_Trec [p|PP][B:Trm]is_ff (Trm_eq B (par p));Immed;
(* all others trivial *)
intros; Refine Q_refl;
intros; Refine Q_refl;
(* par *)
intros;Qrepl Trm_eq_sym (par n) (par p);Immed;
(* all others trivial *)
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Refine Q_refl;
Save not_pocc_not_eq;

Goal {s|SS}{B|Trm}(is_ff (soccur s B))->is_ff (Trm_eq B (sort s));
intros;Refine not_socc_Trec [s|SS][B:Trm]is_ff (Trm_eq B (sort s));Immed;
(* sort *)
intros;Qrepl Trm_eq_sym (sort t) (sort s);Immed;
(* all others trivial *)
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Refine Q_refl;
Save not_socc_not_eq;

(* some lemmas to simplify choosing fresh enough parameters *)
[p:PP][M,M',M'',M''':Trm];

Goal fresh_params_lem1: ex [q:PP]is_ff (poccur q M);
Refine PPinf (params M);
Save fresh_params_lem1;

Goal fresh_params_lem1p:
     ex [q:PP]and (is_ff (PPeq q p)) (is_ff (poccur q M));
Refine PPinf (CONS p (params M));
intros q qFresh;
[qFresh1 : and (is_ff (PPeq q p))
               (is_ff (poccur q M))
         = fst (deMorgan (PPeq q p) (poccur q M)) qFresh];
[neqPP = fst qFresh1][noccM = snd qFresh1];
Refine ExIn q; Refine pair; Immed;
Save fresh_params_lem1p;

Goal fresh_params_lem2:
     ex [q:PP]and (is_ff (poccur q M)) (is_ff (poccur q M'));
intros;Refine PPinf (append (params M) (params M'));
intros q qFresh;
[qFresh1 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem qFresh];
[noccM = fst qFresh1][noccM' = snd qFresh1];
Refine ExIn q;Refine pair;Immed;
Save fresh_params_lem2;

Goal fresh_params_lem2p:
     ex[q:PP] and3 (is_ff (PPeq q p))
                   (is_ff (poccur q M))
                   (is_ff (poccur q M'));
intros;Refine PPinf (CONS p (append (params M) (params M')));
intros q qFresh;
[qFresh1 : and (is_ff (PPeq q p))
               (is_ff (member PPeq q (append (params M) (params M'))))
         = fst (deMorgan (PPeq q p)
                         (member PPeq q (append (params M) (params M'))))
               qFresh];
[qFresh2 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem (snd qFresh1)];
[neqPP = fst qFresh1][noccM = fst qFresh2][noccM' = snd qFresh2];
Refine ExIn q;Refine pair3;Immed;
Save fresh_params_lem2p;

Goal ex [q:PP]and3 (is_ff (poccur q M))
                   (is_ff (poccur q M'))
                   (is_ff (poccur q M''));
intros;Refine PPinf (append (params M) (append (params M') (params M'')));
intros q qFresh;
[qFresh1 : and (is_ff (poccur q M))
               (is_ff (member PPeq q (append (params M') (params M''))))
         = fst (deMorgan (poccur q M)
                         (member PPeq q (append (params M') (params M''))))
               (member_append_lem' PPeq q qFresh)];
[qFresh2 : and (is_ff (poccur q M')) (is_ff (poccur q M''))
         = pocc_combine_lem (snd qFresh1)];
[noccM = fst qFresh1][noccM' = fst qFresh2][noccM'' = snd qFresh2];
Refine ExIn q;Refine pair3;Immed;
Save fresh_params_lem3;

Goal ex [q:PP]and4 (is_ff (PPeq q p)) (is_ff (poccur q M))
                   (is_ff (poccur q M')) (is_ff (poccur q M''));
intros;
Refine PPinf (CONS p (append (params M) (append (params M') (params M''))));
intros q qFresh;
[qFresh1 : and (is_ff(PPeq q p))
               (is_ff (member PPeq q (append (params M)
                                             (append (params M')
                                                     (params M'')))))
         = fst (deMorgan ? ?) qFresh];
[qFresh2 : and (is_ff (poccur q M))
               (is_ff(member PPeq q (append (params M') (params M''))))
         = fst (deMorgan ? ?) (exist_append_lem' (PPeq q) (snd qFresh1))];
[qFresh3 : and (is_ff (poccur q M')) (is_ff (poccur q M''))
         = pocc_combine_lem (snd qFresh2)];
[neqPP = fst qFresh1][noccM = fst qFresh2];
[noccM' = fst qFresh3][noccM'' = snd qFresh3];
Refine ExIn q;Refine pair4;Immed;
Save fresh_params_lem3p;

Goal ex [q:PP]and4 (is_ff (poccur q M)) (is_ff (poccur q M'))
                   (is_ff (poccur q M'')) (is_ff (poccur q M'''));
intros;Refine PPinf (append (append (params M) (params M'))
                            (append (params M'') (params M''')));
intros q qFresh;
[qFresh1 : and (is_ff (member PPeq q (append (params M) (params M'))))
               (is_ff (member PPeq q (append (params M'') (params M'''))))
         = fst (deMorgan (member PPeq q (append (params M) (params M')))
                         (member PPeq q (append (params M'') (params M'''))))
               (member_append_lem' PPeq q qFresh)];
[qFresh2 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem (fst qFresh1)];
[qFresh3 : and (is_ff (poccur q M'')) (is_ff (poccur q M'''))
         = pocc_combine_lem (snd qFresh1)];
[noccM = fst qFresh2][noccM' = snd qFresh2];
[noccM'' = fst qFresh3][noccM''' = snd qFresh3];
Refine ExIn q;Refine pair4;Immed;
Save fresh_params_lem4;

Goal ex [q:PP]and5 (is_ff (PPeq q p))
                   (is_ff (poccur q M)) (is_ff (poccur q M'))
                   (is_ff (poccur q M'')) (is_ff (poccur q M'''));
intros;Refine PPinf (CONS p (append (append (params M) (params M'))
                                    (append (params M'') (params M'''))));
intros q qFresh;
[qFresh1 : and (is_ff(PPeq q p))
               (is_ff (member PPeq q (append (append (params M) (params M'))
                                             (append (params M'') (params M''')))))
         = fst (deMorgan ? ?) qFresh];
[qFresh2 : and (is_ff (member PPeq q (append (params M) (params M'))))
               (is_ff (member PPeq q (append (params M'') (params M'''))))
         = fst (deMorgan ? ?) (exist_append_lem' (PPeq q) (snd qFresh1))];
[qFresh3 : and (is_ff (poccur q M)) (is_ff (poccur q M'))
         = pocc_combine_lem (fst qFresh2)];
[qFresh4 : and (is_ff (poccur q M'')) (is_ff (poccur q M'''))
         = pocc_combine_lem (snd qFresh2)];
[neqPP = fst qFresh1][noccM = fst qFresh3][noccM' = snd qFresh3];
[noccM'' = fst qFresh4][noccM''' = snd qFresh4];
Refine ExIn q;Refine pair5;Immed;
Save fresh_params_lem4p;

Discharge p;

