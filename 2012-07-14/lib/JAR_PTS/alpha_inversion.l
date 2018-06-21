Module alpha_inversion Import alpha;

[s|SS][A,B|Trm][p,q|PP][u,v|VV]$[alph = alpha p v];

Goal {X|Trm}(is_tt (Trm_eq (sort s) (alph X)))->is_tt (Trm_eq X (sort s));
Refine Trec [X:Trm]
            {eq:is_tt (Trm_eq (sort s) (alph X))}is_tt (Trm_eq X (sort s));
intros;Qrepl SSsym s1 s;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}is_tt ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Immed;
intros case;Qrepl case;intros;Immed;
intros;Immed;
intros;Immed;
intros;Immed;
intros;Immed;
Save alpha_sort_character;

Goal {X|Trm}(is_tt (Trm_eq (var u) (alph X)))->and (is_tt (Trm_eq X (var u)))
                                                   (is_ff (VVeq v u));
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (var u) (alph X))}
             and (is_tt (Trm_eq X (var u))) (is_ff (VVeq v u));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}and ? ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine pair;
Qrepl VVsym n u;Qrepl +1 VVdecide ?+0;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_var_character;

Goal {X|Trm}(is_tt (Trm_eq (par q) (alph X)))->or (is_tt (Trm_eq X (par q)))
                                                  (is_tt (Trm_eq X (var v)));
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (par q) (alph X))}
             or (is_tt (Trm_eq X (par q))) (is_tt (Trm_eq X (var v)));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv (is_tt (Trm_eq ? (if (VVeq v n) ? ?)))->or ? ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine inr;Qrepl VVsym n v;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine inl;Qrepl PPsym n q;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_par_character;

Goal {X|Trm}(is_ff (poccur p X))->(is_tt (Trm_eq (par q) (alph X)))->
      or (and (is_ff (PPeq p q)) (is_tt (Trm_eq X (par q))))
         (is_tt (Trm_eq X (var v)));
Refine not_pocc_Trec [p:PP][X:Trm]{eq:is_tt (Trm_eq (par q) (alph X))}
             or (and (is_ff (PPeq p q)) (is_tt (Trm_eq X (par q))))
                (is_tt (Trm_eq X (var v)));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}
                or ? ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine inr;Qrepl VVsym n v;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine inl;Qrepl PPdecide eq;Refine pair noccP;Refine PPrefl n;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_par_nocc_character;

Goal {X|Trm}(is_tt (Trm_eq (pi u A B) (alph X)))->
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (pi u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))));
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (pi u A B) (alph X))}
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (pi u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _____;
Equiv {eq:is_tt (Trm_eq ? (pi n (alph ?) (if (VVeq v n) ? (alph ?))))}Ex2 ?;
Qrepl VVsym v n;
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;Qrepl VVtrans eqV v;Qrepl VVdecide eqV;
Refine Ex2In A1 B1;Refine pair3;Refine Trm_eq_refl;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_pi_character;

Goal {X|Trm}(is_ff (poccur p X))->(is_tt (Trm_eq (pi u A B) (alph X)))->
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (pi u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))))
                          (is_ff (poccur p B'));
Refine not_pocc_Trec [p:PP][X:Trm]{eq:is_tt (Trm_eq (pi u A B) (alph X))}
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (pi u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))))
                          (is_ff (poccur p B'));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;
Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _______;
Equiv {eq:is_tt (Trm_eq ? (pi n (alph A1) (if (VVeq v n) ? (alph B1))))}
       Ex2 ?;
Qrepl VVsym v n;
intros;Refine Trm_eq_pi_lem eq;
intros eqV eqA eqB;Qrepl VVtrans eqV v;Qrepl VVdecide eqV;
Refine Ex2In A1 B1;Refine pair5;Refine Trm_eq_refl;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_pi_nocc_character;

Goal {X|Trm}(is_tt (Trm_eq (lda u A B) (alph X)))->
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (lda u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))));
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (lda u A B) (alph X))}
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (lda u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _____;
Equiv {eq:is_tt (Trm_eq ? (lda n (alph ?) (if (VVeq v n) ? (alph ?))))}Ex2 ?;
Qrepl VVsym v n;
intros;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;Qrepl VVtrans eqV v;Qrepl VVdecide eqV;
Refine Ex2In A1 B1;Refine pair3;Refine Trm_eq_refl;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_lda_character;

Goal {X|Trm}(is_ff (poccur p X))->(is_tt (Trm_eq (lda u A B) (alph X)))->
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (lda u A' B')))
                                 (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))))
                          (is_ff (poccur p B'));
Refine not_pocc_Trec [p:PP][X:Trm]{eq:is_tt (Trm_eq (lda u A B) (alph X))}
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (lda u A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (if (VVeq u v) B' (alph B'))))
                          (is_ff (poccur p B'));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;
Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _______;
Equiv {eq:is_tt (Trm_eq ? (lda n (alph ?) (if (VVeq v n) ? (alph ?))))}
       Ex2 ?;
Qrepl VVsym v n;
intros;Refine Trm_eq_lda_lem eq;
intros eqV eqA eqB;Qrepl VVtrans eqV v;Qrepl VVdecide eqV;
Refine Ex2In A1 B1;Refine pair5;Refine Trm_eq_refl;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
Save alpha_lda_nocc_character;

Goal {X|Trm}(is_tt (Trm_eq (app A B) (alph X)))->
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (app A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (alph B')));
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (app A B) (alph X))}
      Ex2 [A',B':Trm]and3 (is_tt (Trm_eq X (app A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_tt (Trm_eq B (alph B')));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;Refine Ex2In A1 B1;Refine pair3;Refine Trm_eq_refl;Immed;
Save alpha_app_character;

Goal {X|Trm}(is_ff (poccur p X))->(is_tt (Trm_eq (app A B) (alph X)))->
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (app A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (alph B')))
                          (is_ff (poccur p B'));
Refine not_pocc_Trec [p:PP][X:Trm]{eq:is_tt (Trm_eq (app A B) (alph X))}
      Ex2 [A',B':Trm]and5 (is_tt (Trm_eq X (app A' B')))
                          (is_tt (Trm_eq A (alph A')))
                          (is_ff (poccur p A'))
                          (is_tt (Trm_eq B (alph B')))
                          (is_ff (poccur p B'));
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros _;
Equiv {eq:is_tt (Trm_eq ? (if (VVeq v n) ? ?))}Ex2 ?;
Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros case;Qrepl case;intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Refine Trm_eq_app_lem eq;
intros eqA eqB;Refine Ex2In A1 B1;Refine pair5;Refine Trm_eq_refl;Immed;
Save alpha_app_nocc_character;

Discharge s;
