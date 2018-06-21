Module alpha Import substitution;

(* a prelude on the alpha operation *)
Goal Trm_eq_alpha_sort_lem:
     {p|PP}{v|VV}{t|SS}{M|Trm}(is_tt (Trm_eq (alpha p v M) (sort t)))->
     is_tt (Trm_eq M (sort t));
intros;
Refine Trec [M:Trm]{eq:is_tt (Trm_eq (alpha p v M) (sort t))}
             is_tt (Trm_eq M (sort t));
Immed;
(* sort *)
intros;Immed;
(* var *)
intros _;Equiv (is_tt (Trm_eq (if ???) ?)) -> is_tt ?;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;intros;Immed;
intros neqV;Qrepl neqV;intros;Immed;
(* par *)
intros;Immed;
(* pi *)
intros;Immed;
(* lda *)
intros;Immed;
(* app *)
intros;Immed;
Save Trm_eq_alpha_sort_lem;

Goal alpha_preserves_lngth:
     {M:Trm}{p:PP}{v:VV}Q (lngth (alpha p v M)) (lngth M);
Refine Trec [M:Trm]{p|PP}{v|VV}Q (lngth (alpha p v M)) (lngth M);
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; 
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl (VVdecide eqV);
Equiv Q (lngth (if (VVeq ? ?) (par ? ) (var ?))) ?; 
Qrepl VVrefl n; Refine Q_refl;
intros neqV; 
Equiv Q (lngth (if (VVeq ? ?) (par ? ) (var ?))) ?; 
Qrepl neqV; Refine Q_refl;
(* par *)
intros; Refine Q_refl;
(* pi *)
intros;
Equiv Q (lngth (pi n (alpha ???) (if ? ? (alpha ???)))) ?;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl (VVdecide eqV);
Qrepl VVrefl n;
Equiv Q (S (add (lngth (alpha ???)) (lngth B)))
        (S (add (lngth A) (lngth B)));
Refine Q_resp_S; Qrepl ihA|p|n; Refine Q_refl;
intros neqV; Qrepl neqV; Expand if;
Equiv Q (S (add (lngth (alpha ???)) (lngth (alpha ???))))
        (S (add (lngth A) (lngth B)));
Qrepl ihA|p|v; Qrepl ihB|p|v; Refine Q_refl;
(* lda *)
intros;
Equiv Q (lngth (lda n (alpha ???) (if ? ? (alpha ???)))) ?;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl (VVdecide eqV);
Qrepl VVrefl n;
Equiv Q (S (add (lngth (alpha ???)) (lngth B)))
        (S (add (lngth A) (lngth B)));
Refine Q_resp_S; Qrepl ihA|p|n; Refine Q_refl;
intros neqV; Qrepl neqV; Expand if;
Equiv Q (S (add (lngth (alpha ???)) (lngth (alpha ???))))
        (S (add (lngth A) (lngth B)));
Qrepl ihA|p|v; Qrepl ihB|p|v; Refine Q_refl;
(* app *)
intros;
Equiv Q (S (add (lngth (alpha ???)) (lngth (alpha ???))))
        (S (add (lngth ?) (lngth ?)));
Qrepl ihA|p|v; Qrepl ihB|p|v; Refine Q_refl;
Save alpha_preserves_lngth;

[u,v|VV][neqVV:is_ff (VVeq u v)][p,q:PP];
$[a_pu = alpha p u];
$[a_qv = alpha q v];

Goal alpha_commutes_alpha:
     {M:Trm}is_tt (Trm_eq (a_pu (a_qv M)) (a_qv (a_pu M)));
Refine Trec [M|Trm]is_tt (Trm_eq (a_pu (a_qv M)) (a_qv (a_pu M)));
intros;Refine Trm_eq_refl;

intros;Equiv is_tt (Trm_eq (a_pu (if ???)) (a_qv (if ???)));
Qrepl VVsym u n;Qrepl VVsym v n;Refine tt_or_ff (VVeq n u);
intros case_u;Qrepl case_u;Qrepl VVtrans case_u v;Qrepl neqVV;
              Equiv is_tt (Trm_eq (if ???) (par p));Qrepl VVsym u n;Qrepl case_u;
              Refine Trm_eq_refl;
intros case_u;Qrepl case_u;Equiv is_tt (Trm_eq ? (if ???));
              Qrepl VVsym v n;Refine tt_or_ff (VVeq n v);
intros case_v;Qrepl case_v;Refine Trm_eq_refl;
intros case_v;Qrepl case_v;Equiv is_tt (Trm_eq (if ???) ?);
              Qrepl VVsym u n;Qrepl case_u;Refine Trm_eq_refl;

intros;Refine Trm_eq_refl;

intros;Equiv is_tt (Trm_eq (pi n (a_pu (a_qv ?))
                     (if ? (if ? ? (a_qv ?)) (a_pu (if ? ? (a_qv ?))))) 
               (pi n (a_qv (a_pu ?))
                     (if ? (if ? ? (a_pu ?)) (a_qv (if ? ? (a_pu ?))))));
       Qrepl if_inside a_qv B (a_pu B) (VVeq u n);
       Qrepl if_inside a_pu B (a_qv B) (VVeq v n);
       Qrepl middle_four_if B (a_qv B) (a_pu B) (a_pu (a_qv B)) (VVeq u n)
                                                                (VVeq v n);
       Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;

intros;Equiv is_tt (Trm_eq (lda n (a_pu (a_qv ?))
                      (if ? (if ? ? (a_qv ?)) (a_pu (if ? ? (a_qv ?))))) 
               (lda n (a_qv (a_pu ?))
                      (if ? (if ? ? (a_pu ?)) (a_qv (if ? ? (a_pu ?))))));
       Qrepl if_inside a_qv B (a_pu B) (VVeq u n);
       Qrepl if_inside a_pu B (a_qv B) (VVeq v n);
       Qrepl middle_four_if B (a_qv B) (a_pu B) (a_pu (a_qv B)) (VVeq u n)
                                                                (VVeq v n);
       Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
              
intros;Equiv is_tt (Trm_eq (app (a_pu (a_qv ?)) (a_pu (a_qv ?))) 
                           (app (a_qv (a_pu ?)) (a_qv (a_pu ?))));
       Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
Save alpha_commutes_alpha;
Discharge u;


[v:VV][q|PP][M,M'|Trm][noccM:is_ff (poccur q M)][noccM':is_ff (poccur q M')];

Goal alpha_inverse_lem: is_tt (Trm_eq (alpha' v q (alpha q v M)) M);
[a = alpha q v][a'= alpha' v q];
Refine not_pocc_Trec [q|PP][M|Trm]is_tt (Trm_eq (a' (a M)) M);
Refine +7 noccM;
(* sort *)
intros;Refine Trm_eq_refl;
(* var *)
intros;Equiv is_tt (Trm_eq (a' (if ???)) ?);
Qrepl if_inside a' (par q) (var n) (VVeq v n);
Equiv is_tt (Trm_eq (if ? (if ???) (var n)) ?);Qrepl PPrefl q;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Qrepl VVdecide eqV;Refine Trm_eq_refl;
intros neqV;Qrepl neqV;Refine Trm_eq_refl;
(* par *)
intros;Equiv is_tt (Trm_eq (if ???) ?);Qrepl noccP;Refine Trm_eq_refl;
(* pi *)
intros;
Equiv is_tt (Trm_eq (pi n (a' (a A)) (a' (if (VVeq v n) B (a B))))
                    (pi n A B));
Qrepl if_inside a' B (a B) (VVeq v n);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB (var v));
Qrepl Trm_eq_subst ihA;
Qrepl Trm_eq_subst ihB;
Qrepl triv_if (VVeq v n) B;
Refine Trm_eq_refl;
(* lda *)
intros;
Equiv is_tt (Trm_eq (lda n (a' (a A)) (a' (if (VVeq v n) B (a B))))
                    (lda n A B));
Qrepl if_inside a' B (a B) (VVeq v n);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB (var v));
Qrepl Trm_eq_subst ihA;
Qrepl Trm_eq_subst ihB;
Qrepl triv_if (VVeq v n) B;
Refine Trm_eq_refl;
(* app *)
intros;
Equiv is_tt (Trm_eq (app (a' (a A)) (a' (a B))) (app A B));
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;
Refine Trm_eq_refl;

Save alpha_inverse_lem;
DischargeKeep q;

Goal {eq:is_tt (Trm_eq (alpha q v M) (alpha q v M'))}is_tt (Trm_eq M M');
intros;
Qrepl Q_sym (Trm_eq_subst (alpha_inverse_lem noccM));
Qrepl Q_sym (Trm_eq_subst (alpha_inverse_lem noccM'));
Qrepl Trm_eq_subst eq;Refine Trm_eq_refl;
Save alpha_injective;

Discharge v;


Goal {u:VV}{p,q:PP}[a_pu=alpha p u][a_qu=alpha q u]
     {M:Trm}is_tt (Trm_eq (a_pu (a_qu M)) (a_qu M));
intros;Refine Trec [M:Trm]is_tt (Trm_eq (a_pu (a_qu M)) (a_qu M));
(* sort *)
intros;Refine Trm_eq_refl;
(* var *)
intros;Equiv is_tt (Trm_eq (a_pu (if ???)) (if ???));
Qrepl if_inside a_pu (par q) (var n) (VVeq u n);
Equiv is_tt (Trm_eq (if ? (par ?) (if ???)) (if ???));
Qrepl reduce_if_right (par q) (par p) (var n) (VVeq u n);
Refine Trm_eq_refl;
(* par *)
intros;Refine Trm_eq_refl;
(* pi *)
intros;
Equiv is_tt (Trm_eq (pi n (a_pu (a_qu ?))
                     (if ? (if ? ? (a_qu ?)) (a_pu (if ? ? (a_qu ?))))) 
                    (pi n (a_qu ?) (if ? ? (a_qu ?))));
Qrepl if_inside a_pu B (a_qu B) (VVeq u n);
Qrepl reduce_if_left B (a_qu B) (if (VVeq u n) (a_pu B) (a_pu (a_qu B)))
                                (VVeq u n);
Qrepl reduce_if_right B (a_pu B) (a_pu (a_qu B)) (VVeq u n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* lda *)
intros;
Equiv is_tt (Trm_eq (lda n (a_pu (a_qu ?))
                     (if ? (if ? ? (a_qu ?)) (a_pu (if ? ? (a_qu ?)))))
                    (lda n (a_qu ?) (if ? ? (a_qu ?))));
Qrepl if_inside a_pu B (a_qu B) (VVeq u n);
Qrepl reduce_if_left B (a_qu B) (if (VVeq u n) (a_pu B) (a_pu (a_qu B)))
                                (VVeq u n);
Qrepl reduce_if_right B (a_pu B) (a_pu (a_qu B)) (VVeq u n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* app *)
intros;Equiv is_tt (Trm_eq (app (a_pu (a_qu ?)) (a_pu (a_qu ?)))
                           (app (a_qu ?) (a_qu ?)));
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;
Refine Trm_eq_refl;
Save alpha_idempotent_lem;


Goal {u,v|VV}(is_tt (VVeq u v))->
     {p,q:PP}[a_pu=alpha p u][a_qv=alpha q v]
     {M:Trm}is_tt (Trm_eq (a_pu (a_qv M)) (a_qv M));
intros __ eqV _____;Expand a_pu a_qv;
Qrepl VVdecide eqV;
Qrepl Trm_eq_subst (alpha_idempotent_lem v p q M);
Refine Trm_eq_refl;
Save alpha_idempotent;
