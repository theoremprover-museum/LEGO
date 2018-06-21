Module notes6 Import lib_bool lib_nat;

[bool_to_nat = bool_rec one zero];
Goal  Eq (bool_to_nat true) one;
Refine Eq_refl;

Goal  (and (Eq zero one) (Eq one two)) -> Eq zero two;
intros H;
Refine Eq_trans;
Refine one;
Refine fst H;
Refine snd H;

Goal  (and (Eq zero one) (Eq two one)) -> Eq zero two;
intros H;
Refine Eq_trans;
Refine one;
Refine fst H;
Refine Eq_sym (snd H);

Goal  (Eq true false) -> Eq one zero;
intros H;
Refine Eq_resp bool_to_nat H;

