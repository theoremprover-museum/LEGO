Module example Import lib_logic;

[P,Q,R:Prop];

Goal (P->Q->R)->(P->Q)->(P->R);
intros x;
intros y;
intros z;
Prf;
Refine x;
Refine z;
Refine y;
Refine z;

Goal example:(P->Q->R)->(P->Q)->(P->R);
intros x y z;
Refine (x z) (y z);
Save;
