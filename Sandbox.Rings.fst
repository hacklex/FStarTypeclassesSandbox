module Sandbox.Rings

open Sandbox
open FStar.Tactics.Typeclasses

type left_distributivity_lemma #a (eq: binary_relation a) (mul: binary_op a) (add: binary_op a) =
  (x:a) -> (y:a) -> (z:a) -> Lemma (mul x (add y z) `eq` add (mul x y) (mul x z))
type right_distributivity_lemma #a (eq: binary_relation a) (mul: binary_op a) (add: binary_op a) =
  (x:a) -> (y:a) -> (z:a) -> Lemma (mul (add x y) z `eq` add (mul x z) (mul y z))

class ring #a (addition: commutative_group a) (multiplication: monoid a) = 
{   
  eq: (f:binary_relation a{f == addition._group._g_monoid._semigroup._magma._eq.eq /\ 
                           f == multiplication._semigroup._magma._eq.eq });
  add: (f:binary_op a{f == addition._group._g_monoid._semigroup._magma.op });
  mul: (f:binary_op a{f == multiplication._semigroup._magma.op});
  neg: (f:unary_op a{f == addition._group.inv});
  zero: (z:a{z == addition._group._g_monoid.neutral});  
  one: (u:a{u == multiplication.neutral });
  left_distributivity: left_distributivity_lemma eq mul add;
  right_distributivity: right_distributivity_lemma eq mul add
}

let make_ring #a
  (eq: binary_relation a)
  (add: binary_op a)
  (mul: binary_op a)
  (neg: unary_op a)
  (zero: a)
  (one: a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (add_congruence: congruence_lemma eq add) 
  (add_associativity: associativity_lemma eq add)
  (add_commutativity: commutativity_lemma eq add)
  (add_identity: identity_lemma eq add zero)
  (add_inversion: inversion_lemma eq add neg zero)
  (mul_congruence: congruence_lemma eq mul) 
  (mul_associativity: associativity_lemma eq mul)
  (mul_identity: identity_lemma eq mul one)
  (left_distributivity: left_distributivity_lemma eq mul add)
  (right_distributivity: right_distributivity_lemma eq mul add)
   : ring (make_commutative_group a eq add neg zero reflexivity symmetry transitivity
                                  add_congruence add_associativity add_commutativity 
                                  add_identity add_inversion)
          (make_monoid a eq mul one reflexivity symmetry transitivity
                       mul_congruence mul_associativity mul_identity)
    = 
  Mkring eq add mul neg zero one left_distributivity right_distributivity 

let make_ring_from_add_and_mul #a
  (addition: commutative_group a)
  (multiplication: (m:monoid a{ m._semigroup._magma._eq ==
                             addition._cg_commutative_magma._cm_magma._eq }))                             
  (left_distributivity: left_distributivity_lemma 
                          addition._cg_commutative_magma._cm_magma._eq.eq
                          multiplication._semigroup._magma.op
                          addition._cg_commutative_magma._cm_magma.op)                         
  (right_distributivity: right_distributivity_lemma 
                          addition._cg_commutative_magma._cm_magma._eq.eq
                          multiplication._semigroup._magma.op
                          addition._cg_commutative_magma._cm_magma.op)
  : ring addition multiplication =    
  Mkring multiplication._semigroup._magma._eq.eq
         addition._cg_commutative_magma._cm_magma.op
         multiplication._semigroup._magma.op
         addition._group.inv
         addition._group._g_monoid.neutral
         multiplication.neutral
         left_distributivity
         right_distributivity
         
let int_ring = make_ring #int
  (=)
  (+)
  op_Multiply
  op_Minus
  0
  1
  (fun _ -> ())         // eq reflexivity
  (fun _ _ -> ())       // eq symmetry
  (fun _ _ _ -> ())     // eq transitivity
  (fun _ _ _ _ -> ())   // + congruence
  (fun _ _ _ -> ())     // + associativity
  (fun _ _ -> ())       // + commutativity
  (fun _ -> ())         // + identity
  (fun _ -> ())         // + inversion
  (fun _ _ _ _ -> ())   // * congruence
  (fun _ _ _ -> ())     // * associativity
  (fun _  -> ())        // * identity
  (fun _ _ _ -> ())     // *+ left distributivity
  (fun _ _ _ -> ())     // *+ right distributivity

let equality_reflexivity #a (#addition_cg: commutative_group a)
                            (#mul_monoid: monoid a)
                            (r: ring addition_cg mul_monoid)
                            (x: a)
  : Lemma (r.eq x x) [SMTPat(r.eq x)] = reflexivity x
  
let equality_symmetry #a (#addition_cg: commutative_group a)
                         (#mul_monoid: monoid a)
                         (r: ring addition_cg mul_monoid)
                         (x y: a)
  : Lemma (r.eq x y == r.eq y x) [SMTPat(x `r.eq` y)] = symmetry x y
  
let equality_transitivity #a (#addition_cg: commutative_group a)
                         (#mul_monoid: monoid a)
                         (r: ring addition_cg mul_monoid)
                         (x y z: a)
  : Lemma (r.eq x y /\ r.eq y z ==> r.eq x z) 
  = Classical.move_requires_3 transitivity x y z
  
let equality_transitivity_pat #a (#addition_cg: commutative_group a)
                         (#mul_monoid: monoid a)
                         (r: ring addition_cg mul_monoid)
  : Lemma (forall (x y z:a). r.eq x y /\ r.eq y z ==> r.eq x z) [SMTPat(r.eq)]
  = Classical.forall_intro_3 (equality_transitivity r)

let addition_associativity #a (#addition_cg: commutative_group a)
                              (#mul_monoid: monoid a)
                              (r: ring addition_cg mul_monoid)
                              (x y z: a)
  : Lemma (r.eq (r.add x (r.add y z)) (r.add (r.add x y) z)) 
  = addition_cg._group._g_monoid._semigroup.associativity x y z
  
let multiplication_associativity #a (#addition_cg: commutative_group a)
                                    (#mul_monoid: monoid a)
                                    (r: ring addition_cg mul_monoid)
                                    (x y z: a)
  : Lemma (r.eq (r.mul x (r.mul y z)) (r.mul (r.mul x y) z)) 
  = associativity x y z

let addition_commutativity #a (#addition_cg: commutative_group a)
                           (#mul_monoid: monoid a)
                           (r: ring addition_cg mul_monoid)
                           (x y: a) : Lemma (r.eq (r.add x y) (r.add y x)) 
  = addition_cg._cg_commutative_magma.commutativity x y

let addition_inversion #a (#addition_cg: commutative_group a)
                          (#mul_monoid: monoid a)
                          (r: ring addition_cg mul_monoid)
                          (x: a) : Lemma (r.eq (r.add x (r.neg x)) r.zero /\ 
                                          r.eq (r.add x (r.neg x)) r.zero) 
                                   [SMTPat(r.neg x)]
  = addition_cg._group.inversion x

let addition_identity #a (#addition_cg: commutative_group a)
                         (#mul_monoid: monoid a)
                         (r: ring addition_cg mul_monoid)
                         (x: a) 
  : Lemma (r.eq (r.add x r.zero) x /\ r.eq (r.add r.zero x) x) 
    [SMTPatOr [
      [SMTPat(r.add x r.zero)]; 
      [SMTPat(r.add r.zero x)]]
    ] = addition_cg._group._g_monoid.identity x
    
let multiplication_identity #a (#addition_cg: commutative_group a)
                         (#mul_monoid: monoid a)
                         (r: ring addition_cg mul_monoid)
                         (x: a) 
  : Lemma (r.eq (r.mul x r.one) x /\ r.eq (r.mul r.one x) x) 
    [SMTPatOr [
      [SMTPat(r.mul x r.one)]; 
      [SMTPat(r.mul r.one x)]]
    ] = identity x
                         
let ring_zero_is_addition_neutral (#a) (#addition_cg: commutative_group a)
                                       (#mul_monoid: monoid a)
                                       (r: ring addition_cg mul_monoid)
                                       (x: a{x `r.eq` r.zero}) (y:a) 
  : Lemma (r.add x y `r.eq` y /\ r.add y x `r.eq` y) 
  = congruence x y r.zero y;
    congruence y x y r.zero

let ring_zero_eq_minus_zero (#a) (#addition_cg: commutative_group a)
                                 (#mul_monoid: monoid a)
                                 (r: ring addition_cg mul_monoid)
  : Lemma (r.eq r.zero (r.neg r.zero)) = 
  ring_zero_is_addition_neutral r r.zero (r.neg r.zero);
  addition_cg._group.inversion (r.zero)

open FStar.Tactics

let ring_laws #a (#addition: commutative_group a) (#multiplication: monoid a) (r: ring addition multiplication) 
  : Tac unit = 
  let _eq = addition._cg_commutative_magma._cm_magma._eq in
  Classical.forall_intro _eq.reflexivity;
  Classical.forall_intro_2 (Classical.move_requires_2 _eq.symmetry);
  Classical.forall_intro_3 (Classical.move_requires_3 _eq.transitivity);
  assert (r.eq ==  _eq.eq);
  let mul_congruence_impl (x y z w:a) : Lemma (_eq.eq x z /\ _eq.eq y w ==> 
                                               _eq.eq (x `r.mul` y) (z `r.mul` w))
                                    = if (_eq.eq x z && _eq.eq y w) then
                                      multiplication._semigroup._magma.congruence x y z w in
  let add_congruence_impl (x y z w:a) : Lemma (_eq.eq x z /\ _eq.eq y w ==> 
                                               _eq.eq (x `r.add` y) (z `r.add` w))
                                    = if (_eq.eq x z && _eq.eq y w) then
                                      addition._cg_commutative_magma._cm_magma.congruence x y z w in
  Classical.forall_intro_3 (Classical.move_requires_3 _eq.transitivity);
  Classical.forall_intro_4 mul_congruence_impl;   
  Classical.forall_intro_4 add_congruence_impl;   
  Classical.forall_intro_3 r.left_distributivity;
  Classical.forall_intro_3 r.right_distributivity;
  Classical.forall_intro_3 r.right_distributivity;
  Classical.forall_intro addition._group.inversion;
  Classical.forall_intro addition._group._g_monoid.identity;
  Classical.forall_intro_2 addition._cg_commutative_magma.commutativity;
  Classical.forall_intro_3 addition._group._g_monoid._semigroup.associativity;
  Classical.forall_intro multiplication.identity;
  Classical.forall_intro_3 multiplication._semigroup.associativity;
  Classical.forall_intro_2 (ring_zero_is_addition_neutral r);
()
  
#push-options "--z3rlimit 50"
let ring_zero_is_mul_absorber (#a) (#addition_cg: commutative_group a)
                                   (#mul_monoid: monoid a)
                                   (r: ring addition_cg mul_monoid)
                                   (z: a{r.eq z r.zero}) (x:a)
  : Lemma (r.mul z x `r.eq` z /\ r.mul x z `r.eq` z) =
  let trans_lemma = equality_transitivity r in
  let mul = r.mul in
  let add = r.add in
  let one = r.one in
  let neg = r.neg in
  let eq = r.eq in
  let congruence = addition_cg._cg_commutative_magma._cm_magma.congruence in
  let mul_congruence = mul_monoid._semigroup._magma.congruence in
  let substitution (x:a) : Lemma (mul x z `eq` mul x r.zero /\
                                  mul z x `eq` mul r.zero x /\
                                  add x z `eq` add x r.zero /\
                                  add z x `eq` add r.zero x)
  = mul_congruence x z x r.zero;
    mul_congruence z x r.zero x;
    congruence z x r.zero x;
    congruence x z x r.zero in  

  assert (x `add` neg x `eq` z) ; 

  Classical.forall_intro_2 (ring_zero_is_addition_neutral r);
  mul_congruence x (r.add r.zero r.one) x r.one;
  r.left_distributivity x z one;
  assert (add z one `eq` one);
  mul_congruence x (add z one) x one;
  assert (mul x (add z one) `eq` mul x one);
  assert (x `eq` (mul x z `add` mul x one));
  multiplication_identity r x;
  congruence (mul x z) (mul x one) (mul x z) x;
  assert (add x z `eq` x);
  assert (x `eq` (mul x z `add` x));
  congruence x (neg x) (mul x z `add` x) (neg x);
  assert (x `add` neg x `eq` z);
  addition_associativity r (mul x z) x (neg x);
  assert (((mul x z `add` x) `add` neg x) `eq` (mul x z `add` (x `add` neg x)));  
  assert (((mul x z `add` x) `add` neg x) `eq` (mul x z `add` z));
  assert (((mul x z `add` x) `add` neg x) `eq` (mul x z));
  assert (z `eq` (mul x z)); 
  //now for zx=z  
  r.right_distributivity z z x;
  mul_congruence z x (add z z) x;
  addition_associativity r (mul z x) (mul z x) (neg (mul z x));
  let zx = mul z x in
  congruence (add zx zx) (neg (mul z x)) zx (neg zx); 
  congruence zx (zx `add` neg zx) zx (neg zx);
  assert ((zx `add` (zx `add` neg zx)) `eq` (zx `add` neg zx));
  assert ((zx `add` (zx `add` neg zx)) `eq` z);
  assert ((zx `add` z) `eq` z);
  assert (zx `eq` z);
  ()



