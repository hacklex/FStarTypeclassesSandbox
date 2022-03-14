module Sandbox.Rings

open Sandbox
open FStar.Tactics.Typeclasses

class ring #a (addition: commutative_group a) (multiplication: monoid a)               
= {   
  eq: (f:(a -> a -> bool){f == addition._group._g_monoid._semigroup._magma._eq.eq /\ 
  f == multiplication._semigroup._magma._eq.eq });
  add: (f:(a -> a -> a){f == addition._group._g_monoid._semigroup._magma.op });
  mul: (f:(a -> a -> a){f == multiplication._semigroup._magma.op});
  neg: (f:(a -> a){f == addition._group.inv});
  one: (u:a{u == multiplication.neutral });
  zero: (z:a{z == addition._group._g_monoid.neutral});  
  left_distributivity: (x:a)->(y:a)->(z:a)-> Lemma (multiplication._semigroup._magma.op x (addition._group._g_monoid._semigroup._magma.op y z) `eq` 
                                           (addition._group._g_monoid._semigroup._magma.op 
                                           (multiplication._semigroup._magma.op x y) 
                                           (multiplication._semigroup._magma.op x z)));
  right_distributivity:(x:a)->(y:a)->(z:a)-> Lemma (multiplication._semigroup._magma.op (addition._group._g_monoid._semigroup._magma.op x y) z `eq` 
                                           (addition._group._g_monoid._semigroup._magma.op 
                                           (multiplication._semigroup._magma.op x z) 
                                           (multiplication._semigroup._magma.op y z)));
}

instance int_equatable : equatable int = { 
  reflexivity = (fun x -> ());
  symmetry = (fun x y -> ());
  transitivity = (fun x y z -> ());
  eq = fun x y -> x=y
}

instance int_add_magma : magma int = {
  _eq = solve;
  congruence = (fun x y z w -> ());
  op = fun x y -> x+y  
}
instance int_mul_magma : magma int = {
  _eq = solve;
  congruence = (fun x y z w -> ());
  op = fun x y -> op_Multiply x y
}

instance int_add_commutative_group : commutative_group int = {
  _cg_commutative_magma = {
    _cm_magma = int_add_magma;
    commutativity = (fun x y -> ())
  };
  _group = {
    _g_monoid = {
     _semigroup = { 
       _magma = int_add_magma; 
       associativity = (fun x y z -> ()) 
     };
     neutral = 0;
     identity = (fun x -> ())     
    };
    inv = (fun x -> (-x));
    inversion = (fun x -> ())  
  }
}

instance int_mul_monoid : monoid int = {
  _semigroup = { 
    _magma = int_mul_magma; 
    associativity = (fun x y z -> ()) 
  };
  neutral = 1;
  identity = (fun x -> ())     
}

instance int_ring : ring int_add_commutative_group int_mul_monoid = {
  eq = int_equatable.eq;
  add = int_add_magma.op;
  mul = int_mul_magma.op;
  neg = int_add_commutative_group._group.inv;
  one = 1;
  zero = 0; 
  left_distributivity = (fun x y z -> ());
  right_distributivity = (fun x y z -> ())
} 

let ring_addition_is_associative #a (#addition_cg: commutative_group a)
                                    (#mul_monoid: monoid a)
                                    (r: ring addition_cg mul_monoid)
                                    (x y z: a)
  : Lemma (r.eq (r.add x (r.add y z)) (r.add (r.add x y) z)) 
  = addition_cg._group._g_monoid._semigroup.associativity x y z
