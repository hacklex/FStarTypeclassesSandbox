module Sandbox

open FStar.Tactics
open FStar.Tactics.Typeclasses

type binary_relation a = a -> a -> bool

type binary_op a = a -> a -> a

type unary_op a = a -> a

type reflexivity_lemma #a (eq: binary_relation a)
  = (t:a) -> Lemma (t `eq` t)

type symmetry_lemma #a (eq: binary_relation a) 
  = (x:a) -> (y:a) -> Lemma ((x `eq` y) = (y `eq` x))

type transitivity_lemma #a (eq: binary_relation a) 
  = (x:a) -> (y:a) -> (z:a) -> Lemma (requires eq x y /\ eq y z) (ensures eq x z)

type congruence_lemma #a (eq: binary_relation a) (op: binary_op a)
  = (x:a)->(y:a)->(z:a)->(w:a) -> Lemma (requires eq x z /\ eq y w) (ensures eq (op x y) (op z w))

class equatable a = {
  eq : binary_relation a;
  reflexivity: reflexivity_lemma eq;
  symmetry: symmetry_lemma eq;
  transitivity: transitivity_lemma eq
}

noeq type some_weird_type = {
  wtf: string;
  func: int -> int -> int
}

instance si : equatable some_weird_type = {
  reflexivity = (fun x -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
  eq = fun x y -> x.wtf = y.wtf
}

instance int_eq : equatable int = {
  reflexivity = (fun x -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
  eq = op_Equality  
}

instance (=) #c {|equatable c|} : binary_relation c = eq

instance (<>) #c {|equatable c|} : binary_relation c = fun x y ->  not (x `eq` y)

let cmp (x y: int) : bool = x=y

let compare (x y: some_weird_type) : bool = x = y

class has_mul a = {
  _mul_eq: equatable a;
  mul: binary_op a;
  mul_congruence: congruence_lemma #a _mul_eq.eq mul
}

instance equatable_of_has_mul #a (z:has_mul a) = z._mul_eq

instance ( * ) #c {| has_mul c |} : binary_op c = mul

instance int_mul : has_mul int = { 
  _mul_eq = int_eq; 
  mul = op_Multiply;  
  mul_congruence = fun _ _ _ _ -> ()
}

(* Make sure we don't break anything int-related 
   Notice how we haven't declared commutativity for int yet. *)
let test_int_lemma (x: int) (y: int) = assert (x*y = y*x) 

class mul_semigroup c = {
  _mul_sg_hm: has_mul c;
  mul_associativity : (x:c) -> (y:c) -> (z:c) -> Lemma (x*(y*z) = (x*y)*z)
}

class mul_commutative c = {
  _mul_com_hm : has_mul c;
  mul_commutativity: (x:c) -> (y:c) -> Lemma (x*y = y*x)
}

class mul_commutative_semigroup c = 
{
  _mul_csg_hm : has_mul c; //are the following conditions redundant?
  _mul_csg_comm: (com: mul_commutative c { com._mul_com_hm == _mul_csg_hm });
  _mul_csg_sg: (sg:mul_semigroup c { sg._mul_sg_hm == _mul_csg_hm })
}

instance has_mul_of_semigroup #a (sg: mul_semigroup a) = sg._mul_sg_hm

class mul_with_zero a = {
  _mul_z_hm: has_mul a;
  absorber: a;
  annihilation: (x:a) -> Lemma (absorber*x = absorber /\ x*absorber = absorber)  
}

instance has_mul_of_hm_with_zero #a (z:mul_with_zero a) = z._mul_z_hm

class mul_monoid a = {
  _mul_mon_sg: mul_semigroup a;
  one: a;
  identity : (x:a) -> Lemma (one*x = x /\ x*one = x)
}

instance mul_semigroup_of_monoid #a (mm: mul_monoid a) = mm._mul_mon_sg

class mul_comm_monoid a = {
  _mm : mul_monoid a;
  _comm: mul_commutative a 
}

type nonzero_of a {|mwz: mul_with_zero a|} = (x:a{x<>mwz.absorber})

class mul_monoid_with_zero a = {
  _mul_monz_eq : equatable a;
  _mul_monz_mm : mul_monoid a; 
  _mul_monz_z : mul_with_zero a 
}

instance mwz #a (z : mul_monoid_with_zero a) = z._mul_monz_z

instance mm_of_z #a (mz: mul_monoid_with_zero a) = mz._mul_monz_mm

class mul_group a = {
  _mul_g_mz: mul_monoid_with_zero a;
  inv: nonzero_of a #_mul_g_mz._mul_monz_z -> nonzero_of a;
  inversion: (x: nonzero_of a) -> Lemma (((inv x * x) <: a) = one /\ ((x * inv x) <: a) = one)
}

let has_mul_of_group #a (g: mul_group a) : has_mul a = g._mul_g_mz._mul_monz_z._mul_z_hm

class mul_commutative_group a = {
  _mul_cg_g: mul_group a;
  _mul_cg_com : (cm:mul_commutative a { has_mul_of_group _mul_cg_g == cm._mul_com_hm })
}

class has_add a = {
  _add_eq : equatable a;
  add : binary_op a;
  add_congruence : (x:a)->(y:a)->(z:a)->(w:a) -> Lemma(requires x = z /\ y = w) (ensures add x y = add z w);
  add_commutativity : (x:a)->(y:a)-> Lemma (add x y = add y x)
}

instance equatable_of_has_add #a (z:has_add a) = z._add_eq

instance ( + ) #c {| has_add c |} : binary_op c = add

instance int_add : has_add int = { 
  _add_eq = int_eq; 
  add = op_Addition;    
  add_commutativity = (fun _ _ -> ());
  add_congruence = fun a b c d -> ()
}

let just_in_case (x y z: int) : Lemma ((x+y)*z = x*z + y*z) = () // we broke nothing for ints 

class add_semigroup a = {
  _add_sg_ha : has_add a;
  associativity : (x:a)->(y:a)->(z:a)->Lemma (x+(y+z)=(x+y)+z) //operations resolved successfully
}

instance has_add_of_add_sg a (sg: add_semigroup a) = sg._add_sg_ha

class add_monoid a = {
  _add_mon_sg: add_semigroup a;
  zero: a;
  add_identity: (x:a) -> Lemma (zero+x=x /\ x+zero=x)
}

instance sg_of_add_m a (m: add_monoid a) = m._add_mon_sg

class add_group a = {
  _add_g_mon: add_monoid a;
  neg: unary_op a;
  negation: (x:a) -> Lemma (x + neg x = zero /\ neg x + x = zero)
}

instance m_of_add_g a (g: add_group a) = g._add_g_mon

class ring a = {
  _ring_add_g : add_group a;
  _ring_mul_m : mul_monoid a;
  //We need to be sure that (=) is the same between has_add and has_mul
  //I don't know how to achieve that. 
  //Currently I strive to reduce redundance. 
  left_distributivity : (x:a)->(y:a)->(z:a)->Lemma (x*(y+z) = x*y + x*z);
  right_distributivity : (x:a)->(y:a)->(z:a)->Lemma ((x+y)*z = x*z + x*z)
  //addition zero = multiplication absorber is a theorem here  
}

instance add_of_ring a (r: ring a) = r._ring_add_g
instance mul_of_ring a (r: ring a) = r._ring_mul_m

class domain a = {
  _domain_r : ring a;
  domain_law : (x:a) -> (y:a) -> Lemma (((x*y)=zero) <==> ((x=zero) \/ (y=zero)))
}
