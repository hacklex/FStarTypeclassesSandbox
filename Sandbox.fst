module Sandbox

class equatable a = {
  eq: a -> a -> bool;
  reflexivity: (t:a) -> Lemma (t `eq` t);
  symmetry: (x:a) -> (y:a) -> Lemma ((x `eq` y) = (y `eq` x));
  transitivity: (x:a) -> (y:a) -> (z:a) -> Lemma (requires eq x y /\ eq y z) (ensures eq x z)
}
 
class magma a = {
  _eq: equatable a;
  op: a -> a -> a;
  congruence: (x:a)-> (y:a)-> (z:a)->(w:a) -> Lemma (requires eq x z /\ eq y w) (ensures eq (op x y) (op z w))
}

instance equatable_of_magma a (h : magma a) : equatable a = h._eq

class semigroup a = { 
  _magma: magma a;
  associativity: (x:a) -> (y:a) -> (z:a) -> Lemma(op x (op y z) `eq` op (op x y) z)
}

instance magma_of_semigroup a (h : semigroup a) : magma a = h._magma 

class monoid a = {
  _semigroup: semigroup a;
  neutral: a;
  identity: (t:a) -> Lemma (ensures op t neutral `eq` t /\
                                        op neutral t `eq` t)
}

class commutative_magma a = {
  _cm_magma : magma a;
  commutativity: (x:a) -> (y:a) -> Lemma (op x y `eq` op y x)
}

instance magma_of_commutative_magma a (h : commutative_magma a)  : magma a = h._cm_magma

class commutative_semigroup a = {
  _cs_semigroup: semigroup a;
  _commutative_magma: commutative_magma a
}

instance semigroup_of_monoid a (h: monoid a) : semigroup a = h._semigroup

class commutative_monoid a = {
  _monoid: monoid a;
  _commutative_semigroup: commutative_semigroup a;
}

class group a = {
  _g_monoid: monoid a;
  inv: a -> a;
  inversion: (x:a) -> Lemma (inv x `op` x `eq` neutral /\ x `op` inv x `eq` neutral)
}

class commutative_group a = {
  _group: group a;
  _cg_commutative_magma: commutative_magma a;
}

instance group_of_commutative_group a (h: commutative_group a) : group a = h._group
instance commutative_magma_of_commutative_group a (h: commutative_group a) : commutative_magma a = h._cg_commutative_magma

