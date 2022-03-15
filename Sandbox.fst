module Sandbox

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

type associativity_lemma #a (eq: binary_relation a) (op: binary_op a)
  = (x:a) -> (y:a) -> (z:a) -> Lemma(op x (op y z) `eq` op (op x y) z)
  
type commutativity_lemma #a (eq: binary_relation a) (op: binary_op a)
  = (x:a) -> (y:a) -> Lemma (op x y `eq` op y x)

type identity_lemma #a (eq: binary_relation a) (op: binary_op a) (neutral:a) 
  = (t:a) -> Lemma (ensures op t neutral `eq` t /\ op neutral t `eq` t)

type inversion_lemma #a (eq: binary_relation a) (op: binary_op a) (inv: unary_op a) (neutral: a)
  = (x:a) -> Lemma (inv x `op` x `eq` neutral /\ x `op` inv x `eq` neutral)

class equatable a = {
  eq: binary_relation a;
  reflexivity: reflexivity_lemma eq;
  symmetry: symmetry_lemma eq;
  transitivity: transitivity_lemma eq
}

class magma a = {
  _eq: equatable a;
  op: binary_op a;
  congruence: congruence_lemma _eq.eq op
}

let make_magma a 
  (eq: binary_relation a)
  (op: binary_op a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  = Mkmagma (Mkequatable eq reflexivity symmetry transitivity) op congruence
  
instance equatable_of_magma a (h : magma a) : equatable a = h._eq

instance eq_of_magma a (h: magma a) : binary_relation a = h._eq.eq

class semigroup a = { 
  _magma: magma a;
  associativity: associativity_lemma #a eq op
}
 
let make_semigroup a
  (eq: binary_relation a)
  (op: binary_op a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  = Mksemigroup (Mkmagma (Mkequatable eq reflexivity symmetry transitivity) op congruence) associativity

instance magma_of_semigroup a (h : semigroup a) : magma a = h._magma 

class monoid a = {
  _semigroup: semigroup a;
  neutral: a;
  identity: identity_lemma eq op neutral
}


let make_monoid a 
  (eq: binary_relation a)
  (op: binary_op a)
  (neutral: a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  (identity: identity_lemma eq op neutral) = 
  let equ = Mkequatable eq reflexivity symmetry transitivity in
  let mag = Mkmagma equ op congruence in
  let semi = Mksemigroup mag associativity in
  Mkmonoid semi neutral identity

class commutative_magma a = {
  _cm_magma : magma a;
  commutativity: commutativity_lemma #a eq op
}

let make_commutative_magma a
  (eq: binary_relation a)
  (op: binary_op a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (commutativity: commutativity_lemma eq op)
  = Mkcommutative_magma (make_magma a eq op reflexivity symmetry transitivity congruence) 
                        commutativity

instance magma_of_commutative_magma a (h : commutative_magma a)  : magma a = h._cm_magma

class commutative_semigroup a = {
  _cs_semigroup: semigroup a;
  _commutative_magma: (cm:commutative_magma a { cm._cm_magma == _cs_semigroup._magma })
}

let commutative_semigroup_has_one_magma a (cg: commutative_semigroup a) 
  : Lemma (cg._commutative_magma._cm_magma == cg._cs_semigroup._magma) 
    [SMTPat(a, cg)] = ()

let make_commutative_semigroup a 
  (eq: binary_relation a)
  (op: binary_op a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  (commutativity: commutativity_lemma eq op) =
  Mkcommutative_semigroup (make_semigroup a eq op reflexivity symmetry transitivity congruence associativity)
                          (make_commutative_magma a eq op reflexivity symmetry transitivity congruence commutativity)

instance semigroup_of_monoid a (h: monoid a) : semigroup a = h._semigroup

class commutative_monoid a = {
  _monoid: monoid a;
  _cmon_magma: (cm:commutative_magma a { cm._cm_magma == _monoid._semigroup._magma });
}

let commutative_monoid_has_one_magma a (cg: commutative_monoid a) 
  : Lemma (cg._cmon_magma._cm_magma == cg._monoid._semigroup._magma) 
    [SMTPat(a, cg)] = ()

let make_commutative_monoid a
  (eq: binary_relation a)
  (op: binary_op a)
  (neutral: a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  (commutativity: commutativity_lemma eq op)
  (identity: identity_lemma eq op neutral) =
  Mkcommutative_monoid (make_monoid a eq op neutral reflexivity symmetry transitivity congruence associativity identity)
                       (make_commutative_magma a eq op reflexivity symmetry transitivity congruence commutativity)
                       

class group a = {
  _g_monoid: monoid a;
  inv: unary_op a;
  inversion: inversion_lemma eq op inv neutral
}

let make_group a
  (eq: binary_relation a)
  (op: binary_op a)
  (inv: unary_op a)
  (neutral: a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  (identity: identity_lemma eq op neutral) 
  (inversion: inversion_lemma eq op inv neutral) =
  Mkgroup (make_monoid a eq op neutral reflexivity symmetry transitivity congruence associativity identity) inv inversion

class commutative_group a = {
  _group: group a;
  _cg_commutative_magma: (cm:commutative_magma a { cm._cm_magma == _group._g_monoid._semigroup._magma });
}

let commutative_group_has_one_magma a (cg: commutative_group a) : Lemma (
  cg._cg_commutative_magma._cm_magma == cg._group._g_monoid._semigroup._magma
 ) [SMTPat(a, cg)] = ()

let make_commutative_group a 
  (eq: binary_relation a)
  (op: binary_op a)
  (inv: unary_op a)
  (neutral: a)
  (reflexivity: reflexivity_lemma eq)
  (symmetry: symmetry_lemma eq)
  (transitivity: transitivity_lemma eq)
  (congruence: congruence_lemma eq op) 
  (associativity: associativity_lemma eq op)
  (commutativity: commutativity_lemma eq op)
  (identity: identity_lemma eq op neutral)
  (inversion: inversion_lemma eq op inv neutral) =
  Mkcommutative_group (make_group a eq op inv neutral reflexivity symmetry transitivity congruence associativity identity inversion)
                      (make_commutative_magma a eq op reflexivity symmetry transitivity congruence commutativity)

instance identity_of_commutative_group a (h:commutative_group a) : identity_lemma h._cg_commutative_magma._cm_magma._eq.eq h._cg_commutative_magma._cm_magma.op h._group._g_monoid.neutral =
  h._group._g_monoid.identity
  
instance group_of_commutative_group a (h: commutative_group a) : group a = h._group
instance commutative_magma_of_commutative_group a (h: commutative_group a) : commutative_magma a = h._cg_commutative_magma

