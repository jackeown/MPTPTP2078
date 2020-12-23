%------------------------------------------------------------------------------
% File     : MPT1619+2.026 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 026 of t27_yellow_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   6 unit)
%            Number of atoms       :   24 (   9 equality)
%            Maximal formula depth :    7 (   3 average)
%            Number of connectives :   12 (   0   ~;   0   |;   7   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-2 arity)
%            Number of functors    :   11 (   1 constant; 0-3 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 )).

fof(fc11_funct_2,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v1_funct_1(k6_relat_1(A))
      & v1_partfun1(k6_relat_1(A),A) ) )).

fof(redefinition_k6_partfun1,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) )).

fof(d5_yellow_1,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) )).

fof(fc10_yellow_1,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) )).

fof(fc2_funcop_1,axiom,(
    ! [A] : v1_xboole_0(k2_funcop_1(k1_xboole_0,A)) )).

fof(redefinition_k7_funcop_1,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) )).

fof(t26_yellow_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) )).

fof(t27_yellow_1,conjecture,(
    ! [A] :
      ( l1_orders_2(A)
     => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) )).

%------------------------------------------------------------------------------
