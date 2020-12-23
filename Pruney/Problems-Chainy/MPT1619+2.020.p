%------------------------------------------------------------------------------
% File     : MPT1619+2.020 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 020 of t27_yellow_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   14 (   6 unit)
%            Number of atoms       :   32 (  10 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   22 (   4   ~;   0   |;  12   &)
%                                         (   1 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-2 arity)
%            Number of functors    :   12 (   1 constant; 0-5 arity)
%            Number of variables   :   26 (   0 sgn;  25   !;   1   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t7_xboole_0,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t71_enumset1,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) )).

fof(t72_enumset1,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) )).

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

fof(rc1_yellow_1,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) )).

fof(redefinition_k7_funcop_1,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) )).

fof(t134_pboole,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) )).

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
