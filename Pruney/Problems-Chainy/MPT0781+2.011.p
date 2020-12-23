%------------------------------------------------------------------------------
% File     : MPT0781+2.011 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 011 of t30_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   24 (  11 unit)
%            Number of atoms       :   42 (  19 equality)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :   18 (   0   ~;   0   |;   4   &)
%                                         (   1 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :   11 (   1 constant; 0-2 arity)
%            Number of variables   :   39 (   2 sgn;  39   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d6_xboole_0,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) )).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) )).

fof(idempotence_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A )).

fof(l98_xboole_1,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) )).

fof(t12_xboole_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) )).

fof(t2_xboole_1,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) )).

fof(t37_xboole_1,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) )).

fof(t3_boole,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A )).

fof(t40_xboole_1,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) )).

fof(t7_xboole_1,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) )).

fof(t95_xboole_1,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) )).

fof(t9_xboole_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) )).

fof(d6_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) )).

fof(fc16_relat_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) )).

fof(t110_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) )).

fof(t111_relat_1,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 )).

fof(t125_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) )).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 )).

fof(t90_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) )).

fof(t97_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) )).

fof(t18_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) )).

fof(t20_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
        & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) )).

fof(t30_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) )).

%------------------------------------------------------------------------------
