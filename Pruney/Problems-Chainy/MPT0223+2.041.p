%------------------------------------------------------------------------------
% File     : MPT0223+2.041 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 041 of t18_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   6 unit)
%            Number of atoms       :   10 (  10 equality)
%            Maximal formula depth :    4 (   3 average)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 1-4 arity)
%            Number of variables   :   17 (   1 sgn;  17   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A )).

fof(t116_xboole_1,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) )).

fof(t16_xboole_1,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) )).

fof(t22_xboole_1,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A )).

fof(t82_enumset1,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) )).

fof(t13_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) )).

fof(t18_zfmisc_1,conjecture,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) )).

%------------------------------------------------------------------------------
