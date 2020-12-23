%------------------------------------------------------------------------------
% File     : MPT0284+2.020 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 020 of t86_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   9 unit)
%            Number of atoms       :   16 (   7 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    4 (   0   ~;   0   |;   1   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   0 constant; 1-4 arity)
%            Number of variables   :   27 (   0 sgn;  27   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(commutativity_k5_xboole_0,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) )).

fof(t100_xboole_1,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) )).

fof(t109_xboole_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) )).

fof(t110_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) )).

fof(t96_xboole_1,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) )).

fof(t98_xboole_1,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t71_enumset1,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) )).

fof(l51_zfmisc_1,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) )).

fof(t79_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) )).

fof(t86_zfmisc_1,conjecture,(
    ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) )).

%------------------------------------------------------------------------------
