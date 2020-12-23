%------------------------------------------------------------------------------
% File     : MPT0318+2.060 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 060 of t130_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   2 unit)
%            Number of atoms       :   17 (  15 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   19 (   9   ~;   1   |;   4   &)
%                                         (   3 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   1 constant; 0-2 arity)
%            Number of variables   :   14 (   0 sgn;  14   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t4_boole,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t113_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) )).

fof(t20_zfmisc_1,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) )).

fof(t27_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => k2_tarski(A,B) = k1_tarski(C) ) )).

fof(t42_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) )).

fof(t130_zfmisc_1,conjecture,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) )).

%------------------------------------------------------------------------------
