%------------------------------------------------------------------------------
% File     : MPT0276+2.013 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 013 of t74_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   2 unit)
%            Number of atoms       :   11 (   9 equality)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   17 (  10   ~;   0   |;   6   &)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t42_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) )).

fof(t74_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
        & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
        & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
        & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) )).

%------------------------------------------------------------------------------
