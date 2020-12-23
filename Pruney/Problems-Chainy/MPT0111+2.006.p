%------------------------------------------------------------------------------
% File     : MPT0111+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t104_xboole_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   2 unit)
%            Number of atoms       :   12 (   3 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   12 (   5   ~;   1   |;   3   &)
%                                         (   3 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   1 constant; 0-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d8_xboole_0,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) )).

fof(d9_xboole_0,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) )).

fof(t1_boole,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A )).

fof(t7_xboole_1,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) )).

fof(t104_xboole_1,conjecture,(
    ! [A,B] :
      ( ~ ( ~ r2_xboole_0(A,B)
          & A != B
          & ~ r2_xboole_0(B,A) )
    <=> r3_xboole_0(A,B) ) )).

%------------------------------------------------------------------------------
