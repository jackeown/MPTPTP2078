%------------------------------------------------------------------------------
% File     : MPT0099+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t92_xboole_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   3 unit)
%            Number of atoms       :   11 (   5 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :    8 (   2   ~;   0   |;   1   &)
%                                         (   4 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) )).

fof(d6_xboole_0,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) )).

fof(t2_xboole_0,axiom,(
    ! [A,B,C] :
      ( ! [D] :
          ( ~ r2_hidden(D,A)
        <=> ( r2_hidden(D,B)
          <=> r2_hidden(D,C) ) )
     => A = k5_xboole_0(B,C) ) )).

fof(t3_boole,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A )).

fof(t92_xboole_1,conjecture,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 )).

%------------------------------------------------------------------------------
