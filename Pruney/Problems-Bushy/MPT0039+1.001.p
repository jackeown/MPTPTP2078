%------------------------------------------------------------------------------
% File     : MPT0039+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : xboole_1__t32_xboole_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :    9 (   4 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :    7 (   1   ~;   0   |;   1   &)
%                                         (   3 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
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

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) )).

fof(t32_xboole_1,conjecture,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) )).

%------------------------------------------------------------------------------
