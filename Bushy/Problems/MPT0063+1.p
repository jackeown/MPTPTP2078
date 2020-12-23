%------------------------------------------------------------------------------
% File     : MPT0063+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : xboole_1__t56_xboole_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   1 unit)
%            Number of atoms       :   12 (   1 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :   10 (   3   ~;   0   |;   3   &)
%                                         (   1 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   12 (   1 sgn;  12   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t56_xboole_1,conjecture,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) )).

fof(antisymmetry_r2_xboole_0,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) )).

fof(d8_xboole_0,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) )).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) )).

fof(l58_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) )).

%------------------------------------------------------------------------------
