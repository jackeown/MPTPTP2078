%------------------------------------------------------------------------------
% File     : MPT0761+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t5_wellord1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   15 (   2 equality)
%            Maximal formula depth :   12 (   9 average)
%            Number of connectives :   18 (   6   ~;   0   |;   6   &)
%                                         (   3 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :    8 (   0 sgn;   8   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d2_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & r1_xboole_0(k1_wellord1(A,C),B) ) ) ) ) )).

fof(d3_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_wellord1(A,B)
        <=> ! [C] :
              ~ ( r1_tarski(C,B)
                & C != k1_xboole_0
                & ! [D] :
                    ~ ( r2_hidden(D,C)
                      & r1_xboole_0(k1_wellord1(A,D),C) ) ) ) ) )).

fof(t5_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> r1_wellord1(A,k3_relat_1(A)) ) ) )).

%------------------------------------------------------------------------------
