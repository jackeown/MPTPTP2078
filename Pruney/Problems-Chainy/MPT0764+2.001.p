%------------------------------------------------------------------------------
% File     : MPT0764+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t10_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   17 (   2 equality)
%            Maximal formula depth :   14 (  10 average)
%            Number of connectives :   20 (   6   ~;   0   |;   6   &)
%                                         (   1 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t8_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) )).

fof(t9_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_wellord1(B,A)
       => ! [C] :
            ~ ( r1_tarski(C,A)
              & C != k1_xboole_0
              & ! [D] :
                  ~ ( r2_hidden(D,C)
                    & ! [E] :
                        ( r2_hidden(E,C)
                       => r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) )).

fof(t10_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) )).

%------------------------------------------------------------------------------
