%------------------------------------------------------------------------------
% File     : MPT0734+2.004 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 004 of t22_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   27 (   2 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   21 (   2   ~;   0   |;   6   &)
%                                         (   3 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   17 (   0 sgn;  17   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d8_xboole_0,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(l58_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) )).

fof(cc1_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) )).

fof(d2_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) )).

fof(t21_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) )).

fof(t7_ordinal1,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) )).

fof(t22_ordinal1,conjecture,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) )).

%------------------------------------------------------------------------------
