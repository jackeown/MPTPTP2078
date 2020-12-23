%------------------------------------------------------------------------------
% File     : MPT0747+2.009 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 009 of t37_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :    8 (   0 equality)
%            Maximal formula depth :    7 (   6 average)
%            Number of connectives :    9 (   4   ~;   0   |;   2   &)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t36_ordinal1,axiom,(
    ! [A] :
      ~ ( ! [B] :
            ( r2_hidden(B,A)
           => v3_ordinal1(B) )
        & ! [B] :
            ( v3_ordinal1(B)
           => ~ r1_tarski(A,B) ) ) )).

fof(t7_ordinal1,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) )).

fof(t37_ordinal1,conjecture,(
    ! [A] :
      ~ ! [B] :
          ( r2_hidden(B,A)
        <=> v3_ordinal1(B) ) )).

%------------------------------------------------------------------------------
