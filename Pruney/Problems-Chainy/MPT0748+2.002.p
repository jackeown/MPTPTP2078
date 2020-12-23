%------------------------------------------------------------------------------
% File     : MPT0748+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t38_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :    7 (   0 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    6 (   2   ~;   0   |;   1   &)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    7 (   0 sgn;   6   !;   1   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) )).

fof(t37_ordinal1,axiom,(
    ! [A] :
      ~ ! [B] :
          ( r2_hidden(B,A)
        <=> v3_ordinal1(B) ) )).

fof(t38_ordinal1,conjecture,(
    ! [A] :
      ~ ! [B] :
          ( v3_ordinal1(B)
         => r2_hidden(B,A) ) )).

%------------------------------------------------------------------------------
