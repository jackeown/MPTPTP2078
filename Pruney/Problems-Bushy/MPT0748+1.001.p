%------------------------------------------------------------------------------
% File     : MPT0748+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : ordinal1__t38_ordinal1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
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
% SPC      : FOF_THM_RFO_NEQ

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
