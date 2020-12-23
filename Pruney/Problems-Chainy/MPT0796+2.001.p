%------------------------------------------------------------------------------
% File     : MPT0796+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t48_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   12 (   0 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :    8 (   0   ~;   0   |;   3   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-3 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :    6 (   0 sgn;   5   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(fc3_funct_1,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) )).

fof(d8_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) )).

fof(t47_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r3_wellord1(A,A,k6_relat_1(k3_relat_1(A))) ) )).

fof(t48_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => r4_wellord1(A,A) ) )).

%------------------------------------------------------------------------------
