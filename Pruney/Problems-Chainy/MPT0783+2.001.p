%------------------------------------------------------------------------------
% File     : MPT0783+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t32_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   27 (   0 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   19 (   0   ~;   0   |;   4   &)
%                                         (   1 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) )).

fof(dt_k2_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) )).

fof(t22_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_relat_2(B)
       => v1_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t23_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v6_relat_2(B)
       => v6_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t24_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v8_relat_2(B)
       => v8_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t25_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_2(B)
       => v4_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t31_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_wellord1(B)
       => v1_wellord1(k2_wellord1(B,A)) ) ) )).

fof(t32_wellord1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) )).

%------------------------------------------------------------------------------
