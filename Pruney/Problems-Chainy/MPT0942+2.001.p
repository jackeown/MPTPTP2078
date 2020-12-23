%------------------------------------------------------------------------------
% File     : MPT0942+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t7_wellord2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   4 unit)
%            Number of atoms       :   17 (   0 equality)
%            Maximal formula depth :    8 (   3 average)
%            Number of connectives :    9 (   0   ~;   0   |;   4   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :    8 (   0 sgn;   8   !;   0   ?)
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

fof(dt_k1_wellord2,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) )).

fof(t2_wellord2,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) )).

fof(t3_wellord2,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) )).

fof(t4_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v6_relat_2(k1_wellord2(A)) ) )).

fof(t5_wellord2,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) )).

fof(t6_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v1_wellord1(k1_wellord2(A)) ) )).

fof(t7_wellord2,conjecture,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) )).

%------------------------------------------------------------------------------
