%------------------------------------------------------------------------------
% File     : MPT0947+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t12_wellord2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   1 unit)
%            Number of atoms       :   21 (   2 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   16 (   0   ~;   0   |;   2   &)
%                                         (   0 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :   11 (   0 sgn;  11   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t50_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) )).

fof(t52_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) )).

fof(dt_k1_wellord2,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) )).

fof(t11_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
           => A = B ) ) ) )).

fof(t12_wellord2,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r4_wellord1(A,k1_wellord2(B))
                  & r4_wellord1(A,k1_wellord2(C)) )
               => B = C ) ) ) ) )).

%------------------------------------------------------------------------------
