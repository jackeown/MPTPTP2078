%------------------------------------------------------------------------------
% File     : MPT0753+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t46_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   21 (   1 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   15 (   0   ~;   0   |;   5   &)
%                                         (   2 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d19_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) )).

fof(t25_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) )).

fof(t88_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) )).

fof(t98_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) )).

fof(d7_ordinal1,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) )).

fof(t46_ordinal1,conjecture,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v3_ordinal1(k1_relat_1(A))
       => ( v1_relat_1(A)
          & v5_relat_1(A,k2_relat_1(A))
          & v1_funct_1(A)
          & v5_ordinal1(A) ) ) ) )).

%------------------------------------------------------------------------------
