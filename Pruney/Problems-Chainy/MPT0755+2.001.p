%------------------------------------------------------------------------------
% File     : MPT0755+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t48_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   24 (   0 equality)
%            Maximal formula depth :    9 (   7 average)
%            Number of connectives :   20 (   0   ~;   0   |;  15   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(fc8_funct_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) )).

fof(fc22_relat_1,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) )).

fof(fc5_ordinal1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v5_ordinal1(A)
        & v3_ordinal1(B) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v5_relat_1(k7_relat_1(A,B),k2_relat_1(A))
        & v5_ordinal1(k7_relat_1(A,B)) ) ) )).

fof(t48_ordinal1,conjecture,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B)
        & v5_ordinal1(B) )
     => ! [C] :
          ( v3_ordinal1(C)
         => ( v1_relat_1(k7_relat_1(B,C))
            & v5_relat_1(k7_relat_1(B,C),A)
            & v1_funct_1(k7_relat_1(B,C))
            & v5_ordinal1(k7_relat_1(B,C)) ) ) ) )).

%------------------------------------------------------------------------------
