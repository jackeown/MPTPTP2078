%------------------------------------------------------------------------------
% File     : MPT0755+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : ordinal1__t48_ordinal1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   26 (   0 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   21 (   0   ~;   0   |;  15   &)
%                                         (   0 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(dt_k7_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) )).

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

fof(fc8_funct_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) )).

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
