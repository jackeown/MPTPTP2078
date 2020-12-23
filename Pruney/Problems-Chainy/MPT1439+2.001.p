%------------------------------------------------------------------------------
% File     : MPT1439+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t34_filter_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   30 (   0 equality)
%            Maximal formula depth :    9 (   8 average)
%            Number of connectives :   32 (   6   ~;   0   |;  14   &)
%                                         (   1 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
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

fof(d9_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( r1_filter_1(A,B)
          <=> r4_wellord1(k8_filter_1(A),k8_filter_1(B)) ) ) ) )).

fof(dt_k8_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => v1_relat_1(k8_filter_1(A)) ) )).

fof(t34_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v10_lattices(C)
                & l3_lattices(C) )
             => ( ( r1_filter_1(A,B)
                  & r1_filter_1(B,C) )
               => r1_filter_1(A,C) ) ) ) ) )).

%------------------------------------------------------------------------------
