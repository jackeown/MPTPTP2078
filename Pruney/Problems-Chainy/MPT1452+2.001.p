%------------------------------------------------------------------------------
% File     : MPT1452+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t47_filter_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   77 (   0 equality)
%            Maximal formula depth :   15 (  10 average)
%            Number of connectives :   92 (  21   ~;   0   |;  57   &)
%                                         (   3 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(cc5_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) )).

fof(cc6_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v17_lattices(A) ) ) ) )).

fof(dt_k7_filter_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) )).

fof(t39_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v11_lattices(A)
              & l3_lattices(A)
              & ~ v2_struct_0(B)
              & v10_lattices(B)
              & v11_lattices(B)
              & l3_lattices(B) )
          <=> ( ~ v2_struct_0(k7_filter_1(A,B))
              & v10_lattices(k7_filter_1(A,B))
              & v11_lattices(k7_filter_1(A,B))
              & l3_lattices(k7_filter_1(A,B)) ) ) ) ) )).

fof(t46_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v15_lattices(A)
              & v16_lattices(A)
              & l3_lattices(A)
              & ~ v2_struct_0(B)
              & v10_lattices(B)
              & v15_lattices(B)
              & v16_lattices(B)
              & l3_lattices(B) )
          <=> ( ~ v2_struct_0(k7_filter_1(A,B))
              & v10_lattices(k7_filter_1(A,B))
              & v15_lattices(k7_filter_1(A,B))
              & v16_lattices(k7_filter_1(A,B))
              & l3_lattices(k7_filter_1(A,B)) ) ) ) ) )).

fof(t47_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v17_lattices(A)
              & l3_lattices(A)
              & ~ v2_struct_0(B)
              & v10_lattices(B)
              & v17_lattices(B)
              & l3_lattices(B) )
          <=> ( ~ v2_struct_0(k7_filter_1(A,B))
              & v10_lattices(k7_filter_1(A,B))
              & v17_lattices(k7_filter_1(A,B))
              & l3_lattices(k7_filter_1(A,B)) ) ) ) ) )).

%------------------------------------------------------------------------------
