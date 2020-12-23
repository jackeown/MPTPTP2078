%------------------------------------------------------------------------------
% File     : MPT1452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : filter_1__t47_filter_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   16 (   1 unit)
%            Number of atoms       :  139 (   1 equality)
%            Maximal formula depth :   15 (   9 average)
%            Number of connectives :  156 (  33   ~;   0   |; 105   &)
%                                         (   3 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   16 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-4 arity)
%            Number of variables   :   23 (   0 sgn;  16   !;   7   ?)
%            Maximal term depth    :    4 (   1 average)
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

fof(d7_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l3_lattices(B) )
         => k7_filter_1(A,B) = g3_lattices(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)),k6_filter_1(u1_struct_0(A),u1_struct_0(B),u2_lattices(A),u2_lattices(B)),k6_filter_1(u1_struct_0(A),u1_struct_0(B),u1_lattices(A),u1_lattices(B))) ) ) )).

fof(dt_k7_filter_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) )).

fof(existence_l3_lattices,axiom,(
    ? [A] : l3_lattices(A) )).

fof(fc2_filter_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( ~ v2_struct_0(k7_filter_1(A,B))
        & v3_lattices(k7_filter_1(A,B)) ) ) )).

fof(fc3_filter_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & v10_lattices(k7_filter_1(A,B)) ) ) )).

fof(rc11_lattices,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & ~ v2_struct_0(A)
      & v3_lattices(A)
      & v4_lattices(A)
      & v5_lattices(A)
      & v6_lattices(A)
      & v7_lattices(A)
      & v8_lattices(A)
      & v9_lattices(A)
      & v10_lattices(A)
      & v15_lattices(A) ) )).

fof(rc13_lattices,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & ~ v2_struct_0(A)
      & v3_lattices(A)
      & v4_lattices(A)
      & v5_lattices(A)
      & v6_lattices(A)
      & v7_lattices(A)
      & v8_lattices(A)
      & v9_lattices(A)
      & v10_lattices(A)
      & v17_lattices(A) ) )).

fof(rc1_filter_0,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & ~ v2_struct_0(A)
      & v3_lattices(A)
      & v4_lattices(A)
      & v5_lattices(A)
      & v6_lattices(A)
      & v7_lattices(A)
      & v8_lattices(A)
      & v9_lattices(A)
      & v10_lattices(A)
      & v3_filter_0(A) ) )).

fof(rc3_lattices,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & v3_lattices(A) ) )).

fof(rc6_lattices,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & ~ v2_struct_0(A)
      & v3_lattices(A) ) )).

fof(rc9_lattices,axiom,(
    ? [A] :
      ( l3_lattices(A)
      & ~ v2_struct_0(A)
      & v3_lattices(A)
      & v10_lattices(A) ) )).

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
