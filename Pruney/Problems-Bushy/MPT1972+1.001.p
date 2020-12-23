%------------------------------------------------------------------------------
% File     : MPT1972+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t21_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   11 (   0 unit)
%            Number of atoms       :   83 (   3 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   78 (   6   ~;   0   |;  55   &)
%                                         (   2 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   16 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(abstractness_v1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) )).

fof(dt_k7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) )).

fof(fc1_yellow_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v3_orders_2(k7_lattice3(A)) ) ) )).

fof(fc2_yellow_7,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v4_orders_2(k7_lattice3(A)) ) ) )).

fof(fc3_yellow_7,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v5_orders_2(k7_lattice3(A)) ) ) )).

fof(fc5_yellow_7,axiom,(
    ! [A] :
      ( ( v2_lattice3(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v1_lattice3(k7_lattice3(A)) ) ) )).

fof(fc6_yellow_7,axiom,(
    ! [A] :
      ( ( v1_lattice3(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v2_lattice3(k7_lattice3(A)) ) ) )).

fof(t19_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v3_orders_2(B)
            & v4_orders_2(B)
            & v5_orders_2(B)
            & v1_lattice3(B)
            & v2_lattice3(B)
            & l1_orders_2(B) )
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & v2_waybel_0(C,A)
                  & v13_waybel_0(C,A)
                  & v2_waybel_7(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
               => ( ~ v1_xboole_0(C)
                  & v2_waybel_0(C,B)
                  & v13_waybel_0(C,B)
                  & v2_waybel_7(C,B)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) ) ) ) ) ) )).

fof(t20_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & v1_waybel_7(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k7_lattice3(A))
            & v13_waybel_0(B,k7_lattice3(A))
            & v2_waybel_7(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

fof(t8_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) )).

fof(t21_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & v2_waybel_7(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,k7_lattice3(A))
            & v12_waybel_0(B,k7_lattice3(A))
            & v1_waybel_7(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

%------------------------------------------------------------------------------
