%------------------------------------------------------------------------------
% File     : MPT1980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t29_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   15 (   0 unit)
%            Number of atoms       :  118 (   0 equality)
%            Maximal formula depth :   14 (   7 average)
%            Number of connectives :  117 (  14   ~;   0   |;  76   &)
%                                         (   5 <=>;  22  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   18 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-1 arity)
%            Number of variables   :   27 (   0 sgn;  27   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
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

fof(fc8_yellow_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v2_waybel_1(A)
        & l1_orders_2(A) )
     => ( v1_orders_2(k7_lattice3(A))
        & v2_waybel_1(k7_lattice3(A)) ) ) )).

fof(symmetry_r1_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) )).

fof(t21_waybel_7,axiom,(
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

fof(t26_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v1_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v2_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

fof(t27_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & v2_waybel_0(C,A)
                & v13_waybel_0(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ~ ( r1_subset_1(B,C)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v1_waybel_0(D,A)
                        & v12_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v1_waybel_7(D,A)
                          & r1_tarski(B,D)
                          & r1_subset_1(D,C) ) ) ) ) ) ) )).

fof(t27_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v1_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) )
        <=> ( v2_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) )).

fof(t28_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v13_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

fof(t29_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v12_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) )
        <=> ( v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) )).

fof(t29_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & v2_waybel_0(C,A)
                & v13_waybel_0(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ~ ( r1_subset_1(B,C)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v2_waybel_0(D,A)
                        & v13_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v2_waybel_7(D,A)
                          & r1_tarski(C,D)
                          & r1_subset_1(B,D) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
