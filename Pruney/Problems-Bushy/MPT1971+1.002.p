%------------------------------------------------------------------------------
% File     : MPT1971+1.002 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t20_waybel_7---2.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   16 (   0 unit)
%            Number of atoms       :  103 (   4 equality)
%            Maximal formula depth :   14 (   6 average)
%            Number of connectives :   97 (  10   ~;   0   |;  54   &)
%                                         (   5 <=>;  28  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   17 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-3 arity)
%            Number of variables   :   33 (   0 sgn;  33   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d1_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(k12_lattice3(A,C,D),B)
                        & ~ r2_hidden(C,B)
                        & ~ r2_hidden(D,B) ) ) ) ) ) ) )).

fof(d2_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(k13_lattice3(A,C,D),B)
                        & ~ r2_hidden(C,B)
                        & ~ r2_hidden(D,B) ) ) ) ) ) ) )).

fof(d6_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_lattice3(A,B) = B ) ) )).

fof(d7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k7_lattice3(A)))
         => k9_lattice3(A,B) = B ) ) )).

fof(dt_k7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) )).

fof(dt_k8_lattice3,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k8_lattice3(A,B),u1_struct_0(k7_lattice3(A))) ) )).

fof(dt_k9_lattice3,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(k7_lattice3(A))) )
     => m1_subset_1(k9_lattice3(A,B),u1_struct_0(A)) ) )).

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

fof(t21_yellow_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k12_lattice3(A,B,C) = k13_lattice3(k7_lattice3(A),k8_lattice3(A,B),k8_lattice3(A,C)) ) ) ) )).

fof(t22_yellow_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k7_lattice3(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k7_lattice3(A)))
             => k12_lattice3(A,k9_lattice3(A,B),k9_lattice3(A,C)) = k13_lattice3(k7_lattice3(A),B,C) ) ) ) )).

fof(t26_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v1_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v2_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

fof(t28_yellow_7,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v13_waybel_0(B,k7_lattice3(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k7_lattice3(A)))) ) ) ) )).

fof(t20_waybel_7,conjecture,(
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

%------------------------------------------------------------------------------
