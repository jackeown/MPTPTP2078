%------------------------------------------------------------------------------
% File     : MPT1929+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_6__t27_yellow_6.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3895 ( 454 unit)
%            Number of atoms       : 22926 (2658 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 22568 (3537   ~; 160   |;10040   &)
%                                         ( 839 <=>;7992  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  270 (   1 propositional; 0-6 arity)
%            Number of functors    :  352 (   9 constant; 0-10 arity)
%            Number of variables   : 11415 (   9 sgn;10857   !; 558   ?)
%            Maximal term depth    :    6 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
include('Axioms/MPT013+2.ax').
include('Axioms/MPT014+2.ax').
include('Axioms/MPT015+2.ax').
include('Axioms/MPT016+2.ax').
include('Axioms/MPT017+2.ax').
include('Axioms/MPT018+2.ax').
include('Axioms/MPT019+2.ax').
include('Axioms/MPT020+2.ax').
include('Axioms/MPT021+2.ax').
include('Axioms/MPT022+2.ax').
include('Axioms/MPT023+2.ax').
include('Axioms/MPT024+2.ax').
include('Axioms/MPT025+2.ax').
include('Axioms/MPT026+2.ax').
include('Axioms/MPT027+2.ax').
include('Axioms/MPT028+2.ax').
include('Axioms/MPT029+2.ax').
%------------------------------------------------------------------------------
fof(abstractness_v6_waybel_0,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v6_waybel_0(B,A)
       => B = g1_waybel_0(A,u1_struct_0(B),u1_orders_2(B),u1_waybel_0(A,B)) ) ) )).

fof(cc1_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => v3_ordinal1(A) ) )).

fof(cc1_card_3,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_card_3(A) ) ) )).

fof(cc1_classes2,axiom,(
    ! [A] :
      ( v2_classes1(A)
     => v1_classes1(A) ) )).

fof(cc1_pboole,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v2_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) )
         => ( v1_relat_1(B)
            & ~ v3_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) ) ) ) )).

fof(cc1_yellow_3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_struct_0(A)
       => v1_yellow_3(A) ) ) )).

fof(cc2_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_card_1(A) ) )).

fof(cc2_classes2,axiom,(
    ! [A] :
      ( v1_classes2(A)
     => ( v1_ordinal1(A)
        & v2_classes1(A) ) ) )).

fof(cc2_pboole,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v3_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) )
         => ( v1_relat_1(B)
            & ~ v2_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) ) ) ) )).

fof(cc2_yellow_3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ~ v1_yellow_3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(cc3_card_1,axiom,(
    ! [A] :
      ( v7_ordinal1(A)
     => v1_card_1(A) ) )).

fof(cc3_card_3,axiom,(
    ! [A] :
      ( v3_card_3(A)
     => ( v4_funct_1(A)
        & v2_card_3(A) ) ) )).

fof(cc3_classes2,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_classes1(A) )
     => v1_classes2(A) ) )).

fof(cc4_card_3,axiom,(
    ! [A] :
      ( ( ~ v1_finset_1(A)
        & v1_card_1(A) )
     => ( v4_ordinal1(A)
        & v1_card_1(A) ) ) )).

fof(cc4_pboole,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v2_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) )
         => ( v1_relat_1(B)
            & ~ v3_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) ) ) ) )).

fof(cc5_card_1,axiom,(
    ! [A] :
      ( v7_ordinal1(A)
     => v1_finset_1(A) ) )).

fof(cc5_card_3,axiom,(
    ! [A] :
      ( v5_card_3(A)
     => ( ~ v1_finset_1(A)
        & v4_card_3(A) ) ) )).

fof(cc5_pboole,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) )
         => ( ~ v1_xboole_0(B)
            & v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) ) ) ) )).

fof(cc6_card_1,axiom,(
    ! [A] :
      ( ( v3_ordinal1(A)
        & v1_finset_1(A) )
     => v7_ordinal1(A) ) )).

fof(cc6_card_3,axiom,(
    ! [A] :
      ( ( ~ v1_finset_1(A)
        & v4_card_3(A) )
     => v5_card_3(A) ) )).

fof(cc7_card_1,axiom,(
    ! [A] :
      ( v3_card_1(A,k1_xboole_0)
     => v1_xboole_0(A) ) )).

fof(cc7_card_3,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v4_card_3(A) ) )).

fof(cc8_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v3_card_1(A,k1_xboole_0) ) )).

fof(cc8_card_3,axiom,(
    ! [A] :
      ( v4_card_3(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v4_card_3(B) ) ) )).

fof(cc9_card_3,axiom,(
    ! [A] :
      ( v2_card_3(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v2_card_3(B) ) ) )).

fof(d10_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( v1_yellow_6(B,A)
           => ( v2_struct_0(B)
              | k4_yellow_6(A,B) = k3_funct_1(u1_waybel_0(A,B)) ) ) ) ) )).

fof(d12_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v4_orders_2(C)
                & v7_waybel_0(C)
                & l1_waybel_0(C,A) )
             => ( m2_yellow_6(C,A,B)
              <=> ? [D] :
                    ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                    & r2_funct_2(u1_struct_0(C),u1_struct_0(A),u1_waybel_0(A,C),k1_partfun1(u1_struct_0(C),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),D,u1_waybel_0(A,B)))
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ? [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                            & ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( r1_orders_2(C,F,G)
                                 => r1_orders_2(B,E,k2_yellow_6(u1_struct_0(C),B,D,G)) ) ) ) ) ) ) ) ) ) )).

fof(d18_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v3_funct_1(A)
       => ( v1_xboole_0(A)
          | ! [B] :
              ( B = k3_funct_1(A)
            <=> ? [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                  & B = k1_funct_1(A,C) ) ) ) ) ) )).

fof(d1_classes1,axiom,(
    ! [A] :
      ( v1_classes1(A)
    <=> ! [B,C] :
          ( ( r2_hidden(B,A)
            & r1_tarski(C,B) )
         => r2_hidden(C,A) ) ) )).

fof(d4_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k3_card_3(A) = k3_tarski(k2_relat_1(A)) ) )).

fof(d5_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v7_waybel_0(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,B,D)
                    & r1_orders_2(A,C,D) ) ) ) ) ) )).

fof(d7_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,B)
                    & l1_waybel_0(D,B) )
                 => ( D = k3_yellow_6(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A))
                      & r2_funct_2(u1_struct_0(D),u1_struct_0(B),u1_waybel_0(B,D),k8_funcop_1(u1_struct_0(B),u1_struct_0(D),C)) ) ) ) ) ) ) )).

fof(d8_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) )).

fof(d9_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) )).

fof(dt_g1_waybel_0,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,B,u1_struct_0(A))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,u1_struct_0(A)))) )
     => ( v6_waybel_0(g1_waybel_0(A,B,C,D),A)
        & l1_waybel_0(g1_waybel_0(A,B,C,D),A) ) ) )).

fof(dt_k10_pralg_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => l1_struct_0(k10_pralg_1(A,B,C)) ) )).

fof(dt_k1_card_1,axiom,(
    ! [A] : v1_card_1(k1_card_1(A)) )).

fof(dt_k2_yellow_6,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v2_struct_0(B)
        & l1_orders_2(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,u1_struct_0(B))))
        & m1_subset_1(D,A) )
     => m1_subset_1(k2_yellow_6(A,B,C,D),u1_struct_0(B)) ) )).

fof(dt_k3_card_3,axiom,(
    $true )).

fof(dt_k3_funct_1,axiom,(
    $true )).

fof(dt_k3_yellow_6,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k3_yellow_6(A,B,C),B)
        & l1_waybel_0(k3_yellow_6(A,B,C),B) ) ) )).

fof(dt_k4_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) )).

fof(dt_k8_funcop_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(C,A) )
     => ( v1_funct_1(k8_funcop_1(A,B,C))
        & v1_funct_2(k8_funcop_1(A,B,C),B,A)
        & m1_subset_1(k8_funcop_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) )).

fof(dt_m1_yellow_6,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) )).

fof(dt_m2_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) )).

fof(existence_m1_yellow_6,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ? [C] : m1_yellow_6(C,A,B) ) )).

fof(existence_m2_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ? [C] : m2_yellow_6(C,A,B) ) )).

fof(fc10_card_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_finset_1(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_finset_1(k2_zfmisc_1(A,B)) ) )).

fof(fc11_card_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_finset_1(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_finset_1(k2_zfmisc_1(B,A)) ) )).

fof(fc11_yellow_6,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k3_yellow_6(A,B,C),B)
        & v1_yellow_6(k3_yellow_6(A,B,C),B) ) ) )).

fof(fc12_card_3,axiom,(
    ! [A,B] :
      ( ~ v1_finset_1(A)
     => ~ v1_finset_1(k2_funcop_1(A,B)) ) )).

fof(fc12_yellow_6,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_struct_0(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( ~ v2_struct_0(k3_yellow_6(A,B,C))
        & v6_waybel_0(k3_yellow_6(A,B,C),B) ) ) )).

fof(fc13_card_1,axiom,(
    ! [A] : v3_card_1(k1_tarski(A),np__1) )).

fof(fc14_card_1,axiom,(
    ! [A,B] :
      ( ( v1_card_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v3_card_1(B,A) )
     => v3_card_1(k1_relat_1(B),A) ) )).

fof(fc15_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & ~ v1_xboole_0(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A)) ) ) )).

fof(fc16_funcop_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v3_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v3_funct_1(k7_relat_1(A,B)) ) ) )).

fof(fc16_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & v1_yellow_6(B,A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v3_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A)) ) ) )).

fof(fc1_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc1_card_3,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_card_3(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_card_3(k7_relat_1(A,B)) ) ) )).

fof(fc2_card_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v1_xboole_0(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc2_card_3,axiom,(
    ! [A,B] :
      ( v1_card_1(B)
     => v1_card_3(k2_funcop_1(A,B)) ) )).

fof(fc2_pboole,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_relat_1(D)
        & v4_relat_1(D,B)
        & v1_funct_1(D)
        & v1_partfun1(D,B) )
     => ( v1_relat_1(k5_relat_1(C,D))
        & v4_relat_1(k5_relat_1(C,D),A)
        & v1_funct_1(k5_relat_1(C,D))
        & v1_partfun1(k5_relat_1(C,D),A) ) ) )).

fof(fc3_pboole,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v2_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & m1_subset_1(C,A) )
     => ~ v1_xboole_0(k1_funct_1(B,C)) ) )).

fof(fc3_yellow_6,axiom,(
    ! [A,B] :
      ( l1_struct_0(B)
     => v2_pralg_1(k2_funcop_1(A,B)) ) )).

fof(fc4_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v4_funct_1(k4_card_3(A)) ) )).

fof(fc5_waybel_0,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,B,u1_struct_0(A))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,u1_struct_0(A)))) )
     => ( ~ v2_struct_0(g1_waybel_0(A,B,C,D))
        & v6_waybel_0(g1_waybel_0(A,B,C,D),A) ) ) )).

fof(fc6_card_1,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ( v1_finset_1(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc7_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v3_card_3(k4_card_3(A)) ) )).

fof(fc8_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ( ~ v1_finset_1(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc9_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ~ v1_finset_1(k1_zfmisc_1(A)) ) )).

fof(fc9_yellow_3,axiom,(
    ! [A] :
      ( ( ~ v1_yellow_3(A)
        & l1_orders_2(A) )
     => ~ v1_xboole_0(u1_orders_2(A)) ) )).

fof(free_g1_waybel_0,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,B,u1_struct_0(A))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,u1_struct_0(A)))) )
     => ! [E,F,G,H] :
          ( g1_waybel_0(A,B,C,D) = g1_waybel_0(E,F,G,H)
         => ( A = E
            & B = F
            & C = G
            & D = H ) ) ) )).

fof(projectivity_k1_card_1,axiom,(
    ! [A] : k1_card_1(k1_card_1(A)) = k1_card_1(A) )).

fof(rc1_card_1,axiom,(
    ? [A] : v1_card_1(A) )).

fof(rc1_card_3,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & v1_card_3(A) ) )).

fof(rc1_classes2,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_classes2(A) ) )).

fof(rc1_pboole,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A) ) )).

fof(rc1_yellow_6,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & v3_funct_1(A)
      & ~ v1_xboole_0(A)
      & v2_pralg_1(A) ) )).

fof(rc2_card_1,axiom,(
    ? [A] :
      ( v1_ordinal1(A)
      & v2_ordinal1(A)
      & v3_ordinal1(A)
      & v1_finset_1(A)
      & v1_card_1(A) ) )).

fof(rc2_classes2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_classes2(A) )
     => ? [B] :
          ( m1_subset_1(B,A)
          & ~ v1_xboole_0(B) ) ) )).

fof(rc2_pboole,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v3_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A) ) )).

fof(rc3_card_1,axiom,(
    ? [A] : ~ v1_finset_1(A) )).

fof(rc3_card_3,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v4_funct_1(A)
      & v2_card_3(A) ) )).

fof(rc3_pboole,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v2_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A) ) )).

fof(rc4_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_finset_1(B) ) ) )).

fof(rc4_card_3,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v3_card_3(A) ) )).

fof(rc4_pboole,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_funcop_1(B) ) )).

fof(rc4_waybel_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ? [B] :
          ( l1_waybel_0(B,A)
          & v6_waybel_0(B,A) ) ) )).

fof(rc5_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => ? [B] : v3_card_1(B,A) ) )).

fof(rc5_card_3,axiom,(
    ? [A] : v5_card_3(A) )).

fof(rc6_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => ? [B] :
          ( v1_relat_1(B)
          & v1_funct_1(B)
          & v3_card_1(B,A) ) ) )).

fof(rc6_card_3,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & ~ v1_finset_1(A) ) )).

fof(rc7_pboole,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ? [C] :
          ( v1_relat_1(C)
          & v4_relat_1(C,B)
          & v5_relat_1(C,A)
          & v1_funct_1(C)
          & v1_partfun1(C,B) ) ) )).

fof(redefinition_k10_pralg_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => k10_pralg_1(A,B,C) = k1_funct_1(B,C) ) )).

fof(redefinition_k2_yellow_6,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v2_struct_0(B)
        & l1_orders_2(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,u1_struct_0(B))))
        & m1_subset_1(D,A) )
     => k2_yellow_6(A,B,C,D) = k1_funct_1(C,D) ) )).

fof(redefinition_k8_funcop_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(C,A) )
     => k8_funcop_1(A,B,C) = k2_funcop_1(B,C) ) )).

fof(t10_funct_6,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_tarski(k4_card_3(A),k1_funct_2(k1_relat_1(A),k3_card_3(A))) ) )).

fof(t12_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) )).

fof(t13_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k3_yellow_6(A,B,C)) = u1_struct_0(A) ) ) ) )).

fof(t14_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(k3_yellow_6(A,B,C)))
                 => k2_waybel_0(B,k3_yellow_6(A,B,C),D) = C ) ) ) ) )).

fof(t15_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_yellow_0(A,A)
        & m1_yellow_0(A,A) ) ) )).

fof(t16_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ! [C] :
              ( m1_yellow_0(C,B)
             => m1_yellow_0(C,A) ) ) ) )).

fof(t17_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => m1_yellow_6(B,A,B) ) ) )).

fof(t18_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ! [D] :
                  ( m1_yellow_6(D,A,C)
                 => m1_yellow_6(D,A,B) ) ) ) ) )).

fof(t19_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => r1_tarski(u1_struct_0(C),u1_struct_0(B)) ) ) ) )).

fof(t1_classes2,axiom,(
    ! [A,B] :
      ( ( v1_classes1(A)
        & r2_hidden(B,A) )
     => ( ~ r2_tarski(B,A)
        & r2_hidden(k1_card_1(B),k1_card_1(A)) ) ) )).

fof(t20_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(C))
                             => ( ( D = F
                                  & E = G
                                  & r1_orders_2(C,F,G) )
                               => r1_orders_2(B,D,E) ) ) ) ) ) ) ) ) )).

fof(t21_yellow_6,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v2_yellow_6(C,A,B)
                & m1_yellow_6(C,A,B) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(C))
                             => ( ( D = F
                                  & E = G
                                  & r1_orders_2(B,D,E) )
                               => r1_orders_2(C,F,G) ) ) ) ) ) ) ) ) )).

fof(t22_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k4_yellow_6(B,k3_yellow_6(A,B,C)) = C ) ) ) )).

fof(t23_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => m2_yellow_6(B,A,B) ) ) )).

fof(t24_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v4_orders_2(C)
                & v7_waybel_0(C)
                & l1_waybel_0(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v4_orders_2(D)
                    & v7_waybel_0(D)
                    & l1_waybel_0(D,A) )
                 => ( ( m2_yellow_6(B,A,C)
                      & m2_yellow_6(C,A,D) )
                   => m2_yellow_6(B,A,D) ) ) ) ) ) )).

fof(t25_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v1_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k4_yellow_6(A,B) ) ) ) )).

fof(t26_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ~ ( r1_waybel_0(A,B,C)
                & r1_waybel_0(A,B,D)
                & r1_xboole_0(C,D) ) ) ) )).

fof(t27_yellow_6,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( r2_waybel_0(A,C,D)
                 => r2_waybel_0(A,B,D) ) ) ) ) )).

fof(t2_classes1,axiom,(
    ! [A] :
      ( v2_classes1(A)
    <=> ( v1_classes1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => r2_hidden(k9_setfam_1(B),A) )
        & ! [B] :
            ( ( r1_tarski(B,A)
              & r2_hidden(k1_card_1(B),k1_card_1(A)) )
           => r2_hidden(B,A) ) ) ) )).

fof(t5_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_classes2(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( r2_hidden(k1_relat_1(B),A)
              & r1_tarski(k2_relat_1(B),A) )
           => r2_hidden(k4_card_3(B),A) ) ) ) )).

fof(t65_classes2,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & v1_classes2(B) )
     => ( r2_hidden(A,B)
       => ( r2_hidden(k9_setfam_1(A),B)
          & r2_hidden(k3_tarski(A),B)
          & r2_hidden(k1_setfam_1(A),B) ) ) ) )).

fof(t67_classes2,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(C)
        & v1_classes2(C) )
     => ( ( r2_hidden(A,C)
          & r2_hidden(B,C) )
       => ( r2_hidden(k2_zfmisc_1(A,B),C)
          & r2_hidden(k1_funct_2(A,B),C) ) ) ) )).

fof(t80_card_2,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_ordinal1(k1_card_1(k2_relat_1(A)),k1_card_1(k1_relat_1(A))) ) )).

fof(t94_funcop_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] : k3_funct_1(k7_funcop_1(A,B)) = B ) )).

fof(t9_yellow_6,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A)
            & v2_pralg_1(B) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => k1_funct_1(k12_pralg_1(A,B),C) = u1_struct_0(k10_pralg_1(A,B,C)) ) ) ) )).

%------------------------------------------------------------------------------
