%------------------------------------------------------------------------------
% File     : MPT2007+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_9__t6_waybel_9.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 4349 ( 467 unit)
%            Number of atoms       : 27001 (2818 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 26787 (4135   ~; 166   |;12565   &)
%                                         ( 960 <=>;8961  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  314 (   1 propositional; 0-6 arity)
%            Number of functors    :  422 (   9 constant; 0-10 arity)
%            Number of variables   : 12746 (   9 sgn;12099   !; 647   ?)
%            Maximal term depth    :    7 (   1 average)
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
include('Axioms/MPT030+2.ax').
include('Axioms/MPT031+2.ax').
%------------------------------------------------------------------------------
fof(cc1_finsub_1,axiom,(
    ! [A] :
      ( v4_finsub_1(A)
     => ( v1_finsub_1(A)
        & v3_finsub_1(A) ) ) )).

fof(cc1_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v16_waybel_0(A) )
       => ( ~ v2_struct_0(A)
          & v1_lattice3(A)
          & v2_lattice3(A) ) ) ) )).

fof(cc2_finsub_1,axiom,(
    ! [A] :
      ( ( v1_finsub_1(A)
        & v3_finsub_1(A) )
     => v4_finsub_1(A) ) )).

fof(cc2_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v3_orders_2(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) )).

fof(cc3_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v3_orders_2(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v1_waybel_2(A) ) ) ) )).

fof(cc4_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v2_waybel_2(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v1_waybel_2(A) ) ) ) )).

fof(cc5_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v1_waybel_2(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v2_waybel_2(A) ) ) ) )).

fof(cc6_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v9_waybel_1(A)
          & v3_lattice3(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_waybel_1(A)
          & v2_waybel_2(A) ) ) ) )).

fof(cc7_waybel_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_waybel_1(A)
          & v3_lattice3(A)
          & v2_waybel_2(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v9_waybel_1(A) ) ) ) )).

fof(commutativity_k2_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_yellow_4(A,B,C) = k2_yellow_4(A,C,B) ) )).

fof(commutativity_k4_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => k4_yellow_4(A,B,C) = k4_yellow_4(A,C,B) ) )).

fof(d18_waybel_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
             => ( C = k4_waybel_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k3_funct_2(u1_struct_0(A),u1_struct_0(A),C,D) = k11_lattice3(A,B,D) ) ) ) ) ) )).

fof(d1_waybel_9,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_orders_2(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_waybel_0(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( r1_orders_2(A,D,E)
                         => r1_orders_2(B,k2_yellow_6(u1_struct_0(A),B,C,E),k2_yellow_6(u1_struct_0(A),B,C,D)) ) ) ) ) ) ) ) )).

fof(d2_waybel_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_orders_2(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_orders_3(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( r1_orders_2(A,D,E)
                         => r1_orders_2(B,k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D),k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,E)) ) ) ) ) ) ) ) )).

fof(dt_k1_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_yellow_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_k2_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_yellow_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_k3_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k3_yellow_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_k4_waybel_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) )).

fof(dt_k4_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k4_yellow_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(fc12_waybel_2,axiom,(
    ! [A,B] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & v2_waybel_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & v22_waybel_0(k4_waybel_1(A,B),A,A) ) ) )).

fof(fc1_finsub_1,axiom,(
    ! [A] : v4_finsub_1(k1_zfmisc_1(A)) )).

fof(fc1_waybel_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k9_relat_1(C,D)) ) )).

fof(fc1_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k1_yellow_4(A,B,C)) ) )).

fof(fc2_waybel_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v16_waybel_0(A)
        & l1_orders_2(A) )
     => v1_waybel_0(k2_struct_0(A),A) ) )).

fof(fc2_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & v1_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v1_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_waybel_0(k1_yellow_4(A,B,C),A) ) )).

fof(fc3_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & v2_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v2_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v2_waybel_0(k1_yellow_4(A,B,C),A) ) )).

fof(fc4_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & v13_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v13_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v13_waybel_0(k1_yellow_4(A,B,C),A) ) )).

fof(fc5_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k3_yellow_4(A,B,C)) ) )).

fof(fc6_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & v1_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v1_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_waybel_0(k3_yellow_4(A,B,C),A) ) )).

fof(fc7_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & v2_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v2_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v2_waybel_0(k3_yellow_4(A,B,C),A) ) )).

fof(fc8_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & v12_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v12_waybel_0(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v12_waybel_0(k3_yellow_4(A,B,C),A) ) )).

fof(fraenkel_a_2_1_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(B)
        & v5_orders_2(B)
        & v1_lattice3(B)
        & l1_orders_2(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_1_waybel_9(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = k13_lattice3(B,C,D)
            & r2_hidden(D,k2_struct_0(B)) ) ) ) )).

fof(fraenkel_a_2_3_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(B)
        & v5_orders_2(B)
        & v2_lattice3(B)
        & l1_orders_2(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_3_waybel_9(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = k12_lattice3(B,C,D)
            & r2_hidden(D,k2_struct_0(B)) ) ) ) )).

fof(fraenkel_a_3_1_yellow_4,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
        & m1_subset_1(D,u1_struct_0(B)) )
     => ( r2_hidden(A,a_3_1_yellow_4(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(B))
            & A = k10_lattice3(B,D,E)
            & r2_hidden(E,C) ) ) ) )).

fof(fraenkel_a_3_3_yellow_4,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
        & m1_subset_1(D,u1_struct_0(B)) )
     => ( r2_hidden(A,a_3_3_yellow_4(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(B))
            & A = k11_lattice3(B,D,E)
            & r2_hidden(E,C) ) ) ) )).

fof(redefinition_k2_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_yellow_4(A,B,C) = k1_yellow_4(A,B,C) ) )).

fof(redefinition_k4_yellow_4,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => k4_yellow_4(A,B,C) = k3_yellow_4(A,B,C) ) )).

fof(t15_yellow_4,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k1_yellow_4(A,k6_domain_1(u1_struct_0(A),C),B) = a_3_1_yellow_4(A,B,C) ) ) ) )).

fof(t1_waybel_9,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_orders_2(C) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & l1_orders_2(D) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                         => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                              & g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(D),u1_orders_2(D))
                              & E = F
                              & v5_orders_3(E,A,B) )
                           => v5_orders_3(F,C,D) ) ) ) ) ) ) ) )).

fof(t2_waybel_9,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_orders_2(C) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & l1_orders_2(D) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                         => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                              & g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(D),u1_orders_2(D))
                              & E = F
                              & v5_waybel_0(E,A,B) )
                           => v5_waybel_0(F,C,D) ) ) ) ) ) ) ) )).

fof(t3_waybel_9,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                 => ( ( u1_struct_0(A) = u1_struct_0(B)
                      & C = D
                      & m1_setfam_1(C,u1_struct_0(A)) )
                   => m1_setfam_1(D,u1_struct_0(B)) ) ) ) ) ) )).

fof(t42_yellow_4,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_yellow_4(A,k6_domain_1(u1_struct_0(A),C),B) = a_3_3_yellow_4(A,B,C) ) ) ) )).

fof(t4_waybel_9,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k6_waybel_0(A,B) = k2_yellow_4(A,k6_domain_1(u1_struct_0(A),B),k2_struct_0(A)) ) ) )).

fof(t5_waybel_9,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k5_waybel_0(A,B) = k4_yellow_4(A,k6_domain_1(u1_struct_0(A),B),k2_struct_0(A)) ) ) )).

fof(t6_waybel_9,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_waybel_0(A,B)) = k6_domain_1(u1_struct_0(A),B) ) ) )).

%------------------------------------------------------------------------------
