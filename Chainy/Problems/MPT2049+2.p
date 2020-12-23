%------------------------------------------------------------------------------
% File     : MPT2049+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow19__t8_yellow19.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 4506 ( 468 unit)
%            Number of atoms       : 28364 (2903 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 28212 (4354   ~; 166   |;13381   &)
%                                         ( 987 <=>;9324  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  322 (   1 propositional; 0-6 arity)
%            Number of functors    :  447 (   9 constant; 0-10 arity)
%            Number of variables   : 13220 (   9 sgn;12535   !; 685   ?)
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
include('Axioms/MPT032+2.ax').
%------------------------------------------------------------------------------
fof(d1_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_yellow19(A,B) = a_2_0_yellow19(A,B) ) ) )).

fof(d2_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_yellow19(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                    & C = k2_relset_1(u1_struct_0(k4_waybel_9(A,B,D)),u1_struct_0(A),u1_waybel_0(A,k4_waybel_9(A,B,D))) ) ) ) ) ) )).

fof(dt_k1_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) )).

fof(dt_k5_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k5_waybel_9(A,B,C),A)
        & m2_yellow_6(k5_waybel_9(A,B,C),A,B) ) ) )).

fof(dt_m1_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow19(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(dt_o_2_3_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_3_yellow19(A,B),k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B))) ) )).

fof(existence_m1_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ? [C] : m1_yellow19(C,A,B) ) )).

fof(fc1_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k1_yellow19(A,B))
        & v1_subset_1(k1_yellow19(A,B),u1_struct_0(k3_yellow_1(k2_struct_0(A))))
        & v2_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A)))
        & v13_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) )).

fof(fc26_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_finset_1(B) )
     => ( v1_relat_1(k7_relat_1(B,A))
        & v1_finset_1(k7_relat_1(B,A)) ) ) )).

fof(fc27_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k7_relat_1(B,A))
        & v1_finset_1(k7_relat_1(B,A)) ) ) )).

fof(fc8_yellow_6,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v7_waybel_0(k3_yellow_1(A)) ) )).

fof(fraenkel_a_2_0_yellow19,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow19(B,C))
      <=> ? [D] :
            ( m1_connsp_2(D,B,C)
            & A = D ) ) ) )).

fof(redefinition_k5_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => k5_waybel_9(A,B,C) = k4_waybel_9(A,B,C) ) )).

fof(t2_yellow19,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) )).

fof(t3_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(C,k1_yellow19(A,B))
            <=> m1_connsp_2(C,A,B) ) ) ) )).

fof(t4_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
             => ( r2_waybel_7(A,C,B)
              <=> r1_tarski(k1_yellow19(A,B),C) ) ) ) ) )).

fof(t5_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) )).

fof(t6_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,B)
                 => ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                        & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                     => ( r2_waybel_7(A,D,C)
                       => r2_hidden(B,D) ) ) ) ) ) ) ) )).

fof(t7_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(A),u1_waybel_0(A,k4_waybel_9(A,B,C))),A,B) ) ) ) )).

fof(t8_yellow19,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( r2_hidden(D,k2_relset_1(u1_struct_0(k5_waybel_9(A,B,C)),u1_struct_0(A),u1_waybel_0(A,k5_waybel_9(A,B,C))))
                <=> ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,C,E)
                      & D = k2_waybel_0(A,B,E) ) ) ) ) ) )).

%------------------------------------------------------------------------------
