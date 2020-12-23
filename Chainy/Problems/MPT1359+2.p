%------------------------------------------------------------------------------
% File     : MPT1359+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : compts_1__t14_compts_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2451 ( 419 unit)
%            Number of atoms       : 10462 (1895 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 9376 (1365   ~; 115   |;3648   &)
%                                         ( 463 <=>;3785  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  154 (   1 propositional; 0-4 arity)
%            Number of functors    :  189 (   9 constant; 0-10 arity)
%            Number of variables   : 6944 (   9 sgn;6665   !; 279   ?)
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
%------------------------------------------------------------------------------
fof(cc1_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v2_compts_1(B,A) ) ) ) )).

fof(d3_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & v1_tops_2(B,A)
                & ! [C] :
                    ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ~ ( r1_tarski(C,B)
                        & m1_setfam_1(C,u1_struct_0(A))
                        & v1_finset_1(C) ) ) ) ) ) ) )).

fof(d3_finset_1,axiom,(
    ! [A] :
      ( v3_finset_1(A)
    <=> ( A != k1_xboole_0
        & ! [B] :
            ~ ( B != k1_xboole_0
              & r1_tarski(B,A)
              & v1_finset_1(B)
              & k1_setfam_1(B) = k1_xboole_0 ) ) ) )).

fof(d7_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_compts_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( m1_setfam_1(C,B)
                    & v1_tops_2(C,A)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                       => ~ ( r1_tarski(D,C)
                            & m1_setfam_1(D,B)
                            & v1_finset_1(D) ) ) ) ) ) ) ) )).

fof(fc14_tops_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) )).

fof(fc19_finset_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_finset_1(A) )
     => v1_finset_1(k1_relat_1(A)) ) )).

fof(fc22_finset_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_finset_1(A) )
     => v1_finset_1(k2_relat_1(A)) ) )).

fof(rc2_pre_topc,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v1_pre_topc(A)
      & v2_pre_topc(A) ) )).

fof(t10_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) )).

fof(t11_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) )).

fof(t12_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) )).

fof(t13_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_compts_1(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( v3_finset_1(B)
                & v2_tops_2(B,A)
                & k6_setfam_1(u1_struct_0(A),B) = k1_xboole_0 ) ) ) ) )).

fof(t14_compts_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_compts_1(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( B != k1_xboole_0
                & v2_tops_2(B,A)
                & k6_setfam_1(u1_struct_0(A),B) = k1_xboole_0
                & ! [C] :
                    ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ~ ( C != k1_xboole_0
                        & r1_tarski(C,B)
                        & v1_finset_1(C)
                        & k6_setfam_1(u1_struct_0(A),C) = k1_xboole_0 ) ) ) ) ) ) )).

fof(t195_orders_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ~ ( v1_finset_1(B)
            & r1_tarski(B,k2_relat_1(A))
            & ! [C] :
                ~ ( r1_tarski(C,k1_relat_1(A))
                  & v1_finset_1(C)
                  & k9_relat_1(A,C) = B ) ) ) )).

%------------------------------------------------------------------------------
