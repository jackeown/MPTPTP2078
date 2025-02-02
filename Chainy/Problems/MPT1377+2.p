%------------------------------------------------------------------------------
% File     : MPT1377+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : compts_1__t33_compts_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2512 ( 420 unit)
%            Number of atoms       : 10951 (1939 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 9848 (1409   ~; 116   |;3913   &)
%                                         ( 470 <=>;3940  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  161 (   1 propositional; 0-4 arity)
%            Number of functors    :  196 (   9 constant; 0-10 arity)
%            Number of variables   : 7116 (   9 sgn;6819   !; 297   ?)
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

fof(cc2_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_compts_1(B,A)
           => v4_pre_topc(B,A) ) ) ) )).

fof(cc3_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v8_struct_0(A)
          & v2_pre_topc(A) )
       => ( v2_pre_topc(A)
          & v1_compts_1(A) ) ) ) )).

fof(cc3_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_funct_2(C,A,B)
              & v1_finset_1(C) ) ) ) ) )).

fof(cc3_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v11_pre_topc(A)
       => ( v7_pre_topc(A)
          & v9_pre_topc(A) ) ) ) )).

fof(cc4_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_finset_1(B)
           => v2_compts_1(B,A) ) ) ) )).

fof(cc4_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v7_pre_topc(A)
          & v9_pre_topc(A) )
       => v11_pre_topc(A) ) ) )).

fof(cc5_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_struct_0(A)
       => v8_pre_topc(A) ) ) )).

fof(cc5_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v12_pre_topc(A)
       => ( v7_pre_topc(A)
          & v10_pre_topc(A) ) ) ) )).

fof(cc6_compts_1,axiom,(
    ! [A] :
      ( ( v8_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v8_pre_topc(B) ) ) )).

fof(cc6_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v7_pre_topc(A)
          & v10_pre_topc(A) )
       => v12_pre_topc(A) ) ) )).

fof(cc7_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v7_pre_topc(A)
       => v6_pre_topc(A) ) ) )).

fof(cc8_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v8_pre_topc(A)
       => v7_pre_topc(A) ) ) )).

fof(d16_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v8_pre_topc(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( B != C
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ! [E] :
                            ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                           => ~ ( v3_pre_topc(D,A)
                                & v3_pre_topc(E,A)
                                & r2_hidden(B,D)
                                & r2_hidden(C,E)
                                & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) )).

fof(d1_funct_4,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( C = k1_funct_4(A,B)
              <=> ( k1_relat_1(C) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B))
                  & ! [D] :
                      ( r2_hidden(D,k2_xboole_0(k1_relat_1(A),k1_relat_1(B)))
                     => ( ( r2_hidden(D,k1_relat_1(B))
                         => k1_funct_1(C,D) = k1_funct_1(B,D) )
                        & ( ~ r2_hidden(D,k1_relat_1(B))
                         => k1_funct_1(C,D) = k1_funct_1(A,D) ) ) ) ) ) ) ) ) )).

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

fof(d5_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v9_pre_topc(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v4_pre_topc(C,A)
                    & r2_hidden(B,k3_subset_1(u1_struct_0(A),C))
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ! [E] :
                            ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                           => ~ ( v3_pre_topc(D,A)
                                & v3_pre_topc(E,A)
                                & r2_hidden(B,D)
                                & r1_tarski(C,E)
                                & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) )).

fof(d6_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v10_pre_topc(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & C != k1_xboole_0
                    & v4_pre_topc(B,A)
                    & v4_pre_topc(C,A)
                    & r1_xboole_0(B,C)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ! [E] :
                            ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                           => ~ ( v3_pre_topc(D,A)
                                & v3_pre_topc(E,A)
                                & r1_tarski(B,D)
                                & r1_tarski(C,E)
                                & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) )).

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

fof(dt_k1_funct_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k1_funct_3(A))
        & v1_funct_1(k1_funct_3(A)) ) ) )).

fof(dt_k1_funct_4,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k1_funct_4(A,B))
        & v1_funct_1(k1_funct_4(A,B)) ) ) )).

fof(dt_k2_funct_3,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_funct_3(A,B,C))
        & v1_funct_2(k2_funct_3(A,B,C),k1_zfmisc_1(A),k1_zfmisc_1(B))
        & m1_subset_1(k2_funct_3(A,B,C),k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(A),k1_zfmisc_1(B)))) ) ) )).

fof(dt_o_2_0_compts_1,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_0_compts_1(A,B),B) ) )).

fof(dt_o_2_1_compts_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_1_compts_1(A,B),B) ) )).

fof(dt_o_3_0_compts_1,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(o_3_0_compts_1(A,B,C),k9_subset_1(u1_struct_0(A),k6_setfam_1(u1_struct_0(A),C),k5_setfam_1(u1_struct_0(A),B))) ) )).

fof(dt_o_3_1_compts_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(o_3_1_compts_1(A,B,C),k9_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k6_setfam_1(u1_struct_0(A),C))) ) )).

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

fof(fc23_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(A) )
     => v1_finset_1(k10_relat_1(A,B)) ) )).

fof(fc24_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v1_finset_1(B) )
     => ( v1_relat_1(k1_funct_4(A,B))
        & v1_funct_1(k1_funct_4(A,B))
        & v1_finset_1(k1_funct_4(A,B)) ) ) )).

fof(fc2_finset_1,axiom,(
    ! [A,B] : v1_finset_1(k2_tarski(A,B)) )).

fof(fc5_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) )).

fof(idempotence_k1_funct_4,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => k1_funct_4(A,A) = A ) )).

fof(rc1_compts_1,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v2_pre_topc(A)
      & v8_pre_topc(A) ) )).

fof(rc2_compts_1,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v8_struct_0(A)
      & v1_pre_topc(A)
      & v2_pre_topc(A) ) )).

fof(rc2_pre_topc,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v1_pre_topc(A)
      & v2_pre_topc(A) ) )).

fof(rc3_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v2_compts_1(B,A) ) ) )).

fof(rc4_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
          & ~ v1_xboole_0(B)
          & v1_tops_2(B,A) ) ) )).

fof(rc5_finset_1,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_finset_1(C) ) )).

fof(rc9_pre_topc,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v2_pre_topc(A)
      & v7_pre_topc(A) ) )).

fof(redefinition_k2_funct_3,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_funct_3(A,B,C) = k1_funct_3(C) ) )).

fof(s2_wellord2__e7_20__compts_1,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E,F] :
                  ~ ( r2_hidden(E,u1_pre_topc(A))
                    & r2_hidden(F,u1_pre_topc(A))
                    & ? [G] :
                        ( m1_subset_1(G,k1_zfmisc_1(u1_struct_0(A)))
                        & ? [H] :
                            ( m1_subset_1(H,k1_zfmisc_1(u1_struct_0(A)))
                            & E = G
                            & F = H
                            & v3_pre_topc(G,A)
                            & v3_pre_topc(H,A)
                            & r2_hidden(C,G)
                            & r2_hidden(D,H)
                            & k9_subset_1(u1_struct_0(A),G,H) = k1_xboole_0 ) ) ) )
       => ? [D] :
            ( v1_relat_1(D)
            & v1_funct_1(D)
            & ? [E] :
                ( v1_relat_1(E)
                & v1_funct_1(E)
                & k1_relat_1(D) = B
                & k1_relat_1(E) = B
                & ! [F] :
                    ( r2_hidden(F,B)
                   => ? [I] :
                        ( m1_subset_1(I,k1_zfmisc_1(u1_struct_0(A)))
                        & ? [J] :
                            ( m1_subset_1(J,k1_zfmisc_1(u1_struct_0(A)))
                            & k1_funct_1(D,F) = I
                            & k1_funct_1(E,F) = J
                            & v3_pre_topc(I,A)
                            & v3_pre_topc(J,A)
                            & r2_hidden(C,I)
                            & r2_hidden(F,J)
                            & k9_subset_1(u1_struct_0(A),I,J) = k1_xboole_0 ) ) ) ) ) ) ) )).

fof(s2_wellord2__e9_27__compts_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E,F] :
                  ~ ( r2_hidden(E,u1_pre_topc(A))
                    & r2_hidden(F,u1_pre_topc(A))
                    & ? [G] :
                        ( m1_subset_1(G,k1_zfmisc_1(u1_struct_0(A)))
                        & ? [H] :
                            ( m1_subset_1(H,k1_zfmisc_1(u1_struct_0(A)))
                            & E = G
                            & F = H
                            & v3_pre_topc(G,A)
                            & v3_pre_topc(H,A)
                            & r2_hidden(D,G)
                            & r1_tarski(C,H)
                            & k9_subset_1(u1_struct_0(A),G,H) = k1_xboole_0 ) ) ) )
       => ? [D] :
            ( v1_relat_1(D)
            & v1_funct_1(D)
            & ? [E] :
                ( v1_relat_1(E)
                & v1_funct_1(E)
                & k1_relat_1(D) = B
                & k1_relat_1(E) = B
                & ! [F] :
                    ( r2_hidden(F,B)
                   => ? [I] :
                        ( m1_subset_1(I,k1_zfmisc_1(u1_struct_0(A)))
                        & ? [J] :
                            ( m1_subset_1(J,k1_zfmisc_1(u1_struct_0(A)))
                            & k1_funct_1(D,F) = I
                            & k1_funct_1(E,F) = J
                            & v3_pre_topc(I,A)
                            & v3_pre_topc(J,A)
                            & r2_hidden(F,I)
                            & r1_tarski(C,J)
                            & k9_subset_1(u1_struct_0(A),I,J) = k1_xboole_0 ) ) ) ) ) ) ) )).

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

fof(t12_funct_4,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ~ r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k1_funct_4(C,B),A) = k1_funct_1(C,A) ) ) ) )).

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

fof(t14_compts_1,axiom,(
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

fof(t14_funct_4,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k1_funct_4(C,B),A) = k1_funct_1(B,A) ) ) ) )).

fof(t15_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v8_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_compts_1(B,A)
             => ( B = k1_xboole_0
                | ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ ( r2_hidden(C,k3_subset_1(u1_struct_0(A),B))
                        & ! [D] :
                            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                           => ! [E] :
                                ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                               => ~ ( v3_pre_topc(D,A)
                                    & v3_pre_topc(E,A)
                                    & r2_hidden(C,D)
                                    & r1_tarski(B,E)
                                    & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) ) ) )).

fof(t16_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) )).

fof(t16_funct_3,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k1_zfmisc_1(k1_relat_1(B)))
       => k9_relat_1(B,k3_tarski(A)) = k3_tarski(k9_relat_1(k1_funct_3(B),A)) ) ) )).

fof(t17_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) )).

fof(t18_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) )).

fof(t18_funct_4,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => r1_tarski(k2_relat_1(k1_funct_4(A,B)),k2_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) )).

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

fof(t19_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & v2_compts_1(C,A) )
               => v2_compts_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) )).

fof(t20_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v8_pre_topc(A)
                  & v2_compts_1(B,A)
                  & v2_compts_1(C,A) )
               => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) )).

fof(t21_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ( v8_pre_topc(A)
          & v1_compts_1(A) )
       => v9_pre_topc(A) ) ) )).

fof(t22_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ( v8_pre_topc(A)
          & v1_compts_1(A) )
       => v10_pre_topc(A) ) ) )).

fof(t23_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( v1_compts_1(A)
                  & v5_pre_topc(C,A,B)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B) )
               => v1_compts_1(B) ) ) ) ) )).

fof(t24_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                 => ( ( v5_pre_topc(D,A,C)
                      & k2_relset_1(u1_struct_0(A),u1_struct_0(C),D) = k2_struct_0(C)
                      & v2_compts_1(B,A) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(A),u1_struct_0(C),D,B),C) ) ) ) ) ) )).

fof(t25_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( v1_compts_1(A)
                  & v8_pre_topc(B)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v5_pre_topc(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v4_pre_topc(D,A)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) )).

fof(t26_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( v1_compts_1(A)
                  & v8_pre_topc(B)
                  & k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B) )
               => v3_tops_2(C,A,B) ) ) ) ) )).

fof(t27_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_finset_1(u1_struct_0(A))
       => v1_compts_1(A) ) ) )).

fof(t28_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( C = D
                   => ( v2_compts_1(C,A)
                    <=> v2_compts_1(D,B) ) ) ) ) ) ) )).

fof(t29_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( m1_pre_topc(E,A)
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                         => ! [G] :
                              ( ( v1_funct_1(G)
                                & v1_funct_2(G,u1_struct_0(E),u1_struct_0(B))
                                & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) )
                             => ( ( k2_xboole_0(k2_struct_0(D),k2_struct_0(E)) = k2_struct_0(A)
                                  & k9_subset_1(u1_struct_0(E),k2_struct_0(D),k2_struct_0(E)) = k6_domain_1(u1_struct_0(A),C)
                                  & v1_compts_1(D)
                                  & v1_compts_1(E)
                                  & v8_pre_topc(A)
                                  & v5_pre_topc(F,D,B)
                                  & v5_pre_topc(G,E,B)
                                  & k1_funct_1(F,C) = k1_funct_1(G,C) )
                               => ( v1_funct_1(k1_funct_4(F,G))
                                  & v1_funct_2(k1_funct_4(F,G),u1_struct_0(A),u1_struct_0(B))
                                  & v5_pre_topc(k1_funct_4(F,G),A,B)
                                  & m1_subset_1(k1_funct_4(F,G),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) )).

fof(t30_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,B)
             => ! [D] :
                  ( m1_pre_topc(D,B)
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( ( v1_funct_1(G)
                                & v1_funct_2(G,u1_struct_0(C),u1_struct_0(A))
                                & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                             => ! [H] :
                                  ( ( v1_funct_1(H)
                                    & v1_funct_2(H,u1_struct_0(D),u1_struct_0(A))
                                    & m1_subset_1(H,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                                 => ( ( k2_xboole_0(k2_struct_0(C),k2_struct_0(D)) = k2_struct_0(B)
                                      & k9_subset_1(u1_struct_0(D),k2_struct_0(C),k2_struct_0(D)) = k7_domain_1(u1_struct_0(B),E,F)
                                      & v1_compts_1(C)
                                      & v1_compts_1(D)
                                      & v8_pre_topc(B)
                                      & v5_pre_topc(G,C,A)
                                      & v5_pre_topc(H,D,A)
                                      & k1_funct_1(G,E) = k1_funct_1(H,E)
                                      & k1_funct_1(G,F) = k1_funct_1(H,F) )
                                   => ( v1_funct_1(k1_funct_4(G,H))
                                      & v1_funct_2(k1_funct_4(G,H),u1_struct_0(B),u1_struct_0(A))
                                      & v5_pre_topc(k1_funct_4(G,H),B,A)
                                      & m1_subset_1(k1_funct_4(G,H),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ) ) ) ) ) ) ) ) )).

fof(t30_funct_3,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k1_zfmisc_1(k2_relat_1(B)))
       => k3_tarski(k9_relat_1(k3_funct_3(B),A)) = k10_relat_1(B,k3_tarski(A)) ) ) )).

fof(t32_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) )).

fof(t33_compts_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_compts_1(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v2_compts_1(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) )).

fof(t33_funct_3,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(k3_funct_3(B),A),k10_relat_1(k1_funct_3(B),A)) ) )).

%------------------------------------------------------------------------------
