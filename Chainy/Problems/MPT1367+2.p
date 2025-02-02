%------------------------------------------------------------------------------
% File     : MPT1367+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : compts_1__t22_compts_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2475 ( 419 unit)
%            Number of atoms       : 10679 (1916 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 9593 (1389   ~; 116   |;3771   &)
%                                         ( 466 <=>;3851  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  161 (   1 propositional; 0-4 arity)
%            Number of functors    :  193 (   9 constant; 0-10 arity)
%            Number of variables   : 7022 (   9 sgn;6730   !; 292   ?)
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

fof(cc3_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v11_pre_topc(A)
       => ( v7_pre_topc(A)
          & v9_pre_topc(A) ) ) ) )).

fof(cc4_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v7_pre_topc(A)
          & v9_pre_topc(A) )
       => v11_pre_topc(A) ) ) )).

fof(cc5_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v12_pre_topc(A)
       => ( v7_pre_topc(A)
          & v10_pre_topc(A) ) ) ) )).

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

fof(rc2_pre_topc,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v1_pre_topc(A)
      & v2_pre_topc(A) ) )).

fof(rc9_pre_topc,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & ~ v2_struct_0(A)
      & v2_pre_topc(A)
      & v7_pre_topc(A) ) )).

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

fof(t22_compts_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ( v8_pre_topc(A)
          & v1_compts_1(A) )
       => v10_pre_topc(A) ) ) )).

%------------------------------------------------------------------------------
