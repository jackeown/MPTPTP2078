%------------------------------------------------------------------------------
% File     : MPT1704+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t13_tmap_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3337 ( 439 unit)
%            Number of atoms       : 17797 (2444 equality)
%            Maximal formula depth :   35 (   7 average)
%            Number of connectives : 16809 (2349   ~; 128   |;7324   &)
%                                         ( 737 <=>;6271  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  236 (   1 propositional; 0-6 arity)
%            Number of functors    :  323 (   9 constant; 0-10 arity)
%            Number of variables   : 9758 (   9 sgn;9298   !; 460   ?)
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
%------------------------------------------------------------------------------
fof(d1_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) )).

fof(dt_k1_tmap_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) )).

fof(rc1_borsuk_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & v1_pre_topc(B)
          & v2_pre_topc(B)
          & v1_borsuk_1(B,A) ) ) )).

fof(rc2_borsuk_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v1_pre_topc(B)
          & v2_pre_topc(B)
          & v1_borsuk_1(B,A) ) ) )).

fof(t10_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ( ( m1_subset_1(C,k1_zfmisc_1(D))
                               => r1_funct_2(k4_subset_1(A,C,D),B,D,B,k1_tmap_1(A,B,C,D,E,F),F) )
                              & ( r1_funct_2(k4_subset_1(A,C,D),B,D,B,k1_tmap_1(A,B,C,D,E,F),F)
                               => m1_subset_1(C,k1_zfmisc_1(D)) )
                              & ( m1_subset_1(D,k1_zfmisc_1(C))
                               => r1_funct_2(k4_subset_1(A,C,D),B,C,B,k1_tmap_1(A,B,C,D,E,F),E) )
                              & ( r1_funct_2(k4_subset_1(A,C,D),B,C,B,k1_tmap_1(A,B,C,D,E,F),E)
                               => m1_subset_1(D,k1_zfmisc_1(C)) ) ) ) ) ) ) ) ) ) )).

fof(t11_tmap_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) )).

fof(t11_tsep_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) )).

fof(t12_tmap_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) )).

fof(t13_tmap_1,conjecture,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> ( v1_borsuk_1(C,A)
                    & m1_pre_topc(C,A) ) ) ) ) ) ) )).

fof(t1_tsep_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(t6_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ( r1_subset_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                           => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                              & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                              & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) )).

fof(t7_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k4_subset_1(A,C,D),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,C,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [G] :
                              ( ( v1_funct_1(G)
                                & v1_funct_2(G,D,B)
                                & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( ( k2_partfun1(k4_subset_1(A,C,D),B,E,C) = F
                                  & k2_partfun1(k4_subset_1(A,C,D),B,E,D) = G )
                               => r2_funct_2(k4_subset_1(A,C,D),B,E,k1_tmap_1(A,B,C,D,F,G)) ) ) ) ) ) ) ) ) )).

fof(t8_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => r1_funct_2(k4_subset_1(A,C,D),B,k4_subset_1(A,D,C),B,k1_tmap_1(A,B,C,D,E,F),k1_tmap_1(A,B,D,C,F,E)) ) ) ) ) ) ) ) )).

fof(t9_tmap_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( ~ v1_xboole_0(E)
                        & m1_subset_1(E,k1_zfmisc_1(A)) )
                     => ! [F] :
                          ( ( ~ v1_xboole_0(F)
                            & m1_subset_1(F,k1_zfmisc_1(A)) )
                         => ! [G] :
                              ( ( ~ v1_xboole_0(G)
                                & m1_subset_1(G,k1_zfmisc_1(A)) )
                             => ( ( F = k4_subset_1(A,C,D)
                                  & G = k4_subset_1(A,D,E) )
                               => ! [H] :
                                    ( ( v1_funct_1(H)
                                      & v1_funct_2(H,C,B)
                                      & m1_subset_1(H,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                                   => ! [I] :
                                        ( ( v1_funct_1(I)
                                          & v1_funct_2(I,D,B)
                                          & m1_subset_1(I,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                                       => ! [J] :
                                            ( ( v1_funct_1(J)
                                              & v1_funct_2(J,E,B)
                                              & m1_subset_1(J,k1_zfmisc_1(k2_zfmisc_1(E,B))) )
                                           => ( ( k2_partfun1(C,B,H,k9_subset_1(A,C,D)) = k2_partfun1(D,B,I,k9_subset_1(A,C,D))
                                                & k2_partfun1(D,B,I,k9_subset_1(A,D,E)) = k2_partfun1(E,B,J,k9_subset_1(A,D,E))
                                                & k2_partfun1(C,B,H,k9_subset_1(A,C,E)) = k2_partfun1(E,B,J,k9_subset_1(A,C,E)) )
                                             => ! [K] :
                                                  ( ( v1_funct_1(K)
                                                    & v1_funct_2(K,F,B)
                                                    & m1_subset_1(K,k1_zfmisc_1(k2_zfmisc_1(F,B))) )
                                                 => ! [L] :
                                                      ( ( v1_funct_1(L)
                                                        & v1_funct_2(L,G,B)
                                                        & m1_subset_1(L,k1_zfmisc_1(k2_zfmisc_1(G,B))) )
                                                     => ( ( r1_funct_2(F,B,k4_subset_1(A,C,D),B,K,k1_tmap_1(A,B,C,D,H,I))
                                                          & r1_funct_2(G,B,k4_subset_1(A,D,E),B,L,k1_tmap_1(A,B,D,E,I,J)) )
                                                       => r1_funct_2(k4_subset_1(A,F,E),B,k4_subset_1(A,C,G),B,k1_tmap_1(A,B,F,E,K,J),k1_tmap_1(A,B,C,G,H,L)) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
