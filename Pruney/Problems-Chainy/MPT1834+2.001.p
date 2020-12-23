%------------------------------------------------------------------------------
% File     : MPT1834+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t150_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :  136 (   2 equality)
%            Maximal formula depth :   23 (  17 average)
%            Number of connectives :  152 (  23   ~;   1   |;  90   &)
%                                         (   5 <=>;  33  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-4 arity)
%            Number of functors    :    7 (   0 constant; 1-6 arity)
%            Number of variables   :   37 (   0 sgn;  37   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(redefinition_r2_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) )).

fof(d13_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                         => ( ( r1_tsep_1(C,D)
                              | r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F)) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                               => ( G = k10_tmap_1(A,B,C,D,E,F)
                                <=> ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,G),E)
                                    & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,G),F) ) ) ) ) ) ) ) ) ) ) )).

fof(dt_k10_tmap_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) )).

fof(t135_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) )
                         => ( ( v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),B,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                              & v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),u1_struct_0(C),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),C,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                              & v5_pre_topc(E,k1_tsep_1(A,B,C),D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) )).

fof(t145_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( r4_tsep_1(A,C,D)
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) )).

fof(t85_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ( r1_tsep_1(B,C)
                  & r4_tsep_1(A,B,C) )
              <=> r3_tsep_1(A,B,C) ) ) ) ) )).

fof(t150_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(B),u1_struct_0(D))
                            & v5_pre_topc(E,B,D)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                                & v5_pre_topc(F,C,D)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                             => ( v1_funct_1(k10_tmap_1(A,D,B,C,E,F))
                                & v1_funct_2(k10_tmap_1(A,D,B,C,E,F),u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                                & v5_pre_topc(k10_tmap_1(A,D,B,C,E,F),k1_tsep_1(A,B,C),D)
                                & m1_subset_1(k10_tmap_1(A,D,B,C,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
