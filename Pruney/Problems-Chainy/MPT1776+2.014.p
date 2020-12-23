%------------------------------------------------------------------------------
% File     : MPT1776+2.014 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 014 of t87_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   1 unit)
%            Number of atoms       :   88 (   4 equality)
%            Maximal formula depth :   18 (   9 average)
%            Number of connectives :   93 (  15   ~;   1   |;  35   &)
%                                         (   4 <=>;  38  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-4 arity)
%            Number of functors    :    4 (   0 constant; 1-5 arity)
%            Number of variables   :   37 (   0 sgn;  37   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(dt_m1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) )).

fof(t19_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) )).

fof(t1_tsep_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(t7_tsep_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) )).

fof(t81_tmap_1,axiom,(
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
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) )).

fof(t86_tmap_1,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) )).

fof(t87_tmap_1,conjecture,(
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
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                     => ( ( v1_tsep_1(C,B)
                          & m1_pre_topc(C,B)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,A,E,F)
                                  <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
