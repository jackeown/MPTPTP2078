%------------------------------------------------------------------------------
% File     : MPT1876+2.018 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 018 of t44_tex_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   24 (   3 unit)
%            Number of atoms       :   98 (   8 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  100 (  26   ~;   2   |;  35   &)
%                                         (   5 <=>;  32  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   17 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   1 constant; 0-2 arity)
%            Number of variables   :   47 (   0 sgn;  45   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t1_boole,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A )).

fof(fc2_xboole_0,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) )).

fof(l1_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) )).

fof(l3_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) )).

fof(t49_zfmisc_1,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 )).

fof(cc1_subset_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(existence_m2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ? [C] : m2_subset_1(C,A,B) ) )).

fof(redefinition_m2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(dt_m1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) )).

fof(fc7_struct_0,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) )).

fof(t55_pre_topc,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) )).

fof(redefinition_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) )).

fof(cc2_tdlat_3,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) )).

fof(cc2_tex_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) )).

fof(cc6_tdlat_3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) )).

fof(t10_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) )).

fof(t1_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) )).

fof(t34_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) )).

fof(t36_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) )).

fof(t44_tex_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) )).

%------------------------------------------------------------------------------
