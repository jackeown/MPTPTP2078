%------------------------------------------------------------------------------
% File     : MPT1909+2.024 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 024 of t77_tex_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   13 (   1 unit)
%            Number of atoms       :   68 (   7 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :   64 (   9   ~;   1   |;  21   &)
%                                         (   4 <=>;  29  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   16 (   0 propositional; 1-3 arity)
%            Number of functors    :    8 (   0 constant; 1-4 arity)
%            Number of variables   :   34 (   0 sgn;  34   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t63_subset_1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t39_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) )).

fof(redefinition_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) )).

fof(t1_tsep_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(d8_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) )).

fof(t46_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) )).

fof(t76_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) )).

fof(t77_tex_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
