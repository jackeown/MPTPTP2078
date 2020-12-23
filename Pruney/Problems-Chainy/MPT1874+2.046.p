%------------------------------------------------------------------------------
% File     : MPT1874+2.046 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 046 of t42_tex_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   1 unit)
%            Number of atoms       :   34 (   5 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   30 (   6   ~;   0   |;   7   &)
%                                         (   2 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   0 constant; 1-3 arity)
%            Number of variables   :   18 (   0 sgn;  18   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t63_subset_1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(d3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(fc5_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) )).

fof(dt_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) )).

fof(redefinition_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) )).

fof(t41_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) )).

fof(t42_tex_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) )).

%------------------------------------------------------------------------------
