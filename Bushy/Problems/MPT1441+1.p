%------------------------------------------------------------------------------
% File     : MPT1441+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : filter_1__t36_filter_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   57 (  15 unit)
%            Number of atoms       :  240 (  21 equality)
%            Maximal formula depth :   19 (   6 average)
%            Number of connectives :  218 (  35   ~;   1   |; 123   &)
%                                         (   1 <=>;  58  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   22 (   1 propositional; 0-3 arity)
%            Number of functors    :   20 (   2 constant; 0-4 arity)
%            Number of variables   :  124 (   0 sgn; 119   !;   5   ?)
%            Maximal term depth    :    5 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t36_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( k3_lattices(k7_filter_1(A,B),k9_filter_1(A,B,C,E),k9_filter_1(A,B,D,F)) = k9_filter_1(A,B,k3_lattices(A,C,D),k3_lattices(B,E,F))
                            & k4_lattices(k7_filter_1(A,B),k9_filter_1(A,B,C,E),k9_filter_1(A,B,D,F)) = k9_filter_1(A,B,k4_lattices(A,C,D),k4_lattices(B,E,F)) ) ) ) ) ) ) ) )).

fof(dt_k1_funct_1,axiom,(
    $true )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(free_g3_lattices,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ! [D,E,F] :
          ( g3_lattices(A,B,C) = g3_lattices(D,E,F)
         => ( A = D
            & B = E
            & C = F ) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(abstractness_v3_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( v3_lattices(A)
       => A = g3_lattices(u1_struct_0(A),u2_lattices(A),u1_lattices(A)) ) ) )).

fof(existence_l1_lattices,axiom,(
    ? [A] : l1_lattices(A) )).

fof(existence_l1_struct_0,axiom,(
    ? [A] : l1_struct_0(A) )).

fof(existence_l2_lattices,axiom,(
    ? [A] : l2_lattices(A) )).

fof(dt_g3_lattices,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ( v3_lattices(g3_lattices(A,B,C))
        & l3_lattices(g3_lattices(A,B,C)) ) ) )).

fof(dt_k1_binop_1,axiom,(
    $true )).

fof(dt_k1_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k1_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(dt_k2_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k3_funct_4,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k3_funct_4(A,B))
        & v1_funct_1(k3_funct_4(A,B)) ) ) )).

fof(dt_k4_tarski,axiom,(
    $true )).

fof(dt_l1_lattices,axiom,(
    ! [A] :
      ( l1_lattices(A)
     => l1_struct_0(A) ) )).

fof(dt_l1_struct_0,axiom,(
    $true )).

fof(dt_l2_lattices,axiom,(
    ! [A] :
      ( l2_lattices(A)
     => l1_struct_0(A) ) )).

fof(dt_u1_lattices,axiom,(
    ! [A] :
      ( l1_lattices(A)
     => ( v1_funct_1(u1_lattices(A))
        & v1_funct_2(u1_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & m1_subset_1(u1_lattices(A),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A)))) ) ) )).

fof(dt_u2_lattices,axiom,(
    ! [A] :
      ( l2_lattices(A)
     => ( v1_funct_1(u2_lattices(A))
        & v1_funct_2(u2_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & m1_subset_1(u2_lattices(A),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A)))) ) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) )).

fof(d1_lattices,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k1_lattices(A,B,C) = k4_binop_1(u1_struct_0(A),u2_lattices(A),B,C) ) ) ) )).

fof(d2_lattices,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k2_lattices(A,B,C) = k4_binop_1(u1_struct_0(A),u1_lattices(A),B,C) ) ) ) )).

fof(commutativity_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) )).

fof(commutativity_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) )).

fof(existence_l3_lattices,axiom,(
    ? [A] : l3_lattices(A) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(redefinition_k1_domain_1,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => k1_domain_1(A,B,C,D) = k4_tarski(C,D) ) )).

fof(redefinition_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) )).

fof(redefinition_k4_binop_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & m1_subset_1(C,A)
        & m1_subset_1(D,A) )
     => k4_binop_1(A,B,C,D) = k1_binop_1(B,C,D) ) )).

fof(redefinition_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) )).

fof(redefinition_k6_filter_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(B,B),B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
     => k6_filter_1(A,B,C,D) = k3_funct_4(C,D) ) )).

fof(redefinition_k9_filter_1,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B)
        & m1_subset_1(C,u1_struct_0(A))
        & m1_subset_1(D,u1_struct_0(B)) )
     => k9_filter_1(A,B,C,D) = k4_tarski(C,D) ) )).

fof(dt_k1_domain_1,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => m1_subset_1(k1_domain_1(A,B,C,D),k2_zfmisc_1(A,B)) ) )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k4_binop_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & m1_subset_1(C,A)
        & m1_subset_1(D,A) )
     => m1_subset_1(k4_binop_1(A,B,C,D),A) ) )).

fof(dt_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k6_filter_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(B,B),B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
     => ( v1_funct_1(k6_filter_1(A,B,C,D))
        & v1_funct_2(k6_filter_1(A,B,C,D),k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B))
        & m1_subset_1(k6_filter_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B)))) ) ) )).

fof(dt_k7_filter_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) )).

fof(dt_k9_filter_1,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B)
        & m1_subset_1(C,u1_struct_0(A))
        & m1_subset_1(D,u1_struct_0(B)) )
     => m1_subset_1(k9_filter_1(A,B,C,D),u1_struct_0(k7_filter_1(A,B))) ) )).

fof(dt_l3_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(dt_u1_struct_0,axiom,(
    $true )).

fof(cc1_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(d7_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l3_lattices(B) )
         => k7_filter_1(A,B) = g3_lattices(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)),k6_filter_1(u1_struct_0(A),u1_struct_0(B),u2_lattices(A),u2_lattices(B)),k6_filter_1(u1_struct_0(A),u1_struct_0(B),u1_lattices(A),u1_lattices(B))) ) ) )).

fof(t22_filter_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => ! [E] :
                      ( m1_subset_1(E,B)
                     => ! [F] :
                          ( m1_subset_1(F,B)
                         => ! [G] :
                              ( ( v1_funct_1(G)
                                & v1_funct_2(G,k2_zfmisc_1(A,A),A)
                                & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                             => ! [H] :
                                  ( ( v1_funct_1(H)
                                    & v1_funct_2(H,k2_zfmisc_1(B,B),B)
                                    & m1_subset_1(H,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                                 => k4_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,G,H),k1_domain_1(A,B,C,E),k1_domain_1(A,B,D,F)) = k1_domain_1(A,B,k4_binop_1(A,G,C,D),k4_binop_1(B,H,E,F)) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
