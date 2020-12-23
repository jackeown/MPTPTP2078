%------------------------------------------------------------------------------
% File     : MPT1620+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_1__t28_yellow_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   47 (  18 unit)
%            Number of atoms       :  156 (  30 equality)
%            Maximal formula depth :   35 (   5 average)
%            Number of connectives :  118 (   9   ~;   1   |;  61   &)
%                                         (  13 <=>;  34  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   17 (   1 propositional; 0-3 arity)
%            Number of functors    :   18 (   2 constant; 0-2 arity)
%            Number of variables   :   86 (   0 sgn;  78   !;   8   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t28_yellow_1,conjecture,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k1_funct_2(A,u1_struct_0(B)) = u1_struct_0(k6_yellow_1(A,B)) ) )).

fof(abstractness_v1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(d13_pralg_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( C = k12_pralg_1(A,B)
          <=> ! [D] :
                ~ ( r2_hidden(D,A)
                  & ! [E] :
                      ( l1_struct_0(E)
                     => ~ ( E = k1_funct_1(B,D)
                          & k1_funct_1(C,D) = u1_struct_0(E) ) ) ) ) ) ) )).

fof(d2_funct_2,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(d4_partfun1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) )).

fof(d4_yellow_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v1_yellow_1(B) )
     => ! [C] :
          ( ( v1_orders_2(C)
            & l1_orders_2(C) )
         => ( C = k5_yellow_1(A,B)
          <=> ( u1_struct_0(C) = k4_card_3(k12_pralg_1(A,B))
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(C))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(C))
                     => ( r2_hidden(D,k4_card_3(k12_pralg_1(A,B)))
                       => ( r1_orders_2(C,D,E)
                        <=> ? [F] :
                              ( v1_relat_1(F)
                              & v1_funct_1(F)
                              & ? [G] :
                                  ( v1_relat_1(G)
                                  & v1_funct_1(G)
                                  & F = D
                                  & G = E
                                  & ! [H] :
                                      ~ ( r2_hidden(H,A)
                                        & ! [I] :
                                            ( l1_orders_2(I)
                                           => ! [J] :
                                                ( m1_subset_1(J,u1_struct_0(I))
                                               => ! [K] :
                                                    ( m1_subset_1(K,u1_struct_0(I))
                                                   => ~ ( I = k1_funct_1(B,H)
                                                        & J = k1_funct_1(F,H)
                                                        & K = k1_funct_1(G,H)
                                                        & r1_orders_2(I,J,K) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

fof(d5_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k4_card_3(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( v1_relat_1(D)
                  & v1_funct_1(D)
                  & C = D
                  & k1_relat_1(D) = k1_relat_1(A)
                  & ! [E] :
                      ( r2_hidden(E,k1_relat_1(A))
                     => r2_hidden(k1_funct_1(D,E),k1_funct_1(A,E)) ) ) ) ) ) )).

fof(d5_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) )).

fof(d5_yellow_1,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) )).

fof(dt_g1_orders_2,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) )).

fof(dt_k12_pralg_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ( v1_relat_1(k12_pralg_1(A,B))
        & v4_relat_1(k12_pralg_1(A,B),A)
        & v1_funct_1(k12_pralg_1(A,B))
        & v1_partfun1(k12_pralg_1(A,B),A) ) ) )).

fof(dt_k1_funct_1,axiom,(
    $true )).

fof(dt_k1_funct_2,axiom,(
    $true )).

fof(dt_k1_relat_1,axiom,(
    $true )).

fof(dt_k1_tarski,axiom,(
    $true )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k2_funcop_1,axiom,(
    $true )).

fof(dt_k2_relat_1,axiom,(
    $true )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k4_card_3,axiom,(
    $true )).

fof(dt_k5_yellow_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v1_yellow_1(B) )
     => ( v1_orders_2(k5_yellow_1(A,B))
        & l1_orders_2(k5_yellow_1(A,B)) ) ) )).

fof(dt_k6_yellow_1,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => ( v1_orders_2(k6_yellow_1(A,B))
        & l1_orders_2(k6_yellow_1(A,B)) ) ) )).

fof(dt_k7_funcop_1,axiom,(
    ! [A,B] :
      ( v1_funct_1(k7_funcop_1(A,B))
      & v1_funct_2(k7_funcop_1(A,B),A,k1_tarski(B))
      & m1_subset_1(k7_funcop_1(A,B),k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(dt_l1_struct_0,axiom,(
    $true )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(dt_u1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) )).

fof(dt_u1_struct_0,axiom,(
    $true )).

fof(existence_l1_orders_2,axiom,(
    ? [A] : l1_orders_2(A) )).

fof(existence_l1_struct_0,axiom,(
    ? [A] : l1_struct_0(A) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(free_g1_orders_2,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) )).

fof(redefinition_k7_funcop_1,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) )).

fof(t13_funcop_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(B,A)
     => k1_funct_1(k2_funcop_1(A,C),B) = C ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

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

%------------------------------------------------------------------------------
