%------------------------------------------------------------------------------
% File     : MPT1478+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : lattice3__t11_lattice3.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2844 ( 423 unit)
%            Number of atoms       : 13765 (2114 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 12772 (1851   ~; 116   |;5371   &)
%                                         ( 559 <=>;4875  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  188 (   1 propositional; 0-4 arity)
%            Number of functors    :  238 (   9 constant; 0-10 arity)
%            Number of variables   : 8181 (   9 sgn;7850   !; 331   ?)
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
%------------------------------------------------------------------------------
fof(cc1_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(cc2_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(d10_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,B,D)
                    & r1_orders_2(A,C,D)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r1_orders_2(A,B,E)
                            & r1_orders_2(A,C,E) )
                         => r1_orders_2(A,D,E) ) ) ) ) ) ) ) )).

fof(d11_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,D,B)
                    & r1_orders_2(A,D,C)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r1_orders_2(A,E,B)
                            & r1_orders_2(A,E,C) )
                         => r1_orders_2(A,E,D) ) ) ) ) ) ) ) )).

fof(d1_lattice3,axiom,(
    ! [A,B] :
      ( ( v3_lattices(B)
        & l3_lattices(B) )
     => ( B = k1_lattice3(A)
      <=> ( u1_struct_0(B) = k9_setfam_1(A)
          & ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( k1_binop_1(u2_lattices(B),C,D) = k4_subset_1(A,C,D)
                    & k1_binop_1(u1_lattices(B),C,D) = k9_subset_1(A,C,D) ) ) ) ) ) ) )).

fof(d2_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k3_lattice3(A) = g1_orders_2(u1_struct_0(A),k2_lattice3(A)) ) )).

fof(d3_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) )).

fof(d4_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) )).

fof(d5_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) )).

fof(d6_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_lattice3(A,B) = B ) ) )).

fof(d7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k7_lattice3(A)))
         => k9_lattice3(A,B) = B ) ) )).

fof(dt_k1_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) )).

fof(dt_k2_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_partfun1(k2_lattice3(A),u1_struct_0(A))
        & v1_relat_2(k2_lattice3(A))
        & v4_relat_2(k2_lattice3(A))
        & v8_relat_2(k2_lattice3(A))
        & m1_subset_1(k2_lattice3(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) )).

fof(dt_k3_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & l1_orders_2(k3_lattice3(A)) ) ) )).

fof(dt_k4_lattice3,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k4_lattice3(A,B),u1_struct_0(k3_lattice3(A))) ) )).

fof(dt_k5_lattice3,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) )).

fof(dt_k7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) )).

fof(dt_k8_lattice3,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k8_lattice3(A,B),u1_struct_0(k7_lattice3(A))) ) )).

fof(dt_k9_lattice3,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(k7_lattice3(A))) )
     => m1_subset_1(k9_lattice3(A,B),u1_struct_0(A)) ) )).

fof(fc1_lattice3,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) )).

fof(fc2_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) )).

fof(fc3_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v17_lattices(k1_lattice3(A)) ) )).

fof(fc4_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( ~ v2_struct_0(k3_lattice3(A))
        & v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A)) ) ) )).

fof(fc6_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( ~ v2_struct_0(k7_lattice3(A))
        & v1_orders_2(k7_lattice3(A)) ) ) )).

fof(rc4_orders_2,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & v2_struct_0(A)
      & v1_orders_2(A) ) )).

fof(redefinition_k2_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k2_lattice3(A) = k8_filter_1(A) ) )).

fof(t10_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
      <=> v2_lattice3(k7_lattice3(A)) ) ) )).

fof(t11_lattice3,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_lattice3(k3_lattice3(A))
        & v2_lattice3(k3_lattice3(A)) ) ) )).

fof(t1_lattice3,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( k1_lattices(k1_lattice3(A),B,C) = k2_xboole_0(B,C)
            & k2_lattices(k1_lattice3(A),B,C) = k3_xboole_0(B,C) ) ) ) )).

fof(t2_binop_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(A,B),C)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,k2_zfmisc_1(A,B),C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C))) )
         => ( ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => k1_binop_1(D,F,G) = k1_binop_1(E,F,G) ) )
           => r2_funct_2(k2_zfmisc_1(A,B),C,D,E) ) ) ) )).

fof(t2_lattice3,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( r1_lattices(k1_lattice3(A),B,C)
          <=> r1_tarski(B,C) ) ) ) )).

fof(t3_lattice3,axiom,(
    ! [A] :
      ( v13_lattices(k1_lattice3(A))
      & k5_lattices(k1_lattice3(A)) = k1_xboole_0 ) )).

fof(t4_lattice3,axiom,(
    ! [A] :
      ( v14_lattices(k1_lattice3(A))
      & k6_lattices(k1_lattice3(A)) = A ) )).

fof(t5_lattice3,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => k7_lattices(k1_lattice3(A),B) = k6_subset_1(A,B) ) )).

fof(t6_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( k3_lattice3(A) = k3_lattice3(B)
           => g3_lattices(u1_struct_0(A),u2_lattices(A),u1_lattices(A)) = g3_lattices(u1_struct_0(B),u2_lattices(B),u1_lattices(B)) ) ) ) )).

fof(t7_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v7_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r3_lattices(A,B,C)
                      & r3_lattices(A,B,D) )
                   => r3_lattices(A,B,k4_lattices(A,C,D)) ) ) ) ) ) )).

fof(t7_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_lattices(A,B,C)
              <=> r3_orders_2(k3_lattice3(A),k4_lattice3(A,B),k4_lattice3(A,C)) ) ) ) ) )).

fof(t8_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) )).

fof(t9_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r1_orders_2(k7_lattice3(A),k8_lattice3(A,C),k8_lattice3(A,B)) ) ) ) ) )).

%------------------------------------------------------------------------------
