%------------------------------------------------------------------------------
% File     : MPT1674+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_0__t54_waybel_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   1 unit)
%            Number of atoms       :   56 (   9 equality)
%            Maximal formula depth :   18 (  11 average)
%            Number of connectives :   62 (  11   ~;   0   |;  24   &)
%                                         (   2 <=>;  25  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   2 constant; 0-2 arity)
%            Number of variables   :   22 (   0 sgn;  22   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(t47_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( r1_yellow_0(A,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                <=> r2_lattice3(A,C,D) ) ) )
         => k1_yellow_0(A,B) = k1_yellow_0(A,C) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t52_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( ! [D] :
                      ( ( v1_finset_1(D)
                        & m1_subset_1(D,k1_zfmisc_1(B)) )
                     => ( D != k1_xboole_0
                       => r1_yellow_0(A,D) ) )
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r2_hidden(D,C)
                          & ! [E] :
                              ( ( v1_finset_1(E)
                                & m1_subset_1(E,k1_zfmisc_1(B)) )
                             => ~ ( r1_yellow_0(A,E)
                                  & D = k1_yellow_0(A,E) ) ) ) )
                  & ! [D] :
                      ( ( v1_finset_1(D)
                        & m1_subset_1(D,k1_zfmisc_1(B)) )
                     => ( D != k1_xboole_0
                       => r2_hidden(k1_yellow_0(A,D),C) ) ) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                    <=> r2_lattice3(A,C,D) ) ) ) ) ) ) )).

fof(t54_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( ! [D] :
                      ( ( v1_finset_1(D)
                        & m1_subset_1(D,k1_zfmisc_1(B)) )
                     => ( D != k1_xboole_0
                       => r1_yellow_0(A,D) ) )
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r2_hidden(D,C)
                          & ! [E] :
                              ( ( v1_finset_1(E)
                                & m1_subset_1(E,k1_zfmisc_1(B)) )
                             => ~ ( r1_yellow_0(A,E)
                                  & D = k1_yellow_0(A,E) ) ) ) )
                  & ! [D] :
                      ( ( v1_finset_1(D)
                        & m1_subset_1(D,k1_zfmisc_1(B)) )
                     => ( D != k1_xboole_0
                       => r2_hidden(k1_yellow_0(A,D),C) ) )
                  & r1_yellow_0(A,B) )
               => k1_yellow_0(A,C) = k1_yellow_0(A,B) ) ) ) ) )).

%------------------------------------------------------------------------------
