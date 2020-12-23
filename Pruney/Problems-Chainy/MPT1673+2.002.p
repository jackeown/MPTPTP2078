%------------------------------------------------------------------------------
% File     : MPT1673+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t53_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   52 (   6 equality)
%            Maximal formula depth :   18 (  15 average)
%            Number of connectives :   60 (  11   ~;   0   |;  22   &)
%                                         (   3 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   19 (   0 sgn;  19   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t46_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                <=> r2_lattice3(A,C,D) ) )
            & r1_yellow_0(A,B) )
         => r1_yellow_0(A,C) ) ) )).

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

fof(t53_waybel_0,conjecture,(
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
               => ( r1_yellow_0(A,B)
                <=> r1_yellow_0(A,C) ) ) ) ) ) )).

%------------------------------------------------------------------------------
