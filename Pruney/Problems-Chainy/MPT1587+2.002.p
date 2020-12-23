%------------------------------------------------------------------------------
% File     : MPT1587+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t66_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   29 (   2 equality)
%            Maximal formula depth :   11 (   8 average)
%            Number of connectives :   31 (   6   ~;   0   |;  15   &)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-3 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(dt_k7_domain_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) )).

fof(t64_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( ( r2_yellow_0(A,C)
                  & r2_hidden(k2_yellow_0(A,C),u1_struct_0(B)) )
               => ( r2_yellow_0(B,C)
                  & k2_yellow_0(B,C) = k2_yellow_0(A,C) ) ) ) ) ) )).

fof(t66_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ( ( r2_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D))
                      & r2_hidden(k2_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D)),u1_struct_0(B)) )
                   => ( r2_yellow_0(B,k7_domain_1(u1_struct_0(B),C,D))
                      & k2_yellow_0(B,k7_domain_1(u1_struct_0(B),C,D)) = k2_yellow_0(A,k7_domain_1(u1_struct_0(B),C,D)) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
