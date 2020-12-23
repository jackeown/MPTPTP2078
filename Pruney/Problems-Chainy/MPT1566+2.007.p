%------------------------------------------------------------------------------
% File     : MPT1566+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t44_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   35 (   3 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   31 (   2   ~;   0   |;  14   &)
%                                         (   0 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   13 (   0 sgn;  13   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d11_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) )).

fof(dt_k1_yellow_0,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) )).

fof(t30_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) )).

fof(t42_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) )).

fof(t6_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) )).

fof(t44_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) )).

%------------------------------------------------------------------------------
