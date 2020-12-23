%------------------------------------------------------------------------------
% File     : MPT1558+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t36_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   3 unit)
%            Number of atoms       :   83 (   7 equality)
%            Maximal formula depth :   17 (   9 average)
%            Number of connectives :   71 (   0   ~;   0   |;  27   &)
%                                         (   2 <=>;  42  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    7 (   0 constant; 1-3 arity)
%            Number of variables   :   42 (   0 sgn;  41   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(t7_xboole_1,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) )).

fof(t98_xboole_1,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) )).

fof(d7_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r2_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r2_lattice3(A,B,E)
                           => r1_orders_2(A,D,E) ) ) )
                   => D = C ) ) ) ) ) )).

fof(d9_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) )).

fof(dt_k1_yellow_0,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) )).

fof(t10_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C,D] :
          ( m1_subset_1(D,u1_struct_0(A))
         => ( ( ( r1_lattice3(A,B,D)
                & r1_lattice3(A,C,D) )
             => r1_lattice3(A,k2_xboole_0(B,C),D) )
            & ( ( r2_lattice3(A,B,D)
                & r2_lattice3(A,C,D) )
             => r2_lattice3(A,k2_xboole_0(B,C),D) ) ) ) ) )).

fof(t18_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) )
                     => ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) ) )
                    & ( ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) )
                     => ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ) ) ) )).

fof(t34_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( ( r1_tarski(B,C)
            & r1_yellow_0(A,B)
            & r1_yellow_0(A,C) )
         => r1_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) )).

fof(t4_yellow_0,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
               => ! [D] :
                    ( ( r1_lattice3(A,D,C)
                     => r1_lattice3(A,D,B) )
                    & ( r2_lattice3(A,D,B)
                     => r2_lattice3(A,D,C) ) ) ) ) ) ) )).

fof(t9_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) )).

fof(t36_yellow_0,conjecture,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( r1_yellow_0(A,B)
            & r1_yellow_0(A,C)
            & r1_yellow_0(A,k2_xboole_0(B,C)) )
         => k1_yellow_0(A,k2_xboole_0(B,C)) = k10_lattice3(A,k1_yellow_0(A,B),k1_yellow_0(A,C)) ) ) )).

%------------------------------------------------------------------------------
