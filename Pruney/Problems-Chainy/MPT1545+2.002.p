%------------------------------------------------------------------------------
% File     : MPT1545+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t23_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   52 (   5 equality)
%            Maximal formula depth :   17 (  12 average)
%            Number of connectives :   47 (   0   ~;   0   |;  24   &)
%                                         (   2 <=>;  21  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-3 arity)
%            Number of variables   :   20 (   0 sgn;  20   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) )).

fof(redefinition_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) )).

fof(t19_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( D = k11_lattice3(A,B,C)
                        & r2_yellow_0(A,k2_tarski(B,C)) )
                     => ( r1_orders_2(A,D,B)
                        & r1_orders_2(A,D,C)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,E,B)
                                & r1_orders_2(A,E,C) )
                             => r1_orders_2(A,E,D) ) ) ) )
                    & ( ( r1_orders_2(A,D,B)
                        & r1_orders_2(A,D,C)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,E,B)
                                & r1_orders_2(A,E,C) )
                             => r1_orders_2(A,E,D) ) ) )
                     => ( D = k11_lattice3(A,B,C)
                        & r2_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ) ) ) )).

fof(t21_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r2_yellow_0(A,k2_tarski(B,C)) ) ) ) ) )).

fof(t23_yellow_0,conjecture,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
