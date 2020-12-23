%------------------------------------------------------------------------------
% File     : MPT1543+1.002 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_0__t21_yellow_0---2.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   42 (   2 equality)
%            Maximal formula depth :   17 (  12 average)
%            Number of connectives :   38 (   0   ~;   0   |;  17   &)
%                                         (   2 <=>;  19  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-3 arity)
%            Number of variables   :   17 (   0 sgn;  16   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
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

fof(dt_k11_lattice3,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) )).

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

fof(t21_yellow_0,conjecture,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r2_yellow_0(A,k2_tarski(B,C)) ) ) ) ) )).

%------------------------------------------------------------------------------
