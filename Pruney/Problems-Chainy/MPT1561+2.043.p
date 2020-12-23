%------------------------------------------------------------------------------
% File     : MPT1561+2.043 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 043 of t39_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   14 (   1 unit)
%            Number of atoms       :  101 (   9 equality)
%            Maximal formula depth :   17 (   8 average)
%            Number of connectives :   93 (   6   ~;   0   |;  38   &)
%                                         (   3 <=>;  46  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-3 arity)
%            Number of functors    :    7 (   0 constant; 1-3 arity)
%            Number of variables   :   39 (   0 sgn;  37   !;   2   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(redefinition_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) )).

fof(t24_orders_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) )).

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

fof(t15_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) )).

fof(t16_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) )).

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

fof(t31_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) )).

fof(t38_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k6_domain_1(u1_struct_0(A),B))
            & r2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ) )).

fof(t7_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) )).

fof(t39_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k1_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) )).

%------------------------------------------------------------------------------
