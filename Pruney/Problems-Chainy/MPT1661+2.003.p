%------------------------------------------------------------------------------
% File     : MPT1661+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t41_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   69 (   3 equality)
%            Maximal formula depth :   18 (  12 average)
%            Number of connectives :   64 (   2   ~;   0   |;  28   &)
%                                         (   4 <=>;  30  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-3 arity)
%            Number of variables   :   28 (   0 sgn;  28   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) )).

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

fof(d20_waybel_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) )).

fof(d2_waybel_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,E,C)
                                & r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) )).

fof(t41_waybel_0,conjecture,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => r2_hidden(k12_lattice3(A,C,D),B) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
