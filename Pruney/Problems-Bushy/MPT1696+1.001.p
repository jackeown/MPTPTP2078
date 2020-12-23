%------------------------------------------------------------------------------
% File     : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_0__t76_waybel_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   39 (   2 equality)
%            Maximal formula depth :   16 (  11 average)
%            Number of connectives :   39 (   4   ~;   0   |;  15   &)
%                                         (   3 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :   15 (   0 sgn;  13   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d40_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ( v25_waybel_0(A)
      <=> ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) )).

fof(d8_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r1_lattice3(A,B,E)
                           => r1_orders_2(A,E,D) ) ) )
                   => D = C ) ) ) ) ) )).

fof(t25_orders_2,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) )).

fof(t76_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v25_waybel_0(A)
      <=> ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => r2_yellow_0(A,B) ) ) ) )).

%------------------------------------------------------------------------------
