%------------------------------------------------------------------------------
% File     : MPT1147+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t39_orders_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   39 (   1 equality)
%            Maximal formula depth :   14 (  11 average)
%            Number of connectives :   43 (   8   ~;   1   |;  18   &)
%                                         (   3 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :   15 (   0 sgn;  13   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d10_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) )).

fof(t30_orders_2,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) )).

fof(t38_orders_2,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ ( ? [D] :
                        ( v6_orders_2(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(B,D)
                        & r2_hidden(C,D) )
                    & ~ r1_orders_2(A,B,C)
                    & ~ r1_orders_2(A,C,B) )
                & ~ ( ( r1_orders_2(A,B,C)
                      | r1_orders_2(A,C,B) )
                    & ! [D] :
                        ( ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( r2_hidden(B,D)
                            & r2_hidden(C,D) ) ) ) ) ) ) ) )).

fof(t39_orders_2,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ? [D] :
                    ( v6_orders_2(D,A)
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & r2_hidden(B,D)
                    & r2_hidden(C,D) )
              <=> ( r2_orders_2(A,B,C)
                <=> ~ r1_orders_2(A,C,B) ) ) ) ) ) )).

%------------------------------------------------------------------------------
