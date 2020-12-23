%------------------------------------------------------------------------------
% File     : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_0__t13_yellow_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   31 (   6 equality)
%            Maximal formula depth :   14 (   8 average)
%            Number of connectives :   25 (   0   ~;   0   |;   5   &)
%                                         (   2 <=>;  18  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   16 (   0 sgn;  14   !;   2   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) )).

fof(d5_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r2_lattice3(A,u1_struct_0(A),B) ) ) ) )).

fof(dt_u1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) )).

fof(free_g1_orders_2,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) )).

fof(t2_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C,D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ! [E] :
                    ( m1_subset_1(E,u1_struct_0(B))
                   => ( D = E
                     => ( ( r2_lattice3(A,C,D)
                         => r2_lattice3(B,C,E) )
                        & ( r1_lattice3(A,C,D)
                         => r1_lattice3(B,C,E) ) ) ) ) ) ) ) ) )).

fof(t13_yellow_0,conjecture,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ( ( v1_yellow_0(A)
               => v1_yellow_0(B) )
              & ( v2_yellow_0(A)
               => v2_yellow_0(B) ) ) ) ) ) )).

%------------------------------------------------------------------------------
