%------------------------------------------------------------------------------
% File     : MPT1546+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t24_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   14 (   1 unit)
%            Number of atoms       :   54 (   2 equality)
%            Maximal formula depth :   16 (   6 average)
%            Number of connectives :   44 (   4   ~;   1   |;   9   &)
%                                         (   6 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :   29 (   0 sgn;  29   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(cc2_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(d1_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(d4_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) )).

fof(d9_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(dt_u1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) )).

fof(cc1_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(t22_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) )).

fof(t24_yellow_0,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k13_lattice3(A,B,C)
              <=> r1_orders_2(A,C,B) ) ) ) ) )).

%------------------------------------------------------------------------------
