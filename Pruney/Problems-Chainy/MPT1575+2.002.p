%------------------------------------------------------------------------------
% File     : MPT1575+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t53_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   1 unit)
%            Number of atoms       :   43 (   3 equality)
%            Maximal formula depth :   16 (   7 average)
%            Number of connectives :   37 (   2   ~;   0   |;  12   &)
%                                         (   4 <=>;  19  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   23 (   0 sgn;  21   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(t108_xboole_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(d12_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r2_lattice3(A,B,C)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                 => r1_orders_2(A,C,D) ) ) ) ) ) )).

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

fof(t50_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r1_yellow_0(A,B)
           => r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r1_yellow_0(A,B) )
          & ( r2_yellow_0(A,B)
           => r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r2_yellow_0(A,B) ) ) ) )).

fof(t53_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_yellow_0(A,B) )
       => v3_lattice3(A) ) ) )).

%------------------------------------------------------------------------------
