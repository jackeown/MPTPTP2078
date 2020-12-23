%------------------------------------------------------------------------------
% File     : MPT1575+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t53_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    9 (   3 unit)
%            Number of atoms       :   37 (   3 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   30 (   2   ~;   0   |;   8   &)
%                                         (   3 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   0 constant; 1-2 arity)
%            Number of variables   :   22 (   0 sgn;  21   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) )).

fof(t12_setfam_1,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) )).

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
