%------------------------------------------------------------------------------
% File     : MPT1533+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_0__t11_yellow_0.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2973 ( 426 unit)
%            Number of atoms       : 14821 (2227 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 13795 (1947   ~; 116   |;5886   &)
%                                         ( 621 <=>;5225  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  196 (   1 propositional; 0-4 arity)
%            Number of functors    :  281 (   9 constant; 0-10 arity)
%            Number of variables   : 8667 (   9 sgn;8285   !; 382   ?)
%            Maximal term depth    :    6 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
include('Axioms/MPT013+2.ax').
include('Axioms/MPT014+2.ax').
include('Axioms/MPT015+2.ax').
include('Axioms/MPT016+2.ax').
include('Axioms/MPT017+2.ax').
include('Axioms/MPT018+2.ax').
include('Axioms/MPT019+2.ax').
include('Axioms/MPT020+2.ax').
include('Axioms/MPT021+2.ax').
include('Axioms/MPT022+2.ax').
include('Axioms/MPT023+2.ax').
include('Axioms/MPT024+2.ax').
%------------------------------------------------------------------------------
fof(t10_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C,D] :
          ( m1_subset_1(D,u1_struct_0(A))
         => ( ( ( r1_lattice3(A,B,D)
                & r1_lattice3(A,C,D) )
             => r1_lattice3(A,k2_xboole_0(B,C),D) )
            & ( ( r2_lattice3(A,B,D)
                & r2_lattice3(A,C,D) )
             => r2_lattice3(A,k2_xboole_0(B,C),D) ) ) ) ) )).

fof(t11_yellow_0,conjecture,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r2_lattice3(A,B,C)
                  & r1_orders_2(A,C,D) )
               => r2_lattice3(A,B,D) ) ) ) ) )).

fof(t1_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( C = E
                                & D = F )
                             => ( ( r1_orders_2(A,C,D)
                                 => r1_orders_2(B,E,F) )
                                & ( r2_orders_2(A,C,D)
                                 => r2_orders_2(B,E,F) ) ) ) ) ) ) ) ) ) ) )).

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

fof(t3_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
              & v3_lattice3(A) )
           => v3_lattice3(B) ) ) ) )).

fof(t4_yellow_0,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
               => ! [D] :
                    ( ( r1_lattice3(A,D,C)
                     => r1_lattice3(A,D,B) )
                    & ( r2_lattice3(A,D,B)
                     => r2_lattice3(A,D,C) ) ) ) ) ) ) )).

fof(t5_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( ( r2_lattice3(A,B,C)
             => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r2_lattice3(A,B,C) )
            & ( r1_lattice3(A,B,C)
             => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r1_lattice3(A,B,C) ) ) ) ) )).

fof(t6_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) )).

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

fof(t8_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) ) )
                    & ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) )
                     => r1_lattice3(A,k2_tarski(C,D),B) )
                    & ( r2_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) ) )
                    & ( ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) )
                     => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) )).

fof(t9_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) )).

%------------------------------------------------------------------------------
