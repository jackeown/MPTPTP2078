%------------------------------------------------------------------------------
% File     : MPT1469+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : lattice3__t2_lattice3.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2809 ( 423 unit)
%            Number of atoms       : 13591 (2096 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 12614 (1832   ~; 116   |;5298   &)
%                                         ( 553 <=>;4815  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  186 (   1 propositional; 0-4 arity)
%            Number of functors    :  231 (   9 constant; 0-10 arity)
%            Number of variables   : 8112 (   9 sgn;7784   !; 328   ?)
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
%------------------------------------------------------------------------------
fof(dt_k1_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) )).

fof(fc1_lattice3,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) )).

fof(t1_lattice3,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( k1_lattices(k1_lattice3(A),B,C) = k2_xboole_0(B,C)
            & k2_lattices(k1_lattice3(A),B,C) = k3_xboole_0(B,C) ) ) ) )).

fof(t2_lattice3,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( r1_lattices(k1_lattice3(A),B,C)
          <=> r1_tarski(B,C) ) ) ) )).

%------------------------------------------------------------------------------
