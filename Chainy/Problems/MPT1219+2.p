%------------------------------------------------------------------------------
% File     : MPT1219+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tops_1__t21_tops_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2086 ( 390 unit)
%            Number of atoms       : 8730 (1741 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 7909 (1265   ~; 113   |;3132   &)
%                                         ( 403 <=>;2996  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  121 (   1 propositional; 0-4 arity)
%            Number of functors    :  169 (   4 constant; 0-10 arity)
%            Number of variables   : 6147 (   9 sgn;5901   !; 246   ?)
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
%------------------------------------------------------------------------------
fof(t21_tops_1,conjecture,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( k3_subset_1(u1_struct_0(A),B) = k3_subset_1(u1_struct_0(A),C)
               => B = C ) ) ) ) )).

%------------------------------------------------------------------------------
