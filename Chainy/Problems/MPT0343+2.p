%------------------------------------------------------------------------------
% File     : MPT0343+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : subset_1__t8_subset_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :  463 ( 228 unit)
%            Number of atoms       :  946 ( 413 equality)
%            Maximal formula depth :   26 (   5 average)
%            Number of connectives :  716 ( 233   ~;  23   |; 234   &)
%                                         (  71 <=>; 155  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   1 propositional; 0-2 arity)
%            Number of functors    :   21 (   2 constant; 0-10 arity)
%            Number of variables   : 1397 (   4 sgn;1382   !;  15   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) )).

fof(d3_subset_1,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 )).

fof(dt_k1_subset_1,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(fc13_subset_1,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) )).

fof(l3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) )).

fof(rc1_subset_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) )).

fof(rc2_subset_1,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) )).

fof(t4_subset_1,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) )).

fof(t7_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) )).

fof(t8_subset_1,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) )).

%------------------------------------------------------------------------------
