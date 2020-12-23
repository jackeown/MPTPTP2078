%------------------------------------------------------------------------------
% File     : MPT0223+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : zfmisc_1__t18_zfmisc_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :  307 ( 191 unit)
%            Number of atoms       :  528 ( 243 equality)
%            Maximal formula depth :   26 (   5 average)
%            Number of connectives :  324 ( 103   ~;   4   |; 104   &)
%                                         (  37 <=>;  76  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   1 propositional; 0-2 arity)
%            Number of functors    :   18 (   2 constant; 0-10 arity)
%            Number of variables   :  954 (   4 sgn; 949   !;   5   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) )).

fof(d4_tarski,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_tarski,axiom,(
    $true )).

fof(fc2_xboole_0,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) )).

fof(fc3_xboole_0,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) )).

fof(l20_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) )).

fof(l22_zfmisc_1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) )).

fof(l24_zfmisc_1,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) )).

fof(l27_zfmisc_1,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) )).

fof(l29_zfmisc_1,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) )).

fof(l3_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) )).

fof(t10_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ~ ( k2_tarski(A,B) = k2_tarski(C,D)
        & A != C
        & A != D ) )).

fof(t12_zfmisc_1,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) )).

fof(t13_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) )).

fof(t14_zfmisc_1,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) )).

fof(t16_zfmisc_1,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) )).

fof(t17_zfmisc_1,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) )).

fof(t18_zfmisc_1,conjecture,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) )).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) )).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 )).

fof(t6_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) )).

fof(t8_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) )).

fof(t9_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) )).

%------------------------------------------------------------------------------
