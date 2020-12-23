%------------------------------------------------------------------------------
% File     : MPT0591+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t195_relat_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   3 unit)
%            Number of atoms       :   18 (   6 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   15 (   5   ~;   1   |;   4   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(t139_zfmisc_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(t193_relat_1,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) )).

fof(t194_relat_1,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) )).

fof(t21_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) )).

fof(t195_relat_1,conjecture,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) )).

%------------------------------------------------------------------------------
