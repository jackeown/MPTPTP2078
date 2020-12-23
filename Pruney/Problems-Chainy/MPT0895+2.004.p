%------------------------------------------------------------------------------
% File     : MPT0895+2.004 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 004 of t55_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   2 unit)
%            Number of atoms       :   22 (  17 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   26 (  12   ~;   2   |;   9   &)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   1 constant; 0-4 arity)
%            Number of variables   :   17 (   0 sgn;  17   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t2_xboole_1,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) )).

fof(t3_xboole_1,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) )).

fof(t113_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) )).

fof(t117_zfmisc_1,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) )).

fof(t195_relat_1,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) )).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 )).

fof(t53_mcart_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) )).

fof(t55_mcart_1,conjecture,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) )).

%------------------------------------------------------------------------------
