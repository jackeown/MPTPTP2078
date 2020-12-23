%------------------------------------------------------------------------------
% File     : MPT0324+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : zfmisc_1__t137_zfmisc_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   1 unit)
%            Number of atoms       :    8 (   2 equality)
%            Maximal formula depth :    8 (   7 average)
%            Number of connectives :    5 (   0   ~;   0   |;   2   &)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   13 (   0 sgn;  13   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) )).

fof(t123_zfmisc_1,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) )).

fof(t137_zfmisc_1,conjecture,(
    ! [A,B,C,D,E] :
      ( ( r2_hidden(A,k2_zfmisc_1(B,C))
        & r2_hidden(A,k2_zfmisc_1(D,E)) )
     => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) )).

%------------------------------------------------------------------------------
