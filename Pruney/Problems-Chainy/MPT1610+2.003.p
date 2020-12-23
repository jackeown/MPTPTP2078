%------------------------------------------------------------------------------
% File     : MPT1610+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t18_yellow_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   18 (   4 unit)
%            Number of atoms       :   62 (  37 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives :   65 (  21   ~;   3   |;  24   &)
%                                         (   8 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   17 (   1 constant; 0-10 arity)
%            Number of variables   :   46 (   0 sgn;  42   !;   4   ?)
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

fof(d8_enumset1,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J,K] :
      ( K = k8_enumset1(A,B,C,D,E,F,G,H,I,J)
    <=> ! [L] :
          ( r2_hidden(L,K)
        <=> ~ ( L != A
              & L != B
              & L != C
              & L != D
              & L != E
              & L != F
              & L != G
              & L != H
              & L != I
              & L != J ) ) ) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) )).

fof(s1_xboole_0__e1_138_1__zfmisc_1,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,k3_tarski(A))
        & ? [D] :
            ( C = D
            & ? [E] :
                ( r2_hidden(E,D)
                & r2_hidden(E,A) ) ) ) ) )).

fof(t113_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) )).

fof(t203_relat_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => k11_relat_1(k2_zfmisc_1(B,C),A) = C ) )).

fof(t205_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) )).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 )).

fof(t64_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) )).

fof(t18_funct_1,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) )).

fof(t9_mcart_1,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) )).

fof(s3_funct_1__e15_31__wellord2,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(d2_yellow_1,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) )).

fof(t13_yellow_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) )).

fof(t4_yellow_1,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) )).

fof(t18_yellow_1,conjecture,(
    ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 )).

%------------------------------------------------------------------------------
