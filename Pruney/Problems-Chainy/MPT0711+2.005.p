%------------------------------------------------------------------------------
% File     : MPT0711+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t166_funct_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   2 unit)
%            Number of atoms       :   37 (  12 equality)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   27 (   0   ~;   0   |;  10   &)
%                                         (   3 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   1 constant; 0-3 arity)
%            Number of variables   :   27 (   0 sgn;  26   !;   1   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t12_setfam_1,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) )).

fof(t100_relat_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) )).

fof(t86_relat_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) )).

fof(t90_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) )).

fof(t98_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) )).

fof(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) )).

fof(t165_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( r1_tarski(C,k1_relat_1(A))
                & r1_tarski(C,k1_relat_1(B)) )
             => ( k7_relat_1(A,C) = k7_relat_1(B,C)
              <=> ! [D] :
                    ( r2_hidden(D,C)
                   => k1_funct_1(A,D) = k1_funct_1(B,D) ) ) ) ) ) )).

fof(t166_funct_1,conjecture,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( k1_relat_1(A) = k1_relat_1(B)
                & ! [D] :
                    ( r2_hidden(D,C)
                   => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
             => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) )).

%------------------------------------------------------------------------------
