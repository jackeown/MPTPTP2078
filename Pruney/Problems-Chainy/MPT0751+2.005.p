%------------------------------------------------------------------------------
% File     : MPT0751+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t42_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   11 (   2 unit)
%            Number of atoms       :   38 (   6 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   32 (   5   ~;   2   |;   7   &)
%                                         (   6 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   20 (   0 sgn;  19   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(connectedness_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) )).

fof(d1_ordinal1,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) )).

fof(redefinition_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) )).

fof(t13_ordinal1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) )).

fof(t14_ordinal1,axiom,(
    ! [A] : A != k1_ordinal1(A) )).

fof(t29_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) )).

fof(t33_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) )).

fof(t34_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) )).

fof(t41_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) )).

fof(t42_ordinal1,conjecture,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ ( ~ v4_ordinal1(A)
            & ! [B] :
                ( v3_ordinal1(B)
               => A != k1_ordinal1(B) ) )
        & ~ ( ? [B] :
                ( v3_ordinal1(B)
                & A = k1_ordinal1(B) )
            & v4_ordinal1(A) ) ) ) )).

%------------------------------------------------------------------------------
