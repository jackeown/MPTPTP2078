%------------------------------------------------------------------------------
% File     : MPT0740+2.009 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 009 of t30_ordinal1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   36 (   0 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   25 (   1   ~;   1   |;   5   &)
%                                         (   3 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :   25 (   0 sgn;  25   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(t94_zfmisc_1,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) )).

fof(t56_setfam_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) )).

fof(connectedness_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) )).

fof(d2_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) )).

fof(redefinition_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) )).

fof(t10_ordinal1,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) )).

fof(t22_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) )).

fof(t23_ordinal1,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) )).

fof(t29_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) )).

fof(t7_ordinal1,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) )).

fof(t30_ordinal1,conjecture,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k3_tarski(A)) ) )).

%------------------------------------------------------------------------------
