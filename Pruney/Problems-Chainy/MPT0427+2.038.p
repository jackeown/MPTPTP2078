%------------------------------------------------------------------------------
% File     : MPT0427+2.038 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 038 of t59_setfam_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   2 unit)
%            Number of atoms       :   33 (   9 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   29 (   8   ~;   1   |;   7   &)
%                                         (   3 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   1 constant; 0-2 arity)
%            Number of variables   :   26 (   0 sgn;  25   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(t3_xboole_0,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) )).

fof(t7_xboole_0,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) )).

fof(t4_boole,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 )).

fof(t83_xboole_1,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) )).

fof(t4_subset_1,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) )).

fof(d10_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) )).

fof(dt_k8_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) )).

fof(redefinition_k6_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t7_setfam_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) )).

fof(t59_setfam_1,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(B,C)
           => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) )).

%------------------------------------------------------------------------------
