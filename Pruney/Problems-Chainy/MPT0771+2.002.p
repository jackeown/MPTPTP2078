%------------------------------------------------------------------------------
% File     : MPT0771+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t20_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   14 (   1 unit)
%            Number of atoms       :   32 (   4 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   18 (   0   ~;   0   |;   2   &)
%                                         (   1 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   0 constant; 1-2 arity)
%            Number of variables   :   29 (   0 sgn;  29   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) )).

fof(t8_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(cc2_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) )).

fof(d6_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) )).

fof(dt_k7_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) )).

fof(dt_k8_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) )).

fof(t116_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) )).

fof(t140_relat_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) )).

fof(t31_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) )).

fof(t87_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) )).

fof(d6_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) )).

fof(t18_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) )).

fof(t20_wellord1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
        & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) )).

%------------------------------------------------------------------------------
