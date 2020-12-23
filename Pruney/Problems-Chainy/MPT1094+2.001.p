%------------------------------------------------------------------------------
% File     : MPT1094+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t29_finset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   1 unit)
%            Number of atoms       :   29 (   2 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   19 (   0   ~;   0   |;   8   &)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    7 (   0 constant; 1-2 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(t22_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) )).

fof(dt_k9_funct_3,axiom,(
    ! [A,B] :
      ( v1_funct_1(k9_funct_3(A,B))
      & v1_funct_2(k9_funct_3(A,B),k2_zfmisc_1(A,B),A)
      & m1_subset_1(k9_funct_3(A,B),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),A))) ) )).

fof(fc10_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(fc13_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) )).

fof(fc14_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) )).

fof(t100_funct_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) )).

fof(t26_finset_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
       => v1_finset_1(k2_relat_1(A)) ) ) )).

fof(t29_finset_1,conjecture,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
      <=> v1_finset_1(A) ) ) )).

%------------------------------------------------------------------------------
