%------------------------------------------------------------------------------
% File     : MPT1079+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t196_funct_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   11 (   0 unit)
%            Number of atoms       :   73 (   8 equality)
%            Maximal formula depth :   14 (   9 average)
%            Number of connectives :   83 (  21   ~;   0   |;  31   &)
%                                         (   2 <=>;  29  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :   11 (   0 constant; 1-4 arity)
%            Number of variables   :   44 (   0 sgn;  44   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(fc10_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) )).

fof(redefinition_k2_relset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) )).

fof(t23_mcart_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) )).

fof(d6_funct_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                     => ( E = k4_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,B,E,F) = k1_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) )).

fof(d7_funct_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,C)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                     => ( E = k5_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,C,E,F) = k2_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) )).

fof(dt_k4_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k4_funct_2(A,B,C,D))
        & v1_funct_2(k4_funct_2(A,B,C,D),A,B)
        & m1_subset_1(k4_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) )).

fof(dt_k5_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k5_funct_2(A,B,C,D))
        & v1_funct_2(k5_funct_2(A,B,C,D),A,C)
        & m1_subset_1(k5_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) )).

fof(fc9_relset_1,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C))))
     => v1_relat_1(k2_relat_1(D)) ) )).

fof(redefinition_k3_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) )).

fof(t189_funct_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) )).

fof(t196_funct_2,conjecture,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => k3_funct_2(A,k2_zfmisc_1(B,C),D,E) = k4_tarski(k3_funct_2(A,B,k4_funct_2(A,B,C,D),E),k3_funct_2(A,C,k5_funct_2(A,B,C,D),E)) ) ) ) ) ) )).

%------------------------------------------------------------------------------
