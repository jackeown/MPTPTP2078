%------------------------------------------------------------------------------
% File     : MPT1031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : funct_2__t136_funct_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   2 unit)
%            Number of atoms       :   56 (   8 equality)
%            Maximal formula depth :   15 (   6 average)
%            Number of connectives :   46 (   4   ~;   1   |;  17   &)
%                                         (   0 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    8 (   2 constant; 0-3 arity)
%            Number of variables   :   39 (   0 sgn;  37   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc1_funct_2,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) )).

fof(cc1_partfun1,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) )).

fof(cc1_relset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) )).

fof(cc2_relset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) )).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(dt_k1_relset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) )).

fof(dt_o_1_1_funct_2,axiom,(
    ! [A] : m1_subset_1(o_1_1_funct_2(A),A) )).

fof(redefinition_k1_relset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) )).

fof(s5_funct_2__e3_154_1_2__funct_2,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ! [D] :
            ( r2_hidden(D,A)
           => ( ( r2_hidden(D,k1_relset_1(A,B,C))
               => r2_hidden(k1_funct_1(C,D),B) )
              & ( ~ r2_hidden(D,k1_relset_1(A,B,C))
               => r2_hidden(o_1_1_funct_2(B),B) ) ) )
       => ? [D] :
            ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
            & ! [E] :
                ( r2_hidden(E,A)
               => ( ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(D,E) = k1_funct_1(C,E) )
                  & ( ~ r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(D,E) = o_1_1_funct_2(B) ) ) ) ) ) ) )).

fof(t27_partfun1,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => r2_hidden(k1_funct_1(C,B),A) ) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t136_funct_2,conjecture,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
          & ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,B)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ? [E] :
                  ( r2_hidden(E,k1_relset_1(A,B,C))
                  & k1_funct_1(D,E) != k1_funct_1(C,E) ) ) ) ) )).

%------------------------------------------------------------------------------
