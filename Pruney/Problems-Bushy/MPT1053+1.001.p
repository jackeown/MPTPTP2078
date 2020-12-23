%------------------------------------------------------------------------------
% File     : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : funct_2__t170_funct_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   10 (   4 unit)
%            Number of atoms       :   32 (   6 equality)
%            Maximal formula depth :   10 (   4 average)
%            Number of connectives :   23 (   1   ~;   1   |;   8   &)
%                                         (   1 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    8 (   2 constant; 0-2 arity)
%            Number of variables   :   21 (   0 sgn;  19   !;   2   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_subset_1,axiom,(
    ! [A] : k2_subset_1(A) = A )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(s3_relset_1__e2_192__funct_2,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,k9_setfam_1(A))
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,k9_setfam_1(A)))) )
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => ( r2_hidden(C,k2_subset_1(A))
             => r1_tarski(k1_funct_1(B,C),k2_subset_1(A)) ) )
       => ? [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A),k2_subset_1(A))))
            & ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,k2_subset_1(A))
                 => k11_relat_1(C,D) = k1_funct_1(B,D) ) ) ) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) )).

fof(t170_funct_2,conjecture,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,k9_setfam_1(A))
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,k9_setfam_1(A)))) )
     => ? [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
          & ! [D] :
              ( r2_hidden(D,A)
             => k11_relat_1(C,D) = k1_funct_1(B,D) ) ) ) )).

%------------------------------------------------------------------------------
