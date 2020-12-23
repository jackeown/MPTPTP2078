%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1697+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:36 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 259 expanded)
%              Number of clauses        :   54 (  97 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  460 (2650 expanded)
%              Number of equality atoms :   86 ( 441 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tmap_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2)
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) )
                               => ( X7 = k1_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3) = X5
                                    & k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4) = X6 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(dt_k1_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X3,k1_zfmisc_1(X1))
        & ~ v1_xboole_0(X4)
        & m1_subset_1(X4,k1_zfmisc_1(X1))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X3,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X4,X2)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
     => ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
        & m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(t6_tmap_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ( r1_subset_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                           => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( k2_partfun1(k4_subset_1(X13,X15,X16),X14,X19,X15) = X17
        | X19 != k1_tmap_1(X13,X14,X15,X16,X17,X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k4_subset_1(X13,X15,X16),X14)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X13,X15,X16),X14)))
        | k2_partfun1(X15,X14,X17,k9_subset_1(X13,X15,X16)) != k2_partfun1(X16,X14,X18,k9_subset_1(X13,X15,X16))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) )
      & ( k2_partfun1(k4_subset_1(X13,X15,X16),X14,X19,X16) = X18
        | X19 != k1_tmap_1(X13,X14,X15,X16,X17,X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k4_subset_1(X13,X15,X16),X14)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X13,X15,X16),X14)))
        | k2_partfun1(X15,X14,X17,k9_subset_1(X13,X15,X16)) != k2_partfun1(X16,X14,X18,k9_subset_1(X13,X15,X16))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) )
      & ( k2_partfun1(k4_subset_1(X13,X15,X16),X14,X19,X15) != X17
        | k2_partfun1(k4_subset_1(X13,X15,X16),X14,X19,X16) != X18
        | X19 = k1_tmap_1(X13,X14,X15,X16,X17,X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k4_subset_1(X13,X15,X16),X14)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X13,X15,X16),X14)))
        | k2_partfun1(X15,X14,X17,k9_subset_1(X13,X15,X16)) != k2_partfun1(X16,X14,X18,k9_subset_1(X13,X15,X16))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( v1_funct_1(k1_tmap_1(X22,X23,X24,X25,X26,X27))
        | v1_xboole_0(X22)
        | v1_xboole_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X22))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X23)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X23)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X23)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X23))) )
      & ( v1_funct_2(k1_tmap_1(X22,X23,X24,X25,X26,X27),k4_subset_1(X22,X24,X25),X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X22))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X23)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X23)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X23)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X23))) )
      & ( m1_subset_1(k1_tmap_1(X22,X23,X24,X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X22,X24,X25),X23)))
        | v1_xboole_0(X22)
        | v1_xboole_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X22))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X23)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X23)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X23)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X1)) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ( r1_subset_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                             => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tmap_1])).

cnf(c_0_15,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & r1_subset_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk3_0,X2),esk2_0,k1_tmap_1(X1,esk2_0,esk3_0,X2,esk5_0,X3),X2) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(X1,esk3_0,X2)) != k2_partfun1(X2,esk2_0,X3,k9_subset_1(X1,esk3_0,X2))
    | ~ v1_funct_2(X3,X2,esk2_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ( ~ r1_subset_1(X31,X32)
        | r1_xboole_0(X31,X32)
        | v1_xboole_0(X31)
        | v1_xboole_0(X32) )
      & ( ~ r1_xboole_0(X31,X32)
        | r1_subset_1(X31,X32)
        | v1_xboole_0(X31)
        | v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_33,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_partfun1(X38,X39,X41,X40))
        | X39 = k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(k2_partfun1(X38,X39,X41,X40),X40,X39)
        | X39 = k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X41,X40),k1_zfmisc_1(k2_zfmisc_1(X40,X39)))
        | X39 = k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_1(k2_partfun1(X38,X39,X41,X40))
        | X38 != k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(k2_partfun1(X38,X39,X41,X40),X40,X39)
        | X38 != k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X41,X40),k1_zfmisc_1(k2_zfmisc_1(X40,X39)))
        | X38 != k1_xboole_0
        | ~ r1_tarski(X40,X38)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

fof(c_0_34,plain,(
    ! [X35,X36] : r1_tarski(k3_xboole_0(X35,X36),X35) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_35,plain,(
    ! [X37] : k3_xboole_0(X37,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_36,plain,(
    ! [X42] :
      ( ~ v1_xboole_0(X42)
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_37,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk3_0,esk4_0),esk2_0,k1_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(X1,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(X1,esk3_0,esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X20,X21] :
      ( ( ~ r1_xboole_0(X20,X21)
        | k3_xboole_0(X20,X21) = k1_xboole_0 )
      & ( k3_xboole_0(X20,X21) != k1_xboole_0
        | r1_xboole_0(X20,X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk4_0),esk2_0,k1_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),X2) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,esk2_0,X3,k9_subset_1(X1,X2,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(X1,X2,esk4_0))
    | ~ v1_funct_2(X3,X2,esk2_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0
    | k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31]),c_0_24])).

fof(c_0_55,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | k9_subset_1(X28,X29,X30) = k3_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_56,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk3_0,esk4_0),esk2_0,k1_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) = esk5_0
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(X1,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(X1,esk3_0,esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_39])]),c_0_41]),c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,esk4_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_68]),c_0_67])])).

cnf(c_0_73,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) != k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_40])])).

cnf(c_0_74,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_76]),c_0_67])]),
    [proof]).

%------------------------------------------------------------------------------
