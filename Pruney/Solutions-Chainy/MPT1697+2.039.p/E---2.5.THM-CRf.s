%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:40 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 337 expanded)
%              Number of clauses        :   61 ( 124 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  470 (3130 expanded)
%              Number of equality atoms :   84 ( 521 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(t55_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_xboole_0(X2,X3)
       => k5_relset_1(X3,X1,X4,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(c_0_15,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ( v1_funct_1(k1_tmap_1(X46,X47,X48,X49,X50,X51))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) )
      & ( v1_funct_2(k1_tmap_1(X46,X47,X48,X49,X50,X51),k4_subset_1(X46,X48,X49),X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) )
      & ( m1_subset_1(k1_tmap_1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X46,X48,X49),X47)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_xboole_0(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] :
      ( ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41) = X43
        | X45 != k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) )
      & ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42) = X44
        | X45 != k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) )
      & ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41) != X43
        | k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42) != X44
        | X45 = k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))
    | ~ v1_funct_2(X6,X3,X1)
    | ~ v1_funct_2(X5,X2,X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(csr,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_24,c_0_20])]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_partfun1(X35,X36,X37,X38) = k7_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_43,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k5_relset_1(X27,X28,X29,X30) = k7_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_44,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X31)))
      | ~ r1_xboole_0(X32,X33)
      | k5_relset_1(X33,X31,X34,X32) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_20])]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_47,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_51,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31]),c_0_30]),c_0_33]),c_0_32]),c_0_35]),c_0_34]),c_0_36]),c_0_37])]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_53,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_47])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_55,plain,(
    ! [X20,X21] :
      ( ( k9_relat_1(X21,X20) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_xboole_0(k1_relat_1(X21),X20)
        | k9_relat_1(X21,X20) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

fof(c_0_56,plain,(
    ! [X19] : k9_relat_1(k1_xboole_0,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33]),c_0_35])])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_63,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(X3,X4,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_32]),c_0_34])])).

fof(c_0_67,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_68,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_69,plain,(
    ! [X22,X23] :
      ( ( ~ r1_subset_1(X22,X23)
        | r1_xboole_0(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) )
      & ( ~ r1_xboole_0(X22,X23)
        | r1_subset_1(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_70,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_xboole_0(X3,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_60]),c_0_33])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( k2_partfun1(X1,X2,esk5_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_xboole_0(X3,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_65]),c_0_32])])).

cnf(c_0_73,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_32])])).

cnf(c_0_74,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k2_partfun1(X1,X2,esk5_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_34])).

cnf(c_0_81,plain,
    ( k9_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_40]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_78]),c_0_33])])).

cnf(c_0_84,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_79]),c_0_32])])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_47]),c_0_33])])).

cnf(c_0_86,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,esk4_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_34])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88]),c_0_36])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_35,c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.63/1.79  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 1.63/1.79  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.63/1.79  #
% 1.63/1.79  # Preprocessing time       : 0.029 s
% 1.63/1.79  
% 1.63/1.79  # Proof found!
% 1.63/1.79  # SZS status Theorem
% 1.63/1.79  # SZS output start CNFRefutation
% 1.63/1.79  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 1.63/1.79  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.63/1.79  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 1.63/1.79  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 1.63/1.79  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.63/1.79  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.63/1.79  fof(t55_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_xboole_0(X2,X3)=>k5_relset_1(X3,X1,X4,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 1.63/1.79  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.63/1.79  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.63/1.79  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.63/1.79  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.63/1.79  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.63/1.79  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.63/1.79  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.63/1.79  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 1.63/1.79  fof(c_0_15, plain, ![X46, X47, X48, X49, X50, X51]:(((v1_funct_1(k1_tmap_1(X46,X47,X48,X49,X50,X51))|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))))&(v1_funct_2(k1_tmap_1(X46,X47,X48,X49,X50,X51),k4_subset_1(X46,X48,X49),X47)|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))))))&(m1_subset_1(k1_tmap_1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X46,X48,X49),X47)))|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 1.63/1.79  fof(c_0_16, plain, ![X14, X15]:(~v1_xboole_0(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 1.63/1.79  fof(c_0_17, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 1.63/1.79  fof(c_0_18, plain, ![X39, X40, X41, X42, X43, X44, X45]:(((k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41)=X43|X45!=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39))&(k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42)=X44|X45!=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39)))&(k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41)!=X43|k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42)!=X44|X45=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 1.63/1.79  cnf(c_0_19, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.63/1.79  cnf(c_0_20, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.63/1.79  cnf(c_0_21, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.63/1.79  cnf(c_0_22, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.63/1.79  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 1.63/1.79  cnf(c_0_24, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.79  cnf(c_0_25, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_19, c_0_20])).
% 1.63/1.79  cnf(c_0_26, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_21, c_0_20])).
% 1.63/1.79  cnf(c_0_27, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_22, c_0_20])).
% 1.63/1.79  cnf(c_0_28, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_29, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_24, c_0_20])]), c_0_25]), c_0_26]), c_0_27])).
% 1.63/1.79  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_41, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.79  fof(c_0_42, plain, ![X35, X36, X37, X38]:(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_partfun1(X35,X36,X37,X38)=k7_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 1.63/1.79  fof(c_0_43, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k5_relset_1(X27,X28,X29,X30)=k7_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 1.63/1.79  fof(c_0_44, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X31)))|(~r1_xboole_0(X32,X33)|k5_relset_1(X33,X31,X34,X32)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relset_1])])).
% 1.63/1.79  cnf(c_0_45, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38]), c_0_39]), c_0_40])).
% 1.63/1.79  cnf(c_0_46, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41, c_0_20])]), c_0_25]), c_0_26]), c_0_27])).
% 1.63/1.79  cnf(c_0_47, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.63/1.79  cnf(c_0_48, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.63/1.79  cnf(c_0_49, plain, (k5_relset_1(X2,X3,X1,X4)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.63/1.79  fof(c_0_50, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.63/1.79  fof(c_0_51, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.63/1.79  cnf(c_0_52, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31]), c_0_30]), c_0_33]), c_0_32]), c_0_35]), c_0_34]), c_0_36]), c_0_37])]), c_0_38]), c_0_39]), c_0_40])).
% 1.63/1.79  cnf(c_0_53, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_47, c_0_47])).
% 1.63/1.79  cnf(c_0_54, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.63/1.79  fof(c_0_55, plain, ![X20, X21]:((k9_relat_1(X21,X20)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_xboole_0(k1_relat_1(X21),X20)|k9_relat_1(X21,X20)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 1.63/1.79  fof(c_0_56, plain, ![X19]:k9_relat_1(k1_xboole_0,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 1.63/1.79  cnf(c_0_57, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.63/1.79  cnf(c_0_58, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.63/1.79  cnf(c_0_59, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33]), c_0_35])])).
% 1.63/1.79  cnf(c_0_60, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 1.63/1.79  cnf(c_0_61, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.63/1.79  cnf(c_0_62, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.63/1.79  cnf(c_0_63, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.63/1.79  cnf(c_0_64, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.63/1.79  cnf(c_0_65, negated_conjecture, (k7_relat_1(esk5_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_34])).
% 1.63/1.79  cnf(c_0_66, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(X3,X4,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_32]), c_0_34])])).
% 1.63/1.79  fof(c_0_67, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 1.63/1.79  fof(c_0_68, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.63/1.79  fof(c_0_69, plain, ![X22, X23]:((~r1_subset_1(X22,X23)|r1_xboole_0(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))&(~r1_xboole_0(X22,X23)|r1_subset_1(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 1.63/1.79  cnf(c_0_70, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,X3)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_xboole_0(X3,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_60]), c_0_33])])).
% 1.63/1.79  cnf(c_0_71, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 1.63/1.79  cnf(c_0_72, negated_conjecture, (k2_partfun1(X1,X2,esk5_0,X3)=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_xboole_0(X3,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_65]), c_0_32])])).
% 1.63/1.79  cnf(c_0_73, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_47]), c_0_32])])).
% 1.63/1.79  cnf(c_0_74, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.63/1.79  cnf(c_0_75, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.63/1.79  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.63/1.79  cnf(c_0_77, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.63/1.79  cnf(c_0_78, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.63/1.79  cnf(c_0_79, negated_conjecture, (k2_partfun1(X1,X2,esk5_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_72, c_0_71])).
% 1.63/1.79  cnf(c_0_80, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_73, c_0_34])).
% 1.63/1.79  cnf(c_0_81, plain, (k9_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.63/1.79  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_40]), c_0_39])).
% 1.63/1.79  cnf(c_0_83, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_78]), c_0_33])])).
% 1.63/1.79  cnf(c_0_84, negated_conjecture, (k7_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_79]), c_0_32])])).
% 1.63/1.79  cnf(c_0_85, negated_conjecture, (k7_relat_1(esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k7_relat_1(esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_47]), c_0_33])])).
% 1.63/1.79  cnf(c_0_86, negated_conjecture, (k9_subset_1(X1,esk3_0,esk4_0)=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.63/1.79  cnf(c_0_87, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_35])).
% 1.63/1.79  cnf(c_0_88, negated_conjecture, (k7_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_34])).
% 1.63/1.79  cnf(c_0_89, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88]), c_0_36])])).
% 1.63/1.79  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_35, c_0_89]), ['proof']).
% 1.63/1.79  # SZS output end CNFRefutation
% 1.63/1.79  # Proof object total steps             : 91
% 1.63/1.79  # Proof object clause steps            : 61
% 1.63/1.79  # Proof object formula steps           : 30
% 1.63/1.79  # Proof object conjectures             : 37
% 1.63/1.79  # Proof object clause conjectures      : 34
% 1.63/1.79  # Proof object formula conjectures     : 3
% 1.63/1.79  # Proof object initial clauses used    : 30
% 1.63/1.79  # Proof object initial formulas used   : 15
% 1.63/1.79  # Proof object generating inferences   : 25
% 1.63/1.79  # Proof object simplifying inferences  : 65
% 1.63/1.79  # Training examples: 0 positive, 0 negative
% 1.63/1.79  # Parsed axioms                        : 16
% 1.63/1.79  # Removed by relevancy pruning/SinE    : 0
% 1.63/1.79  # Initial clauses                      : 37
% 1.63/1.79  # Removed in clause preprocessing      : 0
% 1.63/1.79  # Initial clauses in saturation        : 37
% 1.63/1.79  # Processed clauses                    : 5568
% 1.63/1.79  # ...of these trivial                  : 0
% 1.63/1.79  # ...subsumed                          : 3813
% 1.63/1.79  # ...remaining for further processing  : 1755
% 1.63/1.79  # Other redundant clauses eliminated   : 5237
% 1.63/1.79  # Clauses deleted for lack of memory   : 0
% 1.63/1.79  # Backward-subsumed                    : 582
% 1.63/1.79  # Backward-rewritten                   : 4
% 1.63/1.79  # Generated clauses                    : 30721
% 1.63/1.79  # ...of the previous two non-trivial   : 25329
% 1.63/1.79  # Contextual simplify-reflections      : 393
% 1.63/1.79  # Paramodulations                      : 25415
% 1.63/1.79  # Factorizations                       : 0
% 1.63/1.79  # Equation resolutions                 : 5306
% 1.63/1.79  # Propositional unsat checks           : 0
% 1.63/1.79  #    Propositional check models        : 0
% 1.63/1.79  #    Propositional check unsatisfiable : 0
% 1.63/1.79  #    Propositional clauses             : 0
% 1.63/1.79  #    Propositional clauses after purity: 0
% 1.63/1.79  #    Propositional unsat core size     : 0
% 1.63/1.79  #    Propositional preprocessing time  : 0.000
% 1.63/1.79  #    Propositional encoding time       : 0.000
% 1.63/1.79  #    Propositional solver time         : 0.000
% 1.63/1.79  #    Success case prop preproc time    : 0.000
% 1.63/1.79  #    Success case prop encoding time   : 0.000
% 1.63/1.79  #    Success case prop solver time     : 0.000
% 1.63/1.79  # Current number of processed clauses  : 1165
% 1.63/1.79  #    Positive orientable unit clauses  : 29
% 1.63/1.79  #    Positive unorientable unit clauses: 0
% 1.63/1.79  #    Negative unit clauses             : 6
% 1.63/1.79  #    Non-unit-clauses                  : 1130
% 1.63/1.79  # Current number of unprocessed clauses: 19478
% 1.63/1.79  # ...number of literals in the above   : 413229
% 1.63/1.79  # Current number of archived formulas  : 0
% 1.63/1.79  # Current number of archived clauses   : 587
% 1.63/1.79  # Clause-clause subsumption calls (NU) : 618509
% 1.63/1.79  # Rec. Clause-clause subsumption calls : 14331
% 1.63/1.79  # Non-unit clause-clause subsumptions  : 4785
% 1.63/1.79  # Unit Clause-clause subsumption calls : 617
% 1.63/1.79  # Rewrite failures with RHS unbound    : 0
% 1.63/1.79  # BW rewrite match attempts            : 5
% 1.63/1.79  # BW rewrite match successes           : 4
% 1.63/1.79  # Condensation attempts                : 0
% 1.63/1.79  # Condensation successes               : 0
% 1.63/1.79  # Termbank termtop insertions          : 2807451
% 1.63/1.79  
% 1.63/1.79  # -------------------------------------------------
% 1.63/1.79  # User time                : 1.416 s
% 1.63/1.79  # System time              : 0.032 s
% 1.63/1.79  # Total time               : 1.448 s
% 1.63/1.79  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
