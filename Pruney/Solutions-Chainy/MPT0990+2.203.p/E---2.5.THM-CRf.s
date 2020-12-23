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
% DateTime   : Thu Dec  3 11:03:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 186 expanded)
%              Number of clauses        :   29 (  56 expanded)
%              Number of leaves         :    6 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  298 (1740 expanded)
%              Number of equality atoms :   82 ( 545 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(t22_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ( k2_relset_1(X1,X2,X3) = X2
        <=> ! [X4] :
              ( X4 != k1_xboole_0
             => ! [X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X2,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) )
                 => ! [X6] :
                      ( ( v1_funct_1(X6)
                        & v1_funct_2(X6,X2,X4)
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) )
                     => ( r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))
                       => r2_relset_1(X2,X4,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
                & v2_funct_1(X3) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( k2_relset_1(X17,X18,X19) != X18
        | X20 = k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X18,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
        | ~ r2_relset_1(X17,X20,k1_partfun1(X17,X18,X18,X20,X19,X21),k1_partfun1(X17,X18,X18,X20,X19,X22))
        | r2_relset_1(X18,X20,X21,X22)
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( esk1_3(X17,X18,X19) != k1_xboole_0
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_1(esk2_3(X17,X18,X19))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_2(esk2_3(X17,X18,X19),X18,esk1_3(X17,X18,X19))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,esk1_3(X17,X18,X19))))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_1(esk3_3(X17,X18,X19))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_2(esk3_3(X17,X18,X19),X18,esk1_3(X17,X18,X19))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk3_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,esk1_3(X17,X18,X19))))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r2_relset_1(X17,esk1_3(X17,X18,X19),k1_partfun1(X17,X18,X18,esk1_3(X17,X18,X19),X19,esk2_3(X17,X18,X19)),k1_partfun1(X17,X18,X18,esk1_3(X17,X18,X19),X19,esk3_3(X17,X18,X19)))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ r2_relset_1(X18,esk1_3(X17,X18,X19),esk2_3(X17,X18,X19),esk3_3(X17,X18,X19))
        | k2_relset_1(X17,X18,X19) = X18
        | X18 = k1_xboole_0
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_2])])])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ~ v1_funct_1(X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_partfun1(X11,X12,X13,X14,X15,X16) = k5_relat_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_9,plain,(
    ! [X29,X30,X31] :
      ( ( k5_relat_1(X31,k2_funct_1(X31)) = k6_partfun1(X29)
        | X30 = k1_xboole_0
        | k2_relset_1(X29,X30,X31) != X30
        | ~ v2_funct_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( k5_relat_1(k2_funct_1(X31),X31) = k6_partfun1(X30)
        | X30 = k1_xboole_0
        | k2_relset_1(X29,X30,X31) != X30
        | ~ v2_funct_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
    & k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))
    & v2_funct_1(esk6_0)
    & esk4_0 != k1_xboole_0
    & esk5_0 != k1_xboole_0
    & esk7_0 != k2_funct_1(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X26,X27,X28] :
      ( ( v1_funct_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v1_funct_2(k2_funct_1(X28),X27,X26)
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( m1_subset_1(k2_funct_1(X28),k1_zfmisc_1(k2_zfmisc_1(X27,X26)))
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_relset_1(X7,X8,X9,X10)
        | X9 = X10
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_relset_1(X7,X8,X9,X10)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_13,plain,
    ( X4 = k1_xboole_0
    | r2_relset_1(X2,X4,X5,X6)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,X3) != X2
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_relset_1(X1,X2,X3,X4)
    | k2_relset_1(X5,X1,X6) != X1
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_2(X6,X5,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | ~ r2_relset_1(X5,X2,k1_partfun1(X5,X1,X1,X2,X6,X3),k5_relat_1(X6,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(esk6_0,k2_funct_1(esk6_0)) = k6_partfun1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( X1 = k2_funct_1(X2)
    | k2_relset_1(X3,X4,X2) != X4
    | ~ v2_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ v1_funct_1(X2)
    | ~ r2_relset_1(X4,X3,X1,k2_funct_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_relset_1(X2,X1,X3,k2_funct_1(esk6_0))
    | k2_relset_1(X4,X2,esk6_0) != X2
    | ~ v1_funct_2(k2_funct_1(esk6_0),X2,X1)
    | ~ v1_funct_2(esk6_0,X4,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3)
    | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X2,X2,X1,esk6_0,X3),k6_partfun1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k2_funct_1(X1) = esk7_0
    | k2_relset_1(esk4_0,esk5_0,X1) != esk5_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,esk4_0,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(esk6_0))
    | ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17]),c_0_19]),c_0_32]),c_0_33]),c_0_16]),c_0_29])]),c_0_34]),c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 != k2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])]),c_0_37])).

cnf(c_0_39,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.41  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.20/0.41  fof(t22_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>(k2_relset_1(X1,X2,X3)=X2<=>![X4]:(X4!=k1_xboole_0=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X2,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4))))=>(r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))=>r2_relset_1(X2,X4,X5,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_2)).
% 0.20/0.41  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.41  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.41  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.41  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.41  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.20/0.41  fof(c_0_7, plain, ![X17, X18, X19, X20, X21, X22]:((k2_relset_1(X17,X18,X19)!=X18|(X20=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,X18,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))|(~v1_funct_1(X22)|~v1_funct_2(X22,X18,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X20)))|(~r2_relset_1(X17,X20,k1_partfun1(X17,X18,X18,X20,X19,X21),k1_partfun1(X17,X18,X18,X20,X19,X22))|r2_relset_1(X18,X20,X21,X22)))))|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((esk1_3(X17,X18,X19)!=k1_xboole_0|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((((v1_funct_1(esk2_3(X17,X18,X19))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(v1_funct_2(esk2_3(X17,X18,X19),X18,esk1_3(X17,X18,X19))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,esk1_3(X17,X18,X19))))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((((v1_funct_1(esk3_3(X17,X18,X19))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(v1_funct_2(esk3_3(X17,X18,X19),X18,esk1_3(X17,X18,X19))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(m1_subset_1(esk3_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(X18,esk1_3(X17,X18,X19))))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((r2_relset_1(X17,esk1_3(X17,X18,X19),k1_partfun1(X17,X18,X18,esk1_3(X17,X18,X19),X19,esk2_3(X17,X18,X19)),k1_partfun1(X17,X18,X18,esk1_3(X17,X18,X19),X19,esk3_3(X17,X18,X19)))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(~r2_relset_1(X18,esk1_3(X17,X18,X19),esk2_3(X17,X18,X19),esk3_3(X17,X18,X19))|k2_relset_1(X17,X18,X19)=X18|X18=k1_xboole_0|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_2])])])])])).
% 0.20/0.41  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16]:(~v1_funct_1(X15)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k1_partfun1(X11,X12,X13,X14,X15,X16)=k5_relat_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.41  fof(c_0_9, plain, ![X29, X30, X31]:((k5_relat_1(X31,k2_funct_1(X31))=k6_partfun1(X29)|X30=k1_xboole_0|(k2_relset_1(X29,X30,X31)!=X30|~v2_funct_1(X31))|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(k5_relat_1(k2_funct_1(X31),X31)=k6_partfun1(X30)|X30=k1_xboole_0|(k2_relset_1(X29,X30,X31)!=X30|~v2_funct_1(X31))|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.41  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0&r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0)))&v2_funct_1(esk6_0))&((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk7_0!=k2_funct_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.41  fof(c_0_11, plain, ![X26, X27, X28]:(((v1_funct_1(k2_funct_1(X28))|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(v1_funct_2(k2_funct_1(X28),X27,X26)|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(m1_subset_1(k2_funct_1(X28),k1_zfmisc_1(k2_zfmisc_1(X27,X26)))|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.41  fof(c_0_12, plain, ![X7, X8, X9, X10]:((~r2_relset_1(X7,X8,X9,X10)|X9=X10|(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_relset_1(X7,X8,X9,X10)|(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.41  cnf(c_0_13, plain, (X4=k1_xboole_0|r2_relset_1(X2,X4,X5,X6)|X2=k1_xboole_0|k2_relset_1(X1,X2,X3)!=X2|~v1_funct_1(X5)|~v1_funct_2(X5,X2,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r2_relset_1(X1,X4,k1_partfun1(X1,X2,X2,X4,X3,X5),k1_partfun1(X1,X2,X2,X4,X3,X6))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_14, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_15, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_22, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_23, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_24, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_25, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_relset_1(X1,X2,X3,X4)|k2_relset_1(X5,X1,X6)!=X1|~v1_funct_2(X4,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_2(X6,X5,X1)|~v1_funct_1(X4)|~v1_funct_1(X3)|~v1_funct_1(X6)|~r2_relset_1(X5,X2,k1_partfun1(X5,X1,X1,X2,X6,X3),k5_relat_1(X6,X4))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X1)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (k5_relat_1(esk6_0,k2_funct_1(esk6_0))=k6_partfun1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.41  cnf(c_0_28, plain, (X1=k2_funct_1(X2)|k2_relset_1(X3,X4,X2)!=X4|~v2_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~v1_funct_1(X2)|~r2_relset_1(X4,X3,X1,k2_funct_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|r2_relset_1(X2,X1,X3,k2_funct_1(esk6_0))|k2_relset_1(X4,X2,esk6_0)!=X2|~v1_funct_2(k2_funct_1(esk6_0),X2,X1)|~v1_funct_2(esk6_0,X4,X2)|~v1_funct_2(X3,X2,X1)|~v1_funct_1(X3)|~r2_relset_1(X4,X1,k1_partfun1(X4,X2,X2,X1,esk6_0,X3),k6_partfun1(esk4_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_20])])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k2_funct_1(X1)=esk7_0|k2_relset_1(esk4_0,esk5_0,X1)!=esk5_0|~v2_funct_1(X1)|~v1_funct_2(X1,esk4_0,esk5_0)|~v1_funct_1(X1)|~r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (r2_relset_1(esk5_0,esk4_0,esk7_0,k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_17]), c_0_19]), c_0_32]), c_0_33]), c_0_16]), c_0_29])]), c_0_34]), c_0_21])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk7_0!=k2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])]), c_0_37])).
% 0.20/0.41  cnf(c_0_39, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_24]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_16])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 42
% 0.20/0.41  # Proof object clause steps            : 29
% 0.20/0.41  # Proof object formula steps           : 13
% 0.20/0.41  # Proof object conjectures             : 23
% 0.20/0.41  # Proof object clause conjectures      : 20
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 19
% 0.20/0.41  # Proof object initial formulas used   : 6
% 0.20/0.41  # Proof object generating inferences   : 10
% 0.20/0.41  # Proof object simplifying inferences  : 42
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 6
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 30
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 30
% 0.20/0.41  # Processed clauses                    : 212
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 4
% 0.20/0.41  # ...remaining for further processing  : 208
% 0.20/0.41  # Other redundant clauses eliminated   : 1
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 311
% 0.20/0.41  # ...of the previous two non-trivial   : 300
% 0.20/0.41  # Contextual simplify-reflections      : 160
% 0.20/0.41  # Paramodulations                      : 304
% 0.20/0.41  # Factorizations                       : 6
% 0.20/0.41  # Equation resolutions                 : 1
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 176
% 0.20/0.41  #    Positive orientable unit clauses  : 13
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 159
% 0.20/0.41  # Current number of unprocessed clauses: 148
% 0.20/0.41  # ...number of literals in the above   : 1274
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 31
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 6674
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 730
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 165
% 0.20/0.41  # Unit Clause-clause subsumption calls : 41
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 1
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 30394
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.063 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.069 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
