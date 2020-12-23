%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:37 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 413 expanded)
%              Number of clauses        :   20 ( 127 expanded)
%              Number of leaves         :    2 (  99 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 (2696 expanded)
%              Number of equality atoms :    8 (  75 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r1_partfun1(X2,X3)
           => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

fof(t142_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r1_partfun1(X2,X3)
             => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t143_funct_2])).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8] :
      ( ( X6 = k1_xboole_0
        | r2_relset_1(X5,X6,X7,X8)
        | ~ r1_partfun1(X7,X8)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X5,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
      & ( X5 != k1_xboole_0
        | r2_relset_1(X5,X6,X7,X8)
        | ~ r1_partfun1(X7,X8)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X5,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_2])])])])).

fof(c_0_4,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r1_partfun1(esk2_0,esk3_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X1 = k1_xboole_0
    | r2_relset_1(X2,X1,X3,X4)
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r2_relset_1(esk1_0,esk1_0,X1,esk3_0)
    | ~ r1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ v1_funct_2(X1,esk1_0,esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r1_partfun1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r2_relset_1(X1,X2,X3,X4)
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_17,plain,
    ( r2_relset_1(k1_xboole_0,X1,X2,X3)
    | ~ r1_partfun1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X3,k1_xboole_0,X1)
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_16]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_16]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,X1,esk3_0)
    | ~ r1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_8])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_16]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_16]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_16]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_11]),c_0_22]),c_0_13])]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
