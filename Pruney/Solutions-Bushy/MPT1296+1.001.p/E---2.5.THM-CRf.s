%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1296+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:04 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   31 (  44 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  85 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t12_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | X14 = k1_xboole_0
      | k5_setfam_1(X13,k7_setfam_1(X13,X14)) = k7_subset_1(X13,k2_subset_1(X13),k6_setfam_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_setfam_1])])).

fof(c_0_8,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tops_2])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | k5_setfam_1(X2,k7_setfam_1(X2,X1)) = k7_subset_1(X2,k2_subset_1(X2),k6_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 != k1_xboole_0
    & k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_14,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | k7_subset_1(X10,X11,X12) = k4_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | k5_setfam_1(X2,k7_setfam_1(X2,X1)) = k7_subset_1(X2,X2,k6_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k7_subset_1(esk1_0,esk1_0,k6_setfam_1(esk1_0,esk2_0)) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) = k4_xboole_0(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k3_subset_1(X5,X6) = k4_xboole_0(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk1_0,k6_setfam_1(esk1_0,esk2_0)) != k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | m1_subset_1(k6_setfam_1(X8,X9),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_setfam_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( m1_subset_1(k6_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])]),
    [proof]).

%------------------------------------------------------------------------------
