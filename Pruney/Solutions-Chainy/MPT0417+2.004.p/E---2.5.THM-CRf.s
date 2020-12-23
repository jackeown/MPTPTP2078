%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:43 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 155 expanded)
%              Number of clauses        :   34 (  67 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 305 expanded)
%              Number of equality atoms :   51 ( 158 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k7_subset_1(X1,k2_subset_1(X1),k5_setfam_1(X1,X2)) = k6_setfam_1(X1,k7_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t48_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(c_0_12,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | X25 = k1_xboole_0
      | k7_subset_1(X24,k2_subset_1(X24),k5_setfam_1(X24,X25)) = k6_setfam_1(X24,k7_setfam_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_setfam_1])])).

fof(c_0_13,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_setfam_1])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | k7_subset_1(X2,k2_subset_1(X2),k5_setfam_1(X2,X1)) = k6_setfam_1(X2,k7_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k7_setfam_1(X18,X19),k1_zfmisc_1(k1_zfmisc_1(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | X23 = k1_xboole_0
      | k7_setfam_1(X22,X23) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

fof(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 != k1_xboole_0
    & k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k7_subset_1(esk1_0,k2_subset_1(esk1_0),k6_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k3_subset_1(X5,X6) = k4_xboole_0(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k7_subset_1(X13,X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_22,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | k7_subset_1(X2,X2,k5_setfam_1(X2,X1)) = k6_setfam_1(X2,k7_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,k3_subset_1(X11,X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k7_subset_1(esk1_0,k2_subset_1(esk1_0),k6_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | m1_subset_1(k7_subset_1(X8,X9,X10),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_34,plain,
    ( k7_subset_1(X1,X1,k5_setfam_1(X1,k7_setfam_1(X1,X2))) = k6_setfam_1(X1,k7_setfam_1(X1,k7_setfam_1(X1,X2)))
    | k7_setfam_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) != k7_subset_1(esk1_0,esk1_0,k6_setfam_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_39,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_41,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k7_subset_1(esk1_0,esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))) = k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_35])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | k7_setfam_1(X20,k7_setfam_1(X20,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_44,plain,
    ( k3_subset_1(X1,k7_subset_1(X2,X1,X3)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k7_subset_1(X1,esk1_0,k6_setfam_1(esk1_0,esk2_0)) != k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_40])])).

cnf(c_0_47,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k3_subset_1(esk1_0,k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)))) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_40])])).

fof(c_0_49,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))
      | m1_subset_1(k5_setfam_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_50,negated_conjecture,
    ( k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) != k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26])])).

cnf(c_0_52,negated_conjecture,
    ( k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_26])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) != k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0)) = k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_26])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_57,c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.027 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t47_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k7_subset_1(X1,k2_subset_1(X1),k5_setfam_1(X1,X2))=k6_setfam_1(X1,k7_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 0.21/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.40  fof(t48_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 0.21/0.40  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.21/0.40  fof(t46_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.21/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.40  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.21/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.21/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.21/0.40  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.21/0.40  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.21/0.40  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.21/0.40  fof(c_0_12, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|(X25=k1_xboole_0|k7_subset_1(X24,k2_subset_1(X24),k5_setfam_1(X24,X25))=k6_setfam_1(X24,k7_setfam_1(X24,X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_setfam_1])])).
% 0.21/0.40  fof(c_0_13, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.40  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k7_subset_1(X1,k2_subset_1(X1),k6_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t48_setfam_1])).
% 0.21/0.40  cnf(c_0_15, plain, (X1=k1_xboole_0|k7_subset_1(X2,k2_subset_1(X2),k5_setfam_1(X2,X1))=k6_setfam_1(X2,k7_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_16, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  fof(c_0_17, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k7_setfam_1(X18,X19),k1_zfmisc_1(k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.21/0.40  fof(c_0_18, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))|(X23=k1_xboole_0|k7_setfam_1(X22,X23)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).
% 0.21/0.40  fof(c_0_19, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(esk2_0!=k1_xboole_0&k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k7_subset_1(esk1_0,k2_subset_1(esk1_0),k6_setfam_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.40  fof(c_0_20, plain, ![X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|k3_subset_1(X5,X6)=k4_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.40  fof(c_0_21, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k7_subset_1(X13,X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.21/0.40  fof(c_0_22, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.21/0.40  cnf(c_0_23, plain, (X1=k1_xboole_0|k7_subset_1(X2,X2,k5_setfam_1(X2,X1))=k6_setfam_1(X2,k7_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.40  cnf(c_0_24, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_25, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|k7_setfam_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  fof(c_0_28, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k3_subset_1(X11,k3_subset_1(X11,X12))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.21/0.40  cnf(c_0_29, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_30, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k7_subset_1(esk1_0,k2_subset_1(esk1_0),k6_setfam_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_32, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  fof(c_0_33, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|m1_subset_1(k7_subset_1(X8,X9,X10),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.21/0.40  cnf(c_0_34, plain, (k7_subset_1(X1,X1,k5_setfam_1(X1,k7_setfam_1(X1,X2)))=k6_setfam_1(X1,k7_setfam_1(X1,k7_setfam_1(X1,X2)))|k7_setfam_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (k7_setfam_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.21/0.40  cnf(c_0_36, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.40  cnf(c_0_37, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))!=k7_subset_1(esk1_0,esk1_0,k6_setfam_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 0.21/0.40  cnf(c_0_39, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_30, c_0_30])).
% 0.21/0.40  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_32, c_0_16])).
% 0.21/0.40  cnf(c_0_41, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (k7_subset_1(esk1_0,esk1_0,k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)))=k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_35])).
% 0.21/0.40  fof(c_0_43, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))|k7_setfam_1(X20,k7_setfam_1(X20,X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.21/0.40  cnf(c_0_44, plain, (k3_subset_1(X1,k7_subset_1(X2,X1,X3))=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (k7_subset_1(X1,esk1_0,k6_setfam_1(esk1_0,esk2_0))!=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_40])])).
% 0.21/0.40  cnf(c_0_47, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (k3_subset_1(esk1_0,k6_setfam_1(esk1_0,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))))=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_42]), c_0_40])])).
% 0.21/0.40  fof(c_0_49, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))|m1_subset_1(k5_setfam_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))!=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.21/0.40  cnf(c_0_51, negated_conjecture, (m1_subset_1(k6_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26])])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_47]), c_0_26])])).
% 0.21/0.40  cnf(c_0_53, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))!=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.21/0.40  cnf(c_0_55, negated_conjecture, (k3_subset_1(esk1_0,k6_setfam_1(esk1_0,esk2_0))=k5_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0))|~m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (~m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0)))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_24]), c_0_26])])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_57, c_0_40]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 59
% 0.21/0.40  # Proof object clause steps            : 34
% 0.21/0.40  # Proof object formula steps           : 25
% 0.21/0.40  # Proof object conjectures             : 20
% 0.21/0.40  # Proof object clause conjectures      : 17
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 14
% 0.21/0.40  # Proof object initial formulas used   : 12
% 0.21/0.40  # Proof object generating inferences   : 16
% 0.21/0.40  # Proof object simplifying inferences  : 19
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 12
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 14
% 0.21/0.40  # Removed in clause preprocessing      : 1
% 0.21/0.40  # Initial clauses in saturation        : 13
% 0.21/0.40  # Processed clauses                    : 306
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 115
% 0.21/0.40  # ...remaining for further processing  : 191
% 0.21/0.40  # Other redundant clauses eliminated   : 2
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 10
% 0.21/0.40  # Backward-rewritten                   : 2
% 0.21/0.40  # Generated clauses                    : 1190
% 0.21/0.40  # ...of the previous two non-trivial   : 1097
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 1188
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 2
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 166
% 0.21/0.40  #    Positive orientable unit clauses  : 13
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 4
% 0.21/0.40  #    Non-unit-clauses                  : 149
% 0.21/0.40  # Current number of unprocessed clauses: 811
% 0.21/0.40  # ...number of literals in the above   : 2736
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 26
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 2849
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 2469
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 125
% 0.21/0.40  # Unit Clause-clause subsumption calls : 104
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 13
% 0.21/0.40  # BW rewrite match successes           : 2
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 25082
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.056 s
% 0.21/0.40  # System time              : 0.007 s
% 0.21/0.40  # Total time               : 0.064 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
