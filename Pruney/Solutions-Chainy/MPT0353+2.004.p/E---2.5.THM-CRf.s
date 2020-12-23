%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:43 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 362 expanded)
%              Number of clauses        :   51 ( 159 expanded)
%              Number of leaves         :   12 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 532 expanded)
%              Number of equality atoms :   64 ( 323 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] : k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X11,X10)) = k3_xboole_0(k5_xboole_0(X9,X11),X10) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_14,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_15,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | m1_subset_1(k9_subset_1(X20,X21,X22),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & k7_subset_1(esk1_0,esk2_0,esk3_0) != k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | k9_subset_1(X28,X29,X30) = k3_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_20,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk1_0,X1,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk2_0) = k3_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk1_0,X1,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk3_0) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_36,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k9_subset_1(X15,X16,X17) = k9_subset_1(X15,X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k7_subset_1(X25,X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k3_subset_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2))) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_38])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk3_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k3_subset_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,esk3_0) != k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( k9_subset_1(esk1_0,esk2_0,X1) = k3_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_33])).

cnf(c_0_54,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_55,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_22]),c_0_21]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))) = k3_subset_1(esk1_0,k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0)) = k3_subset_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1))) = k3_subset_1(esk1_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk3_0)) = k3_subset_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,esk3_0) != k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( k7_subset_1(esk1_0,esk2_0,X1) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k3_xboole_0(X1,esk2_0))) = k3_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_xboole_0(esk1_0,esk2_0)) = k3_subset_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_23]),c_0_23]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,k3_xboole_0(X1,esk3_0))) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_xboole_0(esk1_0,esk3_0)) = k3_subset_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_59]),c_0_23]),c_0_23]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_40])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) = k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_70]),c_0_31]),c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk3_0) = k3_subset_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_71]),c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.37/0.53  # and selection function SelectCQArNTNp.
% 0.37/0.53  #
% 0.37/0.53  # Preprocessing time       : 0.027 s
% 0.37/0.53  # Presaturation interreduction done
% 0.37/0.53  
% 0.37/0.53  # Proof found!
% 0.37/0.53  # SZS status Theorem
% 0.37/0.53  # SZS output start CNFRefutation
% 0.37/0.53  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 0.37/0.53  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.37/0.53  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.37/0.53  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.53  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.37/0.53  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.37/0.53  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.37/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.53  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.37/0.53  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.37/0.53  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.37/0.53  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.37/0.53  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.37/0.53  fof(c_0_13, plain, ![X9, X10, X11]:k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X11,X10))=k3_xboole_0(k5_xboole_0(X9,X11),X10), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.37/0.53  fof(c_0_14, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.37/0.53  fof(c_0_15, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.53  fof(c_0_16, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X20))|m1_subset_1(k9_subset_1(X20,X21,X22),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.37/0.53  fof(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&k7_subset_1(esk1_0,esk2_0,esk3_0)!=k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.37/0.53  fof(c_0_18, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X28))|k9_subset_1(X28,X29,X30)=k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.37/0.53  fof(c_0_19, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.37/0.53  fof(c_0_20, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.53  cnf(c_0_21, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.53  cnf(c_0_22, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.53  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.53  cnf(c_0_24, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.53  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.53  cnf(c_0_26, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.53  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.53  fof(c_0_28, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.37/0.53  cnf(c_0_29, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.53  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.53  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.37/0.53  cnf(c_0_32, negated_conjecture, (m1_subset_1(k9_subset_1(esk1_0,X1,esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.37/0.53  cnf(c_0_33, negated_conjecture, (k9_subset_1(esk1_0,X1,esk2_0)=k3_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.37/0.53  cnf(c_0_34, negated_conjecture, (m1_subset_1(k9_subset_1(esk1_0,X1,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.37/0.53  cnf(c_0_35, negated_conjecture, (k9_subset_1(esk1_0,X1,esk3_0)=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.37/0.53  fof(c_0_36, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X15))|k9_subset_1(X15,X16,X17)=k9_subset_1(X15,X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.37/0.53  fof(c_0_37, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k7_subset_1(X25,X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.37/0.53  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.53  cnf(c_0_39, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.37/0.53  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.37/0.53  cnf(c_0_41, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,esk2_0),k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.37/0.53  cnf(c_0_42, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,esk3_0),k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.37/0.53  cnf(c_0_43, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.53  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.53  fof(c_0_45, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k3_subset_1(X23,k3_subset_1(X23,X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.37/0.53  cnf(c_0_46, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X4,X2)))=k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_21, c_0_38])).
% 0.37/0.53  cnf(c_0_47, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.37/0.53  cnf(c_0_48, negated_conjecture, (m1_subset_1(k3_xboole_0(esk2_0,X1),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 0.37/0.53  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.37/0.53  cnf(c_0_50, negated_conjecture, (m1_subset_1(k3_xboole_0(esk3_0,X1),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.37/0.53  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k3_subset_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_27])).
% 0.37/0.53  cnf(c_0_52, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,esk3_0)!=k9_subset_1(esk1_0,esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.53  cnf(c_0_53, negated_conjecture, (k9_subset_1(esk1_0,esk2_0,X1)=k3_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_33])).
% 0.37/0.53  cnf(c_0_54, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_44, c_0_30])).
% 0.37/0.53  cnf(c_0_55, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.37/0.53  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_22]), c_0_21]), c_0_23])).
% 0.37/0.53  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)))=k3_subset_1(esk1_0,k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.37/0.53  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0))=k3_subset_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_49, c_0_40])).
% 0.37/0.53  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,X1)))=k3_subset_1(esk1_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_50])).
% 0.37/0.53  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk3_0))=k3_subset_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_51, c_0_40])).
% 0.37/0.53  cnf(c_0_61, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,esk3_0)!=k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_23])).
% 0.37/0.53  cnf(c_0_62, negated_conjecture, (k7_subset_1(esk1_0,esk2_0,X1)=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_54, c_0_25])).
% 0.37/0.53  cnf(c_0_63, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,k3_xboole_0(X1,esk2_0)))=k3_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_41])).
% 0.37/0.53  cnf(c_0_64, negated_conjecture, (k3_subset_1(esk1_0,k3_xboole_0(esk1_0,esk2_0))=k3_subset_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_23]), c_0_23]), c_0_58])).
% 0.37/0.53  cnf(c_0_65, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_55, c_0_25])).
% 0.37/0.53  cnf(c_0_66, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,k3_xboole_0(X1,esk3_0)))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_42])).
% 0.37/0.53  cnf(c_0_67, negated_conjecture, (k3_subset_1(esk1_0,k3_xboole_0(esk1_0,esk3_0))=k3_subset_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_59]), c_0_23]), c_0_23]), c_0_60])).
% 0.37/0.53  cnf(c_0_68, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_55, c_0_27])).
% 0.37/0.53  cnf(c_0_69, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.37/0.53  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.37/0.53  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.37/0.53  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,k3_subset_1(esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_69, c_0_40])).
% 0.37/0.53  cnf(c_0_73, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))=k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_70]), c_0_31]), c_0_23])).
% 0.37/0.53  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk1_0,esk3_0)=k3_subset_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_71]), c_0_60])).
% 0.37/0.53  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74])]), ['proof']).
% 0.37/0.53  # SZS output end CNFRefutation
% 0.37/0.53  # Proof object total steps             : 76
% 0.37/0.53  # Proof object clause steps            : 51
% 0.37/0.53  # Proof object formula steps           : 25
% 0.37/0.53  # Proof object conjectures             : 36
% 0.37/0.53  # Proof object clause conjectures      : 33
% 0.37/0.53  # Proof object formula conjectures     : 3
% 0.37/0.53  # Proof object initial clauses used    : 14
% 0.37/0.53  # Proof object initial formulas used   : 12
% 0.37/0.53  # Proof object generating inferences   : 26
% 0.37/0.53  # Proof object simplifying inferences  : 29
% 0.37/0.53  # Training examples: 0 positive, 0 negative
% 0.37/0.53  # Parsed axioms                        : 12
% 0.37/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.53  # Initial clauses                      : 14
% 0.37/0.53  # Removed in clause preprocessing      : 1
% 0.37/0.53  # Initial clauses in saturation        : 13
% 0.37/0.53  # Processed clauses                    : 668
% 0.37/0.53  # ...of these trivial                  : 250
% 0.37/0.53  # ...subsumed                          : 100
% 0.37/0.53  # ...remaining for further processing  : 318
% 0.37/0.53  # Other redundant clauses eliminated   : 0
% 0.37/0.53  # Clauses deleted for lack of memory   : 0
% 0.37/0.53  # Backward-subsumed                    : 0
% 0.37/0.53  # Backward-rewritten                   : 76
% 0.37/0.53  # Generated clauses                    : 10670
% 0.37/0.53  # ...of the previous two non-trivial   : 8646
% 0.37/0.53  # Contextual simplify-reflections      : 0
% 0.37/0.53  # Paramodulations                      : 10670
% 0.37/0.53  # Factorizations                       : 0
% 0.37/0.53  # Equation resolutions                 : 0
% 0.37/0.53  # Propositional unsat checks           : 0
% 0.37/0.53  #    Propositional check models        : 0
% 0.37/0.53  #    Propositional check unsatisfiable : 0
% 0.37/0.53  #    Propositional clauses             : 0
% 0.37/0.53  #    Propositional clauses after purity: 0
% 0.37/0.53  #    Propositional unsat core size     : 0
% 0.37/0.53  #    Propositional preprocessing time  : 0.000
% 0.37/0.53  #    Propositional encoding time       : 0.000
% 0.37/0.53  #    Propositional solver time         : 0.000
% 0.37/0.53  #    Success case prop preproc time    : 0.000
% 0.37/0.53  #    Success case prop encoding time   : 0.000
% 0.37/0.53  #    Success case prop solver time     : 0.000
% 0.37/0.53  # Current number of processed clauses  : 229
% 0.37/0.53  #    Positive orientable unit clauses  : 216
% 0.37/0.53  #    Positive unorientable unit clauses: 7
% 0.37/0.53  #    Negative unit clauses             : 0
% 0.37/0.53  #    Non-unit-clauses                  : 6
% 0.37/0.53  # Current number of unprocessed clauses: 7933
% 0.37/0.53  # ...number of literals in the above   : 7933
% 0.37/0.53  # Current number of archived formulas  : 0
% 0.37/0.53  # Current number of archived clauses   : 90
% 0.37/0.53  # Clause-clause subsumption calls (NU) : 0
% 0.37/0.53  # Rec. Clause-clause subsumption calls : 0
% 0.37/0.53  # Non-unit clause-clause subsumptions  : 0
% 0.37/0.53  # Unit Clause-clause subsumption calls : 61
% 0.37/0.53  # Rewrite failures with RHS unbound    : 0
% 0.37/0.53  # BW rewrite match attempts            : 623
% 0.37/0.53  # BW rewrite match successes           : 137
% 0.37/0.53  # Condensation attempts                : 0
% 0.37/0.53  # Condensation successes               : 0
% 0.37/0.53  # Termbank termtop insertions          : 167374
% 0.37/0.54  
% 0.37/0.54  # -------------------------------------------------
% 0.37/0.54  # User time                : 0.178 s
% 0.37/0.54  # System time              : 0.008 s
% 0.37/0.54  # Total time               : 0.186 s
% 0.37/0.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
