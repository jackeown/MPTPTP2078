%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:43 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   67 (19371 expanded)
%              Number of clauses        :   44 (8631 expanded)
%              Number of leaves         :   11 (5368 expanded)
%              Depth                    :   19
%              Number of atoms          :   92 (19950 expanded)
%              Number of equality atoms :   45 (18903 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_11,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_12,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X22,X23] : k3_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_14,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_25,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] : k4_xboole_0(X17,k4_xboole_0(X18,X19)) = k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_17])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X1),k2_xboole_0(X1,X1))),k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_28]),c_0_23]),c_0_36]),c_0_23]),c_0_36]),c_0_23])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_39]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_28]),c_0_23]),c_0_23]),c_0_28]),c_0_23]),c_0_23]),c_0_28])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))) = X1
    | ~ r1_tarski(X1,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_28]),c_0_23])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_40])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_40]),c_0_40]),c_0_42])])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_43]),c_0_44]),c_0_43])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_44]),c_0_44])).

fof(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))) = k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_43]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_51,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_43]),c_0_23]),c_0_43]),c_0_40]),c_0_43]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_16]),c_0_17])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_55,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,X1),k2_xboole_0(esk1_0,X1)) = esk1_0
    | ~ r1_tarski(k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_16]),c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_60]),c_0_43]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.48/0.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.027 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.48/0.65  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.48/0.65  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.48/0.65  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.48/0.65  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.65  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.48/0.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.48/0.65  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.48/0.65  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.48/0.65  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.48/0.65  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.48/0.65  fof(c_0_11, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.48/0.65  fof(c_0_12, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.48/0.65  fof(c_0_13, plain, ![X22, X23]:k3_xboole_0(X22,X23)=k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.48/0.65  fof(c_0_14, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.48/0.65  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.65  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.65  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.65  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.65  fof(c_0_19, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.65  cnf(c_0_20, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.48/0.65  cnf(c_0_21, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.48/0.65  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.65  cnf(c_0_23, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.65  fof(c_0_24, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.48/0.65  fof(c_0_25, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.48/0.65  fof(c_0_26, plain, ![X17, X18, X19]:k4_xboole_0(X17,k4_xboole_0(X18,X19))=k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.48/0.65  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.48/0.65  cnf(c_0_28, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_23])).
% 0.48/0.65  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.65  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.65  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.65  cnf(c_0_32, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_28])).
% 0.48/0.65  cnf(c_0_33, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_17])).
% 0.48/0.65  cnf(c_0_34, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17])).
% 0.48/0.65  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.48/0.65  cnf(c_0_36, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.48/0.65  cnf(c_0_37, plain, (k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X1),k2_xboole_0(X1,X1))),k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.48/0.65  cnf(c_0_38, plain, (k2_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.48/0.65  cnf(c_0_39, plain, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23]), c_0_28]), c_0_23]), c_0_36]), c_0_23]), c_0_36]), c_0_23])).
% 0.48/0.65  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_39]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_28]), c_0_23]), c_0_23]), c_0_28]), c_0_23]), c_0_23]), c_0_28])).
% 0.48/0.65  cnf(c_0_41, plain, (k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)))=X1|~r1_tarski(X1,k2_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.65  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_28]), c_0_23])).
% 0.48/0.65  cnf(c_0_43, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_40])).
% 0.48/0.65  cnf(c_0_44, plain, (k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_40]), c_0_40]), c_0_42])])).
% 0.48/0.65  cnf(c_0_45, plain, (k2_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_43]), c_0_44]), c_0_43])).
% 0.48/0.65  fof(c_0_46, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.48/0.65  cnf(c_0_47, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_44]), c_0_44])).
% 0.48/0.65  fof(c_0_48, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.48/0.65  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))))=k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_43]), c_0_47])).
% 0.48/0.65  cnf(c_0_50, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.65  fof(c_0_51, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.48/0.65  cnf(c_0_52, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X1|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_43]), c_0_23]), c_0_43]), c_0_40]), c_0_43]), c_0_23])).
% 0.48/0.65  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_16]), c_0_17])).
% 0.48/0.65  cnf(c_0_54, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.65  fof(c_0_55, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.48/0.65  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,X1),k2_xboole_0(esk1_0,X1))=esk1_0|~r1_tarski(k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.48/0.65  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_54, c_0_33])).
% 0.48/0.65  cnf(c_0_58, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.48/0.65  cnf(c_0_59, plain, (k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_43])).
% 0.48/0.65  cnf(c_0_60, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))=esk1_0), inference(spm,[status(thm)],[c_0_56, c_0_33])).
% 0.48/0.65  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.65  cnf(c_0_62, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 0.48/0.65  cnf(c_0_63, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_16]), c_0_17])).
% 0.48/0.65  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_60]), c_0_43]), c_0_47])).
% 0.48/0.65  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.48/0.65  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_23]), c_0_65]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 67
% 0.48/0.65  # Proof object clause steps            : 44
% 0.48/0.65  # Proof object formula steps           : 23
% 0.48/0.65  # Proof object conjectures             : 12
% 0.48/0.65  # Proof object clause conjectures      : 9
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 12
% 0.48/0.65  # Proof object initial formulas used   : 11
% 0.48/0.65  # Proof object generating inferences   : 17
% 0.48/0.65  # Proof object simplifying inferences  : 76
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 11
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 12
% 0.48/0.65  # Removed in clause preprocessing      : 2
% 0.48/0.65  # Initial clauses in saturation        : 10
% 0.48/0.65  # Processed clauses                    : 475
% 0.48/0.65  # ...of these trivial                  : 67
% 0.48/0.65  # ...subsumed                          : 196
% 0.48/0.65  # ...remaining for further processing  : 212
% 0.48/0.65  # Other redundant clauses eliminated   : 0
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 5
% 0.48/0.65  # Backward-rewritten                   : 96
% 0.48/0.65  # Generated clauses                    : 7454
% 0.48/0.65  # ...of the previous two non-trivial   : 6524
% 0.48/0.65  # Contextual simplify-reflections      : 0
% 0.48/0.65  # Paramodulations                      : 7454
% 0.48/0.65  # Factorizations                       : 0
% 0.48/0.65  # Equation resolutions                 : 0
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.65  #    Propositional unsat core size     : 0
% 0.48/0.65  #    Propositional preprocessing time  : 0.000
% 0.48/0.65  #    Propositional encoding time       : 0.000
% 0.48/0.65  #    Propositional solver time         : 0.000
% 0.48/0.65  #    Success case prop preproc time    : 0.000
% 0.48/0.65  #    Success case prop encoding time   : 0.000
% 0.48/0.65  #    Success case prop solver time     : 0.000
% 0.48/0.65  # Current number of processed clauses  : 101
% 0.48/0.65  #    Positive orientable unit clauses  : 37
% 0.48/0.65  #    Positive unorientable unit clauses: 7
% 0.48/0.65  #    Negative unit clauses             : 1
% 0.48/0.65  #    Non-unit-clauses                  : 56
% 0.48/0.65  # Current number of unprocessed clauses: 5925
% 0.48/0.65  # ...number of literals in the above   : 9909
% 0.48/0.65  # Current number of archived formulas  : 0
% 0.48/0.65  # Current number of archived clauses   : 113
% 0.48/0.65  # Clause-clause subsumption calls (NU) : 2495
% 0.48/0.65  # Rec. Clause-clause subsumption calls : 1944
% 0.48/0.65  # Non-unit clause-clause subsumptions  : 200
% 0.48/0.65  # Unit Clause-clause subsumption calls : 117
% 0.48/0.65  # Rewrite failures with RHS unbound    : 0
% 0.48/0.65  # BW rewrite match attempts            : 324
% 0.48/0.65  # BW rewrite match successes           : 42
% 0.48/0.65  # Condensation attempts                : 0
% 0.48/0.65  # Condensation successes               : 0
% 0.48/0.65  # Termbank termtop insertions          : 928585
% 0.48/0.65  
% 0.48/0.65  # -------------------------------------------------
% 0.48/0.65  # User time                : 0.298 s
% 0.48/0.65  # System time              : 0.010 s
% 0.48/0.65  # Total time               : 0.308 s
% 0.48/0.65  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
