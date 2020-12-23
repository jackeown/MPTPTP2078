%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:01 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  100 (72596 expanded)
%              Number of clauses        :   81 (31408 expanded)
%              Number of leaves         :    9 (19270 expanded)
%              Depth                    :   26
%              Number of atoms          :  110 (89079 expanded)
%              Number of equality atoms :   98 (69948 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_9,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(X20,k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_15]),c_0_15])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_24])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))) = k5_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk3_0)) = k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_35,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k4_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_27]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),X1) = k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1))) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_15]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_31])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk3_0)) = k3_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_34]),c_0_29]),c_0_39]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk2_0) = k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) = k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1) = k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_44]),c_0_47]),c_0_29]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_47]),c_0_53]),c_0_47]),c_0_24]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(X1,esk3_0)) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) = k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_58]),c_0_52]),c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk3_0)) = k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0)) = k3_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_53]),c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_15]),c_0_15]),c_0_15]),c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk2_0) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_61]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_70]),c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_72]),c_0_27]),c_0_72]),c_0_73]),c_0_66]),c_0_53]),c_0_53]),c_0_74]),c_0_74]),c_0_73]),c_0_66]),c_0_53]),c_0_53]),c_0_74]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))) = k5_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_74]),c_0_30])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1))) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) = k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1))) = k3_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_28]),c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_80]),c_0_81]),c_0_82]),c_0_68]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_44]),c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_86,c_0_40])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_59]),c_0_27])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_44])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_28]),c_0_76]),c_0_66]),c_0_53]),c_0_53]),c_0_74]),c_0_27]),c_0_28]),c_0_66]),c_0_53]),c_0_53]),c_0_74])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_49]),c_0_52]),c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_89,c_0_53])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0))),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)))) = k3_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_73]),c_0_52]),c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_53]),c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1))) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_27])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.79/0.99  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.79/0.99  # and selection function SelectNewComplexAHP.
% 0.79/0.99  #
% 0.79/0.99  # Preprocessing time       : 0.026 s
% 0.79/0.99  
% 0.79/0.99  # Proof found!
% 0.79/0.99  # SZS status Theorem
% 0.79/0.99  # SZS output start CNFRefutation
% 0.79/0.99  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.79/0.99  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.79/0.99  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 0.79/0.99  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.79/0.99  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.79/0.99  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.79/0.99  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.79/0.99  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.79/0.99  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.79/0.99  fof(c_0_9, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(X20,k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.79/0.99  fof(c_0_10, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.79/0.99  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 0.79/0.99  fof(c_0_12, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.79/0.99  fof(c_0_13, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.79/0.99  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.79/0.99  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.79/0.99  fof(c_0_16, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.79/0.99  fof(c_0_17, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.79/0.99  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.79/0.99  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.79/0.99  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.79/0.99  fof(c_0_21, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.79/0.99  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.79/0.99  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.79/0.99  cnf(c_0_24, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_15]), c_0_15])).
% 0.79/0.99  fof(c_0_25, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.79/0.99  cnf(c_0_26, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.79/0.99  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.79/0.99  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.79/0.99  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_24, c_0_24])).
% 0.79/0.99  cnf(c_0_30, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.79/0.99  cnf(c_0_31, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_27]), c_0_28])).
% 0.79/0.99  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.79/0.99  cnf(c_0_33, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)))=k5_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_30])).
% 0.79/0.99  cnf(c_0_34, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk3_0))=k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.79/0.99  fof(c_0_35, plain, ![X14, X15, X16]:k3_xboole_0(X14,k4_xboole_0(X15,X16))=k4_xboole_0(k3_xboole_0(X14,X15),X16), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.79/0.99  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.79/0.99  cnf(c_0_37, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_27]), c_0_28])).
% 0.79/0.99  cnf(c_0_38, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.79/0.99  cnf(c_0_39, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_28])).
% 0.79/0.99  cnf(c_0_40, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),X1)=k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.79/0.99  cnf(c_0_41, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.79/0.99  cnf(c_0_42, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37]), c_0_38])).
% 0.79/0.99  cnf(c_0_43, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)))=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_40])).
% 0.79/0.99  cnf(c_0_44, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_15]), c_0_15])).
% 0.79/0.99  cnf(c_0_45, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_38, c_0_42])).
% 0.79/0.99  cnf(c_0_46, plain, (k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)=k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3))), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.79/0.99  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1))=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_24])).
% 0.79/0.99  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)))=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_30])).
% 0.79/0.99  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_39]), c_0_31])).
% 0.79/0.99  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_46])).
% 0.79/0.99  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk3_0))=k3_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_34]), c_0_29]), c_0_39]), c_0_27])).
% 0.79/0.99  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk2_0,esk2_0)=k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_49])).
% 0.79/0.99  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_43])).
% 0.79/0.99  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))=k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 0.79/0.99  cnf(c_0_55, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1)=k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_44]), c_0_47]), c_0_29]), c_0_24])).
% 0.79/0.99  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_49])).
% 0.79/0.99  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))=k3_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_47]), c_0_53]), c_0_47]), c_0_24]), c_0_55])).
% 0.79/0.99  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_56, c_0_40])).
% 0.79/0.99  cnf(c_0_59, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.79/0.99  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(X1,esk3_0))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_27])).
% 0.79/0.99  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_57, c_0_28])).
% 0.79/0.99  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))=k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),X1))), inference(rw,[status(thm)],[c_0_54, c_0_40])).
% 0.79/0.99  cnf(c_0_63, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_58]), c_0_52]), c_0_39])).
% 0.79/0.99  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk3_0,X1))=k3_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_59, c_0_57])).
% 0.79/0.99  cnf(c_0_65, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk3_0))=k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.79/0.99  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.79/0.99  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.79/0.99  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_28])).
% 0.79/0.99  cnf(c_0_69, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0))=k3_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_65])).
% 0.79/0.99  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_53]), c_0_58])).
% 0.79/0.99  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_15]), c_0_15]), c_0_15]), c_0_20])).
% 0.79/0.99  cnf(c_0_72, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk2_0)=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_61]), c_0_27])).
% 0.79/0.99  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_70]), c_0_30])).
% 0.79/0.99  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_58, c_0_53])).
% 0.79/0.99  cnf(c_0_75, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.79/0.99  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk2_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_72]), c_0_27]), c_0_72]), c_0_73]), c_0_66]), c_0_53]), c_0_53]), c_0_74]), c_0_74]), c_0_73]), c_0_66]), c_0_53]), c_0_53]), c_0_74]), c_0_74])).
% 0.79/0.99  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)))=k5_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_74]), c_0_30])).
% 0.79/0.99  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1)))=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[c_0_43, c_0_53])).
% 0.79/0.99  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_75, c_0_30])).
% 0.79/0.99  cnf(c_0_80, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_76])).
% 0.79/0.99  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))=k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[c_0_62, c_0_53])).
% 0.79/0.99  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1)))=k3_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_24])).
% 0.79/0.99  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_24])).
% 0.79/0.99  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_28]), c_0_28])).
% 0.79/0.99  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_80]), c_0_81]), c_0_82]), c_0_68]), c_0_83])).
% 0.79/0.99  cnf(c_0_86, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)),esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_45, c_0_54])).
% 0.79/0.99  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_44]), c_0_36])).
% 0.79/0.99  cnf(c_0_88, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(esk3_0,X1))=k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_59, c_0_85])).
% 0.79/0.99  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_86, c_0_40])).
% 0.79/0.99  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_59]), c_0_27])).
% 0.79/0.99  cnf(c_0_91, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_44])).
% 0.79/0.99  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_28]), c_0_76]), c_0_66]), c_0_53]), c_0_53]), c_0_74]), c_0_27]), c_0_28]), c_0_66]), c_0_53]), c_0_53]), c_0_74])).
% 0.79/0.99  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_49]), c_0_52]), c_0_39])).
% 0.79/0.99  cnf(c_0_94, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_89, c_0_53])).
% 0.79/0.99  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),k5_xboole_0(k3_xboole_0(esk3_0,esk3_0),esk2_0))),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_90, c_0_66])).
% 0.79/0.99  cnf(c_0_96, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0))))=k3_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_73]), c_0_52]), c_0_93]), c_0_94])).
% 0.79/0.99  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_53]), c_0_58])).
% 0.79/0.99  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_27])).
% 0.79/0.99  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_27])]), ['proof']).
% 0.79/0.99  # SZS output end CNFRefutation
% 0.79/0.99  # Proof object total steps             : 100
% 0.79/0.99  # Proof object clause steps            : 81
% 0.79/0.99  # Proof object formula steps           : 19
% 0.79/0.99  # Proof object conjectures             : 65
% 0.79/0.99  # Proof object clause conjectures      : 62
% 0.79/0.99  # Proof object formula conjectures     : 3
% 0.79/0.99  # Proof object initial clauses used    : 10
% 0.79/0.99  # Proof object initial formulas used   : 9
% 0.79/0.99  # Proof object generating inferences   : 48
% 0.79/0.99  # Proof object simplifying inferences  : 114
% 0.79/0.99  # Training examples: 0 positive, 0 negative
% 0.79/0.99  # Parsed axioms                        : 9
% 0.79/0.99  # Removed by relevancy pruning/SinE    : 0
% 0.79/0.99  # Initial clauses                      : 10
% 0.79/0.99  # Removed in clause preprocessing      : 2
% 0.79/0.99  # Initial clauses in saturation        : 8
% 0.79/0.99  # Processed clauses                    : 3667
% 0.79/0.99  # ...of these trivial                  : 1621
% 0.79/0.99  # ...subsumed                          : 1611
% 0.79/0.99  # ...remaining for further processing  : 435
% 0.79/0.99  # Other redundant clauses eliminated   : 0
% 0.79/0.99  # Clauses deleted for lack of memory   : 0
% 0.79/0.99  # Backward-subsumed                    : 0
% 0.79/0.99  # Backward-rewritten                   : 118
% 0.79/0.99  # Generated clauses                    : 85613
% 0.79/0.99  # ...of the previous two non-trivial   : 54712
% 0.79/0.99  # Contextual simplify-reflections      : 0
% 0.79/0.99  # Paramodulations                      : 85613
% 0.79/0.99  # Factorizations                       : 0
% 0.79/0.99  # Equation resolutions                 : 0
% 0.79/0.99  # Propositional unsat checks           : 0
% 0.79/0.99  #    Propositional check models        : 0
% 0.79/0.99  #    Propositional check unsatisfiable : 0
% 0.79/0.99  #    Propositional clauses             : 0
% 0.79/0.99  #    Propositional clauses after purity: 0
% 0.79/0.99  #    Propositional unsat core size     : 0
% 0.79/0.99  #    Propositional preprocessing time  : 0.000
% 0.79/0.99  #    Propositional encoding time       : 0.000
% 0.79/0.99  #    Propositional solver time         : 0.000
% 0.79/0.99  #    Success case prop preproc time    : 0.000
% 0.79/0.99  #    Success case prop encoding time   : 0.000
% 0.79/0.99  #    Success case prop solver time     : 0.000
% 0.79/0.99  # Current number of processed clauses  : 317
% 0.79/0.99  #    Positive orientable unit clauses  : 291
% 0.79/0.99  #    Positive unorientable unit clauses: 24
% 0.79/0.99  #    Negative unit clauses             : 0
% 0.79/0.99  #    Non-unit-clauses                  : 2
% 0.79/0.99  # Current number of unprocessed clauses: 50349
% 0.79/0.99  # ...number of literals in the above   : 50349
% 0.79/0.99  # Current number of archived formulas  : 0
% 0.79/0.99  # Current number of archived clauses   : 120
% 0.79/0.99  # Clause-clause subsumption calls (NU) : 1
% 0.79/0.99  # Rec. Clause-clause subsumption calls : 1
% 0.79/0.99  # Non-unit clause-clause subsumptions  : 0
% 0.79/0.99  # Unit Clause-clause subsumption calls : 349
% 0.79/0.99  # Rewrite failures with RHS unbound    : 0
% 0.79/0.99  # BW rewrite match attempts            : 3236
% 0.79/0.99  # BW rewrite match successes           : 338
% 0.79/0.99  # Condensation attempts                : 0
% 0.79/0.99  # Condensation successes               : 0
% 0.79/0.99  # Termbank termtop insertions          : 2098516
% 0.79/0.99  
% 0.79/0.99  # -------------------------------------------------
% 0.79/0.99  # User time                : 0.612 s
% 0.79/0.99  # System time              : 0.029 s
% 0.79/0.99  # Total time               : 0.641 s
% 0.79/0.99  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
