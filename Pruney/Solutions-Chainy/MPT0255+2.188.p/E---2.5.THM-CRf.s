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
% DateTime   : Thu Dec  3 10:41:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (14244 expanded)
%              Number of clauses        :   65 (6279 expanded)
%              Number of leaves         :   12 (3681 expanded)
%              Depth                    :   19
%              Number of atoms          :  106 (14330 expanded)
%              Number of equality atoms :  105 (14329 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_13,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_xboole_0(k1_tarski(X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X14,X15)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k2_xboole_0(X11,X12),X13) = k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)))) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_25])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( k4_xboole_0(X7,X8) != k4_xboole_0(X8,X7)
      | X7 = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(esk1_0),X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26])).

cnf(c_0_32,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X1),X3) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0))) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X3)
    | k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

fof(c_0_39,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k2_xboole_0(k2_tarski(X23,X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_31]),c_0_36])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_tarski(esk1_0),k1_xboole_0),X1),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_38]),c_0_24])).

fof(c_0_44,plain,(
    ! [X16,X17,X18,X19,X20] : k3_enumset1(X16,X17,X18,X19,X20) = k2_xboole_0(k1_enumset1(X16,X17,X18),k2_tarski(X19,X20)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X32,X33,X34,X35,X36] : k4_enumset1(X32,X32,X33,X34,X35,X36) = k3_enumset1(X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_47,plain,(
    ! [X37,X38,X39,X40,X41,X42] : k6_enumset1(X37,X37,X37,X38,X39,X40,X41,X42) = k4_enumset1(X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

fof(c_0_48,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k4_enumset1(X26,X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X1) = k2_xboole_0(X1,X2)
    | k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X1))) != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)),X4),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_40]),c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_41])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X2))),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(esk1_0),X1),k1_xboole_0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_24])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_17])).

cnf(c_0_57,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X1)
    | k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X1)),k1_xboole_0)) != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,esk3_0)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0) = k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0)),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_26]),c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0)) = k2_xboole_0(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_23]),c_0_50])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_17]),c_0_56]),c_0_57]),c_0_58])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_57]),c_0_58]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_30]),c_0_50])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,X1)
    | k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0) = k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X4),X2),X3)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_66])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k1_tarski(X1),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_68])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0) = k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_50]),c_0_63]),c_0_41]),c_0_50]),c_0_63])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2)
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))),k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_63]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0) = k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_35]),c_0_41]),c_0_50]),c_0_63]),c_0_33]),c_0_35]),c_0_33]),c_0_19])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) = k2_xboole_0(X1,X3)
    | k4_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) != k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X3))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_27])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_81]),c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_78]),c_0_78]),c_0_76]),c_0_78])])).

fof(c_0_86,plain,(
    ! [X43,X44] : k2_xboole_0(k1_tarski(X43),X44) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_87,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1) = k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))
    | k2_xboole_0(k1_xboole_0,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_81]),c_0_81]),c_0_27]),c_0_81]),c_0_26]),c_0_84]),c_0_85])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_87]),c_0_63]),c_0_85])]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:10:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.026 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.19/0.48  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.48  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.48  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.19/0.48  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.48  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.19/0.48  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.19/0.48  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.19/0.48  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.48  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.19/0.48  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.19/0.48  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.48  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.19/0.48  fof(c_0_13, negated_conjecture, k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.48  fof(c_0_14, plain, ![X21, X22]:k2_tarski(X21,X22)=k2_xboole_0(k1_tarski(X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.48  fof(c_0_15, plain, ![X14, X15]:k4_xboole_0(X14,k2_xboole_0(X14,X15))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.48  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.48  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.48  fof(c_0_18, plain, ![X11, X12, X13]:k4_xboole_0(k2_xboole_0(X11,X12),X13)=k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.19/0.48  cnf(c_0_19, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_20, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.48  fof(c_0_21, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.48  cnf(c_0_22, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.48  cnf(c_0_24, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1),k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.19/0.48  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))))=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_25])).
% 0.19/0.48  cnf(c_0_27, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.19/0.48  fof(c_0_28, plain, ![X7, X8]:(k4_xboole_0(X7,X8)!=k4_xboole_0(X8,X7)|X7=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.19/0.48  cnf(c_0_29, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)=k2_xboole_0(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)))=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.19/0.48  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(esk1_0),X1))=k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_26])).
% 0.19/0.48  cnf(c_0_32, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.48  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.19/0.48  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.19/0.48  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X1),X3)=k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X3),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_22])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0)))=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.48  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X3)|k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,X2))!=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.48  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k4_xboole_0(k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.19/0.48  fof(c_0_39, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k2_xboole_0(k2_tarski(X23,X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.19/0.48  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 0.19/0.48  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1)=k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_31]), c_0_36])).
% 0.19/0.48  cnf(c_0_42, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)|k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_19])).
% 0.19/0.48  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_tarski(esk1_0),k1_xboole_0),X1),k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_38]), c_0_24])).
% 0.19/0.48  fof(c_0_44, plain, ![X16, X17, X18, X19, X20]:k3_enumset1(X16,X17,X18,X19,X20)=k2_xboole_0(k1_enumset1(X16,X17,X18),k2_tarski(X19,X20)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.19/0.48  cnf(c_0_45, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.48  fof(c_0_46, plain, ![X32, X33, X34, X35, X36]:k4_enumset1(X32,X32,X33,X34,X35,X36)=k3_enumset1(X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.48  fof(c_0_47, plain, ![X37, X38, X39, X40, X41, X42]:k6_enumset1(X37,X37,X37,X38,X39,X40,X41,X42)=k4_enumset1(X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.19/0.48  fof(c_0_48, plain, ![X26, X27, X28, X29, X30, X31]:k4_enumset1(X26,X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.19/0.48  cnf(c_0_49, plain, (k2_xboole_0(X1,X1)=k2_xboole_0(X1,X2)|k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X1)))!=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_19])).
% 0.19/0.48  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k2_xboole_0(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 0.19/0.48  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)),X4),k1_xboole_0)=k2_xboole_0(k1_xboole_0,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_40]), c_0_24])).
% 0.19/0.48  cnf(c_0_52, negated_conjecture, (k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_41])).
% 0.19/0.48  cnf(c_0_53, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)|k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X2))),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_27])).
% 0.19/0.48  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(esk1_0),X1),k1_xboole_0),k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_22]), c_0_24])).
% 0.19/0.48  cnf(c_0_55, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.48  cnf(c_0_56, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_45, c_0_17])).
% 0.19/0.48  cnf(c_0_57, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.48  cnf(c_0_59, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.48  cnf(c_0_60, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k1_xboole_0)=k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.48  cnf(c_0_61, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X1)|k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X1)),k1_xboole_0))!=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.19/0.48  cnf(c_0_62, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,esk3_0))=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_50])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_50])).
% 0.19/0.48  cnf(c_0_64, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0)=k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))|k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0)),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_26]), c_0_29])).
% 0.19/0.48  cnf(c_0_65, negated_conjecture, (k2_xboole_0(k1_xboole_0,k1_tarski(esk2_0))=k2_xboole_0(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_23]), c_0_50])).
% 0.19/0.48  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_17]), c_0_56]), c_0_57]), c_0_58])).
% 0.19/0.48  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_57]), c_0_58]), c_0_58])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)=k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_30]), c_0_50])).
% 0.19/0.48  cnf(c_0_69, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=k2_xboole_0(X1,X1)|k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))!=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_19])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0)=k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))|k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.48  cnf(c_0_72, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X4),X2),X3))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.19/0.48  cnf(c_0_73, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_66])).
% 0.19/0.48  cnf(c_0_74, plain, (k4_xboole_0(k1_tarski(X1),k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_67])).
% 0.19/0.48  cnf(c_0_75, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k1_xboole_0))=k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_68])).
% 0.19/0.48  cnf(c_0_76, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0)=k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))|k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_71, c_0_63])).
% 0.19/0.48  cnf(c_0_78, plain, (k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_50]), c_0_63]), c_0_41]), c_0_50]), c_0_63])).
% 0.19/0.48  cnf(c_0_79, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)|k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))),k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_24])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0))=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_63]), c_0_76])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_xboole_0)=k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78])])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)=k2_xboole_0(k1_xboole_0,k1_xboole_0)|k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)),k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_35]), c_0_41]), c_0_50]), c_0_63]), c_0_33]), c_0_35]), c_0_33]), c_0_19])).
% 0.19/0.48  cnf(c_0_83, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)=k2_xboole_0(X1,X3)|k4_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0))!=k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X3))),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_27])).
% 0.19/0.48  cnf(c_0_84, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_81]), c_0_19])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_78]), c_0_78]), c_0_76]), c_0_78])])).
% 0.19/0.48  fof(c_0_86, plain, ![X43, X44]:k2_xboole_0(k1_tarski(X43),X44)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),X1)=k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))|k2_xboole_0(k1_xboole_0,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_81]), c_0_81]), c_0_27]), c_0_81]), c_0_26]), c_0_84]), c_0_85])).
% 0.19/0.48  cnf(c_0_88, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.48  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_87]), c_0_63]), c_0_85])]), c_0_88]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 90
% 0.19/0.48  # Proof object clause steps            : 65
% 0.19/0.48  # Proof object formula steps           : 25
% 0.19/0.48  # Proof object conjectures             : 34
% 0.19/0.48  # Proof object clause conjectures      : 31
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 12
% 0.19/0.48  # Proof object initial formulas used   : 12
% 0.19/0.48  # Proof object generating inferences   : 40
% 0.19/0.48  # Proof object simplifying inferences  : 65
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 12
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 12
% 0.19/0.48  # Removed in clause preprocessing      : 4
% 0.19/0.48  # Initial clauses in saturation        : 8
% 0.19/0.48  # Processed clauses                    : 1313
% 0.19/0.48  # ...of these trivial                  : 114
% 0.19/0.48  # ...subsumed                          : 865
% 0.19/0.48  # ...remaining for further processing  : 334
% 0.19/0.48  # Other redundant clauses eliminated   : 0
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 2
% 0.19/0.48  # Backward-rewritten                   : 135
% 0.19/0.48  # Generated clauses                    : 9491
% 0.19/0.48  # ...of the previous two non-trivial   : 5984
% 0.19/0.48  # Contextual simplify-reflections      : 0
% 0.19/0.48  # Paramodulations                      : 9489
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 2
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 189
% 0.19/0.49  #    Positive orientable unit clauses  : 95
% 0.19/0.49  #    Positive unorientable unit clauses: 9
% 0.19/0.49  #    Negative unit clauses             : 50
% 0.19/0.49  #    Non-unit-clauses                  : 35
% 0.19/0.49  # Current number of unprocessed clauses: 4317
% 0.19/0.49  # ...number of literals in the above   : 6225
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 149
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 1383
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 1377
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 432
% 0.19/0.49  # Unit Clause-clause subsumption calls : 280
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 343
% 0.19/0.49  # BW rewrite match successes           : 56
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 177054
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.147 s
% 0.19/0.49  # System time              : 0.004 s
% 0.19/0.49  # Total time               : 0.151 s
% 0.19/0.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
