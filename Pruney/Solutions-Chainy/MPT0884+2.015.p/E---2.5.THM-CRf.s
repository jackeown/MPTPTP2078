%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 (1056 expanded)
%              Number of clauses        :   40 ( 415 expanded)
%              Number of leaves         :   16 ( 320 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 (1058 expanded)
%              Number of equality atoms :   74 (1057 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(c_0_16,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_19,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X28,X29,X30,X31,X32] : k3_enumset1(X28,X29,X30,X31,X32) = k2_xboole_0(k2_tarski(X28,X29),k1_enumset1(X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] : k1_enumset1(X12,X13,X14) = k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_26,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_27,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_xboole_0(k1_enumset1(X19,X20,X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_35,plain,(
    ! [X48,X49,X50] : k3_mcart_1(X48,X49,X50) = k4_tarski(k4_tarski(X48,X49),X50) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_36,plain,(
    ! [X51,X52,X53] : k3_zfmisc_1(X51,X52,X53) = k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_37,plain,(
    ! [X45,X46,X47] :
      ( k2_zfmisc_1(k1_tarski(X45),k2_tarski(X46,X47)) = k2_tarski(k4_tarski(X45,X46),k4_tarski(X45,X47))
      & k2_zfmisc_1(k2_tarski(X45,X46),k1_tarski(X47)) = k2_tarski(k4_tarski(X45,X47),k4_tarski(X46,X47)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X41,X42,X43,X44] : k2_zfmisc_1(k2_tarski(X41,X42),k2_tarski(X43,X44)) = k2_enumset1(k4_tarski(X41,X43),k4_tarski(X41,X44),k4_tarski(X42,X43),k4_tarski(X42,X44)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

fof(c_0_49,plain,(
    ! [X23,X24,X25,X26,X27] : k3_enumset1(X23,X24,X25,X26,X27) = k2_xboole_0(k1_tarski(X23),k2_enumset1(X24,X25,X26,X27)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_21]),c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_21]),c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_30]),c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_30]),c_0_21]),c_0_21]),c_0_21]),c_0_32]),c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_30]),c_0_21]),c_0_21]),c_0_21]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_43]),c_0_54])).

cnf(c_0_61,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_51,c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_21]),c_0_21]),c_0_32]),c_0_32])).

cnf(c_0_64,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_30]),c_0_21]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X3,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_43]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_64]),c_0_66]),c_0_61])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X3,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_69]),c_0_43]),c_0_66]),c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 16:10:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.027 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.43  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.21/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.43  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.21/0.43  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 0.21/0.43  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.21/0.43  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.21/0.43  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.43  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.21/0.43  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.43  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.43  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.21/0.43  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.21/0.43  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.21/0.43  fof(c_0_16, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.43  fof(c_0_17, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.43  fof(c_0_18, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.21/0.43  fof(c_0_19, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.43  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.43  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.43  fof(c_0_22, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.43  fof(c_0_23, plain, ![X28, X29, X30, X31, X32]:k3_enumset1(X28,X29,X30,X31,X32)=k2_xboole_0(k2_tarski(X28,X29),k1_enumset1(X30,X31,X32)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.21/0.43  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 0.21/0.43  fof(c_0_25, plain, ![X12, X13, X14]:k1_enumset1(X12,X13,X14)=k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.21/0.43  fof(c_0_26, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.21/0.43  fof(c_0_27, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.43  fof(c_0_28, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_xboole_0(k1_enumset1(X19,X20,X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.21/0.43  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.43  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.43  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.43  cnf(c_0_33, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  fof(c_0_34, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.21/0.43  fof(c_0_35, plain, ![X48, X49, X50]:k3_mcart_1(X48,X49,X50)=k4_tarski(k4_tarski(X48,X49),X50), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.43  fof(c_0_36, plain, ![X51, X52, X53]:k3_zfmisc_1(X51,X52,X53)=k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.43  fof(c_0_37, plain, ![X45, X46, X47]:(k2_zfmisc_1(k1_tarski(X45),k2_tarski(X46,X47))=k2_tarski(k4_tarski(X45,X46),k4_tarski(X45,X47))&k2_zfmisc_1(k2_tarski(X45,X46),k1_tarski(X47))=k2_tarski(k4_tarski(X45,X47),k4_tarski(X46,X47))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.21/0.43  cnf(c_0_38, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_39, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.43  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  cnf(c_0_41, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.43  cnf(c_0_42, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_44, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.43  cnf(c_0_45, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_46, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.43  cnf(c_0_47, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.43  fof(c_0_48, plain, ![X41, X42, X43, X44]:k2_zfmisc_1(k2_tarski(X41,X42),k2_tarski(X43,X44))=k2_enumset1(k4_tarski(X41,X43),k4_tarski(X41,X44),k4_tarski(X42,X43),k4_tarski(X42,X44)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.21/0.43  fof(c_0_49, plain, ![X23, X24, X25, X26, X27]:k3_enumset1(X23,X24,X25,X26,X27)=k2_xboole_0(k1_tarski(X23),k2_enumset1(X24,X25,X26,X27)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.21/0.43  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X2,X3)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_21]), c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_51, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_21]), c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_52, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_53, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_30]), c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_30]), c_0_21]), c_0_21]), c_0_21]), c_0_32]), c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46])).
% 0.21/0.43  cnf(c_0_56, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_30]), c_0_21]), c_0_21]), c_0_21]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_57, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.43  cnf(c_0_58, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.43  cnf(c_0_59, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.43  cnf(c_0_60, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_43]), c_0_54])).
% 0.21/0.43  cnf(c_0_61, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_51, c_0_43])).
% 0.21/0.43  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.43  cnf(c_0_63, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_21]), c_0_21]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_64, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_30]), c_0_21]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 0.21/0.43  cnf(c_0_65, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X3,X1,X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.43  cnf(c_0_66, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_43]), c_0_61])).
% 0.21/0.43  cnf(c_0_67, negated_conjecture, (k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.43  cnf(c_0_68, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_64]), c_0_66]), c_0_61])).
% 0.21/0.43  cnf(c_0_69, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X3,X3,X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.43  cnf(c_0_70, negated_conjecture, (k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.43  cnf(c_0_71, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_69]), c_0_43]), c_0_66]), c_0_61])).
% 0.21/0.43  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 73
% 0.21/0.43  # Proof object clause steps            : 40
% 0.21/0.43  # Proof object formula steps           : 33
% 0.21/0.43  # Proof object conjectures             : 9
% 0.21/0.43  # Proof object clause conjectures      : 6
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 16
% 0.21/0.43  # Proof object initial formulas used   : 16
% 0.21/0.43  # Proof object generating inferences   : 6
% 0.21/0.43  # Proof object simplifying inferences  : 88
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 16
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 17
% 0.21/0.43  # Removed in clause preprocessing      : 6
% 0.21/0.43  # Initial clauses in saturation        : 11
% 0.21/0.43  # Processed clauses                    : 329
% 0.21/0.43  # ...of these trivial                  : 6
% 0.21/0.43  # ...subsumed                          : 241
% 0.21/0.43  # ...remaining for further processing  : 82
% 0.21/0.43  # Other redundant clauses eliminated   : 0
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 2
% 0.21/0.43  # Backward-rewritten                   : 7
% 0.21/0.43  # Generated clauses                    : 6914
% 0.21/0.43  # ...of the previous two non-trivial   : 4512
% 0.21/0.43  # Contextual simplify-reflections      : 0
% 0.21/0.43  # Paramodulations                      : 6914
% 0.21/0.43  # Factorizations                       : 0
% 0.21/0.43  # Equation resolutions                 : 0
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 62
% 0.21/0.43  #    Positive orientable unit clauses  : 20
% 0.21/0.43  #    Positive unorientable unit clauses: 42
% 0.21/0.43  #    Negative unit clauses             : 0
% 0.21/0.43  #    Non-unit-clauses                  : 0
% 0.21/0.43  # Current number of unprocessed clauses: 4199
% 0.21/0.43  # ...number of literals in the above   : 4199
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 26
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.43  # Unit Clause-clause subsumption calls : 961
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 2661
% 0.21/0.43  # BW rewrite match successes           : 943
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 43787
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.074 s
% 0.21/0.43  # System time              : 0.003 s
% 0.21/0.43  # Total time               : 0.077 s
% 0.21/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
