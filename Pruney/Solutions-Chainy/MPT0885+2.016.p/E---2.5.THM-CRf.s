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
% DateTime   : Thu Dec  3 10:59:49 EST 2020

% Result     : Theorem 45.38s
% Output     : CNFRefutation 45.38s
% Verified   : 
% Statistics : Number of formulae       :   78 (15394 expanded)
%              Number of clauses        :   49 (6087 expanded)
%              Number of leaves         :   14 (4653 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 (15396 expanded)
%              Number of equality atoms :   79 (15395 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t45_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k2_tarski(X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] : k1_enumset1(X12,X13,X14) = k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_22,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_18]),c_0_18]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_enumset1(X1,X2,X3,X3,X4) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_30]),c_0_18]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t45_mcart_1])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_41,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_42,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) = k3_enumset1(X1,X2,X3,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X4,X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

fof(c_0_44,plain,(
    ! [X32,X33,X34,X35] : k2_zfmisc_1(k2_tarski(X32,X33),k2_tarski(X34,X35)) = k2_enumset1(k4_tarski(X32,X34),k4_tarski(X32,X35),k4_tarski(X33,X34),k4_tarski(X33,X35)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

fof(c_0_45,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_46,plain,(
    ! [X39,X40,X41] : k3_mcart_1(X39,X40,X41) = k4_tarski(k4_tarski(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_47,plain,(
    ! [X42,X43,X44] : k3_zfmisc_1(X42,X43,X44) = k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X2,X3,X3,X3) = k3_enumset1(X1,X1,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_37]),c_0_37])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X4,X4,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X2,X3,X4,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_48]),c_0_43])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X3,X1,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_49]),c_0_42])).

cnf(c_0_56,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X5,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_49]),c_0_43])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_18]),c_0_18]),c_0_26]),c_0_26])).

fof(c_0_58,plain,(
    ! [X36,X37,X38] :
      ( k2_zfmisc_1(k1_tarski(X36),k2_tarski(X37,X38)) = k2_tarski(k4_tarski(X36,X37),k4_tarski(X36,X38))
      & k2_zfmisc_1(k2_tarski(X36,X37),k1_tarski(X38)) = k2_tarski(k4_tarski(X36,X38),k4_tarski(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_30]),c_0_18]),c_0_18]),c_0_18]),c_0_26]),c_0_26]),c_0_26]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X2,X3,X1,X4,X4) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k3_enumset1(X3,X3,X1,X2,X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_62,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X3)) = k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X4),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_63,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X4,X4,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_66,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)) = k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X4,X4,X4,X4,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_30]),c_0_18]),c_0_18]),c_0_18]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_69,plain,
    ( k3_enumset1(X1,X2,X3,X3,X3) = k3_enumset1(X3,X3,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_70,plain,
    ( k3_enumset1(X1,X1,X2,X3,X1) = k3_enumset1(X2,X2,X3,X3,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)) = k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X2,X2,X4,X4,X4)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_49])).

cnf(c_0_73,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_74,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_75,plain,
    ( k3_enumset1(X1,X1,X2,X2,X3) = k3_enumset1(X1,X1,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_69])).

cnf(c_0_76,plain,
    ( k3_enumset1(X1,X1,X2,X2,X3) = k3_enumset1(X3,X3,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 45.38/45.60  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 45.38/45.60  # and selection function SelectNewComplexAHP.
% 45.38/45.60  #
% 45.38/45.60  # Preprocessing time       : 0.026 s
% 45.38/45.60  # Presaturation interreduction done
% 45.38/45.60  
% 45.38/45.60  # Proof found!
% 45.38/45.60  # SZS status Theorem
% 45.38/45.60  # SZS output start CNFRefutation
% 45.38/45.60  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 45.38/45.60  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 45.38/45.60  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 45.38/45.60  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 45.38/45.60  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 45.38/45.60  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 45.38/45.60  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 45.38/45.60  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 45.38/45.60  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 45.38/45.60  fof(t45_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_mcart_1)).
% 45.38/45.60  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 45.38/45.60  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 45.38/45.60  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 45.38/45.60  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 45.38/45.60  fof(c_0_14, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 45.38/45.60  fof(c_0_15, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 45.38/45.60  fof(c_0_16, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 45.38/45.60  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 45.38/45.60  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 45.38/45.60  fof(c_0_19, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 45.38/45.60  fof(c_0_20, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k2_tarski(X19,X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 45.38/45.60  fof(c_0_21, plain, ![X12, X13, X14]:k1_enumset1(X12,X13,X14)=k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 45.38/45.60  fof(c_0_22, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 45.38/45.60  fof(c_0_23, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 45.38/45.60  cnf(c_0_24, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 45.38/45.60  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 45.38/45.60  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 45.38/45.60  cnf(c_0_27, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 45.38/45.60  fof(c_0_28, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 45.38/45.60  cnf(c_0_29, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 45.38/45.60  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 45.38/45.60  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 45.38/45.60  cnf(c_0_32, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_18]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 45.38/45.60  cnf(c_0_33, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 45.38/45.60  cnf(c_0_34, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 45.38/45.60  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_18]), c_0_18]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 45.38/45.60  cnf(c_0_36, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 45.38/45.60  cnf(c_0_37, plain, (k2_enumset1(X1,X2,X3,X4)=k3_enumset1(X1,X2,X3,X3,X4)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 45.38/45.60  cnf(c_0_38, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_30]), c_0_18]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 45.38/45.60  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))), inference(assume_negation,[status(cth)],[t45_mcart_1])).
% 45.38/45.60  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 45.38/45.60  cnf(c_0_41, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_42, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X1,X1,X2,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)))=k3_enumset1(X1,X2,X3,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_43, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X4,X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 45.38/45.60  fof(c_0_44, plain, ![X32, X33, X34, X35]:k2_zfmisc_1(k2_tarski(X32,X33),k2_tarski(X34,X35))=k2_enumset1(k4_tarski(X32,X34),k4_tarski(X32,X35),k4_tarski(X33,X34),k4_tarski(X33,X35)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 45.38/45.60  fof(c_0_45, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 45.38/45.60  fof(c_0_46, plain, ![X39, X40, X41]:k3_mcart_1(X39,X40,X41)=k4_tarski(k4_tarski(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 45.38/45.60  fof(c_0_47, plain, ![X42, X43, X44]:k3_zfmisc_1(X42,X43,X44)=k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 45.38/45.60  cnf(c_0_48, plain, (k3_enumset1(X1,X2,X3,X3,X3)=k3_enumset1(X1,X1,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_49, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X4,X4,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 45.38/45.60  cnf(c_0_50, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 45.38/45.60  cnf(c_0_51, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 45.38/45.60  cnf(c_0_52, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 45.38/45.60  cnf(c_0_53, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 45.38/45.60  cnf(c_0_54, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X2,X3,X4,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_48]), c_0_43])).
% 45.38/45.60  cnf(c_0_55, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X3,X1,X2,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_49]), c_0_42])).
% 45.38/45.60  cnf(c_0_56, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X5,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_49]), c_0_43])).
% 45.38/45.60  cnf(c_0_57, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_18]), c_0_18]), c_0_26]), c_0_26])).
% 45.38/45.60  fof(c_0_58, plain, ![X36, X37, X38]:(k2_zfmisc_1(k1_tarski(X36),k2_tarski(X37,X38))=k2_tarski(k4_tarski(X36,X37),k4_tarski(X36,X38))&k2_zfmisc_1(k2_tarski(X36,X37),k1_tarski(X38))=k2_tarski(k4_tarski(X36,X38),k4_tarski(X37,X38))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 45.38/45.60  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_30]), c_0_18]), c_0_18]), c_0_18]), c_0_26]), c_0_26]), c_0_26]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53])).
% 45.38/45.60  cnf(c_0_60, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X2,X3,X1,X4,X4)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 45.38/45.60  cnf(c_0_61, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k3_enumset1(X3,X3,X1,X2,X4)), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 45.38/45.60  cnf(c_0_62, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X3))=k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X4),k3_enumset1(X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_37]), c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_63, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X4,X4,X2,X3,X1)), inference(spm,[status(thm)],[c_0_49, c_0_55])).
% 45.38/45.60  cnf(c_0_64, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 45.38/45.60  cnf(c_0_65, negated_conjecture, (k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))!=k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_66, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 45.38/45.60  cnf(c_0_67, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))=k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X4,X4,X4,X4,X2))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 45.38/45.60  cnf(c_0_68, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_30]), c_0_18]), c_0_18]), c_0_18]), c_0_26]), c_0_26]), c_0_26])).
% 45.38/45.60  cnf(c_0_69, plain, (k3_enumset1(X1,X2,X3,X3,X3)=k3_enumset1(X3,X3,X1,X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 45.38/45.60  cnf(c_0_70, plain, (k3_enumset1(X1,X1,X2,X3,X1)=k3_enumset1(X2,X2,X3,X3,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 45.38/45.60  cnf(c_0_71, negated_conjecture, (k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))!=k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 45.38/45.60  cnf(c_0_72, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))=k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X2,X2,X4,X4,X4))), inference(spm,[status(thm)],[c_0_67, c_0_49])).
% 45.38/45.60  cnf(c_0_73, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))=k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_37]), c_0_37]), c_0_37])).
% 45.38/45.60  cnf(c_0_74, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 45.38/45.60  cnf(c_0_75, plain, (k3_enumset1(X1,X1,X2,X2,X3)=k3_enumset1(X1,X1,X2,X3,X1)), inference(spm,[status(thm)],[c_0_49, c_0_69])).
% 45.38/45.60  cnf(c_0_76, plain, (k3_enumset1(X1,X1,X2,X2,X3)=k3_enumset1(X3,X3,X3,X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_70])).
% 45.38/45.60  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76])]), ['proof']).
% 45.38/45.60  # SZS output end CNFRefutation
% 45.38/45.60  # Proof object total steps             : 78
% 45.38/45.60  # Proof object clause steps            : 49
% 45.38/45.60  # Proof object formula steps           : 29
% 45.38/45.60  # Proof object conjectures             : 8
% 45.38/45.60  # Proof object clause conjectures      : 5
% 45.38/45.60  # Proof object formula conjectures     : 3
% 45.38/45.60  # Proof object initial clauses used    : 14
% 45.38/45.60  # Proof object initial formulas used   : 14
% 45.38/45.60  # Proof object generating inferences   : 15
% 45.38/45.60  # Proof object simplifying inferences  : 97
% 45.38/45.60  # Training examples: 0 positive, 0 negative
% 45.38/45.60  # Parsed axioms                        : 14
% 45.38/45.60  # Removed by relevancy pruning/SinE    : 0
% 45.38/45.60  # Initial clauses                      : 15
% 45.38/45.60  # Removed in clause preprocessing      : 6
% 45.38/45.60  # Initial clauses in saturation        : 9
% 45.38/45.60  # Processed clauses                    : 801524
% 45.38/45.60  # ...of these trivial                  : 12658
% 45.38/45.60  # ...subsumed                          : 786589
% 45.38/45.60  # ...remaining for further processing  : 2277
% 45.38/45.60  # Other redundant clauses eliminated   : 0
% 45.38/45.60  # Clauses deleted for lack of memory   : 837769
% 45.38/45.60  # Backward-subsumed                    : 190
% 45.38/45.60  # Backward-rewritten                   : 140
% 45.38/45.60  # Generated clauses                    : 14006412
% 45.38/45.60  # ...of the previous two non-trivial   : 10121827
% 45.38/45.60  # Contextual simplify-reflections      : 0
% 45.38/45.60  # Paramodulations                      : 14006412
% 45.38/45.60  # Factorizations                       : 0
% 45.38/45.60  # Equation resolutions                 : 0
% 45.38/45.60  # Propositional unsat checks           : 0
% 45.38/45.60  #    Propositional check models        : 0
% 45.38/45.60  #    Propositional check unsatisfiable : 0
% 45.38/45.60  #    Propositional clauses             : 0
% 45.38/45.60  #    Propositional clauses after purity: 0
% 45.38/45.60  #    Propositional unsat core size     : 0
% 45.38/45.60  #    Propositional preprocessing time  : 0.000
% 45.38/45.60  #    Propositional encoding time       : 0.000
% 45.38/45.60  #    Propositional solver time         : 0.000
% 45.38/45.60  #    Success case prop preproc time    : 0.000
% 45.38/45.60  #    Success case prop encoding time   : 0.000
% 45.38/45.60  #    Success case prop solver time     : 0.000
% 45.38/45.60  # Current number of processed clauses  : 1938
% 45.38/45.60  #    Positive orientable unit clauses  : 579
% 45.38/45.60  #    Positive unorientable unit clauses: 1359
% 45.38/45.60  #    Negative unit clauses             : 0
% 45.38/45.60  #    Non-unit-clauses                  : 0
% 45.38/45.60  # Current number of unprocessed clauses: 2545875
% 45.38/45.60  # ...number of literals in the above   : 2545875
% 45.38/45.60  # Current number of archived formulas  : 0
% 45.38/45.60  # Current number of archived clauses   : 345
% 45.38/45.60  # Clause-clause subsumption calls (NU) : 0
% 45.38/45.60  # Rec. Clause-clause subsumption calls : 0
% 45.38/45.60  # Non-unit clause-clause subsumptions  : 0
% 45.38/45.60  # Unit Clause-clause subsumption calls : 786643
% 45.38/45.60  # Rewrite failures with RHS unbound    : 0
% 45.38/45.60  # BW rewrite match attempts            : 1291690
% 45.38/45.60  # BW rewrite match successes           : 466482
% 45.38/45.60  # Condensation attempts                : 0
% 45.38/45.60  # Condensation successes               : 0
% 45.38/45.60  # Termbank termtop insertions          : 105197260
% 45.47/45.68  
% 45.47/45.68  # -------------------------------------------------
% 45.47/45.68  # User time                : 44.324 s
% 45.47/45.68  # System time              : 1.016 s
% 45.47/45.68  # Total time               : 45.341 s
% 45.47/45.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
