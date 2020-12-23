%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:44 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   80 (1483 expanded)
%              Number of clauses        :   45 ( 590 expanded)
%              Number of leaves         :   17 ( 446 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 (1485 expanded)
%              Number of equality atoms :   81 (1484 expanded)
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

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

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

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(c_0_17,plain,(
    ! [X41,X42] : k3_tarski(k2_tarski(X41,X42)) = k2_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] : k1_enumset1(X14,X15,X16) = k2_xboole_0(k1_tarski(X14),k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_20,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_25,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X21,X22,X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_26,plain,(
    ! [X30,X31,X32,X33,X34] : k3_enumset1(X30,X31,X32,X33,X34) = k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_27,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_28,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_37,plain,(
    ! [X25,X26,X27,X28,X29] : k3_enumset1(X25,X26,X27,X28,X29) = k2_xboole_0(k2_tarski(X25,X26),k1_enumset1(X27,X28,X29)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_22]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_30]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_30]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_30]),c_0_22]),c_0_31]),c_0_32]),c_0_32])).

fof(c_0_44,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

fof(c_0_45,plain,(
    ! [X50,X51,X52] : k3_mcart_1(X50,X51,X52) = k4_tarski(k4_tarski(X50,X51),X52) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_46,plain,(
    ! [X53,X54,X55] : k3_zfmisc_1(X53,X54,X55) = k2_zfmisc_1(k2_zfmisc_1(X53,X54),X55) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_47,plain,(
    ! [X47,X48,X49] :
      ( k2_zfmisc_1(k1_tarski(X47),k2_tarski(X48,X49)) = k2_tarski(k4_tarski(X47,X48),k4_tarski(X47,X49))
      & k2_zfmisc_1(k2_tarski(X47,X48),k1_tarski(X49)) = k2_tarski(k4_tarski(X47,X49),k4_tarski(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_30]),c_0_30]),c_0_22]),c_0_22]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_53,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_54,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X43,X44,X45,X46] : k2_zfmisc_1(k2_tarski(X43,X44),k2_tarski(X45,X46)) = k2_enumset1(k4_tarski(X43,X45),k4_tarski(X43,X46),k4_tarski(X44,X45),k4_tarski(X44,X46)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_59,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_60,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))) = k3_enumset1(X2,X3,X4,X5,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X2,X2,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_62,plain,
    ( k3_enumset1(X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_51]),c_0_43]),c_0_52])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_30]),c_0_22]),c_0_22]),c_0_22]),c_0_32]),c_0_32]),c_0_32]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_56])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_30]),c_0_22]),c_0_22]),c_0_22]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_52]),c_0_52])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X2,X3,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_41]),c_0_62])).

cnf(c_0_69,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_22]),c_0_22]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_22]),c_0_22]),c_0_32]),c_0_32])).

cnf(c_0_72,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_67])).

cnf(c_0_73,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_68]),c_0_43]),c_0_62]),c_0_62])).

cnf(c_0_74,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_60]),c_0_52]),c_0_52])).

cnf(c_0_75,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) != k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X2,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_74]),c_0_59]),c_0_75]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.53  #
% 0.18/0.53  # Preprocessing time       : 0.027 s
% 0.18/0.53  # Presaturation interreduction done
% 0.18/0.53  
% 0.18/0.53  # Proof found!
% 0.18/0.53  # SZS status Theorem
% 0.18/0.53  # SZS output start CNFRefutation
% 0.18/0.53  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.53  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.18/0.53  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.53  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.53  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.18/0.53  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.18/0.53  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.18/0.53  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.53  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.18/0.53  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 0.18/0.53  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.18/0.53  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.18/0.53  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.18/0.53  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.18/0.53  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.18/0.53  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.18/0.53  fof(c_0_17, plain, ![X41, X42]:k3_tarski(k2_tarski(X41,X42))=k2_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.53  fof(c_0_18, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.53  fof(c_0_19, plain, ![X14, X15, X16]:k1_enumset1(X14,X15,X16)=k2_xboole_0(k1_tarski(X14),k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.18/0.53  fof(c_0_20, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.53  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.53  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.53  fof(c_0_23, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.53  fof(c_0_24, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.18/0.53  fof(c_0_25, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_xboole_0(k1_enumset1(X21,X22,X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.18/0.53  fof(c_0_26, plain, ![X30, X31, X32, X33, X34]:k3_enumset1(X30,X31,X32,X33,X34)=k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_tarski(X34)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.18/0.53  fof(c_0_27, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.53  fof(c_0_28, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.18/0.53  cnf(c_0_29, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.53  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.53  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.53  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.53  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.53  cnf(c_0_34, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.53  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.53  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 0.18/0.53  fof(c_0_37, plain, ![X25, X26, X27, X28, X29]:k3_enumset1(X25,X26,X27,X28,X29)=k2_xboole_0(k2_tarski(X25,X26),k1_enumset1(X27,X28,X29)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.18/0.53  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.53  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.53  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_22]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_41, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_30]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_42, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_30]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_30]), c_0_22]), c_0_31]), c_0_32]), c_0_32])).
% 0.18/0.53  fof(c_0_44, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.18/0.53  fof(c_0_45, plain, ![X50, X51, X52]:k3_mcart_1(X50,X51,X52)=k4_tarski(k4_tarski(X50,X51),X52), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.18/0.53  fof(c_0_46, plain, ![X53, X54, X55]:k3_zfmisc_1(X53,X54,X55)=k2_zfmisc_1(k2_zfmisc_1(X53,X54),X55), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.18/0.53  fof(c_0_47, plain, ![X47, X48, X49]:(k2_zfmisc_1(k1_tarski(X47),k2_tarski(X48,X49))=k2_tarski(k4_tarski(X47,X48),k4_tarski(X47,X49))&k2_zfmisc_1(k2_tarski(X47,X48),k1_tarski(X49))=k2_tarski(k4_tarski(X47,X49),k4_tarski(X48,X49))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.18/0.53  cnf(c_0_48, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.53  cnf(c_0_49, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X1,X2)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_30]), c_0_30]), c_0_22]), c_0_22]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_51, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.53  cnf(c_0_52, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.53  fof(c_0_53, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.18/0.53  cnf(c_0_54, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.53  cnf(c_0_55, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.53  cnf(c_0_56, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.53  cnf(c_0_57, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.53  fof(c_0_58, plain, ![X43, X44, X45, X46]:k2_zfmisc_1(k2_tarski(X43,X44),k2_tarski(X45,X46))=k2_enumset1(k4_tarski(X43,X45),k4_tarski(X43,X46),k4_tarski(X44,X45),k4_tarski(X44,X46)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 0.18/0.53  cnf(c_0_59, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_60, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)))=k3_enumset1(X2,X3,X4,X5,X1)), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.18/0.53  cnf(c_0_61, plain, (k2_enumset1(X1,X2,X2,X2)=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_41])).
% 0.18/0.53  cnf(c_0_62, plain, (k3_enumset1(X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_51]), c_0_43]), c_0_52])).
% 0.18/0.53  cnf(c_0_63, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.53  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_30]), c_0_22]), c_0_22]), c_0_22]), c_0_32]), c_0_32]), c_0_32]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_56])).
% 0.18/0.53  cnf(c_0_65, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_30]), c_0_22]), c_0_22]), c_0_22]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_66, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.53  cnf(c_0_67, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_52]), c_0_52])).
% 0.18/0.53  cnf(c_0_68, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X2,X3,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_41]), c_0_62])).
% 0.18/0.53  cnf(c_0_69, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_22]), c_0_22]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.18/0.53  cnf(c_0_71, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_22]), c_0_22]), c_0_32]), c_0_32])).
% 0.18/0.53  cnf(c_0_72, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_67])).
% 0.18/0.53  cnf(c_0_73, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X1,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_68]), c_0_43]), c_0_62]), c_0_62])).
% 0.18/0.53  cnf(c_0_74, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_60]), c_0_52]), c_0_52])).
% 0.18/0.53  cnf(c_0_75, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_69, c_0_59])).
% 0.18/0.53  cnf(c_0_76, negated_conjecture, (k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))!=k2_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.53  cnf(c_0_77, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X2,X3)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.53  cnf(c_0_78, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_74]), c_0_59]), c_0_75]), c_0_75])).
% 0.18/0.53  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), ['proof']).
% 0.18/0.53  # SZS output end CNFRefutation
% 0.18/0.53  # Proof object total steps             : 80
% 0.18/0.53  # Proof object clause steps            : 45
% 0.18/0.53  # Proof object formula steps           : 35
% 0.18/0.53  # Proof object conjectures             : 8
% 0.18/0.53  # Proof object clause conjectures      : 5
% 0.18/0.53  # Proof object formula conjectures     : 3
% 0.18/0.53  # Proof object initial clauses used    : 17
% 0.18/0.53  # Proof object initial formulas used   : 17
% 0.18/0.53  # Proof object generating inferences   : 9
% 0.18/0.53  # Proof object simplifying inferences  : 103
% 0.18/0.53  # Training examples: 0 positive, 0 negative
% 0.18/0.53  # Parsed axioms                        : 17
% 0.18/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.53  # Initial clauses                      : 18
% 0.18/0.53  # Removed in clause preprocessing      : 6
% 0.18/0.53  # Initial clauses in saturation        : 12
% 0.18/0.53  # Processed clauses                    : 1142
% 0.18/0.53  # ...of these trivial                  : 33
% 0.18/0.53  # ...subsumed                          : 961
% 0.18/0.53  # ...remaining for further processing  : 148
% 0.18/0.53  # Other redundant clauses eliminated   : 0
% 0.18/0.53  # Clauses deleted for lack of memory   : 0
% 0.18/0.53  # Backward-subsumed                    : 4
% 0.18/0.53  # Backward-rewritten                   : 12
% 0.18/0.53  # Generated clauses                    : 28597
% 0.18/0.53  # ...of the previous two non-trivial   : 20048
% 0.18/0.53  # Contextual simplify-reflections      : 0
% 0.18/0.53  # Paramodulations                      : 28597
% 0.18/0.53  # Factorizations                       : 0
% 0.18/0.53  # Equation resolutions                 : 0
% 0.18/0.53  # Propositional unsat checks           : 0
% 0.18/0.53  #    Propositional check models        : 0
% 0.18/0.53  #    Propositional check unsatisfiable : 0
% 0.18/0.53  #    Propositional clauses             : 0
% 0.18/0.53  #    Propositional clauses after purity: 0
% 0.18/0.53  #    Propositional unsat core size     : 0
% 0.18/0.53  #    Propositional preprocessing time  : 0.000
% 0.18/0.53  #    Propositional encoding time       : 0.000
% 0.18/0.53  #    Propositional solver time         : 0.000
% 0.18/0.53  #    Success case prop preproc time    : 0.000
% 0.18/0.53  #    Success case prop encoding time   : 0.000
% 0.18/0.53  #    Success case prop solver time     : 0.000
% 0.18/0.53  # Current number of processed clauses  : 121
% 0.18/0.53  #    Positive orientable unit clauses  : 38
% 0.18/0.53  #    Positive unorientable unit clauses: 83
% 0.18/0.53  #    Negative unit clauses             : 0
% 0.18/0.53  #    Non-unit-clauses                  : 0
% 0.18/0.53  # Current number of unprocessed clauses: 18896
% 0.18/0.53  # ...number of literals in the above   : 18896
% 0.18/0.53  # Current number of archived formulas  : 0
% 0.18/0.53  # Current number of archived clauses   : 33
% 0.18/0.53  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.53  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.53  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.53  # Unit Clause-clause subsumption calls : 3644
% 0.18/0.53  # Rewrite failures with RHS unbound    : 0
% 0.18/0.53  # BW rewrite match attempts            : 8233
% 0.18/0.53  # BW rewrite match successes           : 3313
% 0.18/0.53  # Condensation attempts                : 0
% 0.18/0.53  # Condensation successes               : 0
% 0.18/0.53  # Termbank termtop insertions          : 206913
% 0.18/0.53  
% 0.18/0.53  # -------------------------------------------------
% 0.18/0.53  # User time                : 0.185 s
% 0.18/0.53  # System time              : 0.013 s
% 0.18/0.53  # Total time               : 0.199 s
% 0.18/0.53  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
