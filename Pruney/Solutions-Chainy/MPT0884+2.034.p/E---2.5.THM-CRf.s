%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 262 expanded)
%              Number of clauses        :   23 (  93 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 264 expanded)
%              Number of equality atoms :   53 ( 263 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(t103_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t25_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

fof(c_0_15,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X47,X48,X49] : k3_mcart_1(X47,X48,X49) = k4_tarski(k4_tarski(X47,X48),X49) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_20,plain,(
    ! [X50,X51,X52] : k3_zfmisc_1(X50,X51,X52) = k2_zfmisc_1(k2_zfmisc_1(X50,X51),X52) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_enumset1(X12,X14,X15,X13) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_26,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X9,X11,X10) ),
    inference(variable_rename,[status(thm)],[t103_enumset1])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X44,X45,X46] :
      ( k2_zfmisc_1(k1_tarski(X44),k2_tarski(X45,X46)) = k2_tarski(k4_tarski(X44,X45),k4_tarski(X44,X46))
      & k2_zfmisc_1(k2_tarski(X44,X45),k1_tarski(X46)) = k2_tarski(k4_tarski(X44,X46),k4_tarski(X45,X46)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_45,plain,(
    ! [X53,X54,X55,X56] : k2_zfmisc_1(k2_tarski(X53,X54),k2_tarski(X55,X56)) = k2_enumset1(k4_tarski(X53,X55),k4_tarski(X53,X56),k4_tarski(X54,X55),k4_tarski(X54,X56)) ),
    inference(variable_rename,[status(thm)],[t25_mcart_1])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.38  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 0.20/0.38  fof(t103_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 0.20/0.38  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.20/0.38  fof(t25_mcart_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_mcart_1)).
% 0.20/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 0.20/0.38  fof(c_0_15, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_17, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_18, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_19, plain, ![X47, X48, X49]:k3_mcart_1(X47,X48,X49)=k4_tarski(k4_tarski(X47,X48),X49), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.38  fof(c_0_20, plain, ![X50, X51, X52]:k3_zfmisc_1(X50,X51,X52)=k2_zfmisc_1(k2_zfmisc_1(X50,X51),X52), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_21, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.38  fof(c_0_22, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_23, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.38  fof(c_0_24, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_enumset1(X12,X14,X15,X13), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_30, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_31, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_36, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  fof(c_0_37, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_enumset1(X8,X9,X11,X10), inference(variable_rename,[status(thm)],[t103_enumset1])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  fof(c_0_41, plain, ![X44, X45, X46]:(k2_zfmisc_1(k1_tarski(X44),k2_tarski(X45,X46))=k2_tarski(k4_tarski(X44,X45),k4_tarski(X44,X46))&k2_zfmisc_1(k2_tarski(X44,X45),k1_tarski(X46))=k2_tarski(k4_tarski(X44,X46),k4_tarski(X45,X46))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_44, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  fof(c_0_45, plain, ![X53, X54, X55, X56]:k2_zfmisc_1(k2_tarski(X53,X54),k2_tarski(X55,X56))=k2_enumset1(k4_tarski(X53,X55),k4_tarski(X53,X56),k4_tarski(X54,X55),k4_tarski(X54,X56)), inference(variable_rename,[status(thm)],[t25_mcart_1])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_47, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_48, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k6_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk3_0),k4_tarski(esk2_0,esk3_0)),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_50, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 52
% 0.20/0.38  # Proof object clause steps            : 23
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 9
% 0.20/0.38  # Proof object clause conjectures      : 6
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 0
% 0.20/0.38  # Proof object simplifying inferences  : 84
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 9
% 0.20/0.38  # Initial clauses in saturation        : 6
% 0.20/0.38  # Processed clauses                    : 8
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 8
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 0
% 0.20/0.38  # ...of the previous two non-trivial   : 2
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 0
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 5
% 0.20/0.38  #    Positive orientable unit clauses  : 2
% 0.20/0.38  #    Positive unorientable unit clauses: 3
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 0
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 12
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 3
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 22
% 0.20/0.38  # BW rewrite match successes           : 17
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1050
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.027 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.031 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
