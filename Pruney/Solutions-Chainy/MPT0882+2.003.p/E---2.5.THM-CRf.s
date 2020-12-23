%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 323 expanded)
%              Number of clauses        :   22 ( 122 expanded)
%              Number of leaves         :   13 ( 100 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 359 expanded)
%              Number of equality atoms :   52 ( 358 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)) ),
    inference(assume_negation,[status(cth)],[t42_mcart_1])).

fof(c_0_14,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] : k3_zfmisc_1(X39,X40,X41) = k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35) = k5_enumset1(X29,X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X36,X37,X38] :
      ( k2_zfmisc_1(k1_tarski(X36),k2_tarski(X37,X38)) = k2_tarski(k4_tarski(X36,X37),k4_tarski(X36,X38))
      & k2_zfmisc_1(k2_tarski(X36,X37),k1_tarski(X38)) = k2_tarski(k4_tarski(X36,X38),k4_tarski(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X46,X47,X48,X49] : k4_mcart_1(X46,X47,X48,X49) = k4_tarski(k4_tarski(k4_tarski(X46,X47),X48),X49) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

fof(c_0_35,plain,(
    ! [X42,X43,X44,X45] : k4_mcart_1(X42,X43,X44,X45) = k4_tarski(k3_mcart_1(X42,X43,X44),X45) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X50,X51] :
      ( k1_mcart_1(k4_tarski(X50,X51)) = X50
      & k2_mcart_1(k4_tarski(X50,X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_40,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) != k2_zfmisc_1(k6_enumset1(k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_44,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_tarski(k3_mcart_1(X1,X2,X3),X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.013 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t42_mcart_1, conjecture, ![X1, X2, X3, X4]:k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4))=k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_mcart_1)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.36  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.36  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.36  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.13/0.36  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.13/0.36  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.36  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.36  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4))=k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4))), inference(assume_negation,[status(cth)],[t42_mcart_1])).
% 0.13/0.36  fof(c_0_14, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))!=k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.36  fof(c_0_15, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_16, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_17, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_18, plain, ![X39, X40, X41]:k3_zfmisc_1(X39,X40,X41)=k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.36  fof(c_0_19, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.36  fof(c_0_20, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.36  fof(c_0_21, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.36  fof(c_0_22, plain, ![X29, X30, X31, X32, X33, X34, X35]:k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35)=k5_enumset1(X29,X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.36  fof(c_0_23, plain, ![X36, X37, X38]:(k2_zfmisc_1(k1_tarski(X36),k2_tarski(X37,X38))=k2_tarski(k4_tarski(X36,X37),k4_tarski(X36,X38))&k2_zfmisc_1(k2_tarski(X36,X37),k1_tarski(X38))=k2_tarski(k4_tarski(X36,X38),k4_tarski(X37,X38))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.13/0.36  cnf(c_0_24, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))!=k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.36  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_28, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.36  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.36  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_33, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  fof(c_0_34, plain, ![X46, X47, X48, X49]:k4_mcart_1(X46,X47,X48,X49)=k4_tarski(k4_tarski(k4_tarski(X46,X47),X48),X49), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.13/0.36  fof(c_0_35, plain, ![X42, X43, X44, X45]:k4_mcart_1(X42,X43,X44,X45)=k4_tarski(k3_mcart_1(X42,X43,X44),X45), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))!=k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.13/0.36  cnf(c_0_37, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 0.13/0.36  cnf(c_0_38, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  fof(c_0_39, plain, ![X50, X51]:(k1_mcart_1(k4_tarski(X50,X51))=X50&k2_mcart_1(k4_tarski(X50,X51))=X51), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.36  cnf(c_0_40, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.36  cnf(c_0_41, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0))!=k2_zfmisc_1(k6_enumset1(k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.36  cnf(c_0_43, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))=k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32])).
% 0.13/0.36  cnf(c_0_44, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.36  cnf(c_0_45, plain, (k4_tarski(k3_mcart_1(X1,X2,X3),X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.36  cnf(c_0_46, negated_conjecture, (k6_enumset1(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0))!=k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.36  cnf(c_0_47, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_44])).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 49
% 0.13/0.36  # Proof object clause steps            : 22
% 0.13/0.36  # Proof object formula steps           : 27
% 0.13/0.36  # Proof object conjectures             : 8
% 0.13/0.36  # Proof object clause conjectures      : 5
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 14
% 0.13/0.36  # Proof object initial formulas used   : 13
% 0.13/0.36  # Proof object generating inferences   : 1
% 0.13/0.36  # Proof object simplifying inferences  : 78
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 13
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 15
% 0.13/0.36  # Removed in clause preprocessing      : 9
% 0.13/0.36  # Initial clauses in saturation        : 6
% 0.13/0.36  # Processed clauses                    : 14
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 13
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 3
% 0.13/0.36  # Generated clauses                    : 2
% 0.13/0.36  # ...of the previous two non-trivial   : 3
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 2
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 4
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 0
% 0.13/0.36  #    Non-unit-clauses                  : 0
% 0.13/0.36  # Current number of unprocessed clauses: 1
% 0.13/0.36  # ...number of literals in the above   : 1
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 18
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 3
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 991
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.010 s
% 0.13/0.36  # System time              : 0.006 s
% 0.13/0.36  # Total time               : 0.016 s
% 0.13/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
