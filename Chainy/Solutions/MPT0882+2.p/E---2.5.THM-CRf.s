%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0882+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:56 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 221 expanded)
%              Number of clauses        :   14 (  76 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 ( 225 expanded)
%              Number of equality atoms :   38 ( 224 expanded)
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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t36_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X2,X4)) ),
    inference(assume_negation,[status(cth)],[t42_mcart_1])).

fof(c_0_12,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X107] : k2_tarski(X107,X107) = k1_tarski(X107) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X108,X109] : k1_enumset1(X108,X108,X109) = k2_tarski(X108,X109) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X1236,X1237,X1238] : k2_enumset1(X1236,X1236,X1237,X1238) = k1_enumset1(X1236,X1237,X1238) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X285,X286,X287] : k3_mcart_1(X285,X286,X287) = k4_tarski(k4_tarski(X285,X286),X287) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_17,plain,(
    ! [X318,X319,X320] : k3_zfmisc_1(X318,X319,X320) = k2_zfmisc_1(k2_zfmisc_1(X318,X319),X320) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X1239,X1240,X1241,X1242] : k3_enumset1(X1239,X1239,X1240,X1241,X1242) = k2_enumset1(X1239,X1240,X1241,X1242) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X1377,X1378,X1379,X1380,X1381] : k4_enumset1(X1377,X1377,X1378,X1379,X1380,X1381) = k3_enumset1(X1377,X1378,X1379,X1380,X1381) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X1533,X1534,X1535,X1536,X1537,X1538] : k5_enumset1(X1533,X1533,X1534,X1535,X1536,X1537,X1538) = k4_enumset1(X1533,X1534,X1535,X1536,X1537,X1538) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X1610,X1611,X1612,X1613,X1614,X1615,X1616] : k6_enumset1(X1610,X1610,X1611,X1612,X1613,X1614,X1615,X1616) = k5_enumset1(X1610,X1611,X1612,X1613,X1614,X1615,X1616) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X182,X183,X184] :
      ( k2_zfmisc_1(k1_tarski(X182),k2_tarski(X183,X184)) = k2_tarski(k4_tarski(X182,X183),k4_tarski(X182,X184))
      & k2_zfmisc_1(k2_tarski(X182,X183),k1_tarski(X184)) = k2_tarski(k4_tarski(X182,X184),k4_tarski(X183,X184)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_23,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_mcart_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) != k6_enumset1(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
