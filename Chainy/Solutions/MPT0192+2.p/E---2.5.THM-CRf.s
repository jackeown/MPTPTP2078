%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0192+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:40 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 114 expanded)
%              Number of clauses        :   11 (  41 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 ( 114 expanded)
%              Number of equality atoms :   25 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

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

fof(l123_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(t103_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(assume_negation,[status(cth)],[t111_enumset1])).

fof(c_0_8,negated_conjecture,(
    k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk20_0,esk21_0,esk22_0,esk19_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X712,X713,X714,X715] : k3_enumset1(X712,X712,X713,X714,X715) = k2_enumset1(X712,X713,X714,X715) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_10,plain,(
    ! [X716,X717,X718,X719,X720] : k4_enumset1(X716,X716,X717,X718,X719,X720) = k3_enumset1(X716,X717,X718,X719,X720) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_11,plain,(
    ! [X721,X722,X723,X724,X725,X726] : k5_enumset1(X721,X721,X722,X723,X724,X725,X726) = k4_enumset1(X721,X722,X723,X724,X725,X726) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_12,plain,(
    ! [X727,X728,X729,X730,X731,X732,X733] : k6_enumset1(X727,X727,X728,X729,X730,X731,X732,X733) = k5_enumset1(X727,X728,X729,X730,X731,X732,X733) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_13,plain,(
    ! [X466,X467,X468,X469] : k2_enumset1(X466,X467,X468,X469) = k2_enumset1(X467,X468,X466,X469) ),
    inference(variable_rename,[status(thm)],[l123_enumset1])).

fof(c_0_14,plain,(
    ! [X506,X507,X508,X509] : k2_enumset1(X506,X507,X508,X509) = k2_enumset1(X506,X507,X509,X508) ),
    inference(variable_rename,[status(thm)],[t103_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk20_0,esk21_0,esk22_0,esk19_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k6_enumset1(esk20_0,esk20_0,esk20_0,esk20_0,esk20_0,esk21_0,esk22_0,esk19_0) != k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_23,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
