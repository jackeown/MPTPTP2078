%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0193+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:40 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 142 expanded)
%              Number of clauses        :   13 (  51 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 ( 142 expanded)
%              Number of equality atoms :   29 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t112_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t111_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    inference(assume_negation,[status(cth)],[t112_enumset1])).

fof(c_0_9,negated_conjecture,(
    k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk20_0,esk22_0,esk19_0,esk21_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X716,X717,X718,X719] : k3_enumset1(X716,X716,X717,X718,X719) = k2_enumset1(X716,X717,X718,X719) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_11,plain,(
    ! [X720,X721,X722,X723,X724] : k4_enumset1(X720,X720,X721,X722,X723,X724) = k3_enumset1(X720,X721,X722,X723,X724) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_12,plain,(
    ! [X725,X726,X727,X728,X729,X730] : k5_enumset1(X725,X725,X726,X727,X728,X729,X730) = k4_enumset1(X725,X726,X727,X728,X729,X730) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_13,plain,(
    ! [X731,X732,X733,X734,X735,X736,X737] : k6_enumset1(X731,X731,X732,X733,X734,X735,X736,X737) = k5_enumset1(X731,X732,X733,X734,X735,X736,X737) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_14,plain,(
    ! [X534,X535,X536,X537] : k2_enumset1(X534,X535,X536,X537) = k2_enumset1(X535,X536,X537,X534) ),
    inference(variable_rename,[status(thm)],[t111_enumset1])).

fof(c_0_15,plain,(
    ! [X514,X515,X516,X517] : k2_enumset1(X514,X515,X516,X517) = k2_enumset1(X514,X516,X517,X515) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

fof(c_0_16,plain,(
    ! [X518,X519,X520,X521] : k2_enumset1(X518,X519,X520,X521) = k2_enumset1(X518,X521,X520,X519) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk20_0,esk22_0,esk19_0,esk21_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k6_enumset1(esk20_0,esk20_0,esk20_0,esk20_0,esk20_0,esk22_0,esk19_0,esk21_0) != k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_26]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
