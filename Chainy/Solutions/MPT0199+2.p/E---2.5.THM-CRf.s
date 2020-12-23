%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0199+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 114 expanded)
%              Number of clauses        :   13 (  41 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 ( 114 expanded)
%              Number of equality atoms :   29 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

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

fof(t119_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(t103_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(assume_negation,[status(cth)],[t123_enumset1])).

fof(c_0_9,negated_conjecture,(
    k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk22_0,esk20_0,esk21_0,esk19_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X744,X745,X746,X747] : k3_enumset1(X744,X744,X745,X746,X747) = k2_enumset1(X744,X745,X746,X747) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_11,plain,(
    ! [X748,X749,X750,X751,X752] : k4_enumset1(X748,X748,X749,X750,X751,X752) = k3_enumset1(X748,X749,X750,X751,X752) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_12,plain,(
    ! [X753,X754,X755,X756,X757,X758] : k5_enumset1(X753,X753,X754,X755,X756,X757,X758) = k4_enumset1(X753,X754,X755,X756,X757,X758) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_13,plain,(
    ! [X759,X760,X761,X762,X763,X764,X765] : k6_enumset1(X759,X759,X760,X761,X762,X763,X764,X765) = k5_enumset1(X759,X760,X761,X762,X763,X764,X765) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_14,plain,(
    ! [X562,X563,X564,X565] : k2_enumset1(X562,X563,X564,X565) = k2_enumset1(X564,X565,X563,X562) ),
    inference(variable_rename,[status(thm)],[t119_enumset1])).

fof(c_0_15,plain,(
    ! [X522,X523,X524,X525] : k2_enumset1(X522,X523,X524,X525) = k2_enumset1(X522,X525,X524,X523) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_16,plain,(
    ! [X510,X511,X512,X513] : k2_enumset1(X510,X511,X512,X513) = k2_enumset1(X510,X511,X513,X512) ),
    inference(variable_rename,[status(thm)],[t103_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk22_0,esk20_0,esk21_0,esk19_0) ),
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
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k6_enumset1(esk22_0,esk22_0,esk22_0,esk22_0,esk22_0,esk20_0,esk21_0,esk19_0) != k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X4,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
