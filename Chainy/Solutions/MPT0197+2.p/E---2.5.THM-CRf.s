%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0197+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:40 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 170 expanded)
%              Number of clauses        :   15 (  61 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 ( 170 expanded)
%              Number of equality atoms :   33 ( 169 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t118_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

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

fof(t117_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(t103_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(assume_negation,[status(cth)],[t118_enumset1])).

fof(c_0_10,negated_conjecture,(
    k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk21_0,esk22_0,esk19_0,esk20_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X736,X737,X738,X739] : k3_enumset1(X736,X736,X737,X738,X739) = k2_enumset1(X736,X737,X738,X739) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_12,plain,(
    ! [X740,X741,X742,X743,X744] : k4_enumset1(X740,X740,X741,X742,X743,X744) = k3_enumset1(X740,X741,X742,X743,X744) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_13,plain,(
    ! [X745,X746,X747,X748,X749,X750] : k5_enumset1(X745,X745,X746,X747,X748,X749,X750) = k4_enumset1(X745,X746,X747,X748,X749,X750) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_14,plain,(
    ! [X751,X752,X753,X754,X755,X756,X757] : k6_enumset1(X751,X751,X752,X753,X754,X755,X756,X757) = k5_enumset1(X751,X752,X753,X754,X755,X756,X757) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_15,plain,(
    ! [X554,X555,X556,X557] : k2_enumset1(X554,X555,X556,X557) = k2_enumset1(X556,X555,X557,X554) ),
    inference(variable_rename,[status(thm)],[t117_enumset1])).

fof(c_0_16,plain,(
    ! [X522,X523,X524,X525] : k2_enumset1(X522,X523,X524,X525) = k2_enumset1(X522,X525,X524,X523) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_17,plain,(
    ! [X518,X519,X520,X521] : k2_enumset1(X518,X519,X520,X521) = k2_enumset1(X518,X520,X521,X519) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

fof(c_0_18,plain,(
    ! [X510,X511,X512,X513] : k2_enumset1(X510,X511,X512,X513) = k2_enumset1(X510,X511,X513,X512) ),
    inference(variable_rename,[status(thm)],[t103_enumset1])).

cnf(c_0_19,negated_conjecture,
    ( k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk21_0,esk22_0,esk19_0,esk20_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k6_enumset1(esk21_0,esk21_0,esk21_0,esk21_0,esk21_0,esk22_0,esk19_0,esk20_0) != k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X2,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_30]),c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
