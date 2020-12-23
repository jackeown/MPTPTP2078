%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0195+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   22 (  58 expanded)
%              Number of clauses        :    9 (  21 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  58 expanded)
%              Number of equality atoms :   21 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

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

fof(l129_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    inference(assume_negation,[status(cth)],[t116_enumset1])).

fof(c_0_7,negated_conjecture,(
    k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk21_0,esk20_0,esk19_0,esk22_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X728,X729,X730,X731] : k3_enumset1(X728,X728,X729,X730,X731) = k2_enumset1(X728,X729,X730,X731) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_9,plain,(
    ! [X732,X733,X734,X735,X736] : k4_enumset1(X732,X732,X733,X734,X735,X736) = k3_enumset1(X732,X733,X734,X735,X736) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_10,plain,(
    ! [X737,X738,X739,X740,X741,X742] : k5_enumset1(X737,X737,X738,X739,X740,X741,X742) = k4_enumset1(X737,X738,X739,X740,X741,X742) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_11,plain,(
    ! [X743,X744,X745,X746,X747,X748,X749] : k6_enumset1(X743,X743,X744,X745,X746,X747,X748,X749) = k5_enumset1(X743,X744,X745,X746,X747,X748,X749) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_12,plain,(
    ! [X470,X471,X472,X473] : k2_enumset1(X470,X471,X472,X473) = k2_enumset1(X472,X471,X470,X473) ),
    inference(variable_rename,[status(thm)],[l129_enumset1])).

cnf(c_0_13,negated_conjecture,
    ( k2_enumset1(esk19_0,esk20_0,esk21_0,esk22_0) != k2_enumset1(esk21_0,esk20_0,esk19_0,esk22_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k6_enumset1(esk21_0,esk21_0,esk21_0,esk21_0,esk21_0,esk20_0,esk19_0,esk22_0) != k6_enumset1(esk19_0,esk19_0,esk19_0,esk19_0,esk19_0,esk20_0,esk21_0,esk22_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_16]),c_0_16]),c_0_17]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
