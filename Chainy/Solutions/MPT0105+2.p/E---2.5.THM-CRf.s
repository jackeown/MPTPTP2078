%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 188 expanded)
%              Number of clauses        :   30 (  85 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 188 expanded)
%              Number of equality atoms :   54 ( 187 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_12,plain,(
    ! [X362,X363] : k2_xboole_0(X362,X363) = k5_xboole_0(k5_xboole_0(X362,X363),k3_xboole_0(X362,X363)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,plain,(
    ! [X226,X227] : k4_xboole_0(X226,k4_xboole_0(X226,X227)) = k3_xboole_0(X226,X227) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X208,X209,X210] : k4_xboole_0(k4_xboole_0(X208,X209),X210) = k4_xboole_0(X208,k2_xboole_0(X209,X210)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X243,X244,X245] : k4_xboole_0(X243,k2_xboole_0(X244,X245)) = k3_xboole_0(k4_xboole_0(X243,X244),k4_xboole_0(X243,X245)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X356,X357,X358] : k5_xboole_0(k5_xboole_0(X356,X357),X358) = k5_xboole_0(X356,k5_xboole_0(X357,X358)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_21,plain,(
    ! [X104,X105,X106] : k4_xboole_0(X104,k3_xboole_0(X105,X106)) = k2_xboole_0(k4_xboole_0(X104,X105),k4_xboole_0(X104,X106)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X240,X241,X242] : k4_xboole_0(X240,k4_xboole_0(X241,X242)) = k2_xboole_0(k4_xboole_0(X240,X241),k3_xboole_0(X240,X242)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X176] : k3_xboole_0(X176,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

fof(c_0_31,plain,(
    ! [X202,X203] : k2_xboole_0(X202,k4_xboole_0(X203,X202)) = k2_xboole_0(X202,X203) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_19])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24]),c_0_28])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X204] : k4_xboole_0(X204,k1_xboole_0) = X204 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_37,negated_conjecture,(
    k2_xboole_0(esk16_0,esk17_0) != k5_xboole_0(esk16_0,k4_xboole_0(esk17_0,esk16_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_16]),c_0_19])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_24])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk16_0,esk17_0) != k5_xboole_0(esk16_0,k4_xboole_0(esk17_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_19]),c_0_19])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_34]),c_0_24]),c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_47,plain,(
    ! [X262] : k5_xboole_0(X262,k1_xboole_0) = X262 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0))) != k5_xboole_0(esk16_0,k4_xboole_0(esk17_0,esk16_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_24]),c_0_24])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_42]),c_0_46]),c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk16_0,k5_xboole_0(esk17_0,k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)))) != k5_xboole_0(esk16_0,k4_xboole_0(esk17_0,esk16_0)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_24])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_46]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
