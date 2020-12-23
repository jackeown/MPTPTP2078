%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0102+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:36 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 459 expanded)
%              Number of clauses        :   50 ( 206 expanded)
%              Number of leaves         :   20 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 465 expanded)
%              Number of equality atoms :   88 ( 456 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_20,plain,(
    ! [X362,X363] : k2_xboole_0(X362,X363) = k5_xboole_0(k5_xboole_0(X362,X363),k3_xboole_0(X362,X363)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_21,plain,(
    ! [X226,X227] : k4_xboole_0(X226,k4_xboole_0(X226,X227)) = k3_xboole_0(X226,X227) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X208,X209,X210] : k4_xboole_0(k4_xboole_0(X208,X209),X210) = k4_xboole_0(X208,k2_xboole_0(X209,X210)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X243,X244,X245] : k4_xboole_0(X243,k2_xboole_0(X244,X245)) = k3_xboole_0(k4_xboole_0(X243,X244),k4_xboole_0(X243,X245)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X356,X357,X358] : k5_xboole_0(k5_xboole_0(X356,X357),X358) = k5_xboole_0(X356,k5_xboole_0(X357,X358)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_29,plain,(
    ! [X104,X105,X106] : k4_xboole_0(X104,k3_xboole_0(X105,X106)) = k2_xboole_0(k4_xboole_0(X104,X105),k4_xboole_0(X104,X106)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X240,X241,X242] : k4_xboole_0(X240,k4_xboole_0(X241,X242)) = k2_xboole_0(k4_xboole_0(X240,X241),k3_xboole_0(X240,X242)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_24]),c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,plain,(
    ! [X176] : k3_xboole_0(X176,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

fof(c_0_39,plain,(
    ! [X202,X203] : k2_xboole_0(X202,k4_xboole_0(X203,X202)) = k2_xboole_0(X202,X203) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_27])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_32]),c_0_36])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X204] : k4_xboole_0(X204,k1_xboole_0) = X204 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_45,negated_conjecture,(
    k3_xboole_0(esk16_0,esk17_0) != k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k2_xboole_0(esk16_0,esk17_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_27])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_32])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X58] : k2_xboole_0(X58,X58) = X58 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_52,plain,(
    ! [X112,X113] : k5_xboole_0(X112,X113) = k4_xboole_0(k2_xboole_0(X112,X113),k3_xboole_0(X112,X113)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk16_0,esk17_0) != k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k2_xboole_0(esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_27]),c_0_27])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_42]),c_0_32]),c_0_48])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_57,plain,(
    ! [X262] : k5_xboole_0(X262,k1_xboole_0) = X262 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X359] : k5_xboole_0(X359,X359) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)) != k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_24]),c_0_27])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_32]),c_0_32])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_50]),c_0_56]),c_0_50])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X13,X14] : k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_24]),c_0_27])).

fof(c_0_69,plain,(
    ! [X224,X225] : k4_xboole_0(X224,k3_xboole_0(X224,X225)) = k4_xboole_0(X224,X225) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk16_0,k5_xboole_0(esk17_0,k5_xboole_0(esk16_0,k5_xboole_0(esk17_0,k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)))))) != k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_32]),c_0_32])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_56]),c_0_64])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_56]),c_0_50])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_32])).

fof(c_0_75,plain,(
    ! [X102,X103] :
      ( ( k4_xboole_0(X102,X103) != k1_xboole_0
        | r1_tarski(X102,X103) )
      & ( ~ r1_tarski(X102,X103)
        | k4_xboole_0(X102,X103) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_77,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk16_0,k5_xboole_0(esk17_0,k5_xboole_0(esk16_0,k4_xboole_0(esk17_0,esk16_0)))) != k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_32])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_67]),c_0_73])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_74,c_0_71])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_24])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X196,X197] : r1_tarski(k4_xboole_0(X196,X197),X196) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(esk17_0,k4_xboole_0(esk17_0,esk16_0)) != k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_72]),c_0_80])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_64]),c_0_83])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_24]),c_0_24])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
