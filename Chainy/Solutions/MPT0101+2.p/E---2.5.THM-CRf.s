%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:36 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 184 expanded)
%              Number of clauses        :   36 (  79 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 184 expanded)
%              Number of equality atoms :   68 ( 183 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d6_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_16,plain,(
    ! [X226,X227,X228] : k3_xboole_0(X226,k4_xboole_0(X227,X228)) = k4_xboole_0(k3_xboole_0(X226,X227),X228) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_17,plain,(
    ! [X224,X225] : k4_xboole_0(X224,k4_xboole_0(X224,X225)) = k3_xboole_0(X224,X225) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

fof(c_0_19,plain,(
    ! [X130,X131,X132] : k3_xboole_0(k3_xboole_0(X130,X131),X132) = k3_xboole_0(X130,k3_xboole_0(X131,X132)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X206,X207,X208] : k4_xboole_0(k4_xboole_0(X206,X207),X208) = k4_xboole_0(X206,k2_xboole_0(X207,X208)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_23,plain,(
    ! [X200,X201] : k2_xboole_0(X200,k4_xboole_0(X201,X200)) = k2_xboole_0(X200,X201) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_24,negated_conjecture,(
    k2_xboole_0(esk16_0,esk17_0) != k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k3_xboole_0(esk16_0,esk17_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_25,plain,(
    ! [X52,X53] : k5_xboole_0(X52,X53) = k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_31,plain,(
    ! [X174] : k3_xboole_0(X174,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_32,plain,(
    ! [X104,X105,X106] : k4_xboole_0(X104,k3_xboole_0(X105,X106)) = k2_xboole_0(k4_xboole_0(X104,X105),k4_xboole_0(X104,X106)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_33,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_34,plain,(
    ! [X238,X239,X240] : k4_xboole_0(X238,k4_xboole_0(X239,X240)) = k2_xboole_0(k4_xboole_0(X238,X239),k3_xboole_0(X238,X240)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk16_0,esk17_0) != k5_xboole_0(k5_xboole_0(esk16_0,esk17_0),k3_xboole_0(esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X286,X287] : k2_xboole_0(X286,k2_xboole_0(X286,X287)) = k2_xboole_0(X286,X287) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X202] : k4_xboole_0(X202,k1_xboole_0) = X202 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(esk16_0,esk17_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk17_0,esk16_0)),k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0))),k4_xboole_0(k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)),k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk17_0,esk16_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_21]),c_0_36]),c_0_36])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_28]),c_0_28]),c_0_39])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_21])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_53,plain,(
    ! [X141] : k2_xboole_0(X141,k1_xboole_0) = X141 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_54,plain,(
    ! [X230,X231,X232] : k2_xboole_0(k2_xboole_0(X230,X231),X232) = k2_xboole_0(X230,k2_xboole_0(X231,X232)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_21]),c_0_21])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk16_0,k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk17_0,esk16_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk17_0,esk16_0)),k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)))) != k2_xboole_0(esk16_0,esk17_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_41]),c_0_28]),c_0_48])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_39])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X1),X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_57]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)),k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk17_0,esk16_0))) != k2_xboole_0(esk16_0,esk17_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_29])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_60]),c_0_52]),c_0_41]),c_0_29]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
