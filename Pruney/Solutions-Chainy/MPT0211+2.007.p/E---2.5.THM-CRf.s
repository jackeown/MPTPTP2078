%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:42 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 786 expanded)
%              Number of clauses        :   26 ( 279 expanded)
%              Number of leaves         :   13 ( 253 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 786 expanded)
%              Number of equality atoms :   52 ( 785 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k4_enumset1(X23,X24,X25,X26,X27,X28) = k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_15,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_18,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k5_enumset1(X29,X30,X31,X32,X33,X34,X35) = k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k2_tarski(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_24,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_25,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20,X21,X22] : k4_enumset1(X17,X18,X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_29]),c_0_29]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_29]),c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X5,X4,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk1_0,esk3_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k6_enumset1(X1,X1,X1,X2,X3,X5,X4,X6) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.67  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.47/0.67  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.47/0.67  #
% 0.47/0.67  # Preprocessing time       : 0.026 s
% 0.47/0.67  # Presaturation interreduction done
% 0.47/0.67  
% 0.47/0.67  # Proof found!
% 0.47/0.67  # SZS status Theorem
% 0.47/0.67  # SZS output start CNFRefutation
% 0.47/0.67  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 0.47/0.67  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.47/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.67  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.47/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.67  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.47/0.67  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.47/0.67  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.47/0.67  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.47/0.67  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 0.47/0.67  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.47/0.67  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.47/0.67  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.47/0.67  fof(c_0_14, plain, ![X23, X24, X25, X26, X27, X28]:k4_enumset1(X23,X24,X25,X26,X27,X28)=k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.47/0.67  fof(c_0_15, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.67  fof(c_0_16, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.67  fof(c_0_17, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k5_xboole_0(X8,k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.47/0.67  fof(c_0_18, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.67  fof(c_0_19, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.47/0.67  fof(c_0_20, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.47/0.67  fof(c_0_21, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.47/0.67  fof(c_0_22, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.47/0.67  fof(c_0_23, plain, ![X29, X30, X31, X32, X33, X34, X35]:k5_enumset1(X29,X30,X31,X32,X33,X34,X35)=k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k2_tarski(X34,X35)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.47/0.67  fof(c_0_24, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_tarski(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.47/0.67  fof(c_0_25, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.47/0.67  fof(c_0_26, plain, ![X17, X18, X19, X20, X21, X22]:k4_enumset1(X17,X18,X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.47/0.67  cnf(c_0_27, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.67  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.67  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.67  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.67  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.67  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.67  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.67  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.67  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.67  cnf(c_0_36, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.67  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.67  cnf(c_0_38, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.67  cnf(c_0_39, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.67  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.47/0.67  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.47/0.67  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_29]), c_0_29]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.47/0.67  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_29]), c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.47/0.67  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.47/0.67  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.47/0.67  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X7,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_41])).
% 0.47/0.67  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_42]), c_0_42]), c_0_42])).
% 0.47/0.67  cnf(c_0_48, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X6),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.47/0.67  cnf(c_0_49, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X5,X4,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_41])).
% 0.47/0.67  cnf(c_0_50, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk1_0,esk3_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_41])).
% 0.47/0.67  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k6_enumset1(X1,X1,X1,X2,X3,X5,X4,X6)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_48])).
% 0.47/0.67  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])]), ['proof']).
% 0.47/0.67  # SZS output end CNFRefutation
% 0.47/0.67  # Proof object total steps             : 53
% 0.47/0.67  # Proof object clause steps            : 26
% 0.47/0.67  # Proof object formula steps           : 27
% 0.47/0.67  # Proof object conjectures             : 8
% 0.47/0.67  # Proof object clause conjectures      : 5
% 0.47/0.67  # Proof object formula conjectures     : 3
% 0.47/0.67  # Proof object initial clauses used    : 13
% 0.47/0.67  # Proof object initial formulas used   : 13
% 0.47/0.67  # Proof object generating inferences   : 4
% 0.47/0.67  # Proof object simplifying inferences  : 93
% 0.47/0.67  # Training examples: 0 positive, 0 negative
% 0.47/0.67  # Parsed axioms                        : 14
% 0.47/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.67  # Initial clauses                      : 14
% 0.47/0.67  # Removed in clause preprocessing      : 8
% 0.47/0.67  # Initial clauses in saturation        : 6
% 0.47/0.67  # Processed clauses                    : 835
% 0.47/0.67  # ...of these trivial                  : 18
% 0.47/0.67  # ...subsumed                          : 624
% 0.47/0.67  # ...remaining for further processing  : 193
% 0.47/0.67  # Other redundant clauses eliminated   : 0
% 0.47/0.67  # Clauses deleted for lack of memory   : 0
% 0.47/0.67  # Backward-subsumed                    : 11
% 0.47/0.67  # Backward-rewritten                   : 2
% 0.47/0.67  # Generated clauses                    : 61183
% 0.47/0.67  # ...of the previous two non-trivial   : 51647
% 0.47/0.67  # Contextual simplify-reflections      : 0
% 0.47/0.67  # Paramodulations                      : 61183
% 0.47/0.67  # Factorizations                       : 0
% 0.47/0.67  # Equation resolutions                 : 0
% 0.47/0.67  # Propositional unsat checks           : 0
% 0.47/0.67  #    Propositional check models        : 0
% 0.47/0.67  #    Propositional check unsatisfiable : 0
% 0.47/0.67  #    Propositional clauses             : 0
% 0.47/0.67  #    Propositional clauses after purity: 0
% 0.47/0.67  #    Propositional unsat core size     : 0
% 0.47/0.67  #    Propositional preprocessing time  : 0.000
% 0.47/0.67  #    Propositional encoding time       : 0.000
% 0.47/0.67  #    Propositional solver time         : 0.000
% 0.47/0.67  #    Success case prop preproc time    : 0.000
% 0.47/0.67  #    Success case prop encoding time   : 0.000
% 0.47/0.67  #    Success case prop solver time     : 0.000
% 0.47/0.67  # Current number of processed clauses  : 174
% 0.47/0.67  #    Positive orientable unit clauses  : 29
% 0.47/0.67  #    Positive unorientable unit clauses: 145
% 0.47/0.67  #    Negative unit clauses             : 0
% 0.47/0.67  #    Non-unit-clauses                  : 0
% 0.47/0.67  # Current number of unprocessed clauses: 50661
% 0.47/0.67  # ...number of literals in the above   : 50661
% 0.47/0.67  # Current number of archived formulas  : 0
% 0.47/0.67  # Current number of archived clauses   : 27
% 0.47/0.67  # Clause-clause subsumption calls (NU) : 0
% 0.47/0.67  # Rec. Clause-clause subsumption calls : 0
% 0.47/0.67  # Non-unit clause-clause subsumptions  : 0
% 0.47/0.67  # Unit Clause-clause subsumption calls : 13810
% 0.47/0.67  # Rewrite failures with RHS unbound    : 0
% 0.47/0.67  # BW rewrite match attempts            : 24864
% 0.47/0.67  # BW rewrite match successes           : 7116
% 0.47/0.67  # Condensation attempts                : 0
% 0.47/0.67  # Condensation successes               : 0
% 0.47/0.67  # Termbank termtop insertions          : 215281
% 0.47/0.67  
% 0.47/0.67  # -------------------------------------------------
% 0.47/0.67  # User time                : 0.308 s
% 0.47/0.67  # System time              : 0.019 s
% 0.47/0.67  # Total time               : 0.328 s
% 0.47/0.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
