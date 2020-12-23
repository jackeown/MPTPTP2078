%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 497 expanded)
%              Number of clauses        :   26 ( 212 expanded)
%              Number of leaves         :   10 ( 142 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 ( 497 expanded)
%              Number of equality atoms :   46 ( 496 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(t127_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t129_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(t131_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(assume_negation,[status(cth)],[t134_enumset1])).

fof(c_0_11,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30,X31] : k7_enumset1(X23,X24,X25,X26,X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X23),k6_enumset1(X24,X25,X26,X27,X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t127_enumset1])).

fof(c_0_12,plain,(
    ! [X50] : k2_tarski(X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X51,X52] : k1_enumset1(X51,X51,X52) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_16,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40] : k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40) = k2_xboole_0(k1_enumset1(X32,X33,X34),k4_enumset1(X35,X36,X37,X38,X39,X40)) ),
    inference(variable_rename,[status(thm)],[t129_enumset1])).

fof(c_0_25,plain,(
    ! [X53,X54,X55,X56,X57,X58] : k5_enumset1(X53,X53,X54,X55,X56,X57,X58) = k4_enumset1(X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_26,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0))) != k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k1_enumset1(esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19]),c_0_22])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_19])).

cnf(c_0_28,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22] : k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49] : k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49) = k2_xboole_0(k3_enumset1(X41,X42,X43,X44,X45),k2_enumset1(X46,X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t131_enumset1])).

cnf(c_0_32,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk9_0,esk9_0,esk9_0),k4_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk9_0,esk9_0))) != k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_29]),c_0_22])).

cnf(c_0_34,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk9_0,esk1_0,esk2_0),k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk1_0,esk2_0))) != k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_19]),c_0_22])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk9_0,esk1_0,esk2_0),k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk1_0,esk2_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k2_enumset1(X6,X7,X8,X9),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k3_enumset1(esk8_0,esk9_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k3_enumset1(X6,X7,X8,X9,X1),k2_enumset1(X2,X3,X4,X5))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:38:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t134_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.12/0.37  fof(t127_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.12/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.37  fof(t129_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_enumset1)).
% 0.12/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.37  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 0.12/0.37  fof(t131_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_enumset1)).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(assume_negation,[status(cth)],[t134_enumset1])).
% 0.12/0.37  fof(c_0_11, plain, ![X23, X24, X25, X26, X27, X28, X29, X30, X31]:k7_enumset1(X23,X24,X25,X26,X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X23),k6_enumset1(X24,X25,X26,X27,X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t127_enumset1])).
% 0.12/0.37  fof(c_0_12, plain, ![X50]:k2_tarski(X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_13, plain, ![X51, X52]:k1_enumset1(X51,X51,X52)=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_14, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(X12,k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.37  cnf(c_0_16, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_tarski(X1),k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_20, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k2_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.37  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_24, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40]:k7_enumset1(X32,X33,X34,X35,X36,X37,X38,X39,X40)=k2_xboole_0(k1_enumset1(X32,X33,X34),k4_enumset1(X35,X36,X37,X38,X39,X40)), inference(variable_rename,[status(thm)],[t129_enumset1])).
% 0.12/0.37  fof(c_0_25, plain, ![X53, X54, X55, X56, X57, X58]:k5_enumset1(X53,X53,X54,X55,X56,X57,X58)=k4_enumset1(X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))!=k5_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k4_xboole_0(k1_enumset1(esk9_0,esk9_0,esk9_0),k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19]), c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_28, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  fof(c_0_30, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22]:k7_enumset1(X14,X15,X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.12/0.37  fof(c_0_31, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49]:k7_enumset1(X41,X42,X43,X44,X45,X46,X47,X48,X49)=k2_xboole_0(k3_enumset1(X41,X42,X43,X44,X45),k2_enumset1(X46,X47,X48,X49)), inference(variable_rename,[status(thm)],[t131_enumset1])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k5_xboole_0(k1_enumset1(esk9_0,esk9_0,esk9_0),k4_xboole_0(k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk9_0,esk9_0)))!=k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_33, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_29]), c_0_22])).
% 0.12/0.37  cnf(c_0_34, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_35, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k1_enumset1(esk9_0,esk1_0,esk2_0),k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk1_0,esk2_0)))!=k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k6_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_37, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_19]), c_0_22])).
% 0.12/0.37  cnf(c_0_38, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_22])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (k5_xboole_0(k1_enumset1(esk9_0,esk1_0,esk2_0),k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_enumset1(esk9_0,esk1_0,esk2_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.37  cnf(c_0_40, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.12/0.37  cnf(c_0_41, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k3_enumset1(X1,X2,X3,X4,X5)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk9_0,esk1_0,esk2_0,esk3_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  cnf(c_0_43, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k2_enumset1(X6,X7,X8,X9),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_enumset1(X6,X7,X8,X9)))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k4_xboole_0(k3_enumset1(esk8_0,esk9_0,esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.37  cnf(c_0_45, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X6,X7,X8,X9),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k3_enumset1(X6,X7,X8,X9,X1),k2_enumset1(X2,X3,X4,X5)))), inference(spm,[status(thm)],[c_0_43, c_0_43])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45]), c_0_45])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 47
% 0.12/0.37  # Proof object clause steps            : 26
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 11
% 0.12/0.37  # Proof object clause conjectures      : 8
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 4
% 0.12/0.37  # Proof object simplifying inferences  : 25
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 5
% 0.12/0.37  # Initial clauses in saturation        : 5
% 0.12/0.37  # Processed clauses                    : 22
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 19
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 7
% 0.12/0.37  # Generated clauses                    : 41
% 0.12/0.37  # ...of the previous two non-trivial   : 33
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 41
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 7
% 0.12/0.37  #    Positive orientable unit clauses  : 3
% 0.12/0.37  #    Positive unorientable unit clauses: 4
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 0
% 0.12/0.37  # Current number of unprocessed clauses: 16
% 0.12/0.37  # ...number of literals in the above   : 16
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 17
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 30
% 0.12/0.37  # BW rewrite match successes           : 30
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1579
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.001 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
