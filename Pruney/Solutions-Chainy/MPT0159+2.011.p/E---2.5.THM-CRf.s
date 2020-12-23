%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 195 expanded)
%              Number of clauses        :   25 (  82 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 195 expanded)
%              Number of equality atoms :   45 ( 194 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t59_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(assume_negation,[status(cth)],[t75_enumset1])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] : k5_enumset1(X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k2_tarski(X14,X15),k3_enumset1(X16,X17,X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(k5_xboole_0(X12,X13),k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) = k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k2_enumset1(X47,X48,X49,X50)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

fof(c_0_14,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_16,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34] : k5_enumset1(X28,X29,X30,X31,X32,X33,X34) = k2_xboole_0(k2_enumset1(X28,X29,X30,X31),k1_enumset1(X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t59_enumset1])).

fof(c_0_19,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] : k5_xboole_0(k5_xboole_0(X9,X10),X11) = k5_xboole_0(X9,k5_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_23,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X35,X36,X37,X38,X39,X40,X41,X42) = k2_xboole_0(k1_enumset1(X35,X36,X37),k3_enumset1(X38,X39,X40,X41,X42)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

cnf(c_0_24,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_17])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] : k5_enumset1(X21,X22,X23,X24,X25,X26,X27) = k2_xboole_0(k1_enumset1(X21,X22,X23),k2_enumset1(X24,X25,X26,X27)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_21]),c_0_17]),c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27]),c_0_21]),c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk1_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))) != k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)))) = k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_29]),c_0_34]),c_0_29])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) = k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_27]),c_0_21]),c_0_21]),c_0_17]),c_0_25])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk6_0,esk7_0) != k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_29]),c_0_40]),c_0_29]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0) != k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7) = k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t75_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 0.13/0.37  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.37  fof(t65_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t59_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.37  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 0.13/0.37  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(assume_negation,[status(cth)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_11, plain, ![X14, X15, X16, X17, X18, X19, X20]:k5_enumset1(X14,X15,X16,X17,X18,X19,X20)=k2_xboole_0(k2_tarski(X14,X15),k3_enumset1(X16,X17,X18,X19,X20)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.13/0.37  fof(c_0_12, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(k5_xboole_0(X12,X13),k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.37  fof(c_0_13, plain, ![X43, X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)=k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k2_enumset1(X47,X48,X49,X50)), inference(variable_rename,[status(thm)],[t65_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_15, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.37  cnf(c_0_16, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_18, plain, ![X28, X29, X30, X31, X32, X33, X34]:k5_enumset1(X28,X29,X30,X31,X32,X33,X34)=k2_xboole_0(k2_enumset1(X28,X29,X30,X31),k1_enumset1(X32,X33,X34)), inference(variable_rename,[status(thm)],[t59_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  cnf(c_0_20, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_22, plain, ![X9, X10, X11]:k5_xboole_0(k5_xboole_0(X9,X10),X11)=k5_xboole_0(X9,k5_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.37  fof(c_0_23, plain, ![X35, X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X35,X36,X37,X38,X39,X40,X41,X42)=k2_xboole_0(k1_enumset1(X35,X36,X37),k3_enumset1(X38,X39,X40,X41,X42)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_25, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_28, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_17])).
% 0.13/0.37  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  fof(c_0_30, plain, ![X21, X22, X23, X24, X25, X26, X27]:k5_enumset1(X21,X22,X23,X24,X25,X26,X27)=k2_xboole_0(k1_enumset1(X21,X22,X23),k2_enumset1(X24,X25,X26,X27)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.13/0.37  cnf(c_0_31, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k5_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)))=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_21]), c_0_17]), c_0_25])).
% 0.13/0.37  cnf(c_0_34, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k5_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_36, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27]), c_0_21]), c_0_17])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k5_xboole_0(k2_tarski(esk1_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k3_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))))!=k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_32, c_0_29])).
% 0.13/0.37  cnf(c_0_38, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))))=k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_29]), c_0_34]), c_0_29])).
% 0.13/0.37  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)))=k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_27]), c_0_21]), c_0_21]), c_0_17]), c_0_25])).
% 0.13/0.37  cnf(c_0_40, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_36, c_0_29])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk6_0,esk7_0)!=k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.37  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7)=k6_enumset1(X1,X2,X3,X4,X5,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_29]), c_0_40]), c_0_29]), c_0_38])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k6_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X4,X5,X6,X7)=k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 46
% 0.13/0.37  # Proof object clause steps            : 25
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 9
% 0.13/0.37  # Proof object clause conjectures      : 6
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 1
% 0.13/0.37  # Proof object simplifying inferences  : 32
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 10
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 6
% 0.13/0.37  # Processed clauses                    : 16
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 16
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 12
% 0.13/0.37  # ...of the previous two non-trivial   : 6
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 12
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 7
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 2
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 2
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 13
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 25
% 0.13/0.37  # BW rewrite match successes           : 7
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1003
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.030 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
