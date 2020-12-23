%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 496 expanded)
%              Number of clauses        :   22 ( 203 expanded)
%              Number of leaves         :    8 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 ( 496 expanded)
%              Number of equality atoms :   38 ( 495 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t58_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(c_0_8,plain,(
    ! [X20,X21,X22] : k1_enumset1(X20,X21,X22) = k2_xboole_0(k1_tarski(X20),k2_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_9,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t58_enumset1])).

fof(c_0_14,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k5_enumset1(X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k1_tarski(X31),k4_enumset1(X32,X33,X34,X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30] : k2_enumset1(X27,X28,X29,X30) = k2_xboole_0(k1_enumset1(X27,X28,X29),k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_19,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_12]),c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] : k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_25,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_12]),c_0_17]),c_0_17]),c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_12]),c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k1_tarski(esk5_0))),k1_tarski(esk4_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_12]),c_0_17]),c_0_17]),c_0_22]),c_0_26])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_12]),c_0_17]),c_0_22]),c_0_22]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k2_tarski(esk2_0,esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k1_tarski(esk5_0))),k1_tarski(esk4_0))),k2_tarski(esk2_0,esk3_0))),k1_tarski(esk1_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_tarski(X2,X3))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(X5,k2_tarski(X3,X4))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k2_tarski(X3,X4))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k2_tarski(esk4_0,esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k2_tarski(esk4_0,esk5_0))),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X5),k4_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:04:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.026 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.36  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.36  fof(t58_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 0.20/0.36  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 0.20/0.36  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.20/0.36  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.36  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 0.20/0.36  fof(c_0_8, plain, ![X20, X21, X22]:k1_enumset1(X20,X21,X22)=k2_xboole_0(k1_tarski(X20),k2_tarski(X21,X22)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.36  fof(c_0_9, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.36  fof(c_0_10, plain, ![X23, X24, X25, X26]:k2_enumset1(X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.36  cnf(c_0_11, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(assume_negation,[status(cth)],[t58_enumset1])).
% 0.20/0.36  fof(c_0_14, plain, ![X31, X32, X33, X34, X35, X36, X37]:k5_enumset1(X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k1_tarski(X31),k4_enumset1(X32,X33,X34,X35,X36,X37)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.20/0.36  fof(c_0_15, plain, ![X27, X28, X29, X30]:k2_enumset1(X27,X28,X29,X30)=k2_xboole_0(k1_enumset1(X27,X28,X29),k1_tarski(X30)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.20/0.36  cnf(c_0_16, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.36  cnf(c_0_17, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.36  fof(c_0_18, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.36  fof(c_0_19, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.36  cnf(c_0_20, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_21, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.36  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_12]), c_0_17])).
% 0.20/0.36  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.36  fof(c_0_24, plain, ![X13, X14, X15, X16, X17, X18, X19]:k5_enumset1(X13,X14,X15,X16,X17,X18,X19)=k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.20/0.36  cnf(c_0_25, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.36  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_20, c_0_12])).
% 0.20/0.36  cnf(c_0_27, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_12]), c_0_17]), c_0_17]), c_0_22])).
% 0.20/0.36  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_12]), c_0_12]), c_0_12]), c_0_12])).
% 0.20/0.36  cnf(c_0_29, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.36  cnf(c_0_30, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k1_tarski(esk5_0))),k1_tarski(esk4_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_12]), c_0_17]), c_0_17]), c_0_22]), c_0_26])).
% 0.20/0.36  cnf(c_0_31, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.36  cnf(c_0_32, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1))),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k1_tarski(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_12]), c_0_17]), c_0_22]), c_0_22]), c_0_26])).
% 0.20/0.36  cnf(c_0_33, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k2_tarski(esk2_0,esk3_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk4_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k1_tarski(esk5_0))),k1_tarski(esk4_0))),k2_tarski(esk2_0,esk3_0))),k1_tarski(esk1_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.20/0.36  cnf(c_0_34, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_tarski(X2,X3))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(X5,k2_tarski(X3,X4))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_28]), c_0_28]), c_0_28])).
% 0.20/0.36  cnf(c_0_35, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k2_tarski(X6,X7),k1_tarski(X5))),k2_tarski(X3,X4))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_28]), c_0_28])).
% 0.20/0.36  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k5_xboole_0(k2_tarski(esk4_0,esk5_0),k4_xboole_0(k2_tarski(esk6_0,esk7_0),k2_tarski(esk4_0,esk5_0))),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 0.20/0.36  cnf(c_0_37, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k2_tarski(X4,X5),k4_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.36  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 39
% 0.20/0.36  # Proof object clause steps            : 22
% 0.20/0.36  # Proof object formula steps           : 17
% 0.20/0.36  # Proof object conjectures             : 8
% 0.20/0.36  # Proof object clause conjectures      : 5
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 8
% 0.20/0.36  # Proof object initial formulas used   : 8
% 0.20/0.36  # Proof object generating inferences   : 1
% 0.20/0.36  # Proof object simplifying inferences  : 34
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 8
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 8
% 0.20/0.36  # Removed in clause preprocessing      : 4
% 0.20/0.36  # Initial clauses in saturation        : 4
% 0.20/0.37  # Processed clauses                    : 10
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 10
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 7
% 0.20/0.37  # ...of the previous two non-trivial   : 4
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 7
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 4
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 0
% 0.20/0.37  # Current number of unprocessed clauses: 2
% 0.20/0.37  # ...number of literals in the above   : 2
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 10
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 20
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1386
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.030 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
