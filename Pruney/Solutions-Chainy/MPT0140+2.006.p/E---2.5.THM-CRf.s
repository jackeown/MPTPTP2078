%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  61 expanded)
%              Number of clauses        :   13 (  26 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  61 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(t53_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t56_enumset1])).

fof(c_0_7,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k4_enumset1(X29,X30,X31,X32,X33,X34) = k2_xboole_0(k1_enumset1(X29,X30,X31),k1_enumset1(X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t53_enumset1])).

fof(c_0_8,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_9,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28] : k2_enumset1(X25,X26,X27,X28) = k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_14,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] : k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)))),k3_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_11]),c_0_15]),c_0_15])).

cnf(c_0_20,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_11]),c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_21,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_enumset1(esk5_0,esk6_0,esk7_0))) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_11]),c_0_22]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:56:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t56_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 0.13/0.38  fof(t53_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 0.13/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.38  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(assume_negation,[status(cth)],[t56_enumset1])).
% 0.13/0.38  fof(c_0_7, plain, ![X29, X30, X31, X32, X33, X34]:k4_enumset1(X29,X30,X31,X32,X33,X34)=k2_xboole_0(k1_enumset1(X29,X30,X31),k1_enumset1(X32,X33,X34)), inference(variable_rename,[status(thm)],[t53_enumset1])).
% 0.13/0.38  fof(c_0_8, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.38  cnf(c_0_10, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_12, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X25, X26, X27, X28]:k2_enumset1(X25,X26,X27,X28)=k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X27,X28)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_17, plain, ![X13, X14, X15, X16, X17, X18, X19]:k5_enumset1(X13,X14,X15,X16,X17,X18,X19)=k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)))),k3_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k5_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_11]), c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_20, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_11]), c_0_11]), c_0_11]), c_0_11])).
% 0.13/0.38  cnf(c_0_21, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)))), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_enumset1(esk5_0,esk6_0,esk7_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k3_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0))),k1_enumset1(esk5_0,esk6_0,esk7_0)))!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_11]), c_0_22]), c_0_22])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 26
% 0.13/0.38  # Proof object clause steps            : 13
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 7
% 0.13/0.38  # Proof object clause conjectures      : 4
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 6
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 0
% 0.13/0.38  # Proof object simplifying inferences  : 15
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 9
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 5
% 0.13/0.38  # Processed clauses                    : 5
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 5
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 0
% 0.13/0.38  # ...of the previous two non-trivial   : 1
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 0
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 3
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 1
% 0.13/0.38  # ...number of literals in the above   : 1
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 6
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 885
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.026 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.029 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
