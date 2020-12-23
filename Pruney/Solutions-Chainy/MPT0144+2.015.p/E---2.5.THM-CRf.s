%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:18 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   30 (  73 expanded)
%              Number of clauses        :   15 (  30 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  73 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t60_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t59_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19] : k2_enumset1(X16,X17,X18,X19) = k2_xboole_0(k2_tarski(X16,X17),k2_tarski(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_8,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_xboole_0(k1_tarski(X11),k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(assume_negation,[status(cth)],[t60_enumset1])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24] : k3_enumset1(X20,X21,X22,X23,X24) = k2_xboole_0(k1_tarski(X20),k2_enumset1(X21,X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_14,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

fof(c_0_17,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k5_enumset1(X44,X45,X46,X47,X48,X49,X50) = k2_xboole_0(k2_enumset1(X44,X45,X46,X47),k1_enumset1(X48,X49,X50)) ),
    inference(variable_rename,[status(thm)],[t59_enumset1])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)))),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_12]),c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))))))) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.26  % Computer   : n015.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 15:29:38 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.08/0.26  # Version: 2.5pre002
% 0.08/0.26  # No SInE strategy applied
% 0.08/0.26  # Trying AutoSched0 for 299 seconds
% 0.08/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.08/0.29  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.08/0.29  #
% 0.08/0.29  # Preprocessing time       : 0.025 s
% 0.08/0.29  # Presaturation interreduction done
% 0.08/0.29  
% 0.08/0.29  # Proof found!
% 0.08/0.29  # SZS status Theorem
% 0.08/0.29  # SZS output start CNFRefutation
% 0.08/0.29  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 0.08/0.29  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.08/0.29  fof(t60_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.08/0.29  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.08/0.29  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.08/0.29  fof(t59_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_enumset1)).
% 0.08/0.29  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.08/0.29  fof(c_0_7, plain, ![X16, X17, X18, X19]:k2_enumset1(X16,X17,X18,X19)=k2_xboole_0(k2_tarski(X16,X17),k2_tarski(X18,X19)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.08/0.29  fof(c_0_8, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_xboole_0(k1_tarski(X11),k1_tarski(X12)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.08/0.29  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(assume_negation,[status(cth)],[t60_enumset1])).
% 0.08/0.29  fof(c_0_10, plain, ![X20, X21, X22, X23, X24]:k3_enumset1(X20,X21,X22,X23,X24)=k2_xboole_0(k1_tarski(X20),k2_enumset1(X21,X22,X23,X24)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.08/0.29  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.08/0.29  cnf(c_0_12, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.29  fof(c_0_13, plain, ![X13, X14, X15]:k1_enumset1(X13,X14,X15)=k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.08/0.29  fof(c_0_14, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.08/0.29  cnf(c_0_15, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.29  cnf(c_0_16, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.08/0.29  fof(c_0_17, plain, ![X44, X45, X46, X47, X48, X49, X50]:k5_enumset1(X44,X45,X46,X47,X48,X49,X50)=k2_xboole_0(k2_enumset1(X44,X45,X46,X47),k1_enumset1(X48,X49,X50)), inference(variable_rename,[status(thm)],[t59_enumset1])).
% 0.08/0.29  cnf(c_0_18, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.29  cnf(c_0_19, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.08/0.29  cnf(c_0_20, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.08/0.29  fof(c_0_21, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.08/0.29  cnf(c_0_22, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.08/0.29  cnf(c_0_23, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_18, c_0_12])).
% 0.08/0.29  cnf(c_0_24, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)))),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_12]), c_0_20])).
% 0.08/0.29  cnf(c_0_25, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.08/0.29  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_16])).
% 0.08/0.29  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))))))!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.08/0.29  cnf(c_0_28, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.08/0.29  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), ['proof']).
% 0.08/0.29  # SZS output end CNFRefutation
% 0.08/0.29  # Proof object total steps             : 30
% 0.08/0.29  # Proof object clause steps            : 15
% 0.08/0.29  # Proof object formula steps           : 15
% 0.08/0.29  # Proof object conjectures             : 7
% 0.08/0.29  # Proof object clause conjectures      : 4
% 0.08/0.29  # Proof object formula conjectures     : 3
% 0.08/0.29  # Proof object initial clauses used    : 7
% 0.08/0.29  # Proof object initial formulas used   : 7
% 0.08/0.29  # Proof object generating inferences   : 0
% 0.08/0.29  # Proof object simplifying inferences  : 19
% 0.08/0.29  # Training examples: 0 positive, 0 negative
% 0.08/0.29  # Parsed axioms                        : 10
% 0.08/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.29  # Initial clauses                      : 10
% 0.08/0.29  # Removed in clause preprocessing      : 5
% 0.08/0.29  # Initial clauses in saturation        : 5
% 0.08/0.29  # Processed clauses                    : 4
% 0.08/0.29  # ...of these trivial                  : 1
% 0.08/0.29  # ...subsumed                          : 0
% 0.08/0.29  # ...remaining for further processing  : 3
% 0.08/0.29  # Other redundant clauses eliminated   : 0
% 0.08/0.29  # Clauses deleted for lack of memory   : 0
% 0.08/0.29  # Backward-subsumed                    : 0
% 0.08/0.29  # Backward-rewritten                   : 1
% 0.08/0.29  # Generated clauses                    : 0
% 0.08/0.29  # ...of the previous two non-trivial   : 0
% 0.08/0.29  # Contextual simplify-reflections      : 0
% 0.08/0.29  # Paramodulations                      : 0
% 0.08/0.29  # Factorizations                       : 0
% 0.08/0.29  # Equation resolutions                 : 0
% 0.08/0.29  # Propositional unsat checks           : 0
% 0.08/0.29  #    Propositional check models        : 0
% 0.08/0.29  #    Propositional check unsatisfiable : 0
% 0.08/0.29  #    Propositional clauses             : 0
% 0.08/0.29  #    Propositional clauses after purity: 0
% 0.08/0.29  #    Propositional unsat core size     : 0
% 0.08/0.29  #    Propositional preprocessing time  : 0.000
% 0.08/0.29  #    Propositional encoding time       : 0.000
% 0.08/0.29  #    Propositional solver time         : 0.000
% 0.08/0.29  #    Success case prop preproc time    : 0.000
% 0.08/0.29  #    Success case prop encoding time   : 0.000
% 0.08/0.29  #    Success case prop solver time     : 0.000
% 0.08/0.29  # Current number of processed clauses  : 2
% 0.08/0.29  #    Positive orientable unit clauses  : 2
% 0.08/0.29  #    Positive unorientable unit clauses: 0
% 0.08/0.29  #    Negative unit clauses             : 0
% 0.08/0.29  #    Non-unit-clauses                  : 0
% 0.08/0.29  # Current number of unprocessed clauses: 1
% 0.08/0.29  # ...number of literals in the above   : 1
% 0.08/0.29  # Current number of archived formulas  : 0
% 0.08/0.29  # Current number of archived clauses   : 6
% 0.08/0.29  # Clause-clause subsumption calls (NU) : 0
% 0.08/0.29  # Rec. Clause-clause subsumption calls : 0
% 0.08/0.29  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.29  # Unit Clause-clause subsumption calls : 0
% 0.08/0.29  # Rewrite failures with RHS unbound    : 0
% 0.08/0.29  # BW rewrite match attempts            : 4
% 0.08/0.29  # BW rewrite match successes           : 1
% 0.08/0.29  # Condensation attempts                : 0
% 0.08/0.29  # Condensation successes               : 0
% 0.08/0.29  # Termbank termtop insertions          : 836
% 0.08/0.29  
% 0.08/0.29  # -------------------------------------------------
% 0.08/0.29  # User time                : 0.024 s
% 0.08/0.29  # System time              : 0.004 s
% 0.08/0.29  # Total time               : 0.027 s
% 0.08/0.29  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
