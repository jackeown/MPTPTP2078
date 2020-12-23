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
% DateTime   : Thu Dec  3 10:35:20 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 124 expanded)
%              Number of clauses        :   17 (  49 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 ( 124 expanded)
%              Number of equality atoms :   33 ( 123 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t61_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_8,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_9,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_xboole_0(k1_tarski(X11),k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] : k2_enumset1(X16,X17,X18,X19) = k2_xboole_0(k1_enumset1(X16,X17,X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23,X24] : k3_enumset1(X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(assume_negation,[status(cth)],[t61_enumset1])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k4_enumset1(X25,X26,X27,X28,X29,X30) = k2_xboole_0(k3_enumset1(X25,X26,X27,X28,X29),k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k5_enumset1(X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X31,X32,X33,X34,X35),k2_tarski(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

cnf(c_0_24,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)),k1_tarski(esk4_0)),k1_tarski(esk5_0)),k1_tarski(esk6_0)),k1_tarski(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_12]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))))))) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 13:55:23 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.026 s
% 0.18/0.35  # Presaturation interreduction done
% 0.18/0.35  
% 0.18/0.35  # Proof found!
% 0.18/0.35  # SZS status Theorem
% 0.18/0.35  # SZS output start CNFRefutation
% 0.18/0.35  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.18/0.35  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.18/0.35  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.18/0.35  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.18/0.35  fof(t61_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 0.18/0.35  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.18/0.35  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.18/0.35  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.35  fof(c_0_8, plain, ![X13, X14, X15]:k1_enumset1(X13,X14,X15)=k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.18/0.35  fof(c_0_9, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_xboole_0(k1_tarski(X11),k1_tarski(X12)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.18/0.35  fof(c_0_10, plain, ![X16, X17, X18, X19]:k2_enumset1(X16,X17,X18,X19)=k2_xboole_0(k1_enumset1(X16,X17,X18),k1_tarski(X19)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.18/0.35  cnf(c_0_11, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.35  cnf(c_0_12, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.35  fof(c_0_13, plain, ![X20, X21, X22, X23, X24]:k3_enumset1(X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.18/0.35  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.35  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(assume_negation,[status(cth)],[t61_enumset1])).
% 0.18/0.35  fof(c_0_17, plain, ![X25, X26, X27, X28, X29, X30]:k4_enumset1(X25,X26,X27,X28,X29,X30)=k2_xboole_0(k3_enumset1(X25,X26,X27,X28,X29),k1_tarski(X30)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.18/0.35  cnf(c_0_18, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.35  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.35  fof(c_0_20, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.18/0.35  cnf(c_0_21, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.35  cnf(c_0_22, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.35  fof(c_0_23, plain, ![X31, X32, X33, X34, X35, X36, X37]:k5_enumset1(X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X31,X32,X33,X34,X35),k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.18/0.35  cnf(c_0_24, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.35  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.35  fof(c_0_26, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.35  cnf(c_0_27, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.35  cnf(c_0_28, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k1_tarski(esk3_0)),k1_tarski(esk4_0)),k1_tarski(esk5_0)),k1_tarski(esk6_0)),k1_tarski(esk7_0))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.35  cnf(c_0_29, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.35  cnf(c_0_30, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_12]), c_0_22])).
% 0.18/0.35  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))))))!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.18/0.35  cnf(c_0_32, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.18/0.35  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.18/0.35  # SZS output end CNFRefutation
% 0.18/0.35  # Proof object total steps             : 34
% 0.18/0.35  # Proof object clause steps            : 17
% 0.18/0.35  # Proof object formula steps           : 17
% 0.18/0.35  # Proof object conjectures             : 7
% 0.18/0.35  # Proof object clause conjectures      : 4
% 0.18/0.35  # Proof object formula conjectures     : 3
% 0.18/0.35  # Proof object initial clauses used    : 8
% 0.18/0.35  # Proof object initial formulas used   : 8
% 0.18/0.35  # Proof object generating inferences   : 0
% 0.18/0.35  # Proof object simplifying inferences  : 34
% 0.18/0.35  # Training examples: 0 positive, 0 negative
% 0.18/0.35  # Parsed axioms                        : 8
% 0.18/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.35  # Initial clauses                      : 8
% 0.18/0.35  # Removed in clause preprocessing      : 5
% 0.18/0.35  # Initial clauses in saturation        : 3
% 0.18/0.35  # Processed clauses                    : 3
% 0.18/0.35  # ...of these trivial                  : 0
% 0.18/0.35  # ...subsumed                          : 0
% 0.18/0.35  # ...remaining for further processing  : 3
% 0.18/0.35  # Other redundant clauses eliminated   : 0
% 0.18/0.35  # Clauses deleted for lack of memory   : 0
% 0.18/0.35  # Backward-subsumed                    : 0
% 0.18/0.35  # Backward-rewritten                   : 1
% 0.18/0.35  # Generated clauses                    : 0
% 0.18/0.35  # ...of the previous two non-trivial   : 0
% 0.18/0.35  # Contextual simplify-reflections      : 0
% 0.18/0.35  # Paramodulations                      : 0
% 0.18/0.35  # Factorizations                       : 0
% 0.18/0.35  # Equation resolutions                 : 0
% 0.18/0.35  # Propositional unsat checks           : 0
% 0.18/0.35  #    Propositional check models        : 0
% 0.18/0.35  #    Propositional check unsatisfiable : 0
% 0.18/0.35  #    Propositional clauses             : 0
% 0.18/0.35  #    Propositional clauses after purity: 0
% 0.18/0.35  #    Propositional unsat core size     : 0
% 0.18/0.35  #    Propositional preprocessing time  : 0.000
% 0.18/0.35  #    Propositional encoding time       : 0.000
% 0.18/0.35  #    Propositional solver time         : 0.000
% 0.18/0.35  #    Success case prop preproc time    : 0.000
% 0.18/0.35  #    Success case prop encoding time   : 0.000
% 0.18/0.35  #    Success case prop solver time     : 0.000
% 0.18/0.35  # Current number of processed clauses  : 2
% 0.18/0.35  #    Positive orientable unit clauses  : 2
% 0.18/0.35  #    Positive unorientable unit clauses: 0
% 0.18/0.35  #    Negative unit clauses             : 0
% 0.18/0.35  #    Non-unit-clauses                  : 0
% 0.18/0.35  # Current number of unprocessed clauses: 0
% 0.18/0.35  # ...number of literals in the above   : 0
% 0.18/0.35  # Current number of archived formulas  : 0
% 0.18/0.35  # Current number of archived clauses   : 6
% 0.18/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.35  # Unit Clause-clause subsumption calls : 0
% 0.18/0.35  # Rewrite failures with RHS unbound    : 0
% 0.18/0.35  # BW rewrite match attempts            : 4
% 0.18/0.35  # BW rewrite match successes           : 1
% 0.18/0.35  # Condensation attempts                : 0
% 0.18/0.35  # Condensation successes               : 0
% 0.18/0.35  # Termbank termtop insertions          : 672
% 0.18/0.35  
% 0.18/0.35  # -------------------------------------------------
% 0.18/0.35  # User time                : 0.028 s
% 0.18/0.35  # System time              : 0.002 s
% 0.18/0.35  # Total time               : 0.030 s
% 0.18/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
