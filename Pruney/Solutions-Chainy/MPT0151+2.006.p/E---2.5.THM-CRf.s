%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  79 expanded)
%              Number of clauses        :   17 (  34 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  79 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t67_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_8,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30,X31] : k3_enumset1(X27,X28,X29,X30,X31) = k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_10,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(assume_negation,[status(cth)],[t67_enumset1])).

fof(c_0_13,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k4_enumset1(X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

fof(c_0_16,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12) = k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] : k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k2_enumset1(X21,X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_21,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k1_tarski(X6)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)),k1_tarski(esk6_0)),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_11]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X5) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X4),X5)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_23])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))) != k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k2_xboole_0(X3,X4),X5))),X6) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:00:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.026 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.12/0.35  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.35  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.12/0.35  fof(t67_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 0.12/0.35  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.12/0.35  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.12/0.35  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.12/0.35  fof(c_0_7, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X13,X14),k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.12/0.35  fof(c_0_8, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.35  fof(c_0_9, plain, ![X27, X28, X29, X30, X31]:k3_enumset1(X27,X28,X29,X30,X31)=k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.12/0.35  cnf(c_0_10, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_11, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(assume_negation,[status(cth)],[t67_enumset1])).
% 0.12/0.35  fof(c_0_13, plain, ![X32, X33, X34, X35, X36, X37]:k4_enumset1(X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k1_tarski(X37)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.12/0.35  cnf(c_0_14, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.12/0.35  fof(c_0_16, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.35  cnf(c_0_17, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_18, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.35  fof(c_0_19, plain, ![X9, X10, X11, X12]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X9,X10),X11),X12)=k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.12/0.35  fof(c_0_20, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k2_enumset1(X21,X22,X23,X24)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_22, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k1_tarski(X5)),k1_tarski(X6))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.35  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.35  cnf(c_0_24, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.35  cnf(c_0_25, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)),k1_tarski(esk6_0)),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_11]), c_0_22])).
% 0.12/0.35  cnf(c_0_26, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X5)=k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X4),X5))), inference(spm,[status(thm)],[c_0_23, c_0_23])).
% 0.12/0.35  cnf(c_0_27, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 0.12/0.35  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)),k1_tarski(esk6_0)))),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))!=k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 0.12/0.35  cnf(c_0_29, plain, (k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k2_xboole_0(X3,X4),X5))),X6)=k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X4,X5),X6))), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.12/0.35  cnf(c_0_30, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.12/0.35  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 32
% 0.12/0.35  # Proof object clause steps            : 17
% 0.12/0.35  # Proof object formula steps           : 15
% 0.12/0.35  # Proof object conjectures             : 7
% 0.12/0.35  # Proof object clause conjectures      : 4
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 7
% 0.12/0.35  # Proof object initial formulas used   : 7
% 0.12/0.35  # Proof object generating inferences   : 2
% 0.12/0.35  # Proof object simplifying inferences  : 16
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 7
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 7
% 0.12/0.35  # Removed in clause preprocessing      : 4
% 0.12/0.35  # Initial clauses in saturation        : 3
% 0.12/0.35  # Processed clauses                    : 9
% 0.12/0.35  # ...of these trivial                  : 1
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 8
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 1
% 0.12/0.35  # Generated clauses                    : 36
% 0.12/0.35  # ...of the previous two non-trivial   : 7
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 36
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 4
% 0.12/0.35  #    Positive orientable unit clauses  : 4
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 0
% 0.12/0.35  #    Non-unit-clauses                  : 0
% 0.12/0.35  # Current number of unprocessed clauses: 4
% 0.12/0.35  # ...number of literals in the above   : 4
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 8
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 0
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 7
% 0.12/0.35  # BW rewrite match successes           : 1
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 1382
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.029 s
% 0.12/0.35  # System time              : 0.001 s
% 0.12/0.35  # Total time               : 0.031 s
% 0.12/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
