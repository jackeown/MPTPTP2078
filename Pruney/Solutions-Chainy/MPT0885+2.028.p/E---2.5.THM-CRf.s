%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:51 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  82 expanded)
%              Number of clauses        :   12 (  31 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  84 expanded)
%              Number of equality atoms :   28 (  83 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t41_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_mcart_1)).

fof(t132_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t45_mcart_1])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9] : k2_enumset1(X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X8,X9)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_9,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_xboole_0(k1_tarski(X10),k1_tarski(X11)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,negated_conjecture,(
    k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] : k3_mcart_1(X15,X16,X17) = k4_tarski(k4_tarski(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] : k3_zfmisc_1(X18,X19,X20) = k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] : k3_zfmisc_1(k1_tarski(X21),k2_tarski(X22,X23),k1_tarski(X24)) = k2_tarski(k3_mcart_1(X21,X22,X24),k3_mcart_1(X21,X23,X24)) ),
    inference(variable_rename,[status(thm)],[t41_mcart_1])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( k2_zfmisc_1(k2_tarski(X12,X13),X14) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X12),X14),k2_zfmisc_1(k1_tarski(X13),X14))
      & k2_zfmisc_1(X14,k2_tarski(X12,X13)) = k2_xboole_0(k2_zfmisc_1(X14,k1_tarski(X12)),k2_zfmisc_1(X14,k1_tarski(X13))) ) ),
    inference(variable_rename,[status(thm)],[t132_zfmisc_1])).

cnf(c_0_17,negated_conjecture,
    ( k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,k2_tarski(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X1,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_14]),c_0_14]),c_0_18]),c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X2),X4)),k1_tarski(k4_tarski(k4_tarski(X1,X3),X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_14]),c_0_14]),c_0_18]),c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) = k2_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X1,k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___300_C01_F1_SE_CS_SP_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t45_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_mcart_1)).
% 0.12/0.36  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.12/0.36  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.36  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.36  fof(t41_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_mcart_1)).
% 0.12/0.36  fof(t132_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_tarski(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))&k2_zfmisc_1(X3,k2_tarski(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 0.12/0.36  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))), inference(assume_negation,[status(cth)],[t45_mcart_1])).
% 0.12/0.36  fof(c_0_8, plain, ![X6, X7, X8, X9]:k2_enumset1(X6,X7,X8,X9)=k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X8,X9)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.12/0.36  fof(c_0_9, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_xboole_0(k1_tarski(X10),k1_tarski(X11)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.36  fof(c_0_10, negated_conjecture, k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.36  fof(c_0_11, plain, ![X15, X16, X17]:k3_mcart_1(X15,X16,X17)=k4_tarski(k4_tarski(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.36  fof(c_0_12, plain, ![X18, X19, X20]:k3_zfmisc_1(X18,X19,X20)=k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.36  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_14, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  fof(c_0_15, plain, ![X21, X22, X23, X24]:k3_zfmisc_1(k1_tarski(X21),k2_tarski(X22,X23),k1_tarski(X24))=k2_tarski(k3_mcart_1(X21,X22,X24),k3_mcart_1(X21,X23,X24)), inference(variable_rename,[status(thm)],[t41_mcart_1])).
% 0.12/0.36  fof(c_0_16, plain, ![X12, X13, X14]:(k2_zfmisc_1(k2_tarski(X12,X13),X14)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X12),X14),k2_zfmisc_1(k1_tarski(X13),X14))&k2_zfmisc_1(X14,k2_tarski(X12,X13))=k2_xboole_0(k2_zfmisc_1(X14,k1_tarski(X12)),k2_zfmisc_1(X14,k1_tarski(X13)))), inference(variable_rename,[status(thm)],[t132_zfmisc_1])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (k3_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk2_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk2_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_18, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_19, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.12/0.36  cnf(c_0_21, plain, (k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_22, plain, (k2_zfmisc_1(X1,k2_tarski(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X1,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)))!=k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk4_0)),k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_14]), c_0_14]), c_0_18]), c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.36  cnf(c_0_24, plain, (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))=k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X2),X4)),k1_tarski(k4_tarski(k4_tarski(X1,X3),X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_14]), c_0_14]), c_0_18]), c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_25, plain, (k2_zfmisc_1(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))=k2_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X1,k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_22, c_0_14])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_25])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 27
% 0.12/0.36  # Proof object clause steps            : 12
% 0.12/0.36  # Proof object formula steps           : 15
% 0.12/0.36  # Proof object conjectures             : 6
% 0.12/0.36  # Proof object clause conjectures      : 3
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 7
% 0.12/0.36  # Proof object initial formulas used   : 7
% 0.12/0.36  # Proof object generating inferences   : 0
% 0.12/0.36  # Proof object simplifying inferences  : 20
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 7
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 8
% 0.12/0.36  # Removed in clause preprocessing      : 4
% 0.12/0.36  # Initial clauses in saturation        : 4
% 0.12/0.36  # Processed clauses                    : 5
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 5
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 1
% 0.12/0.36  # Generated clauses                    : 11
% 0.12/0.36  # ...of the previous two non-trivial   : 5
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 11
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 4
% 0.12/0.36  #    Positive orientable unit clauses  : 2
% 0.12/0.36  #    Positive unorientable unit clauses: 2
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 0
% 0.12/0.36  # Current number of unprocessed clauses: 4
% 0.12/0.36  # ...number of literals in the above   : 4
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 5
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 944
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.024 s
% 0.12/0.36  # System time              : 0.006 s
% 0.12/0.36  # Total time               : 0.030 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
