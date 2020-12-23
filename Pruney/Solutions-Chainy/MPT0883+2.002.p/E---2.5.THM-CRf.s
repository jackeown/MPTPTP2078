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
% DateTime   : Thu Dec  3 10:59:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 107 expanded)
%              Number of clauses        :   13 (  40 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 ( 127 expanded)
%              Number of equality atoms :   29 ( 126 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t40_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t43_mcart_1])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_9,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,plain,(
    ! [X23,X24,X25,X26] : k3_zfmisc_1(k2_tarski(X23,X24),k1_tarski(X25),k1_tarski(X26)) = k2_tarski(k3_mcart_1(X23,X25,X26),k3_mcart_1(X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t40_mcart_1])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] :
      ( k2_zfmisc_1(k2_xboole_0(X14,X15),X16) = k2_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X16))
      & k2_zfmisc_1(X16,k2_xboole_0(X14,X15)) = k2_xboole_0(k2_zfmisc_1(X16,X14),k2_zfmisc_1(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_20,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X3),X4)),k1_tarski(k4_tarski(k4_tarski(X2,X3),X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_15]),c_0_15]),c_0_17]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_15]),c_0_15]),c_0_17]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_21])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X4,X2),X3))) = k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_26]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t43_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5))=k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_mcart_1)).
% 0.13/0.37  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.13/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.37  fof(t40_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_mcart_1)).
% 0.13/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5))=k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5))), inference(assume_negation,[status(cth)],[t43_mcart_1])).
% 0.13/0.37  fof(c_0_8, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.13/0.37  fof(c_0_9, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.37  fof(c_0_10, plain, ![X23, X24, X25, X26]:k3_zfmisc_1(k2_tarski(X23,X24),k1_tarski(X25),k1_tarski(X26))=k2_tarski(k3_mcart_1(X23,X25,X26),k3_mcart_1(X24,X25,X26)), inference(variable_rename,[status(thm)],[t40_mcart_1])).
% 0.13/0.37  fof(c_0_11, plain, ![X17, X18, X19]:k3_mcart_1(X17,X18,X19)=k4_tarski(k4_tarski(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.37  fof(c_0_12, plain, ![X20, X21, X22]:k3_zfmisc_1(X20,X21,X22)=k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.37  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_15, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_16, plain, (k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_17, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_19, plain, ![X14, X15, X16]:(k2_zfmisc_1(k2_xboole_0(X14,X15),X16)=k2_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X16))&k2_zfmisc_1(X16,k2_xboole_0(X14,X15))=k2_xboole_0(k2_zfmisc_1(X16,X14),k2_zfmisc_1(X16,X15))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))=k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X3),X4)),k1_tarski(k4_tarski(k4_tarski(X2,X3),X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_15]), c_0_15]), c_0_17]), c_0_17]), c_0_18])).
% 0.13/0.37  cnf(c_0_23, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))),k1_tarski(esk5_0))!=k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0)),k1_tarski(k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_15]), c_0_15]), c_0_17]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_21])).
% 0.13/0.37  cnf(c_0_25, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X4,X2),X3)))=k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_zfmisc_1(k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_26]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 28
% 0.13/0.37  # Proof object clause steps            : 13
% 0.13/0.37  # Proof object formula steps           : 15
% 0.13/0.37  # Proof object conjectures             : 6
% 0.13/0.37  # Proof object clause conjectures      : 3
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 0
% 0.13/0.37  # Proof object simplifying inferences  : 26
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 9
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 5
% 0.13/0.37  # Processed clauses                    : 6
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 5
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 0
% 0.13/0.37  # ...of the previous two non-trivial   : 1
% 0.13/0.37  # Contextual simplify-reflections      : 0
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
% 0.13/0.38  # Current number of processed clauses  : 4
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 5
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 11
% 0.13/0.38  # BW rewrite match successes           : 11
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 683
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.024 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
