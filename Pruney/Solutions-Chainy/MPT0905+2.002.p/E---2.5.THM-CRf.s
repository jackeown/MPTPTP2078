%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:04 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 112 expanded)
%              Number of clauses        :   13 (  43 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 ( 118 expanded)
%              Number of equality atoms :   31 ( 117 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4)) = k1_tarski(k4_mcart_1(X1,X2,X3,X4)) ),
    inference(assume_negation,[status(cth)],[t65_mcart_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20] : k4_mcart_1(X17,X18,X19,X20) = k4_tarski(k3_mcart_1(X17,X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24] : k4_zfmisc_1(X21,X22,X23,X24) = k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] : k3_zfmisc_1(X14,X15,X16) = k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,negated_conjecture,(
    k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_16,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] :
      ( k2_zfmisc_1(k1_tarski(X8),k2_tarski(X9,X10)) = k2_tarski(k4_tarski(X8,X9),k4_tarski(X8,X10))
      & k2_zfmisc_1(k2_tarski(X8,X9),k1_tarski(X10)) = k2_tarski(k4_tarski(X8,X10),k4_tarski(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_21,negated_conjecture,
    ( k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)) != k1_enumset1(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_25])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)) = k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n011.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 14:14:11 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  # Version: 2.5pre002
% 0.15/0.30  # No SInE strategy applied
% 0.15/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.32  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.15/0.32  # and selection function SelectNewComplexAHP.
% 0.15/0.32  #
% 0.15/0.32  # Preprocessing time       : 0.021 s
% 0.15/0.32  # Presaturation interreduction done
% 0.15/0.32  
% 0.15/0.32  # Proof found!
% 0.15/0.32  # SZS status Theorem
% 0.15/0.32  # SZS output start CNFRefutation
% 0.15/0.32  fof(t65_mcart_1, conjecture, ![X1, X2, X3, X4]:k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4))=k1_tarski(k4_mcart_1(X1,X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_mcart_1)).
% 0.15/0.32  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.15/0.32  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.15/0.32  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.15/0.32  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.15/0.32  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.32  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.15/0.32  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:k4_zfmisc_1(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3),k1_tarski(X4))=k1_tarski(k4_mcart_1(X1,X2,X3,X4))), inference(assume_negation,[status(cth)],[t65_mcart_1])).
% 0.15/0.32  fof(c_0_9, plain, ![X17, X18, X19, X20]:k4_mcart_1(X17,X18,X19,X20)=k4_tarski(k3_mcart_1(X17,X18,X19),X20), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.15/0.32  fof(c_0_10, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.15/0.32  fof(c_0_11, plain, ![X21, X22, X23, X24]:k4_zfmisc_1(X21,X22,X23,X24)=k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.15/0.32  fof(c_0_12, plain, ![X14, X15, X16]:k3_zfmisc_1(X14,X15,X16)=k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.15/0.32  fof(c_0_13, negated_conjecture, k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.15/0.32  fof(c_0_14, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.32  fof(c_0_15, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.32  cnf(c_0_16, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.32  cnf(c_0_17, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.32  cnf(c_0_19, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.32  fof(c_0_20, plain, ![X8, X9, X10]:(k2_zfmisc_1(k1_tarski(X8),k2_tarski(X9,X10))=k2_tarski(k4_tarski(X8,X9),k4_tarski(X8,X10))&k2_zfmisc_1(k2_tarski(X8,X9),k1_tarski(X10))=k2_tarski(k4_tarski(X8,X10),k4_tarski(X9,X10))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.15/0.32  cnf(c_0_21, negated_conjecture, (k4_zfmisc_1(k1_tarski(esk1_0),k1_tarski(esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.32  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.32  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.32  cnf(c_0_24, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.15/0.32  cnf(c_0_25, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.32  cnf(c_0_26, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.32  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk2_0)),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk4_0,esk4_0,esk4_0))!=k1_enumset1(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_25])).
% 0.15/0.32  cnf(c_0_28, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_23]), c_0_23]), c_0_23])).
% 0.15/0.32  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28]), c_0_28])]), ['proof']).
% 0.15/0.32  # SZS output end CNFRefutation
% 0.15/0.32  # Proof object total steps             : 30
% 0.15/0.32  # Proof object clause steps            : 13
% 0.15/0.32  # Proof object formula steps           : 17
% 0.15/0.32  # Proof object conjectures             : 6
% 0.15/0.32  # Proof object clause conjectures      : 3
% 0.15/0.32  # Proof object formula conjectures     : 3
% 0.15/0.32  # Proof object initial clauses used    : 8
% 0.15/0.32  # Proof object initial formulas used   : 8
% 0.15/0.32  # Proof object generating inferences   : 0
% 0.15/0.32  # Proof object simplifying inferences  : 24
% 0.15/0.32  # Training examples: 0 positive, 0 negative
% 0.15/0.32  # Parsed axioms                        : 8
% 0.15/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.32  # Initial clauses                      : 9
% 0.15/0.32  # Removed in clause preprocessing      : 6
% 0.15/0.32  # Initial clauses in saturation        : 3
% 0.15/0.32  # Processed clauses                    : 2
% 0.15/0.32  # ...of these trivial                  : 0
% 0.15/0.32  # ...subsumed                          : 0
% 0.15/0.32  # ...remaining for further processing  : 2
% 0.15/0.32  # Other redundant clauses eliminated   : 0
% 0.15/0.32  # Clauses deleted for lack of memory   : 0
% 0.15/0.32  # Backward-subsumed                    : 0
% 0.15/0.32  # Backward-rewritten                   : 1
% 0.15/0.32  # Generated clauses                    : 0
% 0.15/0.32  # ...of the previous two non-trivial   : 0
% 0.15/0.32  # Contextual simplify-reflections      : 0
% 0.15/0.32  # Paramodulations                      : 0
% 0.15/0.32  # Factorizations                       : 0
% 0.15/0.32  # Equation resolutions                 : 0
% 0.15/0.32  # Propositional unsat checks           : 0
% 0.15/0.32  #    Propositional check models        : 0
% 0.15/0.32  #    Propositional check unsatisfiable : 0
% 0.15/0.32  #    Propositional clauses             : 0
% 0.15/0.32  #    Propositional clauses after purity: 0
% 0.15/0.32  #    Propositional unsat core size     : 0
% 0.15/0.32  #    Propositional preprocessing time  : 0.000
% 0.15/0.32  #    Propositional encoding time       : 0.000
% 0.15/0.32  #    Propositional solver time         : 0.000
% 0.15/0.32  #    Success case prop preproc time    : 0.000
% 0.15/0.32  #    Success case prop encoding time   : 0.000
% 0.15/0.32  #    Success case prop solver time     : 0.000
% 0.15/0.32  # Current number of processed clauses  : 1
% 0.15/0.32  #    Positive orientable unit clauses  : 1
% 0.15/0.32  #    Positive unorientable unit clauses: 0
% 0.15/0.32  #    Negative unit clauses             : 0
% 0.15/0.32  #    Non-unit-clauses                  : 0
% 0.15/0.32  # Current number of unprocessed clauses: 1
% 0.15/0.32  # ...number of literals in the above   : 1
% 0.15/0.32  # Current number of archived formulas  : 0
% 0.15/0.32  # Current number of archived clauses   : 7
% 0.15/0.32  # Clause-clause subsumption calls (NU) : 0
% 0.15/0.32  # Rec. Clause-clause subsumption calls : 0
% 0.15/0.32  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.32  # Unit Clause-clause subsumption calls : 0
% 0.15/0.32  # Rewrite failures with RHS unbound    : 0
% 0.15/0.32  # BW rewrite match attempts            : 1
% 0.15/0.32  # BW rewrite match successes           : 1
% 0.15/0.32  # Condensation attempts                : 0
% 0.15/0.32  # Condensation successes               : 0
% 0.15/0.32  # Termbank termtop insertions          : 512
% 0.15/0.32  
% 0.15/0.32  # -------------------------------------------------
% 0.15/0.32  # User time                : 0.021 s
% 0.15/0.32  # System time              : 0.003 s
% 0.15/0.32  # Total time               : 0.024 s
% 0.15/0.32  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
