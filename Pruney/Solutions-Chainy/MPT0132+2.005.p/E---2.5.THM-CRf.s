%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 128 expanded)
%              Number of clauses        :   19 (  57 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 ( 128 expanded)
%              Number of equality atoms :   35 ( 127 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t48_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_8,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_9,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21] : k2_enumset1(X18,X19,X20,X21) = k2_xboole_0(k1_tarski(X18),k1_enumset1(X19,X20,X21)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t48_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_xboole_0(k1_tarski(X16),k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_15,plain,(
    ! [X22,X23,X24,X25,X26] : k3_enumset1(X22,X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_19,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k5_xboole_0(X11,X12),X13) = k5_xboole_0(X11,k5_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_22]),c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k3_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_17]),c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)),k5_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k3_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.37  fof(t48_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.13/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.37  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.13/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.13/0.37  fof(c_0_8, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.37  fof(c_0_9, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  fof(c_0_10, plain, ![X18, X19, X20, X21]:k2_enumset1(X18,X19,X20,X21)=k2_xboole_0(k1_tarski(X18),k1_enumset1(X19,X20,X21)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.37  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(assume_negation,[status(cth)],[t48_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_xboole_0(k1_tarski(X16),k1_tarski(X17)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X22, X23, X24, X25, X26]:k3_enumset1(X22,X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.13/0.37  cnf(c_0_16, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  fof(c_0_18, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.37  fof(c_0_19, negated_conjecture, k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  fof(c_0_23, plain, ![X11, X12, X13]:k5_xboole_0(k5_xboole_0(X11,X12),X13)=k5_xboole_0(X11,k5_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.13/0.37  cnf(c_0_27, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_22]), c_0_22])).
% 0.13/0.37  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k3_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_17]), c_0_26]), c_0_26])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_tarski(X2)))),k1_tarski(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.13/0.37  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)),k5_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k3_xboole_0(k1_enumset1(esk3_0,esk4_0,esk5_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_28]), c_0_28])).
% 0.13/0.37  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_xboole_0(k1_tarski(X2),k1_tarski(X1)),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 36
% 0.13/0.37  # Proof object clause steps            : 19
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 7
% 0.13/0.37  # Proof object clause conjectures      : 4
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 0
% 0.13/0.37  # Proof object simplifying inferences  : 24
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 8
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 4
% 0.13/0.37  # Processed clauses                    : 6
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 6
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 0
% 0.13/0.37  # ...of the previous two non-trivial   : 2
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 0
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
% 0.13/0.37  # Current number of processed clauses  : 3
% 0.13/0.37  #    Positive orientable unit clauses  : 3
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 7
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 692
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.001 s
% 0.13/0.37  # Total time               : 0.030 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
