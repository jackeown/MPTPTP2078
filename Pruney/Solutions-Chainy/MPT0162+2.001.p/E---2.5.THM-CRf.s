%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 (  71 expanded)
%              Number of clauses        :   20 (  30 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  71 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t78_enumset1,conjecture,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t49_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t78_enumset1])).

fof(c_0_12,plain,(
    ! [X67,X68,X69,X70,X71] : k3_enumset1(X67,X68,X69,X70,X71) = k2_xboole_0(k1_enumset1(X67,X68,X69),k2_tarski(X70,X71)) ),
    inference(variable_rename,[status(thm)],[t49_enumset1])).

fof(c_0_13,plain,(
    ! [X72,X73] : k1_enumset1(X72,X72,X73) = k2_tarski(X72,X73) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X59,X60] : k2_xboole_0(X59,X60) = k5_xboole_0(X59,k4_xboole_0(X60,X59)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X25,X24)) = k3_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_22,plain,(
    ! [X15] : k3_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_23,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_24,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X4,X5),k3_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

fof(c_0_27,plain,(
    ! [X61,X62,X63] : k1_enumset1(X61,X62,X63) = k2_xboole_0(k1_tarski(X61),k2_tarski(X62,X63)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_28,plain,(
    ! [X74] : k1_enumset1(X74,X74,X74) = k1_tarski(X74) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k3_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0)))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k3_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3)))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:44:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t78_enumset1, conjecture, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.13/0.39  fof(t49_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.39  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.13/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.13/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.39  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.13/0.39  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.13/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t78_enumset1])).
% 0.13/0.39  fof(c_0_12, plain, ![X67, X68, X69, X70, X71]:k3_enumset1(X67,X68,X69,X70,X71)=k2_xboole_0(k1_enumset1(X67,X68,X69),k2_tarski(X70,X71)), inference(variable_rename,[status(thm)],[t49_enumset1])).
% 0.13/0.39  fof(c_0_13, plain, ![X72, X73]:k1_enumset1(X72,X72,X73)=k2_tarski(X72,X73), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_14, plain, ![X59, X60]:k2_xboole_0(X59,X60)=k5_xboole_0(X59,k4_xboole_0(X60,X59)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.39  fof(c_0_15, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.39  fof(c_0_16, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.39  cnf(c_0_17, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_21, plain, ![X23, X24, X25]:k5_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X25,X24))=k3_xboole_0(k5_xboole_0(X23,X25),X24), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.13/0.39  fof(c_0_22, plain, ![X15]:k3_xboole_0(X15,X15)=X15, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.39  fof(c_0_23, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.13/0.39  fof(c_0_24, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X4,X5),k3_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.39  fof(c_0_27, plain, ![X61, X62, X63]:k1_enumset1(X61,X62,X63)=k2_xboole_0(k1_tarski(X61),k2_tarski(X62,X63)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.13/0.39  fof(c_0_28, plain, ![X74]:k1_enumset1(X74,X74,X74)=k1_tarski(X74), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.13/0.39  cnf(c_0_29, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_30, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_31, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0))))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_34, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k5_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k3_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0))))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.13/0.39  cnf(c_0_38, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19]), c_0_20])).
% 0.13/0.39  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k3_xboole_0(k1_enumset1(esk2_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk2_0,esk2_0,esk3_0))))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.13/0.39  cnf(c_0_41, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k3_xboole_0(k1_enumset1(X2,X2,X3),k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3))))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 43
% 0.13/0.39  # Proof object clause steps            : 20
% 0.13/0.39  # Proof object formula steps           : 23
% 0.13/0.39  # Proof object conjectures             : 8
% 0.13/0.39  # Proof object clause conjectures      : 5
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 11
% 0.13/0.39  # Proof object initial formulas used   : 11
% 0.13/0.39  # Proof object generating inferences   : 2
% 0.13/0.39  # Proof object simplifying inferences  : 15
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 31
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 32
% 0.13/0.39  # Removed in clause preprocessing      : 5
% 0.13/0.39  # Initial clauses in saturation        : 27
% 0.13/0.39  # Processed clauses                    : 215
% 0.13/0.39  # ...of these trivial                  : 22
% 0.13/0.39  # ...subsumed                          : 91
% 0.13/0.39  # ...remaining for further processing  : 102
% 0.13/0.39  # Other redundant clauses eliminated   : 18
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 1
% 0.13/0.39  # Backward-rewritten                   : 24
% 0.13/0.39  # Generated clauses                    : 1359
% 0.13/0.39  # ...of the previous two non-trivial   : 985
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 1339
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 20
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 52
% 0.13/0.39  #    Positive orientable unit clauses  : 30
% 0.13/0.39  #    Positive unorientable unit clauses: 4
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 18
% 0.13/0.39  # Current number of unprocessed clauses: 813
% 0.13/0.39  # ...number of literals in the above   : 1064
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 55
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 198
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 198
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 44
% 0.13/0.39  # Unit Clause-clause subsumption calls : 18
% 0.13/0.39  # Rewrite failures with RHS unbound    : 16
% 0.13/0.39  # BW rewrite match attempts            : 141
% 0.13/0.39  # BW rewrite match successes           : 41
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 17353
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.049 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.052 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
