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
% DateTime   : Thu Dec  3 10:35:16 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 545 expanded)
%              Number of clauses        :   24 ( 222 expanded)
%              Number of leaves         :    9 ( 161 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 545 expanded)
%              Number of equality atoms :   42 ( 544 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t60_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(c_0_9,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_xboole_0(k1_tarski(X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_10,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33] : k5_enumset1(X27,X28,X29,X30,X31,X32,X33) = k2_xboole_0(k2_tarski(X27,X28),k3_enumset1(X29,X30,X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k5_enumset1(X34,X35,X36,X37,X38,X39,X40) = k2_xboole_0(k1_enumset1(X34,X35,X36),k2_enumset1(X37,X38,X39,X40)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] : k5_enumset1(X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(assume_negation,[status(cth)],[t60_enumset1])).

cnf(c_0_22,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_16])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_16]),c_0_23]),c_0_23])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)))),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_16]),c_0_26]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X2,X1,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_29])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X5,X6,X7,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_15]),c_0_16]),c_0_23]),c_0_23])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_enumset1(X1,X2,X3,X4,X5)))) = k5_enumset1(X6,X7,X1,X2,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X6,X5,X7,X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X2,X3,X4,X5,X6,X7,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k5_enumset1(esk1_0,esk7_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_35]),c_0_38])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X7,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n011.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:37:12 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.22/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.038 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.22/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.22/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.22/0.41  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.22/0.41  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.22/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.22/0.41  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.22/0.41  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.22/0.41  fof(t60_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.22/0.41  fof(c_0_9, plain, ![X21, X22]:k2_tarski(X21,X22)=k2_xboole_0(k1_tarski(X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.22/0.41  fof(c_0_10, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(X12,k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.22/0.41  fof(c_0_11, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.22/0.41  fof(c_0_12, plain, ![X23, X24, X25, X26]:k2_enumset1(X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X23),k1_enumset1(X24,X25,X26)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.22/0.41  fof(c_0_13, plain, ![X27, X28, X29, X30, X31, X32, X33]:k5_enumset1(X27,X28,X29,X30,X31,X32,X33)=k2_xboole_0(k2_tarski(X27,X28),k3_enumset1(X29,X30,X31,X32,X33)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.22/0.41  cnf(c_0_14, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.41  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.41  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.41  fof(c_0_17, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.22/0.41  fof(c_0_18, plain, ![X34, X35, X36, X37, X38, X39, X40]:k5_enumset1(X34,X35,X36,X37,X38,X39,X40)=k2_xboole_0(k1_enumset1(X34,X35,X36),k2_enumset1(X37,X38,X39,X40)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.22/0.41  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  fof(c_0_20, plain, ![X14, X15, X16, X17, X18, X19, X20]:k5_enumset1(X14,X15,X16,X17,X18,X19,X20)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.22/0.41  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(assume_negation,[status(cth)],[t60_enumset1])).
% 0.22/0.41  cnf(c_0_22, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.41  cnf(c_0_23, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.22/0.41  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.41  cnf(c_0_25, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.41  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_16])).
% 0.22/0.41  cnf(c_0_27, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.22/0.41  fof(c_0_28, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.22/0.41  cnf(c_0_29, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_15]), c_0_16]), c_0_23]), c_0_23])).
% 0.22/0.41  cnf(c_0_30, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.22/0.41  cnf(c_0_31, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)))),k3_xboole_0(k5_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)))),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_16]), c_0_26]), c_0_26])).
% 0.22/0.41  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))),k5_xboole_0(k1_enumset1(X5,X6,X7),k3_xboole_0(k1_enumset1(X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_16]), c_0_26]), c_0_26])).
% 0.22/0.41  cnf(c_0_33, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.22/0.41  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X2,X1,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_29])).
% 0.22/0.41  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X5,X6,X7,X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.22/0.41  cnf(c_0_36, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k5_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_xboole_0(k5_xboole_0(k1_tarski(esk6_0),k5_xboole_0(k1_tarski(esk7_0),k3_xboole_0(k1_tarski(esk7_0),k1_tarski(esk6_0)))),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_15]), c_0_16]), c_0_23]), c_0_23])).
% 0.22/0.41  cnf(c_0_37, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k5_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_xboole_0(k5_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X7),k3_xboole_0(k1_tarski(X7),k1_tarski(X6)))),k3_enumset1(X1,X2,X3,X4,X5))))=k5_enumset1(X6,X7,X1,X2,X3,X4,X5)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.22/0.41  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X6,X5,X7,X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.22/0.41  cnf(c_0_39, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X2,X3,X4,X5,X6,X7,X1)), inference(spm,[status(thm)],[c_0_35, c_0_35])).
% 0.22/0.41  cnf(c_0_40, negated_conjecture, (k5_enumset1(esk1_0,esk7_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_35]), c_0_38])).
% 0.22/0.41  cnf(c_0_41, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X7,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.22/0.41  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.22/0.41  # SZS output end CNFRefutation
% 0.22/0.41  # Proof object total steps             : 43
% 0.22/0.41  # Proof object clause steps            : 24
% 0.22/0.41  # Proof object formula steps           : 19
% 0.22/0.41  # Proof object conjectures             : 7
% 0.22/0.41  # Proof object clause conjectures      : 4
% 0.22/0.41  # Proof object formula conjectures     : 3
% 0.22/0.41  # Proof object initial clauses used    : 9
% 0.22/0.41  # Proof object initial formulas used   : 9
% 0.22/0.41  # Proof object generating inferences   : 6
% 0.22/0.41  # Proof object simplifying inferences  : 31
% 0.22/0.41  # Training examples: 0 positive, 0 negative
% 0.22/0.41  # Parsed axioms                        : 9
% 0.22/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.41  # Initial clauses                      : 9
% 0.22/0.41  # Removed in clause preprocessing      : 4
% 0.22/0.41  # Initial clauses in saturation        : 5
% 0.22/0.41  # Processed clauses                    : 42
% 0.22/0.41  # ...of these trivial                  : 1
% 0.22/0.41  # ...subsumed                          : 15
% 0.22/0.41  # ...remaining for further processing  : 26
% 0.22/0.41  # Other redundant clauses eliminated   : 0
% 0.22/0.41  # Clauses deleted for lack of memory   : 0
% 0.22/0.41  # Backward-subsumed                    : 0
% 0.22/0.41  # Backward-rewritten                   : 2
% 0.22/0.41  # Generated clauses                    : 410
% 0.22/0.41  # ...of the previous two non-trivial   : 355
% 0.22/0.41  # Contextual simplify-reflections      : 0
% 0.22/0.41  # Paramodulations                      : 410
% 0.22/0.41  # Factorizations                       : 0
% 0.22/0.41  # Equation resolutions                 : 0
% 0.22/0.41  # Propositional unsat checks           : 0
% 0.22/0.41  #    Propositional check models        : 0
% 0.22/0.41  #    Propositional check unsatisfiable : 0
% 0.22/0.41  #    Propositional clauses             : 0
% 0.22/0.41  #    Propositional clauses after purity: 0
% 0.22/0.41  #    Propositional unsat core size     : 0
% 0.22/0.41  #    Propositional preprocessing time  : 0.000
% 0.22/0.41  #    Propositional encoding time       : 0.000
% 0.22/0.41  #    Propositional solver time         : 0.000
% 0.22/0.41  #    Success case prop preproc time    : 0.000
% 0.22/0.41  #    Success case prop encoding time   : 0.000
% 0.22/0.41  #    Success case prop solver time     : 0.000
% 0.22/0.41  # Current number of processed clauses  : 19
% 0.22/0.41  #    Positive orientable unit clauses  : 4
% 0.22/0.41  #    Positive unorientable unit clauses: 15
% 0.22/0.41  #    Negative unit clauses             : 0
% 0.22/0.41  #    Non-unit-clauses                  : 0
% 0.22/0.41  # Current number of unprocessed clauses: 323
% 0.22/0.41  # ...number of literals in the above   : 323
% 0.22/0.41  # Current number of archived formulas  : 0
% 0.22/0.41  # Current number of archived clauses   : 11
% 0.22/0.41  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.41  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.41  # Unit Clause-clause subsumption calls : 158
% 0.22/0.41  # Rewrite failures with RHS unbound    : 0
% 0.22/0.41  # BW rewrite match attempts            : 277
% 0.22/0.41  # BW rewrite match successes           : 277
% 0.22/0.41  # Condensation attempts                : 0
% 0.22/0.41  # Condensation successes               : 0
% 0.22/0.41  # Termbank termtop insertions          : 2290
% 0.22/0.41  
% 0.22/0.41  # -------------------------------------------------
% 0.22/0.41  # User time                : 0.044 s
% 0.22/0.41  # System time              : 0.006 s
% 0.22/0.41  # Total time               : 0.051 s
% 0.22/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
