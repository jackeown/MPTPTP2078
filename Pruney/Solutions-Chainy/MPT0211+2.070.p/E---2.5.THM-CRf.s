%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:51 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 771 expanded)
%              Number of clauses        :   25 ( 288 expanded)
%              Number of leaves         :   10 ( 241 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 771 expanded)
%              Number of equality atoms :   45 ( 770 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t111_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_10,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X21,X22,X23),k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_11,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11,X12] : k3_enumset1(X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X8,X9,X10),k2_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_17,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X18,X19,X20,X17) ),
    inference(variable_rename,[status(thm)],[t111_enumset1])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23]),c_0_23])).

fof(c_0_30,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X4,X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

fof(c_0_33,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_enumset1(X13,X16,X15,X14) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X2,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_28])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_enumset1(X2,X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X2,X3,X4) = k3_enumset1(X2,X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X2,X3,X1,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_28])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_23]),c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk1_0,esk3_0) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_29]),c_0_29]),c_0_29]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_28])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X1,X4,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.22/1.40  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 1.22/1.40  # and selection function SelectNewComplexAHP.
% 1.22/1.40  #
% 1.22/1.40  # Preprocessing time       : 0.026 s
% 1.22/1.40  # Presaturation interreduction done
% 1.22/1.40  
% 1.22/1.40  # Proof found!
% 1.22/1.40  # SZS status Theorem
% 1.22/1.40  # SZS output start CNFRefutation
% 1.22/1.40  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.22/1.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.22/1.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.22/1.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.22/1.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.22/1.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.22/1.40  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.22/1.40  fof(t111_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 1.22/1.40  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 1.22/1.40  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 1.22/1.40  fof(c_0_10, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_xboole_0(k1_enumset1(X21,X22,X23),k1_tarski(X24)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 1.22/1.40  fof(c_0_11, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.22/1.40  fof(c_0_12, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.22/1.40  fof(c_0_13, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k5_xboole_0(X6,k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.22/1.40  fof(c_0_14, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.22/1.40  fof(c_0_15, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.22/1.40  fof(c_0_16, plain, ![X8, X9, X10, X11, X12]:k3_enumset1(X8,X9,X10,X11,X12)=k2_xboole_0(k1_enumset1(X8,X9,X10),k2_tarski(X11,X12)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 1.22/1.40  fof(c_0_17, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_enumset1(X18,X19,X20,X17), inference(variable_rename,[status(thm)],[t111_enumset1])).
% 1.22/1.40  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.22/1.40  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.22/1.40  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.22/1.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.22/1.40  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.22/1.40  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.22/1.40  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.22/1.40  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.22/1.40  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 1.22/1.40  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X1,X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 1.22/1.40  cnf(c_0_28, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23])).
% 1.22/1.40  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_23]), c_0_23])).
% 1.22/1.40  fof(c_0_30, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 1.22/1.40  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 1.22/1.40  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X4,X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 1.22/1.40  fof(c_0_33, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_enumset1(X13,X16,X15,X14), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 1.22/1.40  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.22/1.40  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X2,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_28])).
% 1.22/1.40  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_enumset1(X2,X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.22/1.40  cnf(c_0_37, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.22/1.40  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 1.22/1.40  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X2,X3,X4)=k3_enumset1(X2,X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 1.22/1.40  cnf(c_0_40, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X2,X3,X1,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_28])).
% 1.22/1.40  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_23]), c_0_23])).
% 1.22/1.40  cnf(c_0_42, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk1_0,esk3_0)!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_29]), c_0_29]), c_0_29]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_28])).
% 1.22/1.40  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.22/1.40  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X1,X4,X3)), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 1.22/1.40  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), ['proof']).
% 1.22/1.40  # SZS output end CNFRefutation
% 1.22/1.40  # Proof object total steps             : 46
% 1.22/1.40  # Proof object clause steps            : 25
% 1.22/1.40  # Proof object formula steps           : 21
% 1.22/1.40  # Proof object conjectures             : 7
% 1.22/1.40  # Proof object clause conjectures      : 4
% 1.22/1.40  # Proof object formula conjectures     : 3
% 1.22/1.40  # Proof object initial clauses used    : 10
% 1.22/1.40  # Proof object initial formulas used   : 10
% 1.22/1.40  # Proof object generating inferences   : 7
% 1.22/1.40  # Proof object simplifying inferences  : 49
% 1.22/1.40  # Training examples: 0 positive, 0 negative
% 1.22/1.40  # Parsed axioms                        : 10
% 1.22/1.40  # Removed by relevancy pruning/SinE    : 0
% 1.22/1.40  # Initial clauses                      : 10
% 1.22/1.40  # Removed in clause preprocessing      : 5
% 1.22/1.40  # Initial clauses in saturation        : 5
% 1.22/1.40  # Processed clauses                    : 18715
% 1.22/1.40  # ...of these trivial                  : 34
% 1.22/1.40  # ...subsumed                          : 18233
% 1.22/1.40  # ...remaining for further processing  : 448
% 1.22/1.40  # Other redundant clauses eliminated   : 0
% 1.22/1.40  # Clauses deleted for lack of memory   : 0
% 1.22/1.40  # Backward-subsumed                    : 9
% 1.22/1.40  # Backward-rewritten                   : 2
% 1.22/1.40  # Generated clauses                    : 310188
% 1.22/1.40  # ...of the previous two non-trivial   : 294207
% 1.22/1.40  # Contextual simplify-reflections      : 0
% 1.22/1.40  # Paramodulations                      : 310188
% 1.22/1.40  # Factorizations                       : 0
% 1.22/1.40  # Equation resolutions                 : 0
% 1.22/1.40  # Propositional unsat checks           : 0
% 1.22/1.40  #    Propositional check models        : 0
% 1.22/1.40  #    Propositional check unsatisfiable : 0
% 1.22/1.40  #    Propositional clauses             : 0
% 1.22/1.40  #    Propositional clauses after purity: 0
% 1.22/1.40  #    Propositional unsat core size     : 0
% 1.22/1.40  #    Propositional preprocessing time  : 0.000
% 1.22/1.40  #    Propositional encoding time       : 0.000
% 1.22/1.40  #    Propositional solver time         : 0.000
% 1.22/1.40  #    Success case prop preproc time    : 0.000
% 1.22/1.40  #    Success case prop encoding time   : 0.000
% 1.22/1.40  #    Success case prop solver time     : 0.000
% 1.22/1.40  # Current number of processed clauses  : 432
% 1.22/1.40  #    Positive orientable unit clauses  : 15
% 1.22/1.40  #    Positive unorientable unit clauses: 417
% 1.22/1.40  #    Negative unit clauses             : 0
% 1.22/1.40  #    Non-unit-clauses                  : 0
% 1.22/1.40  # Current number of unprocessed clauses: 273652
% 1.22/1.40  # ...number of literals in the above   : 273652
% 1.22/1.40  # Current number of archived formulas  : 0
% 1.22/1.40  # Current number of archived clauses   : 21
% 1.22/1.40  # Clause-clause subsumption calls (NU) : 0
% 1.22/1.40  # Rec. Clause-clause subsumption calls : 0
% 1.22/1.40  # Non-unit clause-clause subsumptions  : 0
% 1.22/1.40  # Unit Clause-clause subsumption calls : 91136
% 1.22/1.40  # Rewrite failures with RHS unbound    : 0
% 1.22/1.40  # BW rewrite match attempts            : 93859
% 1.22/1.40  # BW rewrite match successes           : 14884
% 1.22/1.40  # Condensation attempts                : 0
% 1.22/1.40  # Condensation successes               : 0
% 1.22/1.40  # Termbank termtop insertions          : 881715
% 1.22/1.41  
% 1.22/1.41  # -------------------------------------------------
% 1.22/1.41  # User time                : 0.985 s
% 1.22/1.41  # System time              : 0.072 s
% 1.22/1.41  # Total time               : 1.056 s
% 1.22/1.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
