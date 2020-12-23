%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (1043 expanded)
%              Number of clauses        :   27 ( 400 expanded)
%              Number of leaves         :    9 ( 321 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (1043 expanded)
%              Number of equality atoms :   45 (1042 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

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

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_9,plain,(
    ! [X16,X17,X18] : k1_enumset1(X16,X17,X18) = k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_10,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_xboole_0(k2_tarski(X12,X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_15,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_19])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] : k2_xboole_0(k2_xboole_0(X7,X8),X9) = k2_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_28,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k2_enumset1(X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0))) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_18]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X2,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X2,X2))) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(X5,k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( k2_enumset1(esk2_0,esk1_0,esk3_0,esk1_0) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_36]),c_0_25])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_36]),c_0_25])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk1_0,esk3_0) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:03:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.19/0.43  # and selection function SelectNewComplexAHP.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.027 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.43  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.43  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.19/0.43  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.43  fof(c_0_9, plain, ![X16, X17, X18]:k1_enumset1(X16,X17,X18)=k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.19/0.43  fof(c_0_10, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  fof(c_0_11, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_12, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.43  fof(c_0_13, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  fof(c_0_14, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_xboole_0(k2_tarski(X12,X13),k2_tarski(X14,X15)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.43  fof(c_0_15, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.43  cnf(c_0_16, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.43  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_21, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.19/0.43  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.43  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.43  cnf(c_0_26, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_19])).
% 0.19/0.43  fof(c_0_27, plain, ![X7, X8, X9]:k2_xboole_0(k2_xboole_0(X7,X8),X9)=k2_xboole_0(X7,k2_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.43  fof(c_0_28, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.43  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.43  cnf(c_0_30, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_25])).
% 0.19/0.43  cnf(c_0_31, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k2_enumset1(X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0)))!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_18]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.43  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_33])).
% 0.19/0.43  cnf(c_0_37, plain, (k5_xboole_0(k2_enumset1(X1,X1,X2,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X2,X2)))=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 0.19/0.43  cnf(c_0_38, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k4_xboole_0(X5,k2_enumset1(X3,X3,X3,X4))),k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (k2_enumset1(esk2_0,esk1_0,esk3_0,esk1_0)!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_35, c_0_25])).
% 0.19/0.43  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_36]), c_0_25])).
% 0.19/0.43  cnf(c_0_41, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_36]), c_0_25])).
% 0.19/0.43  cnf(c_0_42, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1)))=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_25])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk1_0,esk3_0)!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.43  cnf(c_0_44, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_42])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_41])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 46
% 0.19/0.43  # Proof object clause steps            : 27
% 0.19/0.43  # Proof object formula steps           : 19
% 0.19/0.43  # Proof object conjectures             : 8
% 0.19/0.43  # Proof object clause conjectures      : 5
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 9
% 0.19/0.43  # Proof object initial formulas used   : 9
% 0.19/0.43  # Proof object generating inferences   : 9
% 0.19/0.43  # Proof object simplifying inferences  : 39
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 9
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 9
% 0.19/0.43  # Removed in clause preprocessing      : 4
% 0.19/0.43  # Initial clauses in saturation        : 5
% 0.19/0.43  # Processed clauses                    : 2657
% 0.19/0.43  # ...of these trivial                  : 354
% 0.19/0.43  # ...subsumed                          : 2223
% 0.19/0.43  # ...remaining for further processing  : 80
% 0.19/0.43  # Other redundant clauses eliminated   : 0
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 0
% 0.19/0.43  # Backward-rewritten                   : 3
% 0.19/0.43  # Generated clauses                    : 9045
% 0.19/0.43  # ...of the previous two non-trivial   : 6141
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 9045
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 0
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 72
% 0.19/0.43  #    Positive orientable unit clauses  : 27
% 0.19/0.43  #    Positive unorientable unit clauses: 45
% 0.19/0.43  #    Negative unit clauses             : 0
% 0.19/0.43  #    Non-unit-clauses                  : 0
% 0.19/0.43  # Current number of unprocessed clauses: 3494
% 0.19/0.43  # ...number of literals in the above   : 3494
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 12
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.43  # Unit Clause-clause subsumption calls : 568
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 1745
% 0.19/0.43  # BW rewrite match successes           : 676
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 83942
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.085 s
% 0.19/0.43  # System time              : 0.007 s
% 0.19/0.43  # Total time               : 0.092 s
% 0.19/0.43  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
