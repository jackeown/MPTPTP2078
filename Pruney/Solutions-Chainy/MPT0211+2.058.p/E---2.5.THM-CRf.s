%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:50 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 376 expanded)
%              Number of clauses        :   26 ( 153 expanded)
%              Number of leaves         :   10 ( 111 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 376 expanded)
%              Number of equality atoms :   46 ( 375 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l129_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24,X25,X26] : k2_enumset1(X23,X24,X25,X26) = k2_enumset1(X23,X26,X25,X24) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

fof(c_0_14,plain,(
    ! [X32,X33,X34,X35] : k3_enumset1(X32,X32,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_enumset1(X19,X21,X22,X20) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

fof(c_0_16,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_17,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X10,X11,X12,X13] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X12,X11,X10,X13) ),
    inference(variable_rename,[status(thm)],[l129_enumset1])).

fof(c_0_22,plain,(
    ! [X14,X15,X16,X17,X18] : k3_enumset1(X14,X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X14,X15,X16),k2_tarski(X17,X18)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X3,X3,X2,X1,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_24]),c_0_24])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X4,X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X2,X2,X3)))) = k3_enumset1(X2,X1,X3,X4,X5) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X3,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_enumset1(X1,X1,X2,X2,X3)))) = k3_enumset1(X2,X1,X3,X5,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X2,X1,X3,X4) = k3_enumset1(X4,X4,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:51:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.47  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.18/0.47  # and selection function SelectNewComplexAHP.
% 0.18/0.47  #
% 0.18/0.47  # Preprocessing time       : 0.026 s
% 0.18/0.47  # Presaturation interreduction done
% 0.18/0.47  
% 0.18/0.47  # Proof found!
% 0.18/0.47  # SZS status Theorem
% 0.18/0.47  # SZS output start CNFRefutation
% 0.18/0.47  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.18/0.47  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.47  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 0.18/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.47  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 0.18/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.47  fof(l129_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X1,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l129_enumset1)).
% 0.18/0.47  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.18/0.47  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.18/0.47  fof(c_0_11, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k5_xboole_0(X8,k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.47  fof(c_0_12, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.47  fof(c_0_13, plain, ![X23, X24, X25, X26]:k2_enumset1(X23,X24,X25,X26)=k2_enumset1(X23,X26,X25,X24), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.18/0.47  fof(c_0_14, plain, ![X32, X33, X34, X35]:k3_enumset1(X32,X32,X33,X34,X35)=k2_enumset1(X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.47  fof(c_0_15, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_enumset1(X19,X21,X22,X20), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.18/0.47  fof(c_0_16, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.18/0.47  fof(c_0_17, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.47  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.47  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.47  fof(c_0_20, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.47  fof(c_0_21, plain, ![X10, X11, X12, X13]:k2_enumset1(X10,X11,X12,X13)=k2_enumset1(X12,X11,X10,X13), inference(variable_rename,[status(thm)],[l129_enumset1])).
% 0.18/0.47  fof(c_0_22, plain, ![X14, X15, X16, X17, X18]:k3_enumset1(X14,X15,X16,X17,X18)=k2_xboole_0(k1_enumset1(X14,X15,X16),k2_tarski(X17,X18)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.18/0.47  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.47  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.47  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.47  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.47  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.47  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.47  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  cnf(c_0_30, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.47  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.47  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.18/0.47  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 0.18/0.47  cnf(c_0_34, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.47  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X3,X3,X2,X1,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_24]), c_0_24])).
% 0.18/0.47  cnf(c_0_36, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.18/0.47  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.47  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk1_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk1_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.18/0.47  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X4,X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.18/0.47  cnf(c_0_40, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X5),k3_enumset1(X1,X1,X2,X2,X3))))=k3_enumset1(X2,X1,X3,X4,X5)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.18/0.47  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X3,X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 0.18/0.47  cnf(c_0_42, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X3,X2,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_36])).
% 0.18/0.47  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.18/0.47  cnf(c_0_44, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_xboole_0(k3_enumset1(X4,X4,X5,X5,X5),k3_enumset1(X1,X1,X2,X2,X3))))=k3_enumset1(X2,X1,X3,X5,X4)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.47  cnf(c_0_45, plain, (k3_enumset1(X1,X2,X1,X3,X4)=k3_enumset1(X4,X4,X3,X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.47  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_32])]), ['proof']).
% 0.18/0.47  # SZS output end CNFRefutation
% 0.18/0.47  # Proof object total steps             : 47
% 0.18/0.47  # Proof object clause steps            : 26
% 0.18/0.47  # Proof object formula steps           : 21
% 0.18/0.47  # Proof object conjectures             : 8
% 0.18/0.47  # Proof object clause conjectures      : 5
% 0.18/0.47  # Proof object formula conjectures     : 3
% 0.18/0.47  # Proof object initial clauses used    : 10
% 0.18/0.47  # Proof object initial formulas used   : 10
% 0.18/0.47  # Proof object generating inferences   : 7
% 0.18/0.47  # Proof object simplifying inferences  : 43
% 0.18/0.47  # Training examples: 0 positive, 0 negative
% 0.18/0.47  # Parsed axioms                        : 10
% 0.18/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.47  # Initial clauses                      : 10
% 0.18/0.47  # Removed in clause preprocessing      : 5
% 0.18/0.47  # Initial clauses in saturation        : 5
% 0.18/0.47  # Processed clauses                    : 7746
% 0.18/0.47  # ...of these trivial                  : 161
% 0.18/0.47  # ...subsumed                          : 7501
% 0.18/0.47  # ...remaining for further processing  : 84
% 0.18/0.47  # Other redundant clauses eliminated   : 0
% 0.18/0.47  # Clauses deleted for lack of memory   : 0
% 0.18/0.47  # Backward-subsumed                    : 0
% 0.18/0.47  # Backward-rewritten                   : 3
% 0.18/0.47  # Generated clauses                    : 14831
% 0.18/0.47  # ...of the previous two non-trivial   : 11492
% 0.18/0.47  # Contextual simplify-reflections      : 0
% 0.18/0.47  # Paramodulations                      : 14831
% 0.18/0.47  # Factorizations                       : 0
% 0.18/0.47  # Equation resolutions                 : 0
% 0.18/0.47  # Propositional unsat checks           : 0
% 0.18/0.47  #    Propositional check models        : 0
% 0.18/0.47  #    Propositional check unsatisfiable : 0
% 0.18/0.47  #    Propositional clauses             : 0
% 0.18/0.47  #    Propositional clauses after purity: 0
% 0.18/0.47  #    Propositional unsat core size     : 0
% 0.18/0.47  #    Propositional preprocessing time  : 0.000
% 0.18/0.47  #    Propositional encoding time       : 0.000
% 0.18/0.47  #    Propositional solver time         : 0.000
% 0.18/0.47  #    Success case prop preproc time    : 0.000
% 0.18/0.47  #    Success case prop encoding time   : 0.000
% 0.18/0.47  #    Success case prop solver time     : 0.000
% 0.18/0.47  # Current number of processed clauses  : 76
% 0.18/0.47  #    Positive orientable unit clauses  : 19
% 0.18/0.47  #    Positive unorientable unit clauses: 57
% 0.18/0.47  #    Negative unit clauses             : 0
% 0.18/0.47  #    Non-unit-clauses                  : 0
% 0.18/0.47  # Current number of unprocessed clauses: 3748
% 0.18/0.47  # ...number of literals in the above   : 3748
% 0.18/0.47  # Current number of archived formulas  : 0
% 0.18/0.47  # Current number of archived clauses   : 13
% 0.18/0.47  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.47  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.47  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.47  # Unit Clause-clause subsumption calls : 1655
% 0.18/0.47  # Rewrite failures with RHS unbound    : 0
% 0.18/0.47  # BW rewrite match attempts            : 3210
% 0.18/0.47  # BW rewrite match successes           : 1656
% 0.18/0.47  # Condensation attempts                : 0
% 0.18/0.47  # Condensation successes               : 0
% 0.18/0.47  # Termbank termtop insertions          : 74942
% 0.18/0.47  
% 0.18/0.47  # -------------------------------------------------
% 0.18/0.47  # User time                : 0.126 s
% 0.18/0.47  # System time              : 0.009 s
% 0.18/0.47  # Total time               : 0.135 s
% 0.18/0.47  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
