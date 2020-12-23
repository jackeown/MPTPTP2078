%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 565 expanded)
%              Number of clauses        :   27 ( 216 expanded)
%              Number of leaves         :   10 ( 174 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 565 expanded)
%              Number of equality atoms :   47 ( 564 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(c_0_10,plain,(
    ! [X16,X17,X18] : k1_enumset1(X16,X17,X18) = k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_11,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_xboole_0(k2_tarski(X9,X10),k2_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
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
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X19),k1_enumset1(X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_27,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_21])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_29])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0))) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k2_enumset1(X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k2_enumset1(esk2_0,esk1_0,esk3_0,esk1_0) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_39]),c_0_37])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X2,X2,X3) = k2_enumset1(X2,X3,X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk3_0,esk2_0) != k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_34])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X2,X4,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_44]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.20/0.41  # and selection function SelectNewComplexAHP.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.026 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.41  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.20/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.41  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 0.20/0.41  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.41  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.41  fof(c_0_10, plain, ![X16, X17, X18]:k1_enumset1(X16,X17,X18)=k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.20/0.41  fof(c_0_11, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_12, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_13, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.41  fof(c_0_14, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.41  fof(c_0_15, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_xboole_0(k2_tarski(X9,X10),k2_tarski(X11,X12)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.20/0.41  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.41  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 0.20/0.41  cnf(c_0_18, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  fof(c_0_25, plain, ![X13, X14, X15]:k1_enumset1(X13,X14,X15)=k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.41  fof(c_0_26, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X19),k1_enumset1(X20,X21,X22)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.41  fof(c_0_27, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.41  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_30, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_21])).
% 0.20/0.41  cnf(c_0_31, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_34, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_35, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_37, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k2_enumset1(X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk1_0)))!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k2_enumset1(X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k2_enumset1(esk2_0,esk1_0,esk3_0,esk1_0)!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_38, c_0_29])).
% 0.20/0.41  cnf(c_0_42, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_39]), c_0_37])).
% 0.20/0.41  cnf(c_0_43, plain, (k2_enumset1(X1,X2,X2,X3)=k2_enumset1(X2,X3,X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.20/0.41  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk3_0,esk2_0)!=k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_34])).
% 0.20/0.41  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X2,X4,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_44]), c_0_29])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 48
% 0.20/0.41  # Proof object clause steps            : 27
% 0.20/0.41  # Proof object formula steps           : 21
% 0.20/0.41  # Proof object conjectures             : 8
% 0.20/0.41  # Proof object clause conjectures      : 5
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 10
% 0.20/0.41  # Proof object initial formulas used   : 10
% 0.20/0.41  # Proof object generating inferences   : 6
% 0.20/0.41  # Proof object simplifying inferences  : 48
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 10
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 10
% 0.20/0.41  # Removed in clause preprocessing      : 4
% 0.20/0.41  # Initial clauses in saturation        : 6
% 0.20/0.41  # Processed clauses                    : 863
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 777
% 0.20/0.41  # ...remaining for further processing  : 86
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 3
% 0.20/0.41  # Generated clauses                    : 9458
% 0.20/0.41  # ...of the previous two non-trivial   : 8900
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 9458
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 74
% 0.20/0.41  #    Positive orientable unit clauses  : 2
% 0.20/0.41  #    Positive unorientable unit clauses: 72
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 0
% 0.20/0.41  # Current number of unprocessed clauses: 8010
% 0.20/0.41  # ...number of literals in the above   : 8010
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 16
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.41  # Unit Clause-clause subsumption calls : 2801
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 4499
% 0.20/0.41  # BW rewrite match successes           : 1397
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 26030
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.071 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.077 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
