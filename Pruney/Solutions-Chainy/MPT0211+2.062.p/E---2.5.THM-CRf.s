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

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 321 expanded)
%              Number of clauses        :   25 ( 128 expanded)
%              Number of leaves         :   10 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 321 expanded)
%              Number of equality atoms :   45 ( 320 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t112_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(c_0_10,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24] : k2_enumset1(X21,X22,X23,X24) = k2_enumset1(X22,X24,X23,X21) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

fof(c_0_14,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X9,X10,X11,X12] : k2_enumset1(X9,X10,X11,X12) = k2_xboole_0(k2_tarski(X9,X10),k2_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_16,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X18,X20,X17,X19) ),
    inference(variable_rename,[status(thm)],[t112_enumset1])).

fof(c_0_21,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_22,plain,(
    ! [X13,X14,X15,X16] : k2_enumset1(X13,X14,X15,X16) = k2_enumset1(X13,X15,X16,X14) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X2,X4,X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_24]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26]),c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_24])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) = k3_enumset1(X2,X2,X4,X3,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X2,X2,X2)))) = k3_enumset1(X1,X1,X4,X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0)))) != k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X2,X2,X2)))) = k3_enumset1(X1,X1,X3,X4,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.34/2.54  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 2.34/2.54  # and selection function SelectNewComplexAHP.
% 2.34/2.54  #
% 2.34/2.54  # Preprocessing time       : 0.026 s
% 2.34/2.54  # Presaturation interreduction done
% 2.34/2.54  
% 2.34/2.54  # Proof found!
% 2.34/2.54  # SZS status Theorem
% 2.34/2.54  # SZS output start CNFRefutation
% 2.34/2.54  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.34/2.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.34/2.54  fof(t137_enumset1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.34/2.54  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 2.34/2.54  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.34/2.54  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.34/2.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/2.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.34/2.54  fof(t112_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 2.34/2.54  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.34/2.54  fof(c_0_10, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.34/2.54  fof(c_0_11, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.34/2.54  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1))=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t137_enumset1])).
% 2.34/2.54  fof(c_0_13, plain, ![X21, X22, X23, X24]:k2_enumset1(X21,X22,X23,X24)=k2_enumset1(X22,X24,X23,X21), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 2.34/2.54  fof(c_0_14, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.34/2.54  fof(c_0_15, plain, ![X9, X10, X11, X12]:k2_enumset1(X9,X10,X11,X12)=k2_xboole_0(k2_tarski(X9,X10),k2_tarski(X11,X12)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 2.34/2.54  fof(c_0_16, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.34/2.54  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.34/2.54  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.34/2.54  fof(c_0_19, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.34/2.54  fof(c_0_20, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_enumset1(X18,X20,X17,X19), inference(variable_rename,[status(thm)],[t112_enumset1])).
% 2.34/2.54  fof(c_0_21, negated_conjecture, k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 2.34/2.54  fof(c_0_22, plain, ![X13, X14, X15, X16]:k2_enumset1(X13,X14,X15,X16)=k2_enumset1(X13,X15,X16,X14), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 2.34/2.54  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.34/2.54  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.34/2.54  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.34/2.54  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.34/2.54  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 2.34/2.54  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.34/2.54  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.34/2.54  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.34/2.54  cnf(c_0_31, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.34/2.54  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 2.34/2.54  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 2.34/2.54  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X2,X4,X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_24]), c_0_24])).
% 2.34/2.54  cnf(c_0_35, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk1_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_26]), c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 2.34/2.54  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_24])).
% 2.34/2.54  cnf(c_0_37, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))=k3_enumset1(X2,X2,X4,X3,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.34/2.54  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X3,X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 2.34/2.54  cnf(c_0_39, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 2.34/2.54  cnf(c_0_40, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))=k3_enumset1(X1,X1,X3,X4,X2)), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 2.34/2.54  cnf(c_0_41, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X2,X2,X2))))=k3_enumset1(X1,X1,X4,X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.34/2.54  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk2_0))))!=k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.34/2.54  cnf(c_0_43, plain, (k5_xboole_0(k3_enumset1(X1,X1,X2,X2,X2),k5_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_xboole_0(k3_enumset1(X3,X3,X4,X4,X4),k3_enumset1(X1,X1,X2,X2,X2))))=k3_enumset1(X1,X1,X3,X4,X2)), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 2.34/2.54  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 2.34/2.54  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_40])]), ['proof']).
% 2.34/2.54  # SZS output end CNFRefutation
% 2.34/2.54  # Proof object total steps             : 46
% 2.34/2.54  # Proof object clause steps            : 25
% 2.34/2.54  # Proof object formula steps           : 21
% 2.34/2.54  # Proof object conjectures             : 8
% 2.34/2.54  # Proof object clause conjectures      : 5
% 2.34/2.54  # Proof object formula conjectures     : 3
% 2.34/2.54  # Proof object initial clauses used    : 10
% 2.34/2.54  # Proof object initial formulas used   : 10
% 2.34/2.54  # Proof object generating inferences   : 6
% 2.34/2.54  # Proof object simplifying inferences  : 41
% 2.34/2.54  # Training examples: 0 positive, 0 negative
% 2.34/2.54  # Parsed axioms                        : 10
% 2.34/2.54  # Removed by relevancy pruning/SinE    : 0
% 2.34/2.54  # Initial clauses                      : 10
% 2.34/2.54  # Removed in clause preprocessing      : 5
% 2.34/2.54  # Initial clauses in saturation        : 5
% 2.34/2.54  # Processed clauses                    : 21024
% 2.34/2.54  # ...of these trivial                  : 0
% 2.34/2.54  # ...subsumed                          : 20639
% 2.34/2.54  # ...remaining for further processing  : 385
% 2.34/2.54  # Other redundant clauses eliminated   : 0
% 2.34/2.54  # Clauses deleted for lack of memory   : 0
% 2.34/2.54  # Backward-subsumed                    : 0
% 2.34/2.54  # Backward-rewritten                   : 3
% 2.34/2.54  # Generated clauses                    : 507063
% 2.34/2.54  # ...of the previous two non-trivial   : 504614
% 2.34/2.54  # Contextual simplify-reflections      : 0
% 2.34/2.54  # Paramodulations                      : 507063
% 2.34/2.54  # Factorizations                       : 0
% 2.34/2.54  # Equation resolutions                 : 0
% 2.34/2.54  # Propositional unsat checks           : 0
% 2.34/2.54  #    Propositional check models        : 0
% 2.34/2.54  #    Propositional check unsatisfiable : 0
% 2.34/2.54  #    Propositional clauses             : 0
% 2.34/2.54  #    Propositional clauses after purity: 0
% 2.34/2.54  #    Propositional unsat core size     : 0
% 2.34/2.54  #    Propositional preprocessing time  : 0.000
% 2.34/2.54  #    Propositional encoding time       : 0.000
% 2.34/2.54  #    Propositional solver time         : 0.000
% 2.34/2.54  #    Success case prop preproc time    : 0.000
% 2.34/2.54  #    Success case prop encoding time   : 0.000
% 2.34/2.54  #    Success case prop solver time     : 0.000
% 2.34/2.54  # Current number of processed clauses  : 377
% 2.34/2.54  #    Positive orientable unit clauses  : 0
% 2.34/2.54  #    Positive unorientable unit clauses: 377
% 2.34/2.54  #    Negative unit clauses             : 0
% 2.34/2.54  #    Non-unit-clauses                  : 0
% 2.34/2.54  # Current number of unprocessed clauses: 483600
% 2.34/2.54  # ...number of literals in the above   : 483600
% 2.34/2.54  # Current number of archived formulas  : 0
% 2.34/2.54  # Current number of archived clauses   : 13
% 2.34/2.54  # Clause-clause subsumption calls (NU) : 0
% 2.34/2.54  # Rec. Clause-clause subsumption calls : 0
% 2.34/2.54  # Non-unit clause-clause subsumptions  : 0
% 2.34/2.54  # Unit Clause-clause subsumption calls : 36448
% 2.34/2.54  # Rewrite failures with RHS unbound    : 0
% 2.34/2.54  # BW rewrite match attempts            : 56954
% 2.34/2.54  # BW rewrite match successes           : 17924
% 2.34/2.54  # Condensation attempts                : 0
% 2.34/2.54  # Condensation successes               : 0
% 2.34/2.54  # Termbank termtop insertions          : 7161822
% 2.34/2.55  
% 2.34/2.55  # -------------------------------------------------
% 2.34/2.55  # User time                : 2.109 s
% 2.34/2.55  # System time              : 0.101 s
% 2.34/2.55  # Total time               : 2.210 s
% 2.34/2.55  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
