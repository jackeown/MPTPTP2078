%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 158 expanded)
%              Number of clauses        :   20 (  61 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 ( 158 expanded)
%              Number of equality atoms :   40 ( 157 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(t85_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(t117_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(assume_negation,[status(cth)],[t125_enumset1])).

fof(c_0_11,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32,X33] : k5_enumset1(X30,X30,X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t85_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X13,X12,X14,X11) ),
    inference(variable_rename,[status(thm)],[t117_enumset1])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X18,X19] : k3_enumset1(X15,X16,X17,X18,X19) = k2_xboole_0(k2_tarski(X15,X16),k1_enumset1(X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_15,plain,(
    ! [X23,X24] : k2_enumset1(X23,X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X25,X26,X27,X28,X29] : k5_enumset1(X25,X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_19,plain,(
    ! [X8,X9,X10] : k1_enumset1(X8,X9,X10) = k1_enumset1(X10,X9,X8) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_20,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X34,X35,X36] : k1_enumset1(X34,X35,X36) = k1_enumset1(X34,X36,X35) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_30,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X3,X3,X3,X3,X2,X4,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21]),c_0_21])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X4,X5),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_21]),c_0_21]),c_0_21]),c_0_27])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_26]),c_0_21]),c_0_21])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk2_0,esk1_0,esk3_0) != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X1,X1,X2,X5,X4,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_32])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26]),c_0_26]),c_0_21]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk1_0,esk2_0) != k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X1,X1,X2,X3,X5,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 20:26:40 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.038 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t125_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.38  fof(t85_enumset1, axiom, ![X1, X2, X3, X4]:k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_enumset1)).
% 0.19/0.38  fof(t117_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_enumset1)).
% 0.19/0.38  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.19/0.38  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 0.19/0.38  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 0.19/0.38  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(assume_negation,[status(cth)],[t125_enumset1])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X30, X31, X32, X33]:k5_enumset1(X30,X30,X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t85_enumset1])).
% 0.19/0.38  fof(c_0_13, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_enumset1(X13,X12,X14,X11), inference(variable_rename,[status(thm)],[t117_enumset1])).
% 0.19/0.38  fof(c_0_14, plain, ![X15, X16, X17, X18, X19]:k3_enumset1(X15,X16,X17,X18,X19)=k2_xboole_0(k2_tarski(X15,X16),k1_enumset1(X17,X18,X19)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.19/0.38  fof(c_0_15, plain, ![X23, X24]:k2_enumset1(X23,X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.38  fof(c_0_16, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k5_xboole_0(X6,k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.38  fof(c_0_17, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_18, plain, ![X25, X26, X27, X28, X29]:k5_enumset1(X25,X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 0.19/0.38  fof(c_0_19, plain, ![X8, X9, X10]:k1_enumset1(X8,X9,X10)=k1_enumset1(X10,X9,X8), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_21, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_23, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_27, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_28, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_29, plain, ![X34, X35, X36]:k1_enumset1(X34,X35,X36)=k1_enumset1(X34,X36,X35), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.19/0.38  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X3,X3,X3,X3,X2,X4,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21]), c_0_21])).
% 0.19/0.38  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X4,X5),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_21]), c_0_21]), c_0_21]), c_0_27])).
% 0.19/0.38  cnf(c_0_33, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_26]), c_0_21]), c_0_21])).
% 0.19/0.38  cnf(c_0_34, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk2_0,esk1_0,esk3_0)!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X1,X1,X2,X5,X4,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_32])).
% 0.19/0.38  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k5_enumset1(X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26]), c_0_26]), c_0_21]), c_0_21])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk1_0,esk2_0)!=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X1,X1,X2,X3,X5,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_32])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 41
% 0.19/0.38  # Proof object clause steps            : 20
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 8
% 0.19/0.38  # Proof object clause conjectures      : 5
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 2
% 0.19/0.38  # Proof object simplifying inferences  : 25
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 11
% 0.19/0.38  # Removed in clause preprocessing      : 5
% 0.19/0.38  # Initial clauses in saturation        : 6
% 0.19/0.38  # Processed clauses                    : 78
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 48
% 0.19/0.38  # ...remaining for further processing  : 30
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 808
% 0.19/0.38  # ...of the previous two non-trivial   : 709
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 808
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 20
% 0.19/0.38  #    Positive orientable unit clauses  : 1
% 0.19/0.38  #    Positive unorientable unit clauses: 19
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 0
% 0.19/0.38  # Current number of unprocessed clauses: 643
% 0.19/0.38  # ...number of literals in the above   : 643
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 15
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 210
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 586
% 0.19/0.38  # BW rewrite match successes           : 223
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2796
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.047 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
