%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:39 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (1167 expanded)
%              Number of clauses        :   27 ( 470 expanded)
%              Number of leaves         :    9 ( 348 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 (1167 expanded)
%              Number of equality atoms :   45 (1166 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t71_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_10,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24,X25,X26] : k4_enumset1(X21,X22,X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X22,X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X19,X20] : k3_enumset1(X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X16),k2_enumset1(X17,X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X9,X10,X11] : k1_enumset1(X9,X10,X11) = k2_xboole_0(k1_tarski(X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k4_enumset1(X27,X28,X29,X30,X31,X32) = k2_xboole_0(k3_enumset1(X27,X28,X29,X30,X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_23])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_17]),c_0_18])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X6,X6),k3_enumset1(X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16]),c_0_17]),c_0_18]),c_0_26])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))) = k3_enumset1(X1,X2,X3,X3,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k3_enumset1(X1,X2,X3,X4,X4))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X2,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t71_enumset1])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X2,X2))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

fof(c_0_35,negated_conjecture,(
    k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X1,X2,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X2,X3,X3,X3) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2))) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_32]),c_0_37]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0))) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1))) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk3_0) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:31:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.35  # Version: 2.5pre002
% 0.22/0.35  # No SInE strategy applied
% 0.22/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.22/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.22/0.38  #
% 0.22/0.38  # Preprocessing time       : 0.026 s
% 0.22/0.38  # Presaturation interreduction done
% 0.22/0.38  
% 0.22/0.38  # Proof found!
% 0.22/0.38  # SZS status Theorem
% 0.22/0.38  # SZS output start CNFRefutation
% 0.22/0.38  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.22/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.22/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.22/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.22/0.38  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.22/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.22/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.22/0.38  fof(t71_enumset1, conjecture, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.38  fof(c_0_9, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.22/0.38  fof(c_0_10, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.22/0.38  fof(c_0_11, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.38  fof(c_0_12, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.22/0.38  fof(c_0_13, plain, ![X21, X22, X23, X24, X25, X26]:k4_enumset1(X21,X22,X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X21),k3_enumset1(X22,X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.22/0.38  fof(c_0_14, plain, ![X16, X17, X18, X19, X20]:k3_enumset1(X16,X17,X18,X19,X20)=k2_xboole_0(k1_tarski(X16),k2_enumset1(X17,X18,X19,X20)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.22/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.38  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.38  fof(c_0_19, plain, ![X9, X10, X11]:k1_enumset1(X9,X10,X11)=k2_xboole_0(k1_tarski(X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.22/0.38  fof(c_0_20, plain, ![X27, X28, X29, X30, X31, X32]:k4_enumset1(X27,X28,X29,X30,X31,X32)=k2_xboole_0(k3_enumset1(X27,X28,X29,X30,X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.22/0.38  cnf(c_0_21, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.38  cnf(c_0_22, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.38  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.22/0.38  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.22/0.38  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.22/0.38  cnf(c_0_26, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18])).
% 0.22/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_16]), c_0_17]), c_0_18]), c_0_23])).
% 0.22/0.38  cnf(c_0_28, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_17]), c_0_18])).
% 0.22/0.38  cnf(c_0_29, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X6,X6),k3_enumset1(X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16]), c_0_17]), c_0_18]), c_0_26])).
% 0.22/0.38  cnf(c_0_30, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))=k3_enumset1(X1,X2,X3,X3,X4)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.22/0.38  cnf(c_0_31, plain, (k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k3_enumset1(X1,X2,X3,X4,X4)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_27])).
% 0.22/0.38  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X2,X2,X3)=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.22/0.38  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(assume_negation,[status(cth)],[t71_enumset1])).
% 0.22/0.38  cnf(c_0_34, plain, (k5_xboole_0(k1_enumset1(X1,X2,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X2,X2)))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.22/0.38  fof(c_0_35, negated_conjecture, k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.22/0.38  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X1,X2,X2)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.22/0.38  cnf(c_0_37, plain, (k3_enumset1(X1,X2,X3,X3,X3)=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_28])).
% 0.22/0.38  cnf(c_0_38, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.22/0.38  cnf(c_0_39, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X3),k1_enumset1(X1,X1,X2)))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.22/0.38  cnf(c_0_40, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_32]), c_0_37]), c_0_37])).
% 0.22/0.38  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk1_0,esk1_0),k4_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0)))!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_38, c_0_23])).
% 0.22/0.38  cnf(c_0_42, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1)))=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.22/0.38  cnf(c_0_43, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk2_0,esk3_0)!=k1_enumset1(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_41, c_0_30])).
% 0.22/0.38  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X2,X3)=k1_enumset1(X1,X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 0.22/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), ['proof']).
% 0.22/0.38  # SZS output end CNFRefutation
% 0.22/0.38  # Proof object total steps             : 46
% 0.22/0.38  # Proof object clause steps            : 27
% 0.22/0.38  # Proof object formula steps           : 19
% 0.22/0.38  # Proof object conjectures             : 7
% 0.22/0.38  # Proof object clause conjectures      : 4
% 0.22/0.38  # Proof object formula conjectures     : 3
% 0.22/0.38  # Proof object initial clauses used    : 9
% 0.22/0.38  # Proof object initial formulas used   : 9
% 0.22/0.38  # Proof object generating inferences   : 10
% 0.22/0.38  # Proof object simplifying inferences  : 27
% 0.22/0.38  # Training examples: 0 positive, 0 negative
% 0.22/0.38  # Parsed axioms                        : 9
% 0.22/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.38  # Initial clauses                      : 9
% 0.22/0.38  # Removed in clause preprocessing      : 5
% 0.22/0.38  # Initial clauses in saturation        : 4
% 0.22/0.38  # Processed clauses                    : 62
% 0.22/0.38  # ...of these trivial                  : 10
% 0.22/0.38  # ...subsumed                          : 26
% 0.22/0.38  # ...remaining for further processing  : 26
% 0.22/0.38  # Other redundant clauses eliminated   : 0
% 0.22/0.38  # Clauses deleted for lack of memory   : 0
% 0.22/0.38  # Backward-subsumed                    : 0
% 0.22/0.38  # Backward-rewritten                   : 2
% 0.22/0.38  # Generated clauses                    : 200
% 0.22/0.38  # ...of the previous two non-trivial   : 113
% 0.22/0.38  # Contextual simplify-reflections      : 0
% 0.22/0.38  # Paramodulations                      : 200
% 0.22/0.38  # Factorizations                       : 0
% 0.22/0.38  # Equation resolutions                 : 0
% 0.22/0.38  # Propositional unsat checks           : 0
% 0.22/0.38  #    Propositional check models        : 0
% 0.22/0.38  #    Propositional check unsatisfiable : 0
% 0.22/0.38  #    Propositional clauses             : 0
% 0.22/0.38  #    Propositional clauses after purity: 0
% 0.22/0.38  #    Propositional unsat core size     : 0
% 0.22/0.38  #    Propositional preprocessing time  : 0.000
% 0.22/0.38  #    Propositional encoding time       : 0.000
% 0.22/0.38  #    Propositional solver time         : 0.000
% 0.22/0.38  #    Success case prop preproc time    : 0.000
% 0.22/0.38  #    Success case prop encoding time   : 0.000
% 0.22/0.38  #    Success case prop solver time     : 0.000
% 0.22/0.38  # Current number of processed clauses  : 20
% 0.22/0.38  #    Positive orientable unit clauses  : 14
% 0.22/0.38  #    Positive unorientable unit clauses: 6
% 0.22/0.38  #    Negative unit clauses             : 0
% 0.22/0.38  #    Non-unit-clauses                  : 0
% 0.22/0.38  # Current number of unprocessed clauses: 59
% 0.22/0.38  # ...number of literals in the above   : 59
% 0.22/0.38  # Current number of archived formulas  : 0
% 0.22/0.38  # Current number of archived clauses   : 11
% 0.22/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.38  # Unit Clause-clause subsumption calls : 14
% 0.22/0.38  # Rewrite failures with RHS unbound    : 0
% 0.22/0.38  # BW rewrite match attempts            : 131
% 0.22/0.38  # BW rewrite match successes           : 32
% 0.22/0.38  # Condensation attempts                : 0
% 0.22/0.38  # Condensation successes               : 0
% 0.22/0.38  # Termbank termtop insertions          : 2541
% 0.22/0.38  
% 0.22/0.38  # -------------------------------------------------
% 0.22/0.38  # User time                : 0.028 s
% 0.22/0.38  # System time              : 0.004 s
% 0.22/0.38  # Total time               : 0.032 s
% 0.22/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
