%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:46 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   33 (  88 expanded)
%              Number of clauses        :   14 (  33 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  88 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(t74_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(c_0_9,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15,X16,X17] : k4_enumset1(X12,X13,X14,X15,X16,X17) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_tarski(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

fof(c_0_12,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X34,X35,X36,X37,X38] : k4_enumset1(X34,X34,X35,X36,X37,X38) = k3_enumset1(X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24] : k5_enumset1(X18,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t74_enumset1])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,negated_conjecture,(
    k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X1,X1,X2,X3,X4,X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.28  % Computer   : n001.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 20:11:45 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.28  # Version: 2.5pre002
% 0.09/0.29  # No SInE strategy applied
% 0.09/0.29  # Trying AutoSched0 for 299 seconds
% 0.09/0.30  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.09/0.30  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.09/0.30  #
% 0.09/0.30  # Preprocessing time       : 0.018 s
% 0.09/0.30  # Presaturation interreduction done
% 0.09/0.30  
% 0.09/0.30  # Proof found!
% 0.09/0.30  # SZS status Theorem
% 0.09/0.30  # SZS output start CNFRefutation
% 0.09/0.30  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.09/0.30  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.09/0.30  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 0.09/0.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.09/0.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.09/0.30  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.09/0.30  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.09/0.30  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 0.09/0.30  fof(t74_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.09/0.30  fof(c_0_9, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.09/0.30  fof(c_0_10, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.09/0.30  fof(c_0_11, plain, ![X12, X13, X14, X15, X16, X17]:k4_enumset1(X12,X13,X14,X15,X16,X17)=k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_tarski(X16,X17)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.09/0.30  fof(c_0_12, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.09/0.30  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.09/0.30  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.30  fof(c_0_15, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.09/0.30  fof(c_0_16, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.09/0.30  fof(c_0_17, plain, ![X34, X35, X36, X37, X38]:k4_enumset1(X34,X34,X35,X36,X37,X38)=k3_enumset1(X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.09/0.30  fof(c_0_18, plain, ![X18, X19, X20, X21, X22, X23, X24]:k5_enumset1(X18,X19,X20,X21,X22,X23,X24)=k2_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.09/0.30  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t74_enumset1])).
% 0.09/0.30  cnf(c_0_20, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.30  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.09/0.30  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.09/0.30  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.09/0.30  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.09/0.30  cnf(c_0_25, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.09/0.30  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.09/0.30  fof(c_0_27, negated_conjecture, k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.09/0.30  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X1,X1,X1,X2,X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.09/0.30  cnf(c_0_29, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k3_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X7),k4_enumset1(X1,X1,X2,X3,X4,X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.09/0.30  cnf(c_0_30, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.09/0.30  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.09/0.30  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.09/0.30  # SZS output end CNFRefutation
% 0.09/0.30  # Proof object total steps             : 33
% 0.09/0.30  # Proof object clause steps            : 14
% 0.09/0.30  # Proof object formula steps           : 19
% 0.09/0.30  # Proof object conjectures             : 5
% 0.09/0.30  # Proof object clause conjectures      : 2
% 0.09/0.30  # Proof object formula conjectures     : 3
% 0.09/0.30  # Proof object initial clauses used    : 9
% 0.09/0.30  # Proof object initial formulas used   : 9
% 0.09/0.30  # Proof object generating inferences   : 0
% 0.09/0.30  # Proof object simplifying inferences  : 26
% 0.09/0.30  # Training examples: 0 positive, 0 negative
% 0.09/0.30  # Parsed axioms                        : 9
% 0.09/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.09/0.30  # Initial clauses                      : 9
% 0.09/0.30  # Removed in clause preprocessing      : 6
% 0.09/0.30  # Initial clauses in saturation        : 3
% 0.09/0.30  # Processed clauses                    : 4
% 0.09/0.30  # ...of these trivial                  : 0
% 0.09/0.30  # ...subsumed                          : 0
% 0.09/0.30  # ...remaining for further processing  : 4
% 0.09/0.30  # Other redundant clauses eliminated   : 0
% 0.09/0.30  # Clauses deleted for lack of memory   : 0
% 0.09/0.30  # Backward-subsumed                    : 0
% 0.09/0.30  # Backward-rewritten                   : 2
% 0.09/0.30  # Generated clauses                    : 0
% 0.09/0.30  # ...of the previous two non-trivial   : 1
% 0.09/0.30  # Contextual simplify-reflections      : 0
% 0.09/0.30  # Paramodulations                      : 0
% 0.09/0.30  # Factorizations                       : 0
% 0.09/0.30  # Equation resolutions                 : 0
% 0.09/0.30  # Propositional unsat checks           : 0
% 0.09/0.30  #    Propositional check models        : 0
% 0.09/0.30  #    Propositional check unsatisfiable : 0
% 0.09/0.30  #    Propositional clauses             : 0
% 0.09/0.30  #    Propositional clauses after purity: 0
% 0.09/0.30  #    Propositional unsat core size     : 0
% 0.09/0.30  #    Propositional preprocessing time  : 0.000
% 0.09/0.30  #    Propositional encoding time       : 0.000
% 0.09/0.30  #    Propositional solver time         : 0.000
% 0.09/0.30  #    Success case prop preproc time    : 0.000
% 0.09/0.30  #    Success case prop encoding time   : 0.000
% 0.09/0.30  #    Success case prop solver time     : 0.000
% 0.09/0.30  # Current number of processed clauses  : 2
% 0.09/0.30  #    Positive orientable unit clauses  : 2
% 0.09/0.30  #    Positive unorientable unit clauses: 0
% 0.09/0.30  #    Negative unit clauses             : 0
% 0.09/0.30  #    Non-unit-clauses                  : 0
% 0.09/0.30  # Current number of unprocessed clauses: 0
% 0.09/0.30  # ...number of literals in the above   : 0
% 0.09/0.30  # Current number of archived formulas  : 0
% 0.09/0.30  # Current number of archived clauses   : 8
% 0.09/0.30  # Clause-clause subsumption calls (NU) : 0
% 0.09/0.30  # Rec. Clause-clause subsumption calls : 0
% 0.09/0.30  # Non-unit clause-clause subsumptions  : 0
% 0.09/0.30  # Unit Clause-clause subsumption calls : 0
% 0.09/0.30  # Rewrite failures with RHS unbound    : 0
% 0.09/0.30  # BW rewrite match attempts            : 3
% 0.09/0.30  # BW rewrite match successes           : 2
% 0.09/0.30  # Condensation attempts                : 0
% 0.09/0.30  # Condensation successes               : 0
% 0.09/0.30  # Termbank termtop insertions          : 540
% 0.09/0.30  
% 0.09/0.30  # -------------------------------------------------
% 0.09/0.30  # User time                : 0.019 s
% 0.09/0.30  # System time              : 0.002 s
% 0.09/0.30  # Total time               : 0.021 s
% 0.09/0.30  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
