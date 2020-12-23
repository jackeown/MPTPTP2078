%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:47 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  80 expanded)
%              Number of clauses        :   17 (  31 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  80 expanded)
%              Number of equality atoms :   37 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(c_0_10,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] : k6_enumset1(X22,X23,X24,X25,X26,X27,X28,X29) = k2_xboole_0(k2_tarski(X22,X23),k4_enumset1(X24,X25,X26,X27,X28,X29)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_11,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,plain,(
    ! [X48,X49,X50,X51,X52] : k4_enumset1(X48,X48,X49,X50,X51,X52) = k3_enumset1(X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t74_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] : k5_enumset1(X15,X16,X17,X18,X19,X20,X21) = k2_xboole_0(k1_tarski(X15),k4_enumset1(X16,X17,X18,X19,X20,X21)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

fof(c_0_17,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12,X13,X14] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k2_tarski(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

fof(c_0_19,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k2_tarski(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,negated_conjecture,(
    k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_enumset1(X7,X7,X7,X7,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.38  fof(t74_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.38  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 0.14/0.38  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.14/0.38  fof(c_0_10, plain, ![X22, X23, X24, X25, X26, X27, X28, X29]:k6_enumset1(X22,X23,X24,X25,X26,X27,X28,X29)=k2_xboole_0(k2_tarski(X22,X23),k4_enumset1(X24,X25,X26,X27,X28,X29)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.14/0.38  fof(c_0_11, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_12, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_13, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  fof(c_0_14, plain, ![X48, X49, X50, X51, X52]:k4_enumset1(X48,X48,X49,X50,X51,X52)=k3_enumset1(X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t74_enumset1])).
% 0.14/0.38  fof(c_0_16, plain, ![X15, X16, X17, X18, X19, X20, X21]:k5_enumset1(X15,X16,X17,X18,X19,X20,X21)=k2_xboole_0(k1_tarski(X15),k4_enumset1(X16,X17,X18,X19,X20,X21)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 0.14/0.38  fof(c_0_17, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_18, plain, ![X9, X10, X11, X12, X13, X14]:k4_enumset1(X9,X10,X11,X12,X13,X14)=k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k2_tarski(X13,X14)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.14/0.38  fof(c_0_19, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k4_enumset1(X30,X31,X32,X33,X34,X35),k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.14/0.38  cnf(c_0_20, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_24, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_25, negated_conjecture, k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.14/0.38  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_29, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_30, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.14/0.38  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_21]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24])).
% 0.14/0.38  cnf(c_0_34, plain, (k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_enumset1(X7,X7,X7,X7,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_30])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_36, plain, (k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X2,X3,X4,X5,X6))=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 38
% 0.14/0.38  # Proof object clause steps            : 17
% 0.14/0.38  # Proof object formula steps           : 21
% 0.14/0.38  # Proof object conjectures             : 6
% 0.14/0.38  # Proof object clause conjectures      : 3
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 1
% 0.14/0.38  # Proof object simplifying inferences  : 23
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 10
% 0.14/0.38  # Removed in clause preprocessing      : 7
% 0.14/0.38  # Initial clauses in saturation        : 3
% 0.14/0.38  # Processed clauses                    : 7
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 7
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 6
% 0.14/0.38  # ...of the previous two non-trivial   : 4
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 6
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 3
% 0.14/0.38  #    Positive orientable unit clauses  : 2
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 0
% 0.14/0.38  # Current number of unprocessed clauses: 3
% 0.14/0.38  # ...number of literals in the above   : 3
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 11
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 14
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 693
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.030 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
