%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:45 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 194 expanded)
%              Number of clauses        :   23 (  87 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 194 expanded)
%              Number of equality atoms :   45 ( 193 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t67_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(t74_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18,X19,X20] : k4_enumset1(X15,X16,X17,X18,X19,X20) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X25] : k3_enumset1(X21,X22,X23,X24,X25) = k2_xboole_0(k2_tarski(X21,X22),k1_enumset1(X23,X24,X25)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_17,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k5_enumset1(X32,X33,X34,X35,X36,X37,X38) = k2_xboole_0(k4_enumset1(X32,X33,X34,X35,X36,X37),k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

fof(c_0_19,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k4_enumset1(X39,X40,X41,X42,X43,X44),k2_tarski(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t67_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k4_enumset1(X26,X27,X28,X29,X30,X31) = k2_xboole_0(k3_enumset1(X26,X27,X28,X29,X30),k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,negated_conjecture,(
    k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_21])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_26]),c_0_21]),c_0_29]),c_0_29])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X8),k3_xboole_0(k1_enumset1(X7,X7,X8),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26]),c_0_21]),c_0_29]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28]),c_0_26]),c_0_21]),c_0_33]),c_0_33]),c_0_29])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk1_0,esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)))) != k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))) = k5_enumset1(X1,X1,X2,X3,X4,X5,X6) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:46:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.11/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.026 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.11/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.11/0.35  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 0.11/0.35  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.11/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.35  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 0.11/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.35  fof(t67_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 0.11/0.35  fof(t74_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.11/0.35  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.11/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.11/0.35  fof(c_0_11, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.11/0.35  fof(c_0_12, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.11/0.35  fof(c_0_13, plain, ![X15, X16, X17, X18, X19, X20]:k4_enumset1(X15,X16,X17,X18,X19,X20)=k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.11/0.35  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.35  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  fof(c_0_16, plain, ![X21, X22, X23, X24, X25]:k3_enumset1(X21,X22,X23,X24,X25)=k2_xboole_0(k2_tarski(X21,X22),k1_enumset1(X23,X24,X25)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.11/0.35  fof(c_0_17, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.35  fof(c_0_18, plain, ![X32, X33, X34, X35, X36, X37, X38]:k5_enumset1(X32,X33,X34,X35,X36,X37,X38)=k2_xboole_0(k4_enumset1(X32,X33,X34,X35,X36,X37),k1_tarski(X38)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.11/0.35  fof(c_0_19, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.35  cnf(c_0_20, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.35  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.11/0.35  fof(c_0_22, plain, ![X39, X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X39,X40,X41,X42,X43,X44,X45,X46)=k2_xboole_0(k4_enumset1(X39,X40,X41,X42,X43,X44),k2_tarski(X45,X46)), inference(variable_rename,[status(thm)],[t67_enumset1])).
% 0.11/0.35  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t74_enumset1])).
% 0.11/0.35  fof(c_0_24, plain, ![X26, X27, X28, X29, X30, X31]:k4_enumset1(X26,X27,X28,X29,X30,X31)=k2_xboole_0(k3_enumset1(X26,X27,X28,X29,X30),k1_tarski(X31)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.11/0.35  cnf(c_0_25, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.35  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.35  cnf(c_0_27, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.35  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.35  cnf(c_0_29, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.11/0.35  cnf(c_0_30, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.35  fof(c_0_31, negated_conjecture, k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.11/0.35  cnf(c_0_32, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.35  cnf(c_0_33, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_21])).
% 0.11/0.35  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X7),k3_xboole_0(k1_enumset1(X7,X7,X7),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_26]), c_0_21]), c_0_29]), c_0_29])).
% 0.11/0.35  cnf(c_0_35, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))),k5_xboole_0(k1_enumset1(X7,X7,X8),k3_xboole_0(k1_enumset1(X7,X7,X8),k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_26]), c_0_21]), c_0_29]), c_0_29])).
% 0.11/0.35  cnf(c_0_36, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.11/0.35  fof(c_0_37, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.11/0.35  cnf(c_0_38, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))),k5_xboole_0(k1_enumset1(X6,X6,X6),k3_xboole_0(k1_enumset1(X6,X6,X6),k5_xboole_0(k1_enumset1(X1,X1,X2),k5_xboole_0(k1_enumset1(X3,X4,X5),k3_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_28]), c_0_26]), c_0_21]), c_0_33]), c_0_33]), c_0_29])).
% 0.11/0.35  cnf(c_0_39, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.11/0.35  cnf(c_0_40, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_enumset1(esk1_0,esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_36, c_0_29])).
% 0.11/0.35  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.11/0.35  cnf(c_0_42, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35]), c_0_39])).
% 0.11/0.35  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k5_xboole_0(k1_enumset1(esk4_0,esk5_0,esk6_0),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0))))!=k5_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.11/0.35  cnf(c_0_44, plain, (k5_xboole_0(k1_enumset1(X1,X2,X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))))=k5_enumset1(X1,X1,X2,X3,X4,X5,X6)), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.11/0.35  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 46
% 0.11/0.35  # Proof object clause steps            : 23
% 0.11/0.35  # Proof object formula steps           : 23
% 0.11/0.35  # Proof object conjectures             : 7
% 0.11/0.35  # Proof object clause conjectures      : 4
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 11
% 0.11/0.35  # Proof object initial formulas used   : 11
% 0.11/0.35  # Proof object generating inferences   : 1
% 0.11/0.35  # Proof object simplifying inferences  : 26
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 11
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 11
% 0.11/0.35  # Removed in clause preprocessing      : 6
% 0.11/0.35  # Initial clauses in saturation        : 5
% 0.11/0.35  # Processed clauses                    : 12
% 0.11/0.35  # ...of these trivial                  : 0
% 0.11/0.35  # ...subsumed                          : 0
% 0.11/0.35  # ...remaining for further processing  : 12
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 3
% 0.11/0.35  # Generated clauses                    : 4
% 0.11/0.35  # ...of the previous two non-trivial   : 4
% 0.11/0.35  # Contextual simplify-reflections      : 0
% 0.11/0.35  # Paramodulations                      : 4
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 4
% 0.11/0.35  #    Positive orientable unit clauses  : 3
% 0.11/0.35  #    Positive unorientable unit clauses: 1
% 0.11/0.35  #    Negative unit clauses             : 0
% 0.11/0.35  #    Non-unit-clauses                  : 0
% 0.11/0.35  # Current number of unprocessed clauses: 2
% 0.11/0.35  # ...number of literals in the above   : 2
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 14
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.35  # Unit Clause-clause subsumption calls : 0
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 7
% 0.11/0.35  # BW rewrite match successes           : 3
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 949
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.022 s
% 0.11/0.35  # System time              : 0.009 s
% 0.11/0.35  # Total time               : 0.031 s
% 0.11/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
