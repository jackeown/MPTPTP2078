%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:59 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  78 expanded)
%              Number of clauses        :   15 (  29 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  78 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_enumset1,conjecture,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t91_enumset1])).

fof(c_0_11,plain,(
    ! [X10,X11,X12] : k1_enumset1(X10,X11,X12) = k2_xboole_0(k2_tarski(X10,X11),k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_12,plain,(
    ! [X23,X24] : k2_enumset1(X23,X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_13,plain,(
    ! [X40] : k3_enumset1(X40,X40,X40,X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_14,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X25,X26,X27,X28] : k4_enumset1(X25,X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_17,plain,(
    ! [X29,X30,X31,X32,X33] : k5_enumset1(X29,X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_18,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k6_enumset1(X34,X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] : k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k2_tarski(X13,X14),k3_enumset1(X15,X16,X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_20,negated_conjecture,(
    k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_24]),c_0_26]),c_0_26]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_23]),c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X2,X3,X3,X3,X3,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t91_enumset1, conjecture, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 0.14/0.37  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.14/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.14/0.37  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 0.14/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.14/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.37  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 0.14/0.37  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 0.14/0.37  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.14/0.37  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.14/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t91_enumset1])).
% 0.14/0.37  fof(c_0_11, plain, ![X10, X11, X12]:k1_enumset1(X10,X11,X12)=k2_xboole_0(k2_tarski(X10,X11),k1_tarski(X12)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.14/0.37  fof(c_0_12, plain, ![X23, X24]:k2_enumset1(X23,X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.14/0.37  fof(c_0_13, plain, ![X40]:k3_enumset1(X40,X40,X40,X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.14/0.37  fof(c_0_14, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k5_xboole_0(X8,k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.14/0.37  fof(c_0_15, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.37  fof(c_0_16, plain, ![X25, X26, X27, X28]:k4_enumset1(X25,X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 0.14/0.37  fof(c_0_17, plain, ![X29, X30, X31, X32, X33]:k5_enumset1(X29,X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 0.14/0.37  fof(c_0_18, plain, ![X34, X35, X36, X37, X38, X39]:k6_enumset1(X34,X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.14/0.37  fof(c_0_19, plain, ![X13, X14, X15, X16, X17, X18, X19]:k5_enumset1(X13,X14,X15,X16,X17,X18,X19)=k2_xboole_0(k2_tarski(X13,X14),k3_enumset1(X15,X16,X17,X18,X19)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.14/0.37  fof(c_0_20, negated_conjecture, k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.14/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_27, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_28, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_29, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 0.14/0.37  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_24]), c_0_26]), c_0_26]), c_0_27]), c_0_28]), c_0_28])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_23]), c_0_27]), c_0_28])).
% 0.14/0.37  cnf(c_0_34, plain, (k5_enumset1(X1,X2,X3,X3,X3,X3,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 36
% 0.14/0.37  # Proof object clause steps            : 15
% 0.14/0.37  # Proof object formula steps           : 21
% 0.14/0.37  # Proof object conjectures             : 6
% 0.14/0.37  # Proof object clause conjectures      : 3
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 10
% 0.14/0.37  # Proof object generating inferences   : 0
% 0.14/0.37  # Proof object simplifying inferences  : 24
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 10
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 10
% 0.14/0.37  # Removed in clause preprocessing      : 7
% 0.14/0.37  # Initial clauses in saturation        : 3
% 0.14/0.37  # Processed clauses                    : 3
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 3
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 0
% 0.14/0.37  # ...of the previous two non-trivial   : 0
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 0
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 2
% 0.14/0.37  #    Positive orientable unit clauses  : 1
% 0.14/0.37  #    Positive unorientable unit clauses: 1
% 0.14/0.37  #    Negative unit clauses             : 0
% 0.14/0.37  #    Non-unit-clauses                  : 0
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 8
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 5
% 0.14/0.37  # BW rewrite match successes           : 3
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 476
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.001 s
% 0.14/0.37  # Total time               : 0.029 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
