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
% DateTime   : Thu Dec  3 10:43:57 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 188 expanded)
%              Number of clauses        :   16 (  73 expanded)
%              Number of leaves         :    7 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 ( 199 expanded)
%              Number of equality atoms :   39 ( 198 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
        & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    inference(assume_negation,[status(cth)],[t132_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))
    | k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0)) != k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_12,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( k2_zfmisc_1(k2_xboole_0(X17,X18),X19) = k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))
      & k2_zfmisc_1(X19,k2_xboole_0(X17,X18)) = k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))
    | k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0)) != k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != k3_tarski(k2_enumset1(k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))
    | k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) != k3_tarski(k2_enumset1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_17]),c_0_17]),c_0_13]),c_0_13]),c_0_13]),c_0_13]),c_0_13]),c_0_13]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3))) = k3_tarski(k2_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X5,X6,X7,X8] : k2_enumset1(X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_25,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) != k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(esk3_0,k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))) != k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X3) = k3_tarski(k2_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0) != k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(esk3_0,k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))) != k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_13]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:54:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.22/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.025 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t132_zfmisc_1, conjecture, ![X1, X2, X3]:(k2_zfmisc_1(k2_tarski(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))&k2_zfmisc_1(X3,k2_tarski(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 0.22/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.22/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.22/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.39  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.22/0.39  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.22/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(k2_zfmisc_1(k2_tarski(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))&k2_zfmisc_1(X3,k2_tarski(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t132_zfmisc_1])).
% 0.22/0.39  fof(c_0_8, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.22/0.39  fof(c_0_9, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.39  fof(c_0_10, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))|k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0))!=k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.22/0.39  fof(c_0_11, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.22/0.39  cnf(c_0_12, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.39  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.39  fof(c_0_14, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.39  fof(c_0_15, plain, ![X17, X18, X19]:(k2_zfmisc_1(k2_xboole_0(X17,X18),X19)=k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))&k2_zfmisc_1(X19,k2_xboole_0(X17,X18))=k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.22/0.39  cnf(c_0_16, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))|k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0))!=k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.39  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.39  cnf(c_0_18, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.22/0.39  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.39  cnf(c_0_20, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=k3_tarski(k2_enumset1(k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))|k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)!=k3_tarski(k2_enumset1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_17]), c_0_17]), c_0_13]), c_0_13]), c_0_13]), c_0_13]), c_0_13]), c_0_13]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.22/0.39  cnf(c_0_22, plain, (k2_zfmisc_1(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))=k3_tarski(k2_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.22/0.39  cnf(c_0_23, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  fof(c_0_24, plain, ![X5, X6, X7, X8]:k2_enumset1(X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.22/0.39  cnf(c_0_25, negated_conjecture, (k3_tarski(k2_enumset1(k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))!=k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(esk3_0,k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))!=k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.22/0.39  cnf(c_0_26, plain, (k2_zfmisc_1(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X3)=k3_tarski(k2_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.22/0.39  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.39  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))),esk3_0)!=k2_zfmisc_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(esk3_0,k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))!=k2_zfmisc_1(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.22/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_13]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.22/0.39  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 31
% 0.22/0.39  # Proof object clause steps            : 16
% 0.22/0.39  # Proof object formula steps           : 15
% 0.22/0.39  # Proof object conjectures             : 8
% 0.22/0.39  # Proof object clause conjectures      : 5
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 8
% 0.22/0.39  # Proof object initial formulas used   : 7
% 0.22/0.39  # Proof object generating inferences   : 0
% 0.22/0.39  # Proof object simplifying inferences  : 43
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 7
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 8
% 0.22/0.39  # Removed in clause preprocessing      : 4
% 0.22/0.39  # Initial clauses in saturation        : 4
% 0.22/0.39  # Processed clauses                    : 5
% 0.22/0.39  # ...of these trivial                  : 0
% 0.22/0.39  # ...subsumed                          : 0
% 0.22/0.39  # ...remaining for further processing  : 5
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 2
% 0.22/0.39  # Generated clauses                    : 0
% 0.22/0.39  # ...of the previous two non-trivial   : 1
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 0
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 3
% 0.22/0.39  #    Positive orientable unit clauses  : 3
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 0
% 0.22/0.39  #    Non-unit-clauses                  : 0
% 0.22/0.39  # Current number of unprocessed clauses: 0
% 0.22/0.39  # ...number of literals in the above   : 0
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 6
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.39  # Unit Clause-clause subsumption calls : 0
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 3
% 0.22/0.39  # BW rewrite match successes           : 2
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 625
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.026 s
% 0.22/0.39  # System time              : 0.003 s
% 0.22/0.39  # Total time               : 0.029 s
% 0.22/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
