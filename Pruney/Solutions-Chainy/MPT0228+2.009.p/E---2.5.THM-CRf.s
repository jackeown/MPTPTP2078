%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 (  99 expanded)
%              Number of clauses        :   16 (  37 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 ( 114 expanded)
%              Number of equality atoms :   34 ( 103 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t23_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | k4_xboole_0(k2_xboole_0(X6,X7),X7) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_10,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_xboole_0(k1_tarski(X8),k1_tarski(X9)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,negated_conjecture,
    ( esk1_0 != esk2_0
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( X16 = X17
      | r1_xboole_0(k1_tarski(X16),k1_tarski(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_26,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_17]),c_0_21]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X1,X1,X1,X1)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( X1 = X2
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t23_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 0.12/0.37  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.12/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t23_zfmisc_1])).
% 0.12/0.37  fof(c_0_9, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|k4_xboole_0(k2_xboole_0(X6,X7),X7)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.12/0.37  fof(c_0_10, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_xboole_0(k1_tarski(X8),k1_tarski(X9)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.37  fof(c_0_12, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_13, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_14, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, (esk1_0!=esk2_0&k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0))!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.37  cnf(c_0_16, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_18, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0))!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_23, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.37  fof(c_0_25, plain, ![X16, X17]:(X16=X17|r1_xboole_0(k1_tarski(X16),k1_tarski(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_17]), c_0_21]), c_0_21]), c_0_21]), c_0_21])).
% 0.12/0.37  cnf(c_0_27, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X2)))=k2_enumset1(X1,X1,X1,X1)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_28, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_30, plain, (X1=X2|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 33
% 0.12/0.37  # Proof object clause steps            : 16
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 8
% 0.12/0.37  # Proof object clause conjectures      : 5
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 3
% 0.12/0.37  # Proof object simplifying inferences  : 26
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 9
% 0.12/0.37  # Removed in clause preprocessing      : 4
% 0.12/0.37  # Initial clauses in saturation        : 5
% 0.12/0.37  # Processed clauses                    : 12
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 12
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 4
% 0.12/0.37  # ...of the previous two non-trivial   : 3
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 4
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 7
% 0.12/0.37  #    Positive orientable unit clauses  : 1
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 3
% 0.12/0.37  # Current number of unprocessed clauses: 1
% 0.12/0.37  # ...number of literals in the above   : 2
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 9
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 509
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.000 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
