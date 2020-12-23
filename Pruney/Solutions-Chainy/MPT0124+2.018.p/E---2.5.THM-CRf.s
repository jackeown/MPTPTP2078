%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:02 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 104 expanded)
%              Number of clauses        :   17 (  44 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 ( 115 expanded)
%              Number of equality atoms :   31 ( 103 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_7,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_8,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] : k4_xboole_0(X11,k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X13)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_12]),c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_12]),c_0_12])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k5_xboole_0(k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_12]),c_0_16])).

cnf(c_0_23,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_27,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0)))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:31 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 1.05/1.32  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 1.05/1.32  # and selection function SelectNewComplexAHP.
% 1.05/1.32  #
% 1.05/1.32  # Preprocessing time       : 0.026 s
% 1.05/1.32  
% 1.05/1.32  # Proof found!
% 1.05/1.32  # SZS status Theorem
% 1.05/1.32  # SZS output start CNFRefutation
% 1.05/1.32  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 1.05/1.32  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.05/1.32  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 1.05/1.32  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.05/1.32  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.05/1.32  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.05/1.32  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.05/1.32  fof(c_0_7, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 1.05/1.32  fof(c_0_8, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.05/1.32  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 1.05/1.32  fof(c_0_10, plain, ![X11, X12, X13]:k4_xboole_0(X11,k4_xboole_0(X12,X13))=k2_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(X11,X13)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.05/1.32  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.05/1.32  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.05/1.32  fof(c_0_13, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.05/1.32  fof(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 1.05/1.32  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.05/1.32  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 1.05/1.32  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.05/1.32  cnf(c_0_18, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.05/1.32  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_12]), c_0_16])).
% 1.05/1.32  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_12]), c_0_12])).
% 1.05/1.32  fof(c_0_21, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 1.05/1.32  cnf(c_0_22, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k5_xboole_0(k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_12]), c_0_16])).
% 1.05/1.32  cnf(c_0_23, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.05/1.32  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.05/1.32  cnf(c_0_25, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.05/1.32  fof(c_0_26, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.05/1.32  cnf(c_0_27, negated_conjecture, (k5_xboole_0(k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0))))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20]), c_0_20]), c_0_20])).
% 1.05/1.32  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 1.05/1.32  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.05/1.32  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.05/1.32  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_20]), c_0_29]), c_0_30])]), ['proof']).
% 1.05/1.32  # SZS output end CNFRefutation
% 1.05/1.32  # Proof object total steps             : 32
% 1.05/1.32  # Proof object clause steps            : 17
% 1.05/1.32  # Proof object formula steps           : 15
% 1.05/1.32  # Proof object conjectures             : 9
% 1.05/1.32  # Proof object clause conjectures      : 6
% 1.05/1.32  # Proof object formula conjectures     : 3
% 1.05/1.32  # Proof object initial clauses used    : 8
% 1.05/1.32  # Proof object initial formulas used   : 7
% 1.05/1.32  # Proof object generating inferences   : 3
% 1.05/1.32  # Proof object simplifying inferences  : 15
% 1.05/1.32  # Training examples: 0 positive, 0 negative
% 1.05/1.32  # Parsed axioms                        : 7
% 1.05/1.32  # Removed by relevancy pruning/SinE    : 0
% 1.05/1.32  # Initial clauses                      : 9
% 1.05/1.32  # Removed in clause preprocessing      : 2
% 1.05/1.32  # Initial clauses in saturation        : 7
% 1.05/1.32  # Processed clauses                    : 4888
% 1.05/1.32  # ...of these trivial                  : 769
% 1.05/1.32  # ...subsumed                          : 3285
% 1.05/1.32  # ...remaining for further processing  : 834
% 1.05/1.32  # Other redundant clauses eliminated   : 0
% 1.05/1.32  # Clauses deleted for lack of memory   : 0
% 1.05/1.32  # Backward-subsumed                    : 4
% 1.05/1.32  # Backward-rewritten                   : 327
% 1.05/1.32  # Generated clauses                    : 116393
% 1.05/1.32  # ...of the previous two non-trivial   : 81531
% 1.05/1.32  # Contextual simplify-reflections      : 0
% 1.05/1.32  # Paramodulations                      : 116387
% 1.05/1.32  # Factorizations                       : 0
% 1.05/1.32  # Equation resolutions                 : 6
% 1.05/1.32  # Propositional unsat checks           : 0
% 1.05/1.32  #    Propositional check models        : 0
% 1.05/1.32  #    Propositional check unsatisfiable : 0
% 1.05/1.32  #    Propositional clauses             : 0
% 1.05/1.32  #    Propositional clauses after purity: 0
% 1.05/1.32  #    Propositional unsat core size     : 0
% 1.05/1.32  #    Propositional preprocessing time  : 0.000
% 1.05/1.32  #    Propositional encoding time       : 0.000
% 1.05/1.32  #    Propositional solver time         : 0.000
% 1.05/1.32  #    Success case prop preproc time    : 0.000
% 1.05/1.32  #    Success case prop encoding time   : 0.000
% 1.05/1.32  #    Success case prop solver time     : 0.000
% 1.05/1.32  # Current number of processed clauses  : 503
% 1.05/1.32  #    Positive orientable unit clauses  : 223
% 1.05/1.32  #    Positive unorientable unit clauses: 22
% 1.05/1.32  #    Negative unit clauses             : 0
% 1.05/1.32  #    Non-unit-clauses                  : 258
% 1.05/1.32  # Current number of unprocessed clauses: 75098
% 1.05/1.32  # ...number of literals in the above   : 114185
% 1.05/1.32  # Current number of archived formulas  : 0
% 1.05/1.32  # Current number of archived clauses   : 333
% 1.05/1.32  # Clause-clause subsumption calls (NU) : 37745
% 1.05/1.32  # Rec. Clause-clause subsumption calls : 37745
% 1.05/1.32  # Non-unit clause-clause subsumptions  : 2529
% 1.05/1.32  # Unit Clause-clause subsumption calls : 7513
% 1.05/1.32  # Rewrite failures with RHS unbound    : 0
% 1.05/1.32  # BW rewrite match attempts            : 12514
% 1.05/1.32  # BW rewrite match successes           : 410
% 1.05/1.32  # Condensation attempts                : 0
% 1.05/1.32  # Condensation successes               : 0
% 1.05/1.32  # Termbank termtop insertions          : 3269678
% 1.16/1.33  
% 1.16/1.33  # -------------------------------------------------
% 1.16/1.33  # User time                : 0.942 s
% 1.16/1.33  # System time              : 0.037 s
% 1.16/1.33  # Total time               : 0.980 s
% 1.16/1.33  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
