%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:25 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   34 (  82 expanded)
%              Number of clauses        :   19 (  35 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  87 expanded)
%              Number of equality atoms :   31 (  79 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t53_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_7,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k4_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_8,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t53_xboole_1])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_14,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_15,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,negated_conjecture,(
    k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4))) = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k1_xboole_0,X3))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_18]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))))) != k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_18])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 3.04/3.22  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 3.04/3.22  # and selection function SelectNewComplexAHP.
% 3.04/3.22  #
% 3.04/3.22  # Preprocessing time       : 0.027 s
% 3.04/3.22  # Presaturation interreduction done
% 3.04/3.22  
% 3.04/3.22  # Proof found!
% 3.04/3.22  # SZS status Theorem
% 3.04/3.22  # SZS output start CNFRefutation
% 3.04/3.22  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.04/3.22  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.04/3.22  fof(t53_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 3.04/3.22  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.04/3.22  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.04/3.22  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.04/3.22  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.04/3.22  fof(c_0_7, plain, ![X14, X15, X16]:k3_xboole_0(X14,k4_xboole_0(X15,X16))=k4_xboole_0(k3_xboole_0(X14,X15),X16), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 3.04/3.22  fof(c_0_8, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.04/3.22  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t53_xboole_1])).
% 3.04/3.22  cnf(c_0_10, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.04/3.22  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.04/3.22  fof(c_0_12, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.04/3.22  fof(c_0_13, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 3.04/3.22  fof(c_0_14, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.04/3.22  fof(c_0_15, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 3.04/3.22  fof(c_0_16, negated_conjecture, k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 3.04/3.22  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 3.04/3.22  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.04/3.22  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.04/3.22  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.04/3.22  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.04/3.22  cnf(c_0_22, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.04/3.22  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 3.04/3.22  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 3.04/3.22  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 3.04/3.22  cnf(c_0_26, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_18]), c_0_18]), c_0_18])).
% 3.04/3.22  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_22, c_0_11])).
% 3.04/3.22  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)))=k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_23]), c_0_18]), c_0_18]), c_0_18])).
% 3.04/3.22  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 3.04/3.22  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k1_xboole_0,X3)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_18]), c_0_26])).
% 3.04/3.22  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)))))!=k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_18])).
% 3.04/3.22  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 3.04/3.22  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 3.04/3.22  # SZS output end CNFRefutation
% 3.04/3.22  # Proof object total steps             : 34
% 3.04/3.22  # Proof object clause steps            : 19
% 3.04/3.22  # Proof object formula steps           : 15
% 3.04/3.22  # Proof object conjectures             : 7
% 3.04/3.22  # Proof object clause conjectures      : 4
% 3.04/3.22  # Proof object formula conjectures     : 3
% 3.04/3.22  # Proof object initial clauses used    : 7
% 3.04/3.22  # Proof object initial formulas used   : 7
% 3.04/3.22  # Proof object generating inferences   : 6
% 3.04/3.22  # Proof object simplifying inferences  : 17
% 3.04/3.22  # Training examples: 0 positive, 0 negative
% 3.04/3.22  # Parsed axioms                        : 7
% 3.04/3.22  # Removed by relevancy pruning/SinE    : 0
% 3.04/3.22  # Initial clauses                      : 8
% 3.04/3.22  # Removed in clause preprocessing      : 1
% 3.04/3.22  # Initial clauses in saturation        : 7
% 3.04/3.22  # Processed clauses                    : 6417
% 3.04/3.22  # ...of these trivial                  : 2996
% 3.04/3.22  # ...subsumed                          : 146
% 3.04/3.22  # ...remaining for further processing  : 3275
% 3.04/3.22  # Other redundant clauses eliminated   : 0
% 3.04/3.22  # Clauses deleted for lack of memory   : 0
% 3.04/3.22  # Backward-subsumed                    : 0
% 3.04/3.22  # Backward-rewritten                   : 259
% 3.04/3.22  # Generated clauses                    : 636468
% 3.04/3.22  # ...of the previous two non-trivial   : 219835
% 3.04/3.22  # Contextual simplify-reflections      : 0
% 3.04/3.22  # Paramodulations                      : 636461
% 3.04/3.22  # Factorizations                       : 0
% 3.04/3.22  # Equation resolutions                 : 7
% 3.04/3.22  # Propositional unsat checks           : 0
% 3.04/3.22  #    Propositional check models        : 0
% 3.04/3.22  #    Propositional check unsatisfiable : 0
% 3.04/3.22  #    Propositional clauses             : 0
% 3.04/3.22  #    Propositional clauses after purity: 0
% 3.04/3.22  #    Propositional unsat core size     : 0
% 3.04/3.22  #    Propositional preprocessing time  : 0.000
% 3.04/3.22  #    Propositional encoding time       : 0.000
% 3.04/3.22  #    Propositional solver time         : 0.000
% 3.04/3.22  #    Success case prop preproc time    : 0.000
% 3.04/3.22  #    Success case prop encoding time   : 0.000
% 3.04/3.22  #    Success case prop solver time     : 0.000
% 3.04/3.22  # Current number of processed clauses  : 3009
% 3.04/3.22  #    Positive orientable unit clauses  : 2967
% 3.04/3.22  #    Positive unorientable unit clauses: 0
% 3.04/3.22  #    Negative unit clauses             : 0
% 3.04/3.22  #    Non-unit-clauses                  : 42
% 3.04/3.22  # Current number of unprocessed clauses: 213069
% 3.04/3.22  # ...number of literals in the above   : 218945
% 3.04/3.22  # Current number of archived formulas  : 0
% 3.04/3.22  # Current number of archived clauses   : 267
% 3.04/3.22  # Clause-clause subsumption calls (NU) : 838
% 3.04/3.22  # Rec. Clause-clause subsumption calls : 838
% 3.04/3.22  # Non-unit clause-clause subsumptions  : 146
% 3.04/3.22  # Unit Clause-clause subsumption calls : 17
% 3.04/3.22  # Rewrite failures with RHS unbound    : 0
% 3.04/3.22  # BW rewrite match attempts            : 313922
% 3.04/3.22  # BW rewrite match successes           : 259
% 3.04/3.22  # Condensation attempts                : 0
% 3.04/3.22  # Condensation successes               : 0
% 3.04/3.22  # Termbank termtop insertions          : 9693472
% 3.04/3.23  
% 3.04/3.23  # -------------------------------------------------
% 3.04/3.23  # User time                : 2.763 s
% 3.04/3.23  # System time              : 0.125 s
% 3.04/3.23  # Total time               : 2.888 s
% 3.04/3.23  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
