%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:23 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 134 expanded)
%              Number of clauses        :   21 (  59 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 ( 134 expanded)
%              Number of equality atoms :   37 ( 133 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t52_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_8,plain,(
    ! [X42,X43,X44] : k3_xboole_0(X42,k4_xboole_0(X43,X44)) = k4_xboole_0(k3_xboole_0(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_9,plain,(
    ! [X40,X41] : k4_xboole_0(X40,k4_xboole_0(X40,X41)) = k3_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] : k4_xboole_0(k4_xboole_0(X29,X30),X31) = k4_xboole_0(X29,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] : k3_xboole_0(X15,k2_xboole_0(X16,X17)) = k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_14,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k3_xboole_0(X38,X39)) = k4_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t52_xboole_1])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_11]),c_0_11]),c_0_11])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_11]),c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_11])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))) != k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_16]),c_0_28]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.64/0.82  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.64/0.82  # and selection function SelectNewComplexAHP.
% 0.64/0.82  #
% 0.64/0.82  # Preprocessing time       : 0.027 s
% 0.64/0.82  # Presaturation interreduction done
% 0.64/0.82  
% 0.64/0.82  # Proof found!
% 0.64/0.82  # SZS status Theorem
% 0.64/0.82  # SZS output start CNFRefutation
% 0.64/0.82  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.64/0.82  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.64/0.82  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.64/0.82  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.64/0.82  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.64/0.82  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.64/0.82  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.64/0.82  fof(t52_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.64/0.82  fof(c_0_8, plain, ![X42, X43, X44]:k3_xboole_0(X42,k4_xboole_0(X43,X44))=k4_xboole_0(k3_xboole_0(X42,X43),X44), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.64/0.82  fof(c_0_9, plain, ![X40, X41]:k4_xboole_0(X40,k4_xboole_0(X40,X41))=k3_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.64/0.82  cnf(c_0_10, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.64/0.82  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.64/0.82  fof(c_0_12, plain, ![X29, X30, X31]:k4_xboole_0(k4_xboole_0(X29,X30),X31)=k4_xboole_0(X29,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.64/0.82  fof(c_0_13, plain, ![X15, X16, X17]:k3_xboole_0(X15,k2_xboole_0(X16,X17))=k2_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X17)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.64/0.82  fof(c_0_14, plain, ![X38, X39]:k4_xboole_0(X38,k3_xboole_0(X38,X39))=k4_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.64/0.82  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.64/0.82  cnf(c_0_16, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.64/0.82  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.64/0.82  fof(c_0_18, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.64/0.82  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t52_xboole_1])).
% 0.64/0.82  cnf(c_0_20, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.64/0.82  cnf(c_0_21, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.64/0.82  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.64/0.82  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.64/0.82  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.64/0.82  fof(c_0_25, negated_conjecture, k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.64/0.82  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_11]), c_0_11]), c_0_11])).
% 0.64/0.82  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_11])).
% 0.64/0.82  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.64/0.82  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_11]), c_0_11])).
% 0.64/0.82  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.64/0.82  cnf(c_0_31, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_27])).
% 0.64/0.82  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.64/0.82  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_30, c_0_11])).
% 0.64/0.82  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_32])).
% 0.64/0.82  cnf(c_0_35, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)))!=k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.64/0.82  cnf(c_0_36, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_16]), c_0_28]), c_0_27])).
% 0.64/0.82  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.64/0.82  # SZS output end CNFRefutation
% 0.64/0.82  # Proof object total steps             : 38
% 0.64/0.82  # Proof object clause steps            : 21
% 0.64/0.82  # Proof object formula steps           : 17
% 0.64/0.82  # Proof object conjectures             : 7
% 0.64/0.82  # Proof object clause conjectures      : 4
% 0.64/0.82  # Proof object formula conjectures     : 3
% 0.64/0.82  # Proof object initial clauses used    : 8
% 0.64/0.82  # Proof object initial formulas used   : 8
% 0.64/0.82  # Proof object generating inferences   : 5
% 0.64/0.82  # Proof object simplifying inferences  : 19
% 0.64/0.82  # Training examples: 0 positive, 0 negative
% 0.64/0.82  # Parsed axioms                        : 18
% 0.64/0.82  # Removed by relevancy pruning/SinE    : 0
% 0.64/0.82  # Initial clauses                      : 18
% 0.64/0.82  # Removed in clause preprocessing      : 1
% 0.64/0.82  # Initial clauses in saturation        : 17
% 0.64/0.82  # Processed clauses                    : 1715
% 0.64/0.82  # ...of these trivial                  : 787
% 0.64/0.82  # ...subsumed                          : 555
% 0.64/0.82  # ...remaining for further processing  : 373
% 0.64/0.82  # Other redundant clauses eliminated   : 0
% 0.64/0.82  # Clauses deleted for lack of memory   : 0
% 0.64/0.82  # Backward-subsumed                    : 2
% 0.64/0.82  # Backward-rewritten                   : 135
% 0.64/0.82  # Generated clauses                    : 48279
% 0.64/0.82  # ...of the previous two non-trivial   : 26433
% 0.64/0.82  # Contextual simplify-reflections      : 0
% 0.64/0.82  # Paramodulations                      : 48279
% 0.64/0.82  # Factorizations                       : 0
% 0.64/0.82  # Equation resolutions                 : 0
% 0.64/0.82  # Propositional unsat checks           : 0
% 0.64/0.82  #    Propositional check models        : 0
% 0.64/0.82  #    Propositional check unsatisfiable : 0
% 0.64/0.82  #    Propositional clauses             : 0
% 0.64/0.82  #    Propositional clauses after purity: 0
% 0.64/0.82  #    Propositional unsat core size     : 0
% 0.64/0.82  #    Propositional preprocessing time  : 0.000
% 0.64/0.82  #    Propositional encoding time       : 0.000
% 0.64/0.82  #    Propositional solver time         : 0.000
% 0.64/0.82  #    Success case prop preproc time    : 0.000
% 0.64/0.82  #    Success case prop encoding time   : 0.000
% 0.64/0.82  #    Success case prop solver time     : 0.000
% 0.64/0.82  # Current number of processed clauses  : 219
% 0.64/0.82  #    Positive orientable unit clauses  : 195
% 0.64/0.82  #    Positive unorientable unit clauses: 9
% 0.64/0.82  #    Negative unit clauses             : 0
% 0.64/0.82  #    Non-unit-clauses                  : 15
% 0.64/0.82  # Current number of unprocessed clauses: 23967
% 0.64/0.82  # ...number of literals in the above   : 24521
% 0.64/0.82  # Current number of archived formulas  : 0
% 0.64/0.82  # Current number of archived clauses   : 155
% 0.64/0.82  # Clause-clause subsumption calls (NU) : 95
% 0.64/0.82  # Rec. Clause-clause subsumption calls : 95
% 0.64/0.82  # Non-unit clause-clause subsumptions  : 8
% 0.64/0.82  # Unit Clause-clause subsumption calls : 79
% 0.64/0.82  # Rewrite failures with RHS unbound    : 36
% 0.64/0.82  # BW rewrite match attempts            : 1735
% 0.64/0.82  # BW rewrite match successes           : 406
% 0.64/0.82  # Condensation attempts                : 0
% 0.64/0.82  # Condensation successes               : 0
% 0.64/0.82  # Termbank termtop insertions          : 446841
% 0.64/0.83  
% 0.64/0.83  # -------------------------------------------------
% 0.64/0.83  # User time                : 0.456 s
% 0.64/0.83  # System time              : 0.031 s
% 0.64/0.83  # Total time               : 0.488 s
% 0.64/0.83  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
