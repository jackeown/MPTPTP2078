%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:06 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 129 expanded)
%              Number of clauses        :   23 (  58 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 ( 129 expanded)
%              Number of equality atoms :   35 ( 128 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_6,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_7,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_8,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_9,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_10,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_14])).

fof(c_0_22,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k4_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_13])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X3,X1),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_13]),c_0_15])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_12]),c_0_12])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_12]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.28/2.49  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 2.28/2.49  # and selection function SelectNewComplexAHP.
% 2.28/2.49  #
% 2.28/2.49  # Preprocessing time       : 0.030 s
% 2.28/2.49  # Presaturation interreduction done
% 2.28/2.49  
% 2.28/2.49  # Proof found!
% 2.28/2.49  # SZS status Theorem
% 2.28/2.49  # SZS output start CNFRefutation
% 2.28/2.49  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.28/2.49  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.28/2.49  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.28/2.49  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.28/2.49  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.28/2.49  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.28/2.49  fof(c_0_6, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.28/2.49  fof(c_0_7, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.28/2.49  fof(c_0_8, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.28/2.49  fof(c_0_9, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.28/2.49  fof(c_0_10, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.28/2.49  cnf(c_0_11, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.28/2.49  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.28/2.49  cnf(c_0_13, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 2.28/2.49  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.28/2.49  cnf(c_0_15, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.28/2.49  cnf(c_0_16, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 2.28/2.49  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 2.28/2.49  cnf(c_0_18, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 2.28/2.49  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_14])).
% 2.28/2.49  cnf(c_0_20, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 2.28/2.49  cnf(c_0_21, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_16]), c_0_14])).
% 2.28/2.49  fof(c_0_22, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 2.28/2.49  cnf(c_0_23, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 2.28/2.49  cnf(c_0_24, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k4_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_19, c_0_12])).
% 2.28/2.49  cnf(c_0_25, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_13])).
% 2.28/2.49  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_20])).
% 2.28/2.49  cnf(c_0_27, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 2.28/2.49  cnf(c_0_28, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.28/2.49  cnf(c_0_29, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X3,X1),X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_23])).
% 2.28/2.49  cnf(c_0_30, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 2.28/2.49  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_13]), c_0_15])).
% 2.28/2.49  cnf(c_0_32, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_23])).
% 2.28/2.49  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_12]), c_0_12])).
% 2.28/2.49  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_12]), c_0_32])).
% 2.28/2.49  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 2.28/2.49  # SZS output end CNFRefutation
% 2.28/2.49  # Proof object total steps             : 36
% 2.28/2.49  # Proof object clause steps            : 23
% 2.28/2.49  # Proof object formula steps           : 13
% 2.28/2.49  # Proof object conjectures             : 6
% 2.28/2.49  # Proof object clause conjectures      : 3
% 2.28/2.49  # Proof object formula conjectures     : 3
% 2.28/2.49  # Proof object initial clauses used    : 6
% 2.28/2.49  # Proof object initial formulas used   : 6
% 2.28/2.49  # Proof object generating inferences   : 15
% 2.28/2.49  # Proof object simplifying inferences  : 14
% 2.28/2.49  # Training examples: 0 positive, 0 negative
% 2.28/2.49  # Parsed axioms                        : 7
% 2.28/2.49  # Removed by relevancy pruning/SinE    : 0
% 2.28/2.49  # Initial clauses                      : 8
% 2.28/2.49  # Removed in clause preprocessing      : 0
% 2.28/2.49  # Initial clauses in saturation        : 8
% 2.28/2.49  # Processed clauses                    : 10655
% 2.28/2.49  # ...of these trivial                  : 1183
% 2.28/2.49  # ...subsumed                          : 8829
% 2.28/2.49  # ...remaining for further processing  : 643
% 2.28/2.49  # Other redundant clauses eliminated   : 0
% 2.28/2.49  # Clauses deleted for lack of memory   : 0
% 2.28/2.49  # Backward-subsumed                    : 5
% 2.28/2.49  # Backward-rewritten                   : 95
% 2.28/2.49  # Generated clauses                    : 248309
% 2.28/2.49  # ...of the previous two non-trivial   : 216134
% 2.28/2.49  # Contextual simplify-reflections      : 0
% 2.28/2.49  # Paramodulations                      : 248306
% 2.28/2.49  # Factorizations                       : 0
% 2.28/2.49  # Equation resolutions                 : 3
% 2.28/2.49  # Propositional unsat checks           : 0
% 2.28/2.49  #    Propositional check models        : 0
% 2.28/2.49  #    Propositional check unsatisfiable : 0
% 2.28/2.49  #    Propositional clauses             : 0
% 2.28/2.49  #    Propositional clauses after purity: 0
% 2.28/2.49  #    Propositional unsat core size     : 0
% 2.28/2.49  #    Propositional preprocessing time  : 0.000
% 2.28/2.49  #    Propositional encoding time       : 0.000
% 2.28/2.49  #    Propositional solver time         : 0.000
% 2.28/2.49  #    Success case prop preproc time    : 0.000
% 2.28/2.49  #    Success case prop encoding time   : 0.000
% 2.28/2.49  #    Success case prop solver time     : 0.000
% 2.28/2.49  # Current number of processed clauses  : 535
% 2.28/2.49  #    Positive orientable unit clauses  : 293
% 2.28/2.49  #    Positive unorientable unit clauses: 70
% 2.28/2.49  #    Negative unit clauses             : 0
% 2.28/2.49  #    Non-unit-clauses                  : 172
% 2.28/2.49  # Current number of unprocessed clauses: 203416
% 2.28/2.49  # ...number of literals in the above   : 251549
% 2.28/2.49  # Current number of archived formulas  : 0
% 2.28/2.49  # Current number of archived clauses   : 108
% 2.28/2.49  # Clause-clause subsumption calls (NU) : 28070
% 2.28/2.49  # Rec. Clause-clause subsumption calls : 28070
% 2.28/2.49  # Non-unit clause-clause subsumptions  : 2881
% 2.28/2.49  # Unit Clause-clause subsumption calls : 2860
% 2.28/2.49  # Rewrite failures with RHS unbound    : 0
% 2.28/2.49  # BW rewrite match attempts            : 6148
% 2.28/2.49  # BW rewrite match successes           : 1162
% 2.28/2.49  # Condensation attempts                : 0
% 2.28/2.49  # Condensation successes               : 0
% 2.28/2.49  # Termbank termtop insertions          : 4163590
% 2.28/2.50  
% 2.28/2.50  # -------------------------------------------------
% 2.28/2.50  # User time                : 2.031 s
% 2.28/2.50  # System time              : 0.130 s
% 2.28/2.50  # Total time               : 2.161 s
% 2.28/2.50  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
