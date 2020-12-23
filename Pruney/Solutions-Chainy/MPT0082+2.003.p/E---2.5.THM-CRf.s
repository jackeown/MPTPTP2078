%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:17 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  59 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  90 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t75_xboole_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_7,plain,(
    ! [X11,X12] : k2_xboole_0(k3_xboole_0(X11,X12),k4_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_8,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    inference(assume_negation,[status(cth)],[t75_xboole_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ( r1_xboole_0(X13,k2_xboole_0(X14,X15))
        | ~ r1_xboole_0(X13,X14)
        | ~ r1_xboole_0(X13,X15) )
      & ( r1_xboole_0(X13,X14)
        | ~ r1_xboole_0(X13,k2_xboole_0(X14,X15)) )
      & ( r1_xboole_0(X13,X15)
        | ~ r1_xboole_0(X13,k2_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_11,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    & r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_12]),c_0_12])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:24:14 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.52  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.22/0.52  # and selection function SelectNewComplexAHP.
% 0.22/0.52  #
% 0.22/0.52  # Preprocessing time       : 0.027 s
% 0.22/0.52  # Presaturation interreduction done
% 0.22/0.52  
% 0.22/0.52  # Proof found!
% 0.22/0.52  # SZS status Theorem
% 0.22/0.52  # SZS output start CNFRefutation
% 0.22/0.52  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.22/0.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.22/0.52  fof(t75_xboole_1, conjecture, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.22/0.52  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.22/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.22/0.52  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.22/0.52  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.22/0.52  fof(c_0_7, plain, ![X11, X12]:k2_xboole_0(k3_xboole_0(X11,X12),k4_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.22/0.52  fof(c_0_8, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.22/0.52  fof(c_0_9, negated_conjecture, ~(![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2)))), inference(assume_negation,[status(cth)],[t75_xboole_1])).
% 0.22/0.52  fof(c_0_10, plain, ![X13, X14, X15]:((r1_xboole_0(X13,k2_xboole_0(X14,X15))|~r1_xboole_0(X13,X14)|~r1_xboole_0(X13,X15))&((r1_xboole_0(X13,X14)|~r1_xboole_0(X13,k2_xboole_0(X14,X15)))&(r1_xboole_0(X13,X15)|~r1_xboole_0(X13,k2_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.22/0.52  cnf(c_0_11, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.52  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.52  fof(c_0_13, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)&r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.22/0.52  cnf(c_0_14, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.52  cnf(c_0_15, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.22/0.52  cnf(c_0_16, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.52  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.22/0.52  fof(c_0_18, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.22/0.52  cnf(c_0_19, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.22/0.52  cnf(c_0_20, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0)), inference(rw,[status(thm)],[c_0_16, c_0_12])).
% 0.22/0.52  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.52  fof(c_0_22, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.22/0.52  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.52  cnf(c_0_24, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.22/0.52  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_12]), c_0_12])).
% 0.22/0.52  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.52  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_12])).
% 0.22/0.52  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.22/0.52  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.52  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_26, c_0_12])).
% 0.22/0.52  cnf(c_0_31, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.22/0.52  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 0.22/0.52  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.22/0.52  cnf(c_0_34, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.52  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.22/0.52  # SZS output end CNFRefutation
% 0.22/0.52  # Proof object total steps             : 36
% 0.22/0.52  # Proof object clause steps            : 21
% 0.22/0.52  # Proof object formula steps           : 15
% 0.22/0.52  # Proof object conjectures             : 11
% 0.22/0.52  # Proof object clause conjectures      : 8
% 0.22/0.52  # Proof object formula conjectures     : 3
% 0.22/0.52  # Proof object initial clauses used    : 9
% 0.22/0.52  # Proof object initial formulas used   : 7
% 0.22/0.52  # Proof object generating inferences   : 6
% 0.22/0.52  # Proof object simplifying inferences  : 8
% 0.22/0.52  # Training examples: 0 positive, 0 negative
% 0.22/0.52  # Parsed axioms                        : 7
% 0.22/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.52  # Initial clauses                      : 11
% 0.22/0.52  # Removed in clause preprocessing      : 1
% 0.22/0.52  # Initial clauses in saturation        : 10
% 0.22/0.52  # Processed clauses                    : 1119
% 0.22/0.52  # ...of these trivial                  : 206
% 0.22/0.52  # ...subsumed                          : 109
% 0.22/0.52  # ...remaining for further processing  : 804
% 0.22/0.52  # Other redundant clauses eliminated   : 0
% 0.22/0.52  # Clauses deleted for lack of memory   : 0
% 0.22/0.52  # Backward-subsumed                    : 3
% 0.22/0.52  # Backward-rewritten                   : 751
% 0.22/0.52  # Generated clauses                    : 17801
% 0.22/0.52  # ...of the previous two non-trivial   : 7384
% 0.22/0.52  # Contextual simplify-reflections      : 0
% 0.22/0.52  # Paramodulations                      : 17800
% 0.22/0.52  # Factorizations                       : 0
% 0.22/0.52  # Equation resolutions                 : 1
% 0.22/0.52  # Propositional unsat checks           : 0
% 0.22/0.52  #    Propositional check models        : 0
% 0.22/0.52  #    Propositional check unsatisfiable : 0
% 0.22/0.52  #    Propositional clauses             : 0
% 0.22/0.52  #    Propositional clauses after purity: 0
% 0.22/0.52  #    Propositional unsat core size     : 0
% 0.22/0.52  #    Propositional preprocessing time  : 0.000
% 0.22/0.52  #    Propositional encoding time       : 0.000
% 0.22/0.52  #    Propositional solver time         : 0.000
% 0.22/0.52  #    Success case prop preproc time    : 0.000
% 0.22/0.52  #    Success case prop encoding time   : 0.000
% 0.22/0.52  #    Success case prop solver time     : 0.000
% 0.22/0.52  # Current number of processed clauses  : 40
% 0.22/0.52  #    Positive orientable unit clauses  : 19
% 0.22/0.52  #    Positive unorientable unit clauses: 1
% 0.22/0.52  #    Negative unit clauses             : 1
% 0.22/0.52  #    Non-unit-clauses                  : 19
% 0.22/0.52  # Current number of unprocessed clauses: 3432
% 0.22/0.52  # ...number of literals in the above   : 4083
% 0.22/0.52  # Current number of archived formulas  : 0
% 0.22/0.52  # Current number of archived clauses   : 765
% 0.22/0.52  # Clause-clause subsumption calls (NU) : 446
% 0.22/0.52  # Rec. Clause-clause subsumption calls : 446
% 0.22/0.52  # Non-unit clause-clause subsumptions  : 112
% 0.22/0.52  # Unit Clause-clause subsumption calls : 27
% 0.22/0.52  # Rewrite failures with RHS unbound    : 0
% 0.22/0.52  # BW rewrite match attempts            : 7079
% 0.22/0.52  # BW rewrite match successes           : 400
% 0.22/0.52  # Condensation attempts                : 0
% 0.22/0.52  # Condensation successes               : 0
% 0.22/0.52  # Termbank termtop insertions          : 207933
% 0.22/0.52  
% 0.22/0.52  # -------------------------------------------------
% 0.22/0.52  # User time                : 0.155 s
% 0.22/0.52  # System time              : 0.009 s
% 0.22/0.52  # Total time               : 0.164 s
% 0.22/0.52  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
