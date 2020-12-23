%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:17 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of clauses        :   22 (  27 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  83 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_xboole_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    inference(assume_negation,[status(cth)],[t75_xboole_1])).

fof(c_0_9,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    & r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] : k4_xboole_0(X16,k3_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.40  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.22/0.40  # and selection function SelectNewComplexAHP.
% 0.22/0.40  #
% 0.22/0.40  # Preprocessing time       : 0.042 s
% 0.22/0.40  # Presaturation interreduction done
% 0.22/0.40  
% 0.22/0.40  # Proof found!
% 0.22/0.40  # SZS status Theorem
% 0.22/0.40  # SZS output start CNFRefutation
% 0.22/0.40  fof(t75_xboole_1, conjecture, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.22/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.22/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.22/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.22/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.22/0.40  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.22/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.22/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.22/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2)))), inference(assume_negation,[status(cth)],[t75_xboole_1])).
% 0.22/0.40  fof(c_0_9, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)&r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.22/0.40  fof(c_0_10, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.22/0.40  fof(c_0_11, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.22/0.40  fof(c_0_12, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.22/0.40  fof(c_0_13, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.22/0.40  cnf(c_0_14, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.40  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.40  fof(c_0_16, plain, ![X16, X17, X18]:k4_xboole_0(X16,k3_xboole_0(X17,X18))=k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.22/0.40  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.40  fof(c_0_18, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.22/0.40  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.40  cnf(c_0_20, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.40  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),esk2_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.22/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.40  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.22/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.40  fof(c_0_25, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.22/0.40  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.22/0.40  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.22/0.40  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_22, c_0_15])).
% 0.22/0.40  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.22/0.40  cnf(c_0_30, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.40  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.40  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.22/0.40  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.22/0.40  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_15])).
% 0.22/0.40  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.22/0.40  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.22/0.40  cnf(c_0_37, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.40  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_36]), c_0_37]), ['proof']).
% 0.22/0.40  # SZS output end CNFRefutation
% 0.22/0.40  # Proof object total steps             : 39
% 0.22/0.40  # Proof object clause steps            : 22
% 0.22/0.40  # Proof object formula steps           : 17
% 0.22/0.40  # Proof object conjectures             : 11
% 0.22/0.40  # Proof object clause conjectures      : 8
% 0.22/0.40  # Proof object formula conjectures     : 3
% 0.22/0.40  # Proof object initial clauses used    : 10
% 0.22/0.40  # Proof object initial formulas used   : 8
% 0.22/0.40  # Proof object generating inferences   : 5
% 0.22/0.40  # Proof object simplifying inferences  : 9
% 0.22/0.40  # Training examples: 0 positive, 0 negative
% 0.22/0.40  # Parsed axioms                        : 15
% 0.22/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.40  # Initial clauses                      : 19
% 0.22/0.40  # Removed in clause preprocessing      : 1
% 0.22/0.40  # Initial clauses in saturation        : 18
% 0.22/0.40  # Processed clauses                    : 77
% 0.22/0.40  # ...of these trivial                  : 7
% 0.22/0.40  # ...subsumed                          : 10
% 0.22/0.40  # ...remaining for further processing  : 60
% 0.22/0.40  # Other redundant clauses eliminated   : 0
% 0.22/0.40  # Clauses deleted for lack of memory   : 0
% 0.22/0.40  # Backward-subsumed                    : 0
% 0.22/0.40  # Backward-rewritten                   : 3
% 0.22/0.40  # Generated clauses                    : 213
% 0.22/0.40  # ...of the previous two non-trivial   : 102
% 0.22/0.40  # Contextual simplify-reflections      : 0
% 0.22/0.40  # Paramodulations                      : 212
% 0.22/0.40  # Factorizations                       : 0
% 0.22/0.40  # Equation resolutions                 : 1
% 0.22/0.40  # Propositional unsat checks           : 0
% 0.22/0.40  #    Propositional check models        : 0
% 0.22/0.40  #    Propositional check unsatisfiable : 0
% 0.22/0.40  #    Propositional clauses             : 0
% 0.22/0.40  #    Propositional clauses after purity: 0
% 0.22/0.40  #    Propositional unsat core size     : 0
% 0.22/0.40  #    Propositional preprocessing time  : 0.000
% 0.22/0.40  #    Propositional encoding time       : 0.000
% 0.22/0.40  #    Propositional solver time         : 0.000
% 0.22/0.40  #    Success case prop preproc time    : 0.000
% 0.22/0.40  #    Success case prop encoding time   : 0.000
% 0.22/0.40  #    Success case prop solver time     : 0.000
% 0.22/0.40  # Current number of processed clauses  : 39
% 0.22/0.40  #    Positive orientable unit clauses  : 24
% 0.22/0.40  #    Positive unorientable unit clauses: 2
% 0.22/0.40  #    Negative unit clauses             : 1
% 0.22/0.40  #    Non-unit-clauses                  : 12
% 0.22/0.40  # Current number of unprocessed clauses: 58
% 0.22/0.40  # ...number of literals in the above   : 76
% 0.22/0.40  # Current number of archived formulas  : 0
% 0.22/0.40  # Current number of archived clauses   : 22
% 0.22/0.40  # Clause-clause subsumption calls (NU) : 69
% 0.22/0.40  # Rec. Clause-clause subsumption calls : 69
% 0.22/0.40  # Non-unit clause-clause subsumptions  : 10
% 0.22/0.40  # Unit Clause-clause subsumption calls : 5
% 0.22/0.40  # Rewrite failures with RHS unbound    : 0
% 0.22/0.40  # BW rewrite match attempts            : 32
% 0.22/0.40  # BW rewrite match successes           : 12
% 0.22/0.40  # Condensation attempts                : 0
% 0.22/0.40  # Condensation successes               : 0
% 0.22/0.40  # Termbank termtop insertions          : 2805
% 0.22/0.40  
% 0.22/0.40  # -------------------------------------------------
% 0.22/0.40  # User time                : 0.049 s
% 0.22/0.40  # System time              : 0.003 s
% 0.22/0.40  # Total time               : 0.052 s
% 0.22/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
