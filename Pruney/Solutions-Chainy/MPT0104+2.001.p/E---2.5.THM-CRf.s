%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:07 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 138 expanded)
%              Number of clauses        :   32 (  61 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 201 expanded)
%              Number of equality atoms :   30 ( 104 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t97_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_10,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
          & r1_tarski(k4_xboole_0(X2,X1),X3) )
       => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t97_xboole_1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(k4_xboole_0(X19,X20),X21)
      | r1_tarski(X19,k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)
    & r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)
    & ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0)) = k2_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

fof(c_0_37,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_38,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_44]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_25]),c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.61/0.77  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.61/0.77  # and selection function SelectNewComplexAHP.
% 0.61/0.77  #
% 0.61/0.77  # Preprocessing time       : 0.026 s
% 0.61/0.77  # Presaturation interreduction done
% 0.61/0.77  
% 0.61/0.77  # Proof found!
% 0.61/0.77  # SZS status Theorem
% 0.61/0.77  # SZS output start CNFRefutation
% 0.61/0.77  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.61/0.77  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.61/0.77  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.61/0.77  fof(t97_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 0.61/0.77  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.61/0.77  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.61/0.77  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.61/0.77  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.61/0.77  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.61/0.77  fof(c_0_9, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.61/0.77  fof(c_0_10, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.61/0.77  fof(c_0_11, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.61/0.77  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.77  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.77  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.61/0.77  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t97_xboole_1])).
% 0.61/0.77  fof(c_0_16, plain, ![X19, X20, X21]:(~r1_tarski(k4_xboole_0(X19,X20),X21)|r1_tarski(X19,k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.61/0.77  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.61/0.77  fof(c_0_18, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.61/0.77  fof(c_0_19, negated_conjecture, ((r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)&r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0))&~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.61/0.77  fof(c_0_20, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.61/0.77  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.77  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.61/0.77  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.77  cnf(c_0_24, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.77  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.77  cnf(c_0_26, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.77  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_22])])).
% 0.61/0.77  cnf(c_0_28, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.61/0.77  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.61/0.77  cnf(c_0_30, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.61/0.77  cnf(c_0_31, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.61/0.77  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.61/0.77  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_14]), c_0_14]), c_0_14])).
% 0.61/0.77  cnf(c_0_34, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.61/0.77  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.61/0.77  cnf(c_0_36, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k2_xboole_0(X1,esk3_0))=k2_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.61/0.77  fof(c_0_37, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.61/0.77  fof(c_0_38, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k4_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.61/0.77  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.61/0.77  cnf(c_0_40, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.77  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.61/0.77  cnf(c_0_42, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.61/0.77  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.61/0.77  cnf(c_0_44, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.77  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.61/0.77  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 0.61/0.77  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.61/0.77  cnf(c_0_48, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_44]), c_0_25])).
% 0.61/0.77  cnf(c_0_49, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.61/0.77  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_25]), c_0_48]), c_0_49]), ['proof']).
% 0.61/0.77  # SZS output end CNFRefutation
% 0.61/0.77  # Proof object total steps             : 51
% 0.61/0.77  # Proof object clause steps            : 32
% 0.61/0.77  # Proof object formula steps           : 19
% 0.61/0.77  # Proof object conjectures             : 17
% 0.61/0.77  # Proof object clause conjectures      : 14
% 0.61/0.77  # Proof object formula conjectures     : 3
% 0.61/0.77  # Proof object initial clauses used    : 12
% 0.61/0.77  # Proof object initial formulas used   : 9
% 0.61/0.77  # Proof object generating inferences   : 17
% 0.61/0.77  # Proof object simplifying inferences  : 13
% 0.61/0.77  # Training examples: 0 positive, 0 negative
% 0.61/0.77  # Parsed axioms                        : 9
% 0.61/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.77  # Initial clauses                      : 12
% 0.61/0.77  # Removed in clause preprocessing      : 1
% 0.61/0.77  # Initial clauses in saturation        : 11
% 0.61/0.77  # Processed clauses                    : 2216
% 0.61/0.77  # ...of these trivial                  : 1151
% 0.61/0.77  # ...subsumed                          : 12
% 0.61/0.77  # ...remaining for further processing  : 1053
% 0.61/0.77  # Other redundant clauses eliminated   : 0
% 0.61/0.77  # Clauses deleted for lack of memory   : 0
% 0.61/0.77  # Backward-subsumed                    : 0
% 0.61/0.77  # Backward-rewritten                   : 160
% 0.61/0.77  # Generated clauses                    : 70977
% 0.61/0.77  # ...of the previous two non-trivial   : 34481
% 0.61/0.77  # Contextual simplify-reflections      : 0
% 0.61/0.77  # Paramodulations                      : 70974
% 0.61/0.77  # Factorizations                       : 0
% 0.61/0.77  # Equation resolutions                 : 3
% 0.61/0.77  # Propositional unsat checks           : 0
% 0.61/0.77  #    Propositional check models        : 0
% 0.61/0.77  #    Propositional check unsatisfiable : 0
% 0.61/0.77  #    Propositional clauses             : 0
% 0.61/0.77  #    Propositional clauses after purity: 0
% 0.61/0.77  #    Propositional unsat core size     : 0
% 0.61/0.77  #    Propositional preprocessing time  : 0.000
% 0.61/0.77  #    Propositional encoding time       : 0.000
% 0.61/0.77  #    Propositional solver time         : 0.000
% 0.61/0.77  #    Success case prop preproc time    : 0.000
% 0.61/0.77  #    Success case prop encoding time   : 0.000
% 0.61/0.77  #    Success case prop solver time     : 0.000
% 0.61/0.77  # Current number of processed clauses  : 882
% 0.61/0.77  #    Positive orientable unit clauses  : 857
% 0.61/0.77  #    Positive unorientable unit clauses: 3
% 0.61/0.77  #    Negative unit clauses             : 1
% 0.61/0.77  #    Non-unit-clauses                  : 21
% 0.61/0.77  # Current number of unprocessed clauses: 32057
% 0.61/0.77  # ...number of literals in the above   : 33097
% 0.61/0.77  # Current number of archived formulas  : 0
% 0.61/0.77  # Current number of archived clauses   : 172
% 0.61/0.77  # Clause-clause subsumption calls (NU) : 78
% 0.61/0.77  # Rec. Clause-clause subsumption calls : 78
% 0.61/0.77  # Non-unit clause-clause subsumptions  : 8
% 0.61/0.77  # Unit Clause-clause subsumption calls : 26
% 0.61/0.77  # Rewrite failures with RHS unbound    : 0
% 0.61/0.77  # BW rewrite match attempts            : 4617
% 0.61/0.77  # BW rewrite match successes           : 214
% 0.61/0.77  # Condensation attempts                : 0
% 0.61/0.77  # Condensation successes               : 0
% 0.61/0.77  # Termbank termtop insertions          : 810982
% 0.61/0.78  
% 0.61/0.78  # -------------------------------------------------
% 0.61/0.78  # User time                : 0.408 s
% 0.61/0.78  # System time              : 0.021 s
% 0.61/0.78  # Total time               : 0.429 s
% 0.61/0.78  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
