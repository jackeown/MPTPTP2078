%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:40 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 275 expanded)
%              Number of clauses        :   35 ( 126 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 351 expanded)
%              Number of equality atoms :   31 ( 194 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_10,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_14]),c_0_14])).

fof(c_0_19,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_24,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

fof(c_0_37,plain,(
    ! [X19] : r1_xboole_0(X19,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_27])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_22])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_41])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_43]),c_0_45])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_51]),c_0_52]),c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.38  fof(c_0_10, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_14]), c_0_14])).
% 0.13/0.38  fof(c_0_19, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_23, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.13/0.38  fof(c_0_24, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_27, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_25, c_0_14])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  fof(c_0_32, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  fof(c_0_34, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_33, c_0_22])).
% 0.13/0.38  fof(c_0_37, plain, ![X19]:r1_xboole_0(X19,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.38  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_35, c_0_14])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_27])).
% 0.13/0.38  cnf(c_0_41, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_22])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_22])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31])).
% 0.13/0.38  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.13/0.38  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_41])).
% 0.13/0.38  cnf(c_0_47, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_44])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_43]), c_0_45])).
% 0.13/0.38  cnf(c_0_52, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk1_0,esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_51]), c_0_52]), c_0_53]), c_0_54]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 35
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 12
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 11
% 0.13/0.38  # Processed clauses                    : 150
% 0.13/0.38  # ...of these trivial                  : 34
% 0.13/0.38  # ...subsumed                          : 22
% 0.13/0.38  # ...remaining for further processing  : 94
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 15
% 0.13/0.38  # Generated clauses                    : 1072
% 0.13/0.38  # ...of the previous two non-trivial   : 612
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 1072
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 68
% 0.13/0.38  #    Positive orientable unit clauses  : 60
% 0.13/0.38  #    Positive unorientable unit clauses: 4
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 3
% 0.13/0.38  # Current number of unprocessed clauses: 472
% 0.13/0.38  # ...number of literals in the above   : 472
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 27
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 13
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 93
% 0.13/0.38  # BW rewrite match successes           : 47
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9700
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
