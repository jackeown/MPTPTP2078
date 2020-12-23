%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:06 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 269 expanded)
%              Number of clauses        :   35 ( 120 expanded)
%              Number of leaves         :    8 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 ( 316 expanded)
%              Number of equality atoms :   45 ( 243 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_9,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_13,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X14,X15),X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X13,X12)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_17]),c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20])).

fof(c_0_24,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_30])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_19])).

fof(c_0_36,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_11]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X3,X1),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_17]),c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_41]),c_0_41])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27]),c_0_27])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_15]),c_0_20]),c_0_46]),c_0_47]),c_0_15]),c_0_20]),c_0_46]),c_0_15]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:59:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.67/0.92  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.67/0.92  # and selection function SelectNewComplexAHP.
% 0.67/0.92  #
% 0.67/0.92  # Preprocessing time       : 0.026 s
% 0.67/0.92  # Presaturation interreduction done
% 0.67/0.92  
% 0.67/0.92  # Proof found!
% 0.67/0.92  # SZS status Theorem
% 0.67/0.92  # SZS output start CNFRefutation
% 0.67/0.92  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.67/0.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.67/0.92  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.67/0.92  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.67/0.92  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.67/0.92  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.67/0.92  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.67/0.92  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.67/0.92  fof(c_0_8, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.67/0.92  fof(c_0_9, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.67/0.92  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.67/0.92  cnf(c_0_11, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.67/0.92  fof(c_0_12, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.67/0.92  fof(c_0_13, plain, ![X14, X15]:k4_xboole_0(k2_xboole_0(X14,X15),X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.67/0.92  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.67/0.92  cnf(c_0_15, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.67/0.92  fof(c_0_16, plain, ![X12, X13]:k2_xboole_0(X12,k4_xboole_0(X13,X12))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.67/0.92  cnf(c_0_17, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.92  cnf(c_0_18, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.67/0.92  cnf(c_0_19, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.67/0.92  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.67/0.92  cnf(c_0_21, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_17]), c_0_15])).
% 0.67/0.92  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.67/0.92  cnf(c_0_23, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_20])).
% 0.67/0.92  fof(c_0_24, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.67/0.92  fof(c_0_25, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.67/0.92  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.67/0.92  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.67/0.92  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.67/0.92  cnf(c_0_29, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X2),X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.67/0.92  cnf(c_0_30, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X2))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.67/0.92  cnf(c_0_31, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_30])).
% 0.67/0.92  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 0.67/0.92  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.67/0.92  cnf(c_0_34, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.67/0.92  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_19])).
% 0.67/0.92  fof(c_0_36, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.67/0.92  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 0.67/0.92  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_20])).
% 0.67/0.92  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2)=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.67/0.92  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_15]), c_0_15]), c_0_15])).
% 0.67/0.92  cnf(c_0_41, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.67/0.92  cnf(c_0_42, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_11]), c_0_27])).
% 0.67/0.92  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.67/0.92  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.67/0.92  cnf(c_0_45, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X3,X1),X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_17]), c_0_38]), c_0_39])).
% 0.67/0.92  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_40])).
% 0.67/0.92  cnf(c_0_47, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_41]), c_0_41])).
% 0.67/0.92  cnf(c_0_48, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_42, c_0_19])).
% 0.67/0.92  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27]), c_0_27])).
% 0.67/0.92  cnf(c_0_50, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_15]), c_0_20]), c_0_46]), c_0_47]), c_0_15]), c_0_20]), c_0_46]), c_0_15]), c_0_48])).
% 0.67/0.92  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_27])]), ['proof']).
% 0.67/0.92  # SZS output end CNFRefutation
% 0.67/0.92  # Proof object total steps             : 52
% 0.67/0.92  # Proof object clause steps            : 35
% 0.67/0.92  # Proof object formula steps           : 17
% 0.67/0.92  # Proof object conjectures             : 6
% 0.67/0.92  # Proof object clause conjectures      : 3
% 0.67/0.92  # Proof object formula conjectures     : 3
% 0.67/0.92  # Proof object initial clauses used    : 9
% 0.67/0.92  # Proof object initial formulas used   : 8
% 0.67/0.92  # Proof object generating inferences   : 23
% 0.67/0.92  # Proof object simplifying inferences  : 25
% 0.67/0.92  # Training examples: 0 positive, 0 negative
% 0.67/0.92  # Parsed axioms                        : 8
% 0.67/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.67/0.92  # Initial clauses                      : 9
% 0.67/0.92  # Removed in clause preprocessing      : 0
% 0.67/0.92  # Initial clauses in saturation        : 9
% 0.67/0.92  # Processed clauses                    : 3098
% 0.67/0.92  # ...of these trivial                  : 1439
% 0.67/0.92  # ...subsumed                          : 1173
% 0.67/0.92  # ...remaining for further processing  : 486
% 0.67/0.92  # Other redundant clauses eliminated   : 0
% 0.67/0.92  # Clauses deleted for lack of memory   : 0
% 0.67/0.92  # Backward-subsumed                    : 0
% 0.67/0.92  # Backward-rewritten                   : 130
% 0.67/0.92  # Generated clauses                    : 93930
% 0.67/0.92  # ...of the previous two non-trivial   : 63207
% 0.67/0.92  # Contextual simplify-reflections      : 0
% 0.67/0.92  # Paramodulations                      : 93929
% 0.67/0.92  # Factorizations                       : 0
% 0.67/0.92  # Equation resolutions                 : 1
% 0.67/0.92  # Propositional unsat checks           : 0
% 0.67/0.92  #    Propositional check models        : 0
% 0.67/0.92  #    Propositional check unsatisfiable : 0
% 0.67/0.92  #    Propositional clauses             : 0
% 0.67/0.92  #    Propositional clauses after purity: 0
% 0.67/0.92  #    Propositional unsat core size     : 0
% 0.67/0.92  #    Propositional preprocessing time  : 0.000
% 0.67/0.92  #    Propositional encoding time       : 0.000
% 0.67/0.92  #    Propositional solver time         : 0.000
% 0.67/0.92  #    Success case prop preproc time    : 0.000
% 0.67/0.92  #    Success case prop encoding time   : 0.000
% 0.67/0.92  #    Success case prop solver time     : 0.000
% 0.67/0.92  # Current number of processed clauses  : 347
% 0.67/0.92  #    Positive orientable unit clauses  : 301
% 0.67/0.92  #    Positive unorientable unit clauses: 10
% 0.67/0.92  #    Negative unit clauses             : 0
% 0.67/0.92  #    Non-unit-clauses                  : 36
% 0.67/0.92  # Current number of unprocessed clauses: 58971
% 0.67/0.92  # ...number of literals in the above   : 62444
% 0.67/0.92  # Current number of archived formulas  : 0
% 0.67/0.92  # Current number of archived clauses   : 139
% 0.67/0.92  # Clause-clause subsumption calls (NU) : 1316
% 0.67/0.92  # Rec. Clause-clause subsumption calls : 1316
% 0.67/0.92  # Non-unit clause-clause subsumptions  : 247
% 0.67/0.92  # Unit Clause-clause subsumption calls : 75
% 0.67/0.92  # Rewrite failures with RHS unbound    : 0
% 0.67/0.92  # BW rewrite match attempts            : 2891
% 0.67/0.92  # BW rewrite match successes           : 530
% 0.67/0.92  # Condensation attempts                : 0
% 0.67/0.92  # Condensation successes               : 0
% 0.67/0.92  # Termbank termtop insertions          : 987018
% 0.76/0.93  
% 0.76/0.93  # -------------------------------------------------
% 0.76/0.93  # User time                : 0.546 s
% 0.76/0.93  # System time              : 0.037 s
% 0.76/0.93  # Total time               : 0.583 s
% 0.76/0.93  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
