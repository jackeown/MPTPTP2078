%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:05 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 976 expanded)
%              Number of clauses        :   44 ( 453 expanded)
%              Number of leaves         :    7 ( 261 expanded)
%              Depth                    :   16
%              Number of atoms          :   69 (1281 expanded)
%              Number of equality atoms :   48 ( 823 expanded)
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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_8,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_14,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X13,X12)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X1),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19]),c_0_36]),c_0_22]),c_0_18]),c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_37]),c_0_35])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_38]),c_0_18])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

fof(c_0_44,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_43])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_42])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_46])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_48]),c_0_49])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_50]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_16]),c_0_16])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_18]),c_0_19]),c_0_54]),c_0_55]),c_0_18]),c_0_19]),c_0_54]),c_0_18]),c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.77  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.60/0.77  # and selection function SelectNewComplexAHP.
% 0.60/0.77  #
% 0.60/0.77  # Preprocessing time       : 0.026 s
% 0.60/0.77  # Presaturation interreduction done
% 0.60/0.77  
% 0.60/0.77  # Proof found!
% 0.60/0.77  # SZS status Theorem
% 0.60/0.77  # SZS output start CNFRefutation
% 0.60/0.77  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.60/0.77  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.60/0.77  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.60/0.77  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.60/0.77  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.60/0.77  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.60/0.77  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.60/0.77  fof(c_0_7, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.60/0.77  fof(c_0_8, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.60/0.77  fof(c_0_9, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.60/0.77  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.60/0.77  cnf(c_0_11, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.77  cnf(c_0_12, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.77  fof(c_0_13, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.60/0.77  fof(c_0_14, plain, ![X12, X13]:k2_xboole_0(X12,k4_xboole_0(X13,X12))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.60/0.77  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.77  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.77  cnf(c_0_17, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.60/0.77  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.77  cnf(c_0_19, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.77  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_12]), c_0_16])).
% 0.60/0.77  cnf(c_0_21, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.77  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.60/0.77  cnf(c_0_23, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.60/0.77  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.60/0.77  cnf(c_0_25, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.60/0.77  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.60/0.77  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.60/0.77  cnf(c_0_28, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.60/0.77  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.60/0.77  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.60/0.77  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 0.60/0.77  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_29])).
% 0.60/0.77  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_16])).
% 0.60/0.77  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.60/0.77  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X1),X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.60/0.77  cnf(c_0_36, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_33])).
% 0.60/0.77  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X2,X1),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19]), c_0_36]), c_0_22]), c_0_18]), c_0_29])).
% 0.60/0.77  cnf(c_0_38, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_37]), c_0_35])).
% 0.60/0.77  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 0.60/0.77  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 0.60/0.77  cnf(c_0_41, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_38]), c_0_18])).
% 0.60/0.77  cnf(c_0_42, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_30])).
% 0.60/0.77  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 0.60/0.77  fof(c_0_44, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.60/0.77  cnf(c_0_45, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_19])).
% 0.60/0.77  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.60/0.77  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.60/0.77  cnf(c_0_48, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_18]), c_0_18]), c_0_18])).
% 0.60/0.77  cnf(c_0_49, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_43])).
% 0.60/0.77  cnf(c_0_50, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_15, c_0_43])).
% 0.60/0.77  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.60/0.77  cnf(c_0_52, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_42])).
% 0.60/0.77  cnf(c_0_53, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_46])).
% 0.60/0.77  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_22]), c_0_48]), c_0_49])).
% 0.60/0.77  cnf(c_0_55, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_50]), c_0_50])).
% 0.60/0.77  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_16]), c_0_16])).
% 0.60/0.77  cnf(c_0_57, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_18]), c_0_19]), c_0_54]), c_0_55]), c_0_18]), c_0_19]), c_0_54]), c_0_18]), c_0_29])).
% 0.60/0.77  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 0.60/0.77  # SZS output end CNFRefutation
% 0.60/0.77  # Proof object total steps             : 59
% 0.60/0.77  # Proof object clause steps            : 44
% 0.60/0.77  # Proof object formula steps           : 15
% 0.60/0.77  # Proof object conjectures             : 6
% 0.60/0.77  # Proof object clause conjectures      : 3
% 0.60/0.77  # Proof object formula conjectures     : 3
% 0.60/0.77  # Proof object initial clauses used    : 8
% 0.60/0.77  # Proof object initial formulas used   : 7
% 0.60/0.77  # Proof object generating inferences   : 33
% 0.60/0.77  # Proof object simplifying inferences  : 31
% 0.60/0.77  # Training examples: 0 positive, 0 negative
% 0.60/0.77  # Parsed axioms                        : 7
% 0.60/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.77  # Initial clauses                      : 8
% 0.60/0.77  # Removed in clause preprocessing      : 0
% 0.60/0.77  # Initial clauses in saturation        : 8
% 0.60/0.77  # Processed clauses                    : 2286
% 0.60/0.77  # ...of these trivial                  : 917
% 0.60/0.77  # ...subsumed                          : 969
% 0.60/0.77  # ...remaining for further processing  : 400
% 0.60/0.77  # Other redundant clauses eliminated   : 0
% 0.60/0.77  # Clauses deleted for lack of memory   : 0
% 0.60/0.77  # Backward-subsumed                    : 0
% 0.60/0.77  # Backward-rewritten                   : 126
% 0.60/0.77  # Generated clauses                    : 61188
% 0.60/0.77  # ...of the previous two non-trivial   : 39411
% 0.60/0.77  # Contextual simplify-reflections      : 0
% 0.60/0.77  # Paramodulations                      : 61187
% 0.60/0.77  # Factorizations                       : 0
% 0.60/0.77  # Equation resolutions                 : 1
% 0.60/0.77  # Propositional unsat checks           : 0
% 0.60/0.77  #    Propositional check models        : 0
% 0.60/0.77  #    Propositional check unsatisfiable : 0
% 0.60/0.77  #    Propositional clauses             : 0
% 0.60/0.77  #    Propositional clauses after purity: 0
% 0.60/0.77  #    Propositional unsat core size     : 0
% 0.60/0.77  #    Propositional preprocessing time  : 0.000
% 0.60/0.77  #    Propositional encoding time       : 0.000
% 0.60/0.77  #    Propositional solver time         : 0.000
% 0.60/0.77  #    Success case prop preproc time    : 0.000
% 0.60/0.77  #    Success case prop encoding time   : 0.000
% 0.60/0.77  #    Success case prop solver time     : 0.000
% 0.60/0.77  # Current number of processed clauses  : 266
% 0.60/0.77  #    Positive orientable unit clauses  : 234
% 0.60/0.77  #    Positive unorientable unit clauses: 7
% 0.60/0.77  #    Negative unit clauses             : 0
% 0.60/0.77  #    Non-unit-clauses                  : 25
% 0.60/0.77  # Current number of unprocessed clauses: 35778
% 0.60/0.77  # ...number of literals in the above   : 37830
% 0.60/0.77  # Current number of archived formulas  : 0
% 0.60/0.77  # Current number of archived clauses   : 134
% 0.60/0.77  # Clause-clause subsumption calls (NU) : 381
% 0.60/0.77  # Rec. Clause-clause subsumption calls : 381
% 0.60/0.77  # Non-unit clause-clause subsumptions  : 90
% 0.60/0.77  # Unit Clause-clause subsumption calls : 63
% 0.60/0.77  # Rewrite failures with RHS unbound    : 0
% 0.60/0.77  # BW rewrite match attempts            : 1476
% 0.60/0.77  # BW rewrite match successes           : 369
% 0.60/0.77  # Condensation attempts                : 0
% 0.60/0.77  # Condensation successes               : 0
% 0.60/0.77  # Termbank termtop insertions          : 635319
% 0.60/0.77  
% 0.60/0.77  # -------------------------------------------------
% 0.60/0.77  # User time                : 0.413 s
% 0.60/0.77  # System time              : 0.022 s
% 0.60/0.77  # Total time               : 0.435 s
% 0.60/0.77  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
