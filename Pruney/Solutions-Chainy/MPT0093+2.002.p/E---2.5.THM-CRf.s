%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:49 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (4219 expanded)
%              Number of clauses        :   46 (1867 expanded)
%              Number of leaves         :    7 (1163 expanded)
%              Depth                    :   18
%              Number of atoms          :   81 (4670 expanded)
%              Number of equality atoms :   51 (4153 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t86_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_7,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] : k3_xboole_0(X11,k4_xboole_0(X12,X13)) = k4_xboole_0(k3_xboole_0(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k4_xboole_0(X14,X15) = X14 )
      & ( k4_xboole_0(X14,X15) != X14
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_11]),c_0_11])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t86_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X1)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) != X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_16])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_31]),c_0_16])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_32]),c_0_30]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_33]),c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_20]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_16])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) != k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_38]),c_0_36]),c_0_21]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),k4_xboole_0(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_41])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_46]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_47]),c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2))) = k4_xboole_0(k4_xboole_0(esk1_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_42]),c_0_21]),c_0_42]),c_0_44]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_54]),c_0_16]),c_0_16])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_42]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.21/0.46  # and selection function SelectNewComplexAHP.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.027 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.46  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.21/0.46  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.46  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.46  fof(t86_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.21/0.46  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.46  fof(c_0_7, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.46  fof(c_0_8, plain, ![X9, X10]:k4_xboole_0(X9,k4_xboole_0(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.46  fof(c_0_9, plain, ![X11, X12, X13]:k3_xboole_0(X11,k4_xboole_0(X12,X13))=k4_xboole_0(k3_xboole_0(X11,X12),X13), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.21/0.46  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.46  fof(c_0_12, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.46  cnf(c_0_13, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.46  fof(c_0_14, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k4_xboole_0(X14,X15)=X14)&(k4_xboole_0(X14,X15)!=X14|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.46  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.21/0.46  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.46  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_11]), c_0_11])).
% 0.21/0.46  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t86_xboole_1])).
% 0.21/0.46  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.46  cnf(c_0_20, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.46  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.21/0.46  fof(c_0_22, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.46  fof(c_0_23, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.21/0.46  cnf(c_0_24, plain, (r1_xboole_0(X1,X1)|k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))!=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.46  cnf(c_0_25, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_16])).
% 0.21/0.46  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.46  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.46  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.46  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])).
% 0.21/0.46  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_21])).
% 0.21/0.46  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.46  cnf(c_0_32, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.21/0.46  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_31]), c_0_16])).
% 0.21/0.46  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_32]), c_0_30]), c_0_32])).
% 0.21/0.46  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_33]), c_0_31])).
% 0.21/0.46  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_20]), c_0_25])).
% 0.21/0.46  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_16])).
% 0.21/0.46  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X1)=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_36]), c_0_36]), c_0_36])).
% 0.21/0.46  cnf(c_0_39, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))!=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.21/0.46  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk1_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_31])).
% 0.21/0.46  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.46  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_38]), c_0_36]), c_0_21]), c_0_32])).
% 0.21/0.46  cnf(c_0_43, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),k4_xboole_0(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.21/0.46  cnf(c_0_44, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_40]), c_0_16])).
% 0.21/0.46  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(spm,[status(thm)],[c_0_28, c_0_41])).
% 0.21/0.46  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_36, c_0_42])).
% 0.21/0.46  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_16])).
% 0.21/0.46  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0)),esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 0.21/0.46  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_46]), c_0_46])).
% 0.21/0.46  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_47]), c_0_25])).
% 0.21/0.46  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_16])).
% 0.21/0.46  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),X2)))=k4_xboole_0(k4_xboole_0(esk1_0,X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_33])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.46  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_51])).
% 0.21/0.46  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_42]), c_0_21]), c_0_42]), c_0_44]), c_0_53])).
% 0.21/0.46  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_54]), c_0_16]), c_0_16])).
% 0.21/0.46  cnf(c_0_57, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.46  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_42]), c_0_56])).
% 0.21/0.46  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.46  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 61
% 0.21/0.46  # Proof object clause steps            : 46
% 0.21/0.46  # Proof object formula steps           : 15
% 0.21/0.46  # Proof object conjectures             : 25
% 0.21/0.46  # Proof object clause conjectures      : 22
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 11
% 0.21/0.46  # Proof object initial formulas used   : 7
% 0.21/0.46  # Proof object generating inferences   : 32
% 0.21/0.46  # Proof object simplifying inferences  : 36
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 7
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 11
% 0.21/0.46  # Removed in clause preprocessing      : 1
% 0.21/0.46  # Initial clauses in saturation        : 10
% 0.21/0.46  # Processed clauses                    : 571
% 0.21/0.46  # ...of these trivial                  : 131
% 0.21/0.46  # ...subsumed                          : 147
% 0.21/0.46  # ...remaining for further processing  : 293
% 0.21/0.46  # Other redundant clauses eliminated   : 0
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 0
% 0.21/0.46  # Backward-rewritten                   : 43
% 0.21/0.46  # Generated clauses                    : 7984
% 0.21/0.46  # ...of the previous two non-trivial   : 4254
% 0.21/0.46  # Contextual simplify-reflections      : 0
% 0.21/0.46  # Paramodulations                      : 7983
% 0.21/0.46  # Factorizations                       : 0
% 0.21/0.46  # Equation resolutions                 : 1
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 240
% 0.21/0.46  #    Positive orientable unit clauses  : 197
% 0.21/0.46  #    Positive unorientable unit clauses: 5
% 0.21/0.46  #    Negative unit clauses             : 1
% 0.21/0.46  #    Non-unit-clauses                  : 37
% 0.21/0.46  # Current number of unprocessed clauses: 3651
% 0.21/0.46  # ...number of literals in the above   : 4325
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 54
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 182
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 182
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 73
% 0.21/0.46  # Unit Clause-clause subsumption calls : 141
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 850
% 0.21/0.46  # BW rewrite match successes           : 75
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 109379
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.104 s
% 0.21/0.46  # System time              : 0.008 s
% 0.21/0.46  # Total time               : 0.113 s
% 0.21/0.46  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
