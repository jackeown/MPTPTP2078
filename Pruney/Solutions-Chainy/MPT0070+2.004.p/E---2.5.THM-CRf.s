%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 263 expanded)
%              Number of clauses        :   41 ( 116 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :   84 ( 329 expanded)
%              Number of equality atoms :   44 ( 205 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X2,X3) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_xboole_1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_13,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_29,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X15] : k2_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_34])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32]),c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40]),c_0_38]),c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_58]),c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_43])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t63_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.38  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t63_xboole_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  fof(c_0_13, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.38  fof(c_0_15, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  fof(c_0_27, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.38  fof(c_0_28, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.38  fof(c_0_29, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_24])).
% 0.13/0.38  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  fof(c_0_35, plain, ![X15]:k2_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.38  fof(c_0_36, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_43, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_34])).
% 0.13/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_43])).
% 0.13/0.38  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_41])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_50, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32]), c_0_34])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_46])).
% 0.13/0.38  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_41])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_33, c_0_49])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40]), c_0_38]), c_0_40])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_54, c_0_32])).
% 0.13/0.38  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_57, c_0_19])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_58]), c_0_38])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_43])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_61]), c_0_62]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 64
% 0.13/0.38  # Proof object clause steps            : 41
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 24
% 0.13/0.38  # Proof object simplifying inferences  : 21
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 15
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 143
% 0.13/0.38  # ...of these trivial                  : 45
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 98
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 5
% 0.13/0.38  # Generated clauses                    : 996
% 0.13/0.38  # ...of the previous two non-trivial   : 416
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 993
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 78
% 0.13/0.38  #    Positive orientable unit clauses  : 64
% 0.13/0.38  #    Positive unorientable unit clauses: 3
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 10
% 0.13/0.38  # Current number of unprocessed clauses: 300
% 0.13/0.38  # ...number of literals in the above   : 317
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 21
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 17
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 17
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 46
% 0.13/0.38  # BW rewrite match successes           : 16
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8451
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
