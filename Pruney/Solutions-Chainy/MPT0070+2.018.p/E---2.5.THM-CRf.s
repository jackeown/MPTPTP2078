%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:38 EST 2020

% Result     : Theorem 0.45s
% Output     : CNFRefutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 128 expanded)
%              Number of clauses        :   37 (  57 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 200 expanded)
%              Number of equality atoms :   43 (  97 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t63_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_12,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_17,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_18,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] : k4_xboole_0(k4_xboole_0(X24,X25),X26) = k4_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_20,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_26,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_24])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X2,X3) )
       => r1_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_xboole_1])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_28])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_37,plain,(
    ! [X29,X30] : k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30)) = X29 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(X1,esk2_0) = X1
    | ~ r1_tarski(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_43]),c_0_24])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_29]),c_0_23]),c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,X2),esk2_0)
    | ~ r1_tarski(esk3_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_49]),c_0_24]),c_0_29]),c_0_50])).

fof(c_0_53,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.45/0.69  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.45/0.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.45/0.69  #
% 0.45/0.69  # Preprocessing time       : 0.026 s
% 0.45/0.69  # Presaturation interreduction done
% 0.45/0.69  
% 0.45/0.69  # Proof found!
% 0.45/0.69  # SZS status Theorem
% 0.45/0.69  # SZS output start CNFRefutation
% 0.45/0.69  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.45/0.69  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.45/0.69  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.45/0.69  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.45/0.69  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.45/0.69  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.45/0.69  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.45/0.69  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.45/0.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.45/0.69  fof(t63_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.45/0.69  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.45/0.69  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.45/0.69  fof(c_0_12, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.45/0.69  fof(c_0_13, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.45/0.69  cnf(c_0_14, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.45/0.69  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.45/0.69  fof(c_0_16, plain, ![X19, X20]:r1_tarski(k4_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.45/0.69  fof(c_0_17, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.45/0.69  fof(c_0_18, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.45/0.69  fof(c_0_19, plain, ![X24, X25, X26]:k4_xboole_0(k4_xboole_0(X24,X25),X26)=k4_xboole_0(X24,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.45/0.69  cnf(c_0_20, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.45/0.69  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.45/0.69  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.45/0.69  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.45/0.69  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.45/0.69  fof(c_0_25, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.45/0.69  fof(c_0_26, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.45/0.69  cnf(c_0_27, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.45/0.69  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.45/0.69  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.45/0.69  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_24])).
% 0.45/0.69  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t63_xboole_1])).
% 0.45/0.69  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.45/0.69  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.45/0.69  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_28])).
% 0.45/0.69  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.45/0.69  fof(c_0_36, negated_conjecture, ((r1_tarski(esk2_0,esk3_0)&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.45/0.69  fof(c_0_37, plain, ![X29, X30]:k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30))=X29, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.45/0.69  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.45/0.69  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.45/0.69  cnf(c_0_40, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.45/0.69  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.45/0.69  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_15])).
% 0.45/0.69  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk2_0,X1)=k1_xboole_0|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.45/0.69  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.45/0.69  cnf(c_0_45, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_41, c_0_33])).
% 0.45/0.69  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.45/0.69  cnf(c_0_47, negated_conjecture, (k2_xboole_0(X1,esk2_0)=X1|~r1_tarski(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_43]), c_0_24])).
% 0.45/0.69  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.45/0.69  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_33])).
% 0.45/0.69  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_29]), c_0_23]), c_0_29])).
% 0.45/0.69  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,X2),esk2_0)|~r1_tarski(esk3_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.45/0.69  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_49]), c_0_24]), c_0_29]), c_0_50])).
% 0.45/0.69  fof(c_0_53, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.45/0.69  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(esk3_0,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.45/0.69  cnf(c_0_55, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.45/0.69  cnf(c_0_56, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 0.45/0.69  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.45/0.69  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.45/0.69  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 0.45/0.69  cnf(c_0_60, negated_conjecture, (~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.45/0.69  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.45/0.69  # SZS output end CNFRefutation
% 0.45/0.69  # Proof object total steps             : 62
% 0.45/0.69  # Proof object clause steps            : 37
% 0.45/0.69  # Proof object formula steps           : 25
% 0.45/0.69  # Proof object conjectures             : 14
% 0.45/0.69  # Proof object clause conjectures      : 11
% 0.45/0.69  # Proof object formula conjectures     : 3
% 0.45/0.69  # Proof object initial clauses used    : 15
% 0.45/0.69  # Proof object initial formulas used   : 12
% 0.45/0.69  # Proof object generating inferences   : 18
% 0.45/0.69  # Proof object simplifying inferences  : 15
% 0.45/0.69  # Training examples: 0 positive, 0 negative
% 0.45/0.69  # Parsed axioms                        : 13
% 0.45/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.45/0.69  # Initial clauses                      : 18
% 0.45/0.69  # Removed in clause preprocessing      : 1
% 0.45/0.69  # Initial clauses in saturation        : 17
% 0.45/0.69  # Processed clauses                    : 4447
% 0.45/0.69  # ...of these trivial                  : 36
% 0.45/0.69  # ...subsumed                          : 3855
% 0.45/0.69  # ...remaining for further processing  : 556
% 0.45/0.69  # Other redundant clauses eliminated   : 0
% 0.45/0.69  # Clauses deleted for lack of memory   : 0
% 0.45/0.69  # Backward-subsumed                    : 65
% 0.45/0.69  # Backward-rewritten                   : 21
% 0.45/0.69  # Generated clauses                    : 30166
% 0.45/0.69  # ...of the previous two non-trivial   : 25877
% 0.45/0.69  # Contextual simplify-reflections      : 6
% 0.45/0.69  # Paramodulations                      : 30165
% 0.45/0.69  # Factorizations                       : 0
% 0.45/0.69  # Equation resolutions                 : 1
% 0.45/0.69  # Propositional unsat checks           : 0
% 0.45/0.69  #    Propositional check models        : 0
% 0.45/0.69  #    Propositional check unsatisfiable : 0
% 0.45/0.69  #    Propositional clauses             : 0
% 0.45/0.69  #    Propositional clauses after purity: 0
% 0.45/0.69  #    Propositional unsat core size     : 0
% 0.45/0.69  #    Propositional preprocessing time  : 0.000
% 0.45/0.69  #    Propositional encoding time       : 0.000
% 0.45/0.69  #    Propositional solver time         : 0.000
% 0.45/0.69  #    Success case prop preproc time    : 0.000
% 0.45/0.69  #    Success case prop encoding time   : 0.000
% 0.45/0.69  #    Success case prop solver time     : 0.000
% 0.45/0.69  # Current number of processed clauses  : 453
% 0.45/0.69  #    Positive orientable unit clauses  : 57
% 0.45/0.69  #    Positive unorientable unit clauses: 3
% 0.45/0.69  #    Negative unit clauses             : 32
% 0.45/0.69  #    Non-unit-clauses                  : 361
% 0.45/0.69  # Current number of unprocessed clauses: 21269
% 0.45/0.69  # ...number of literals in the above   : 53832
% 0.45/0.69  # Current number of archived formulas  : 0
% 0.45/0.69  # Current number of archived clauses   : 104
% 0.45/0.69  # Clause-clause subsumption calls (NU) : 29482
% 0.45/0.69  # Rec. Clause-clause subsumption calls : 17128
% 0.45/0.69  # Non-unit clause-clause subsumptions  : 2331
% 0.45/0.69  # Unit Clause-clause subsumption calls : 3793
% 0.45/0.69  # Rewrite failures with RHS unbound    : 0
% 0.45/0.69  # BW rewrite match attempts            : 379
% 0.45/0.69  # BW rewrite match successes           : 71
% 0.45/0.69  # Condensation attempts                : 0
% 0.45/0.69  # Condensation successes               : 0
% 0.45/0.69  # Termbank termtop insertions          : 310985
% 0.45/0.69  
% 0.45/0.69  # -------------------------------------------------
% 0.45/0.69  # User time                : 0.326 s
% 0.45/0.69  # System time              : 0.017 s
% 0.45/0.69  # Total time               : 0.343 s
% 0.45/0.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
