%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:40 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 142 expanded)
%              Number of clauses        :   34 (  66 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 199 expanded)
%              Number of equality atoms :   37 ( 105 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X14,X15)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_17,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,X24),X24) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_18,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k3_xboole_0(X16,X17)) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_15]),c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,X1))) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,k4_xboole_0(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.49/0.72  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.49/0.72  # and selection function SelectNewComplexAHP.
% 0.49/0.72  #
% 0.49/0.72  # Preprocessing time       : 0.016 s
% 0.49/0.72  # Presaturation interreduction done
% 0.49/0.72  
% 0.49/0.72  # Proof found!
% 0.49/0.72  # SZS status Theorem
% 0.49/0.72  # SZS output start CNFRefutation
% 0.49/0.72  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.49/0.72  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.49/0.72  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.49/0.72  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.49/0.72  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.49/0.72  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.49/0.72  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.49/0.72  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.49/0.72  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.49/0.72  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.49/0.72  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.49/0.72  fof(c_0_11, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.49/0.72  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,k2_xboole_0(X14,X15))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.49/0.72  fof(c_0_13, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_xboole_0(X21,X22)|r1_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.49/0.72  cnf(c_0_14, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.49/0.72  cnf(c_0_15, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.49/0.72  fof(c_0_16, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.49/0.72  fof(c_0_17, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,X24),X24), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.49/0.72  fof(c_0_18, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.49/0.72  fof(c_0_19, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.49/0.72  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 0.49/0.72  cnf(c_0_21, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.49/0.72  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.49/0.72  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.49/0.72  cnf(c_0_24, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.72  fof(c_0_25, plain, ![X16, X17]:k4_xboole_0(X16,k3_xboole_0(X16,X17))=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.49/0.72  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.49/0.72  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.49/0.72  fof(c_0_28, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.49/0.72  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.49/0.72  cnf(c_0_30, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.49/0.72  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.49/0.72  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.49/0.72  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.49/0.72  fof(c_0_34, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.49/0.72  cnf(c_0_35, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.49/0.72  fof(c_0_36, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.49/0.72  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_27])).
% 0.49/0.72  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.49/0.72  cnf(c_0_39, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.49/0.72  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.49/0.72  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_35])).
% 0.49/0.72  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.49/0.72  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.49/0.72  cnf(c_0_44, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_15]), c_0_39])).
% 0.49/0.72  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_39])).
% 0.49/0.72  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_39])).
% 0.49/0.72  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.49/0.72  cnf(c_0_48, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.49/0.72  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 0.49/0.72  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,X1)))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42])).
% 0.49/0.72  cnf(c_0_51, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_14, c_0_48])).
% 0.49/0.72  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_42])).
% 0.49/0.72  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,k4_xboole_0(X1,X3)),X2)), inference(spm,[status(thm)],[c_0_21, c_0_51])).
% 0.49/0.72  cnf(c_0_54, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 0.49/0.72  cnf(c_0_55, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.49/0.72  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.49/0.72  # SZS output end CNFRefutation
% 0.49/0.72  # Proof object total steps             : 57
% 0.49/0.72  # Proof object clause steps            : 34
% 0.49/0.72  # Proof object formula steps           : 23
% 0.49/0.72  # Proof object conjectures             : 12
% 0.49/0.72  # Proof object clause conjectures      : 9
% 0.49/0.72  # Proof object formula conjectures     : 3
% 0.49/0.72  # Proof object initial clauses used    : 12
% 0.49/0.72  # Proof object initial formulas used   : 11
% 0.49/0.72  # Proof object generating inferences   : 20
% 0.49/0.72  # Proof object simplifying inferences  : 9
% 0.49/0.72  # Training examples: 0 positive, 0 negative
% 0.49/0.72  # Parsed axioms                        : 11
% 0.49/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.72  # Initial clauses                      : 14
% 0.49/0.72  # Removed in clause preprocessing      : 1
% 0.49/0.72  # Initial clauses in saturation        : 13
% 0.49/0.72  # Processed clauses                    : 2309
% 0.49/0.72  # ...of these trivial                  : 569
% 0.49/0.72  # ...subsumed                          : 125
% 0.49/0.72  # ...remaining for further processing  : 1615
% 0.49/0.72  # Other redundant clauses eliminated   : 0
% 0.49/0.72  # Clauses deleted for lack of memory   : 0
% 0.49/0.72  # Backward-subsumed                    : 1
% 0.49/0.72  # Backward-rewritten                   : 112
% 0.49/0.72  # Generated clauses                    : 83918
% 0.49/0.72  # ...of the previous two non-trivial   : 25501
% 0.49/0.72  # Contextual simplify-reflections      : 0
% 0.49/0.72  # Paramodulations                      : 83909
% 0.49/0.72  # Factorizations                       : 0
% 0.49/0.72  # Equation resolutions                 : 9
% 0.49/0.72  # Propositional unsat checks           : 0
% 0.49/0.72  #    Propositional check models        : 0
% 0.49/0.72  #    Propositional check unsatisfiable : 0
% 0.49/0.72  #    Propositional clauses             : 0
% 0.49/0.72  #    Propositional clauses after purity: 0
% 0.49/0.72  #    Propositional unsat core size     : 0
% 0.49/0.72  #    Propositional preprocessing time  : 0.000
% 0.49/0.72  #    Propositional encoding time       : 0.000
% 0.49/0.72  #    Propositional solver time         : 0.000
% 0.49/0.72  #    Success case prop preproc time    : 0.000
% 0.49/0.72  #    Success case prop encoding time   : 0.000
% 0.49/0.72  #    Success case prop solver time     : 0.000
% 0.49/0.72  # Current number of processed clauses  : 1489
% 0.49/0.72  #    Positive orientable unit clauses  : 1427
% 0.49/0.72  #    Positive unorientable unit clauses: 0
% 0.49/0.72  #    Negative unit clauses             : 1
% 0.49/0.72  #    Non-unit-clauses                  : 61
% 0.49/0.72  # Current number of unprocessed clauses: 22918
% 0.49/0.72  # ...number of literals in the above   : 24945
% 0.49/0.72  # Current number of archived formulas  : 0
% 0.49/0.72  # Current number of archived clauses   : 127
% 0.49/0.72  # Clause-clause subsumption calls (NU) : 510
% 0.49/0.72  # Rec. Clause-clause subsumption calls : 496
% 0.49/0.72  # Non-unit clause-clause subsumptions  : 126
% 0.49/0.72  # Unit Clause-clause subsumption calls : 43
% 0.49/0.72  # Rewrite failures with RHS unbound    : 0
% 0.49/0.72  # BW rewrite match attempts            : 10946
% 0.49/0.72  # BW rewrite match successes           : 112
% 0.49/0.72  # Condensation attempts                : 0
% 0.49/0.72  # Condensation successes               : 0
% 0.49/0.72  # Termbank termtop insertions          : 840064
% 0.49/0.72  
% 0.49/0.72  # -------------------------------------------------
% 0.49/0.72  # User time                : 0.354 s
% 0.49/0.72  # System time              : 0.012 s
% 0.49/0.72  # Total time               : 0.366 s
% 0.49/0.72  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
