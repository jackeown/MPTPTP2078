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
% DateTime   : Thu Dec  3 10:32:27 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 269 expanded)
%              Number of clauses        :   25 ( 120 expanded)
%              Number of leaves         :   10 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 269 expanded)
%              Number of equality atoms :   45 ( 268 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t55_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_10,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k2_xboole_0(X22,X23)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_11,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_12,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X27,X28,X29] : k2_xboole_0(k2_xboole_0(X27,X28),X29) = k2_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])).

fof(c_0_20,plain,(
    ! [X30,X31] : k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t55_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_25]),c_0_16])).

fof(c_0_30,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_31,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k2_xboole_0(X19,X20),X21) = k2_xboole_0(k4_xboole_0(X19,X21),k4_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_32,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_14])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_14]),c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X3,X1),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_39]),c_0_39])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:44:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.54  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.18/0.54  # and selection function SelectNewComplexAHP.
% 0.18/0.54  #
% 0.18/0.54  # Preprocessing time       : 0.026 s
% 0.18/0.54  # Presaturation interreduction done
% 0.18/0.54  
% 0.18/0.54  # Proof found!
% 0.18/0.54  # SZS status Theorem
% 0.18/0.54  # SZS output start CNFRefutation
% 0.18/0.54  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.18/0.54  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.18/0.54  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.54  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.54  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.18/0.54  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.54  fof(t55_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.18/0.54  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.18/0.54  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.54  fof(c_0_10, plain, ![X22, X23]:k4_xboole_0(X22,k2_xboole_0(X22,X23))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.18/0.54  fof(c_0_11, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.18/0.54  fof(c_0_12, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.54  cnf(c_0_13, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.54  cnf(c_0_14, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.54  fof(c_0_15, plain, ![X27, X28, X29]:k2_xboole_0(k2_xboole_0(X27,X28),X29)=k2_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.54  cnf(c_0_16, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.54  cnf(c_0_17, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.54  cnf(c_0_18, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.54  cnf(c_0_19, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_14])).
% 0.18/0.54  fof(c_0_20, plain, ![X30, X31]:k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.18/0.54  fof(c_0_21, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.54  cnf(c_0_22, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.54  cnf(c_0_23, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.54  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.54  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.54  fof(c_0_26, negated_conjecture, ~(![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t55_xboole_1])).
% 0.18/0.54  cnf(c_0_27, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.54  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.54  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_25]), c_0_16])).
% 0.18/0.54  fof(c_0_30, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.18/0.54  fof(c_0_31, plain, ![X19, X20, X21]:k4_xboole_0(k2_xboole_0(X19,X20),X21)=k2_xboole_0(k4_xboole_0(X19,X21),k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.18/0.54  fof(c_0_32, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.18/0.54  cnf(c_0_33, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.54  cnf(c_0_34, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_14])).
% 0.18/0.54  cnf(c_0_35, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_14]), c_0_18])).
% 0.18/0.54  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.54  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.54  cnf(c_0_38, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.54  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.18/0.54  cnf(c_0_40, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.18/0.54  cnf(c_0_41, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2)))=k4_xboole_0(k2_xboole_0(X3,X1),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.18/0.54  cnf(c_0_42, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.18/0.54  cnf(c_0_43, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_39]), c_0_39])).
% 0.18/0.54  cnf(c_0_44, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.54  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_39])]), ['proof']).
% 0.18/0.54  # SZS output end CNFRefutation
% 0.18/0.54  # Proof object total steps             : 46
% 0.18/0.54  # Proof object clause steps            : 25
% 0.18/0.54  # Proof object formula steps           : 21
% 0.18/0.54  # Proof object conjectures             : 7
% 0.18/0.54  # Proof object clause conjectures      : 4
% 0.18/0.54  # Proof object formula conjectures     : 3
% 0.18/0.54  # Proof object initial clauses used    : 10
% 0.18/0.54  # Proof object initial formulas used   : 10
% 0.18/0.54  # Proof object generating inferences   : 12
% 0.18/0.54  # Proof object simplifying inferences  : 13
% 0.18/0.54  # Training examples: 0 positive, 0 negative
% 0.18/0.54  # Parsed axioms                        : 15
% 0.18/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.54  # Initial clauses                      : 16
% 0.18/0.54  # Removed in clause preprocessing      : 0
% 0.18/0.54  # Initial clauses in saturation        : 16
% 0.18/0.54  # Processed clauses                    : 1633
% 0.18/0.54  # ...of these trivial                  : 828
% 0.18/0.54  # ...subsumed                          : 432
% 0.18/0.54  # ...remaining for further processing  : 373
% 0.18/0.54  # Other redundant clauses eliminated   : 0
% 0.18/0.54  # Clauses deleted for lack of memory   : 0
% 0.18/0.54  # Backward-subsumed                    : 2
% 0.18/0.54  # Backward-rewritten                   : 28
% 0.18/0.54  # Generated clauses                    : 32754
% 0.18/0.54  # ...of the previous two non-trivial   : 17176
% 0.18/0.54  # Contextual simplify-reflections      : 0
% 0.18/0.54  # Paramodulations                      : 32740
% 0.18/0.54  # Factorizations                       : 0
% 0.18/0.54  # Equation resolutions                 : 14
% 0.18/0.54  # Propositional unsat checks           : 0
% 0.18/0.54  #    Propositional check models        : 0
% 0.18/0.54  #    Propositional check unsatisfiable : 0
% 0.18/0.54  #    Propositional clauses             : 0
% 0.18/0.54  #    Propositional clauses after purity: 0
% 0.18/0.54  #    Propositional unsat core size     : 0
% 0.18/0.54  #    Propositional preprocessing time  : 0.000
% 0.18/0.54  #    Propositional encoding time       : 0.000
% 0.18/0.54  #    Propositional solver time         : 0.000
% 0.18/0.54  #    Success case prop preproc time    : 0.000
% 0.18/0.54  #    Success case prop encoding time   : 0.000
% 0.18/0.54  #    Success case prop solver time     : 0.000
% 0.18/0.54  # Current number of processed clauses  : 327
% 0.18/0.54  #    Positive orientable unit clauses  : 281
% 0.18/0.54  #    Positive unorientable unit clauses: 4
% 0.18/0.54  #    Negative unit clauses             : 0
% 0.18/0.54  #    Non-unit-clauses                  : 42
% 0.18/0.54  # Current number of unprocessed clauses: 15431
% 0.18/0.54  # ...number of literals in the above   : 16498
% 0.18/0.54  # Current number of archived formulas  : 0
% 0.18/0.54  # Current number of archived clauses   : 46
% 0.18/0.54  # Clause-clause subsumption calls (NU) : 1123
% 0.18/0.54  # Rec. Clause-clause subsumption calls : 1123
% 0.18/0.54  # Non-unit clause-clause subsumptions  : 352
% 0.18/0.54  # Unit Clause-clause subsumption calls : 29
% 0.18/0.54  # Rewrite failures with RHS unbound    : 0
% 0.18/0.54  # BW rewrite match attempts            : 655
% 0.18/0.54  # BW rewrite match successes           : 146
% 0.18/0.54  # Condensation attempts                : 0
% 0.18/0.54  # Condensation successes               : 0
% 0.18/0.54  # Termbank termtop insertions          : 237838
% 0.18/0.54  
% 0.18/0.54  # -------------------------------------------------
% 0.18/0.54  # User time                : 0.196 s
% 0.18/0.54  # System time              : 0.011 s
% 0.18/0.54  # Total time               : 0.207 s
% 0.18/0.54  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
