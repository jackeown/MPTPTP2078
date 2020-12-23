%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:07 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 278 expanded)
%              Number of clauses        :   30 ( 123 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 296 expanded)
%              Number of equality atoms :   45 ( 259 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_10,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] : k2_xboole_0(k2_xboole_0(X18,X19),X20) = k2_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X13,X14] : k4_xboole_0(k2_xboole_0(X13,X14),X14) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_22]),c_0_27])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_30])).

fof(c_0_36,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_32]),c_0_24]),c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_33])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_40]),c_0_27]),c_0_24])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0)) != k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_15]),c_0_15])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28]),c_0_20]),c_0_44]),c_0_45]),c_0_28]),c_0_20]),c_0_44]),c_0_28]),c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.63/0.79  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.63/0.79  # and selection function SelectNewComplexAHP.
% 0.63/0.79  #
% 0.63/0.79  # Preprocessing time       : 0.026 s
% 0.63/0.79  # Presaturation interreduction done
% 0.63/0.79  
% 0.63/0.79  # Proof found!
% 0.63/0.79  # SZS status Theorem
% 0.63/0.79  # SZS output start CNFRefutation
% 0.63/0.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.63/0.79  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.63/0.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.63/0.79  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.63/0.79  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.63/0.79  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.63/0.79  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.63/0.79  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.63/0.79  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.63/0.79  fof(c_0_9, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.63/0.79  fof(c_0_10, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.63/0.79  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.63/0.79  fof(c_0_12, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.63/0.79  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.63/0.79  cnf(c_0_14, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.63/0.79  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.63/0.79  fof(c_0_16, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.63/0.79  cnf(c_0_17, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.63/0.79  fof(c_0_18, plain, ![X18, X19, X20]:k2_xboole_0(k2_xboole_0(X18,X19),X20)=k2_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.63/0.79  cnf(c_0_19, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.63/0.79  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.63/0.79  fof(c_0_21, plain, ![X13, X14]:k4_xboole_0(k2_xboole_0(X13,X14),X14)=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.63/0.79  cnf(c_0_22, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.63/0.79  fof(c_0_23, plain, ![X15, X16, X17]:k4_xboole_0(k4_xboole_0(X15,X16),X17)=k4_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.63/0.79  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.63/0.79  cnf(c_0_25, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.63/0.79  cnf(c_0_26, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.79  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.63/0.79  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.63/0.79  cnf(c_0_29, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.63/0.79  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_22]), c_0_27])).
% 0.63/0.79  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 0.63/0.79  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 0.63/0.79  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_15])).
% 0.63/0.79  cnf(c_0_34, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_24])).
% 0.63/0.79  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_30])).
% 0.63/0.79  fof(c_0_36, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.63/0.79  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.63/0.79  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_32]), c_0_24]), c_0_33])).
% 0.63/0.79  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_33])).
% 0.63/0.79  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_15])).
% 0.63/0.79  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.63/0.79  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_15])).
% 0.63/0.79  cnf(c_0_43, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.63/0.79  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_40]), c_0_27]), c_0_24])).
% 0.63/0.79  cnf(c_0_45, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_22])).
% 0.63/0.79  cnf(c_0_46, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0))!=k4_xboole_0(k2_xboole_0(esk2_0,esk1_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_15]), c_0_15])).
% 0.63/0.79  cnf(c_0_47, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28]), c_0_20]), c_0_44]), c_0_45]), c_0_28]), c_0_20]), c_0_44]), c_0_28]), c_0_17])).
% 0.63/0.79  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])]), ['proof']).
% 0.63/0.79  # SZS output end CNFRefutation
% 0.63/0.79  # Proof object total steps             : 49
% 0.63/0.79  # Proof object clause steps            : 30
% 0.63/0.79  # Proof object formula steps           : 19
% 0.63/0.79  # Proof object conjectures             : 6
% 0.63/0.79  # Proof object clause conjectures      : 3
% 0.63/0.79  # Proof object formula conjectures     : 3
% 0.63/0.79  # Proof object initial clauses used    : 9
% 0.63/0.79  # Proof object initial formulas used   : 9
% 0.63/0.79  # Proof object generating inferences   : 19
% 0.63/0.79  # Proof object simplifying inferences  : 24
% 0.63/0.79  # Training examples: 0 positive, 0 negative
% 0.63/0.79  # Parsed axioms                        : 9
% 0.63/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.79  # Initial clauses                      : 9
% 0.63/0.79  # Removed in clause preprocessing      : 0
% 0.63/0.79  # Initial clauses in saturation        : 9
% 0.63/0.79  # Processed clauses                    : 1765
% 0.63/0.79  # ...of these trivial                  : 957
% 0.63/0.79  # ...subsumed                          : 483
% 0.63/0.79  # ...remaining for further processing  : 325
% 0.63/0.79  # Other redundant clauses eliminated   : 0
% 0.63/0.79  # Clauses deleted for lack of memory   : 0
% 0.63/0.79  # Backward-subsumed                    : 0
% 0.63/0.79  # Backward-rewritten                   : 35
% 0.63/0.79  # Generated clauses                    : 63205
% 0.63/0.79  # ...of the previous two non-trivial   : 40940
% 0.63/0.79  # Contextual simplify-reflections      : 0
% 0.63/0.79  # Paramodulations                      : 63205
% 0.63/0.79  # Factorizations                       : 0
% 0.63/0.79  # Equation resolutions                 : 0
% 0.63/0.79  # Propositional unsat checks           : 0
% 0.63/0.79  #    Propositional check models        : 0
% 0.63/0.79  #    Propositional check unsatisfiable : 0
% 0.63/0.79  #    Propositional clauses             : 0
% 0.63/0.79  #    Propositional clauses after purity: 0
% 0.63/0.79  #    Propositional unsat core size     : 0
% 0.63/0.79  #    Propositional preprocessing time  : 0.000
% 0.63/0.79  #    Propositional encoding time       : 0.000
% 0.63/0.79  #    Propositional solver time         : 0.000
% 0.63/0.79  #    Success case prop preproc time    : 0.000
% 0.63/0.79  #    Success case prop encoding time   : 0.000
% 0.63/0.79  #    Success case prop solver time     : 0.000
% 0.63/0.79  # Current number of processed clauses  : 281
% 0.63/0.79  #    Positive orientable unit clauses  : 276
% 0.63/0.79  #    Positive unorientable unit clauses: 4
% 0.63/0.79  #    Negative unit clauses             : 0
% 0.63/0.79  #    Non-unit-clauses                  : 1
% 0.63/0.79  # Current number of unprocessed clauses: 39001
% 0.63/0.79  # ...number of literals in the above   : 39001
% 0.63/0.79  # Current number of archived formulas  : 0
% 0.63/0.79  # Current number of archived clauses   : 44
% 0.63/0.79  # Clause-clause subsumption calls (NU) : 0
% 0.63/0.79  # Rec. Clause-clause subsumption calls : 0
% 0.63/0.79  # Non-unit clause-clause subsumptions  : 0
% 0.63/0.79  # Unit Clause-clause subsumption calls : 21
% 0.63/0.79  # Rewrite failures with RHS unbound    : 0
% 0.63/0.79  # BW rewrite match attempts            : 1633
% 0.63/0.79  # BW rewrite match successes           : 116
% 0.63/0.79  # Condensation attempts                : 0
% 0.63/0.79  # Condensation successes               : 0
% 0.63/0.79  # Termbank termtop insertions          : 730269
% 0.63/0.80  
% 0.63/0.80  # -------------------------------------------------
% 0.63/0.80  # User time                : 0.435 s
% 0.63/0.80  # System time              : 0.025 s
% 0.63/0.80  # Total time               : 0.460 s
% 0.63/0.80  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
