%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 100 expanded)
%              Number of clauses        :   28 (  45 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 149 expanded)
%              Number of equality atoms :   37 (  81 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_9,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_10,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_12,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_33]),c_0_25])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(X1,esk3_0)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.13/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.13/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.38  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.38  fof(c_0_9, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.13/0.38  fof(c_0_11, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.38  fof(c_0_12, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.38  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.38  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  fof(c_0_24, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.38  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_25])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.13/0.38  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k2_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_33]), c_0_25])).
% 0.13/0.38  cnf(c_0_37, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_39])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(X1,esk3_0))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 47
% 0.13/0.38  # Proof object clause steps            : 28
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 14
% 0.13/0.38  # Proof object clause conjectures      : 11
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 8
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 13
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 12
% 0.13/0.38  # Processed clauses                    : 99
% 0.13/0.38  # ...of these trivial                  : 23
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 76
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 15
% 0.13/0.38  # Generated clauses                    : 429
% 0.13/0.38  # ...of the previous two non-trivial   : 176
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 427
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
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
% 0.13/0.38  # Current number of processed clauses  : 49
% 0.13/0.38  #    Positive orientable unit clauses  : 37
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 10
% 0.13/0.38  # Current number of unprocessed clauses: 98
% 0.13/0.38  # ...number of literals in the above   : 112
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 28
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 5
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 5
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 2
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 49
% 0.13/0.38  # BW rewrite match successes           : 18
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3764
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
