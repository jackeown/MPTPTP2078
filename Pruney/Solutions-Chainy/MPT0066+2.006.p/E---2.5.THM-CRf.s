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
% DateTime   : Thu Dec  3 10:32:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 259 expanded)
%              Number of clauses        :   30 ( 112 expanded)
%              Number of leaves         :    9 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 483 expanded)
%              Number of equality atoms :   34 ( 197 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t59_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_9,plain,(
    ! [X18,X19] : k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X2,X3) )
       => r2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t59_xboole_1])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | ~ r2_xboole_0(X6,X7) )
      & ( X6 != X7
        | ~ r2_xboole_0(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | X6 = X7
        | r2_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk3_0)
    & ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

fof(c_0_30,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(k2_xboole_0(X11,X12),X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k1_xboole_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(X1,esk2_0) = esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_35]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 = esk3_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( esk1_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_18]),c_0_31]),c_0_18]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35])])).

fof(c_0_45,plain,(
    ! [X8] : ~ r2_xboole_0(X8,X8) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_28])])).

cnf(c_0_47,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.13/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.026 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.13/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.41  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.41  fof(t59_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 0.13/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.41  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.41  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.13/0.41  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.13/0.41  fof(c_0_9, plain, ![X18, X19]:k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.13/0.41  fof(c_0_10, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.41  cnf(c_0_11, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.41  fof(c_0_13, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.41  fof(c_0_14, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.41  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t59_xboole_1])).
% 0.13/0.41  fof(c_0_16, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.41  cnf(c_0_17, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.41  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.41  cnf(c_0_19, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.41  fof(c_0_20, plain, ![X6, X7]:(((r1_tarski(X6,X7)|~r2_xboole_0(X6,X7))&(X6!=X7|~r2_xboole_0(X6,X7)))&(~r1_tarski(X6,X7)|X6=X7|r2_xboole_0(X6,X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.41  fof(c_0_21, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r2_xboole_0(esk2_0,esk3_0))&~r2_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.41  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_18])).
% 0.13/0.41  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_25, negated_conjecture, (r2_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_26, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.13/0.41  cnf(c_0_27, plain, (k2_xboole_0(X1,k1_xboole_0)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.41  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.13/0.41  fof(c_0_30, plain, ![X11, X12, X13]:(~r1_tarski(k2_xboole_0(X11,X12),X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_18])).
% 0.13/0.41  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k1_xboole_0,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.13/0.41  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.41  cnf(c_0_34, negated_conjecture, (k2_xboole_0(X1,esk2_0)=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (~r2_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_37, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(esk2_0,X2)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.41  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X2,k1_xboole_0)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_35]), c_0_18])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (esk1_0=esk3_0|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.13/0.41  cnf(c_0_43, negated_conjecture, (esk1_0=esk2_0|~r1_tarski(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_18]), c_0_31]), c_0_18]), c_0_40])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (esk1_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_35])])).
% 0.13/0.41  fof(c_0_45, plain, ![X8]:~r2_xboole_0(X8,X8), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_28])])).
% 0.13/0.41  cnf(c_0_47, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_46]), c_0_47]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 49
% 0.13/0.41  # Proof object clause steps            : 30
% 0.13/0.41  # Proof object formula steps           : 19
% 0.13/0.41  # Proof object conjectures             : 17
% 0.13/0.41  # Proof object clause conjectures      : 14
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 12
% 0.13/0.41  # Proof object initial formulas used   : 9
% 0.13/0.41  # Proof object generating inferences   : 14
% 0.13/0.41  # Proof object simplifying inferences  : 18
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 9
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 14
% 0.13/0.41  # Removed in clause preprocessing      : 1
% 0.13/0.41  # Initial clauses in saturation        : 13
% 0.13/0.41  # Processed clauses                    : 1052
% 0.13/0.41  # ...of these trivial                  : 9
% 0.13/0.41  # ...subsumed                          : 849
% 0.13/0.41  # ...remaining for further processing  : 194
% 0.13/0.41  # Other redundant clauses eliminated   : 1
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 23
% 0.13/0.41  # Backward-rewritten                   : 64
% 0.13/0.41  # Generated clauses                    : 2772
% 0.13/0.41  # ...of the previous two non-trivial   : 2383
% 0.13/0.41  # Contextual simplify-reflections      : 11
% 0.13/0.41  # Paramodulations                      : 2771
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 1
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 94
% 0.13/0.41  #    Positive orientable unit clauses  : 9
% 0.13/0.41  #    Positive unorientable unit clauses: 1
% 0.13/0.41  #    Negative unit clauses             : 5
% 0.13/0.41  #    Non-unit-clauses                  : 79
% 0.13/0.41  # Current number of unprocessed clauses: 1302
% 0.13/0.41  # ...number of literals in the above   : 4322
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 100
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 2654
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 2420
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 626
% 0.13/0.41  # Unit Clause-clause subsumption calls : 164
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 20
% 0.13/0.41  # BW rewrite match successes           : 12
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 25489
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.064 s
% 0.13/0.41  # System time              : 0.007 s
% 0.13/0.41  # Total time               : 0.071 s
% 0.13/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
