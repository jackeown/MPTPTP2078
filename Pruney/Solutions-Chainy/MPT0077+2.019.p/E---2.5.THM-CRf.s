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
% DateTime   : Thu Dec  3 10:32:55 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 530 expanded)
%              Number of clauses        :   33 ( 237 expanded)
%              Number of leaves         :    8 ( 143 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 820 expanded)
%              Number of equality atoms :   37 ( 506 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_8,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_9,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k3_xboole_0(X15,X16)) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

fof(c_0_32,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk2_0) )
    & ( ~ r1_xboole_0(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0)
      | r1_xboole_0(esk1_0,esk3_0) )
    & ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0)
    | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))
    | k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))
    | ~ r1_xboole_0(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_29]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.61  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.39/0.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.61  #
% 0.39/0.61  # Preprocessing time       : 0.026 s
% 0.39/0.61  # Presaturation interreduction done
% 0.39/0.61  
% 0.39/0.61  # Proof found!
% 0.39/0.61  # SZS status Theorem
% 0.39/0.61  # SZS output start CNFRefutation
% 0.39/0.61  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.39/0.61  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.39/0.61  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.39/0.61  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.39/0.61  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.39/0.61  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.39/0.61  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.39/0.61  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.39/0.61  fof(c_0_8, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.39/0.61  fof(c_0_9, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.39/0.61  fof(c_0_10, plain, ![X15, X16]:k4_xboole_0(X15,k3_xboole_0(X15,X16))=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.39/0.61  fof(c_0_11, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.39/0.61  cnf(c_0_12, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.39/0.61  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.39/0.61  fof(c_0_14, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.39/0.61  fof(c_0_15, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.39/0.61  cnf(c_0_16, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.39/0.61  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.39/0.61  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.39/0.61  cnf(c_0_19, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.61  fof(c_0_20, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.39/0.61  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.61  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_13])).
% 0.39/0.61  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_13])).
% 0.39/0.61  cnf(c_0_24, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.39/0.61  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.61  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 0.39/0.61  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.39/0.61  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_21]), c_0_21]), c_0_21])).
% 0.39/0.61  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])).
% 0.39/0.61  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25])).
% 0.39/0.61  cnf(c_0_31, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.39/0.61  fof(c_0_32, negated_conjecture, ((((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk2_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0))))&((~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|r1_xboole_0(esk1_0,esk3_0))&(r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])])).
% 0.39/0.61  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_13])).
% 0.39/0.61  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.39/0.61  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.61  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_21])).
% 0.39/0.61  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])).
% 0.39/0.61  cnf(c_0_38, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30])])).
% 0.39/0.61  cnf(c_0_39, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.61  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_24])])).
% 0.39/0.61  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.39/0.61  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.61  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_37])).
% 0.39/0.61  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.39/0.61  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.39/0.61  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))|k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 0.39/0.61  cnf(c_0_47, negated_conjecture, (~r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.39/0.61  cnf(c_0_48, negated_conjecture, (r1_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))|~r1_xboole_0(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_29]), c_0_24])])).
% 0.39/0.61  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_45])]), ['proof']).
% 0.39/0.61  # SZS output end CNFRefutation
% 0.39/0.61  # Proof object total steps             : 50
% 0.39/0.61  # Proof object clause steps            : 33
% 0.39/0.61  # Proof object formula steps           : 17
% 0.39/0.61  # Proof object conjectures             : 16
% 0.39/0.61  # Proof object clause conjectures      : 13
% 0.39/0.61  # Proof object formula conjectures     : 3
% 0.39/0.61  # Proof object initial clauses used    : 11
% 0.39/0.61  # Proof object initial formulas used   : 8
% 0.39/0.61  # Proof object generating inferences   : 15
% 0.39/0.61  # Proof object simplifying inferences  : 26
% 0.39/0.61  # Training examples: 0 positive, 0 negative
% 0.39/0.61  # Parsed axioms                        : 9
% 0.39/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.61  # Initial clauses                      : 15
% 0.39/0.61  # Removed in clause preprocessing      : 4
% 0.39/0.61  # Initial clauses in saturation        : 11
% 0.39/0.61  # Processed clauses                    : 3369
% 0.39/0.61  # ...of these trivial                  : 54
% 0.39/0.61  # ...subsumed                          : 2906
% 0.39/0.61  # ...remaining for further processing  : 409
% 0.39/0.61  # Other redundant clauses eliminated   : 0
% 0.39/0.61  # Clauses deleted for lack of memory   : 0
% 0.39/0.61  # Backward-subsumed                    : 26
% 0.39/0.61  # Backward-rewritten                   : 37
% 0.39/0.61  # Generated clauses                    : 26185
% 0.39/0.61  # ...of the previous two non-trivial   : 22238
% 0.39/0.61  # Contextual simplify-reflections      : 5
% 0.39/0.61  # Paramodulations                      : 26185
% 0.39/0.61  # Factorizations                       : 0
% 0.39/0.61  # Equation resolutions                 : 0
% 0.39/0.61  # Propositional unsat checks           : 0
% 0.39/0.61  #    Propositional check models        : 0
% 0.39/0.61  #    Propositional check unsatisfiable : 0
% 0.39/0.61  #    Propositional clauses             : 0
% 0.39/0.61  #    Propositional clauses after purity: 0
% 0.39/0.61  #    Propositional unsat core size     : 0
% 0.39/0.61  #    Propositional preprocessing time  : 0.000
% 0.39/0.61  #    Propositional encoding time       : 0.000
% 0.39/0.61  #    Propositional solver time         : 0.000
% 0.39/0.61  #    Success case prop preproc time    : 0.000
% 0.39/0.61  #    Success case prop encoding time   : 0.000
% 0.39/0.61  #    Success case prop solver time     : 0.000
% 0.39/0.61  # Current number of processed clauses  : 335
% 0.39/0.61  #    Positive orientable unit clauses  : 72
% 0.39/0.61  #    Positive unorientable unit clauses: 7
% 0.39/0.61  #    Negative unit clauses             : 95
% 0.39/0.61  #    Non-unit-clauses                  : 161
% 0.39/0.61  # Current number of unprocessed clauses: 18668
% 0.39/0.61  # ...number of literals in the above   : 39525
% 0.39/0.61  # Current number of archived formulas  : 0
% 0.39/0.61  # Current number of archived clauses   : 75
% 0.39/0.61  # Clause-clause subsumption calls (NU) : 4431
% 0.39/0.61  # Rec. Clause-clause subsumption calls : 4426
% 0.39/0.61  # Non-unit clause-clause subsumptions  : 618
% 0.39/0.61  # Unit Clause-clause subsumption calls : 1266
% 0.39/0.61  # Rewrite failures with RHS unbound    : 0
% 0.39/0.61  # BW rewrite match attempts            : 542
% 0.39/0.61  # BW rewrite match successes           : 130
% 0.39/0.61  # Condensation attempts                : 0
% 0.39/0.61  # Condensation successes               : 0
% 0.39/0.61  # Termbank termtop insertions          : 285062
% 0.39/0.61  
% 0.39/0.61  # -------------------------------------------------
% 0.39/0.61  # User time                : 0.256 s
% 0.39/0.61  # System time              : 0.012 s
% 0.39/0.61  # Total time               : 0.268 s
% 0.39/0.61  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
