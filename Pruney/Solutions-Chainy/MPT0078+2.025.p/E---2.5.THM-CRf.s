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
% DateTime   : Thu Dec  3 10:32:59 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 101 expanded)
%              Number of clauses        :   26 (  45 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 195 expanded)
%              Number of equality atoms :   35 (  84 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_9,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k2_xboole_0(X21,X22)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_10,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

fof(c_0_12,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_13,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k3_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_23,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk5_0
    | r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))
    | r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk3_0)),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk3_0)),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_42]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:39:08 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 1.14/1.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 1.14/1.29  # and selection function SelectLargestOrientable.
% 1.14/1.29  #
% 1.14/1.29  # Preprocessing time       : 0.026 s
% 1.14/1.29  # Presaturation interreduction done
% 1.14/1.29  
% 1.14/1.29  # Proof found!
% 1.14/1.29  # SZS status Theorem
% 1.14/1.29  # SZS output start CNFRefutation
% 1.14/1.29  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.14/1.29  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.14/1.29  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 1.14/1.29  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.14/1.29  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.14/1.29  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 1.14/1.29  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.14/1.29  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.14/1.29  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.14/1.29  fof(c_0_9, plain, ![X21, X22]:k4_xboole_0(X21,k2_xboole_0(X21,X22))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 1.14/1.29  fof(c_0_10, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.14/1.29  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 1.14/1.29  fof(c_0_12, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.14/1.29  fof(c_0_13, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.14/1.29  fof(c_0_14, plain, ![X14, X15, X16]:k4_xboole_0(X14,k3_xboole_0(X15,X16))=k2_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 1.14/1.29  cnf(c_0_15, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.14/1.29  cnf(c_0_16, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.14/1.29  fof(c_0_17, plain, ![X19, X20]:k4_xboole_0(k2_xboole_0(X19,X20),X20)=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.14/1.29  fof(c_0_18, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)&r1_xboole_0(esk3_0,esk4_0))&r1_xboole_0(esk5_0,esk4_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.14/1.29  cnf(c_0_19, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.14/1.29  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.14/1.29  cnf(c_0_21, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.14/1.29  cnf(c_0_22, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.14/1.29  fof(c_0_23, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.14/1.29  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.14/1.29  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.14/1.29  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.14/1.29  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.14/1.29  cnf(c_0_28, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16])).
% 1.14/1.29  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.14/1.29  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.14/1.29  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_25])).
% 1.14/1.29  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.14/1.29  cnf(c_0_33, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.14/1.29  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.14/1.29  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk5_0|r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.14/1.29  cnf(c_0_36, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.14/1.29  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.14/1.29  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.14/1.29  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(esk4_0,esk5_0))|r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk3_0)),k3_xboole_0(esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_35]), c_0_36])).
% 1.14/1.29  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.14/1.29  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.14/1.29  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(esk4_0,esk3_0)),k3_xboole_0(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_39]), c_0_40])])).
% 1.14/1.29  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_41])).
% 1.14/1.29  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_42]), c_0_43])]), ['proof']).
% 1.14/1.29  # SZS output end CNFRefutation
% 1.14/1.29  # Proof object total steps             : 45
% 1.14/1.29  # Proof object clause steps            : 26
% 1.14/1.29  # Proof object formula steps           : 19
% 1.14/1.29  # Proof object conjectures             : 14
% 1.14/1.29  # Proof object clause conjectures      : 11
% 1.14/1.29  # Proof object formula conjectures     : 3
% 1.14/1.29  # Proof object initial clauses used    : 13
% 1.14/1.29  # Proof object initial formulas used   : 9
% 1.14/1.29  # Proof object generating inferences   : 13
% 1.14/1.29  # Proof object simplifying inferences  : 7
% 1.14/1.29  # Training examples: 0 positive, 0 negative
% 1.14/1.29  # Parsed axioms                        : 9
% 1.14/1.29  # Removed by relevancy pruning/SinE    : 0
% 1.14/1.29  # Initial clauses                      : 13
% 1.14/1.29  # Removed in clause preprocessing      : 0
% 1.14/1.29  # Initial clauses in saturation        : 13
% 1.14/1.29  # Processed clauses                    : 5733
% 1.14/1.29  # ...of these trivial                  : 1237
% 1.14/1.29  # ...subsumed                          : 3130
% 1.14/1.29  # ...remaining for further processing  : 1366
% 1.14/1.29  # Other redundant clauses eliminated   : 62
% 1.14/1.29  # Clauses deleted for lack of memory   : 0
% 1.14/1.29  # Backward-subsumed                    : 185
% 1.14/1.29  # Backward-rewritten                   : 236
% 1.14/1.29  # Generated clauses                    : 179378
% 1.14/1.29  # ...of the previous two non-trivial   : 106355
% 1.14/1.29  # Contextual simplify-reflections      : 9
% 1.14/1.29  # Paramodulations                      : 179292
% 1.14/1.29  # Factorizations                       : 24
% 1.14/1.29  # Equation resolutions                 : 62
% 1.14/1.29  # Propositional unsat checks           : 0
% 1.14/1.29  #    Propositional check models        : 0
% 1.14/1.29  #    Propositional check unsatisfiable : 0
% 1.14/1.29  #    Propositional clauses             : 0
% 1.14/1.29  #    Propositional clauses after purity: 0
% 1.14/1.29  #    Propositional unsat core size     : 0
% 1.14/1.29  #    Propositional preprocessing time  : 0.000
% 1.14/1.29  #    Propositional encoding time       : 0.000
% 1.14/1.29  #    Propositional solver time         : 0.000
% 1.14/1.29  #    Success case prop preproc time    : 0.000
% 1.14/1.29  #    Success case prop encoding time   : 0.000
% 1.14/1.29  #    Success case prop solver time     : 0.000
% 1.14/1.29  # Current number of processed clauses  : 932
% 1.14/1.29  #    Positive orientable unit clauses  : 297
% 1.14/1.29  #    Positive unorientable unit clauses: 1
% 1.14/1.29  #    Negative unit clauses             : 15
% 1.14/1.29  #    Non-unit-clauses                  : 619
% 1.14/1.29  # Current number of unprocessed clauses: 95534
% 1.14/1.29  # ...number of literals in the above   : 272378
% 1.14/1.29  # Current number of archived formulas  : 0
% 1.14/1.29  # Current number of archived clauses   : 434
% 1.14/1.29  # Clause-clause subsumption calls (NU) : 65756
% 1.14/1.29  # Rec. Clause-clause subsumption calls : 57833
% 1.14/1.29  # Non-unit clause-clause subsumptions  : 2924
% 1.14/1.29  # Unit Clause-clause subsumption calls : 1299
% 1.14/1.29  # Rewrite failures with RHS unbound    : 0
% 1.14/1.29  # BW rewrite match attempts            : 2074
% 1.14/1.29  # BW rewrite match successes           : 48
% 1.14/1.29  # Condensation attempts                : 0
% 1.14/1.29  # Condensation successes               : 0
% 1.14/1.29  # Termbank termtop insertions          : 3063768
% 1.14/1.29  
% 1.14/1.29  # -------------------------------------------------
% 1.14/1.29  # User time                : 0.904 s
% 1.14/1.29  # System time              : 0.046 s
% 1.14/1.29  # Total time               : 0.950 s
% 1.14/1.29  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
