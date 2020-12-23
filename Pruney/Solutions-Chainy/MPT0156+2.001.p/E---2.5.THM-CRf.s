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
% DateTime   : Thu Dec  3 10:35:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  64 expanded)
%              Number of clauses        :   17 (  27 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  71 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t72_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_9,plain,(
    ! [X18,X19,X20,X21] : k2_enumset1(X18,X19,X20,X21) = k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_10,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X16,X17] : r1_tarski(X16,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X25,X26] : k3_enumset1(X22,X23,X24,X25,X26) = k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_19,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15]),c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),X3)
    | ~ r1_tarski(k2_enumset1(X1,X2,X4,X5),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_14]),c_0_15])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4)) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.14/0.39  # and selection function SelectCQArNTNp.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.026 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.14/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.14/0.39  fof(t72_enumset1, conjecture, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.14/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.14/0.39  fof(c_0_9, plain, ![X18, X19, X20, X21]:k2_enumset1(X18,X19,X20,X21)=k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X20,X21)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.14/0.39  fof(c_0_10, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_11, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_12, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.14/0.39  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  fof(c_0_16, plain, ![X16, X17]:r1_tarski(X16,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.14/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_18, plain, ![X22, X23, X24, X25, X26]:k3_enumset1(X22,X23,X24,X25,X26)=k2_xboole_0(k1_tarski(X22),k2_enumset1(X23,X24,X25,X26)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.14/0.39  fof(c_0_19, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.39  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_21, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_15]), c_0_15])).
% 0.14/0.39  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  fof(c_0_23, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.14/0.39  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  fof(c_0_26, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.14/0.39  cnf(c_0_27, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),X3)|~r1_tarski(k2_enumset1(X1,X2,X4,X5),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.39  cnf(c_0_28, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_14]), c_0_15])).
% 0.14/0.39  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_32, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  cnf(c_0_34, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4))=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 36
% 0.14/0.39  # Proof object clause steps            : 17
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 6
% 0.14/0.39  # Proof object clause conjectures      : 3
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 9
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 4
% 0.14/0.39  # Proof object simplifying inferences  : 10
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 11
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 13
% 0.14/0.39  # Removed in clause preprocessing      : 4
% 0.14/0.39  # Initial clauses in saturation        : 9
% 0.14/0.39  # Processed clauses                    : 375
% 0.14/0.39  # ...of these trivial                  : 63
% 0.14/0.39  # ...subsumed                          : 224
% 0.14/0.39  # ...remaining for further processing  : 88
% 0.14/0.39  # Other redundant clauses eliminated   : 2
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 3
% 0.14/0.39  # Backward-rewritten                   : 3
% 0.14/0.39  # Generated clauses                    : 1336
% 0.14/0.39  # ...of the previous two non-trivial   : 970
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 1334
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 2
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 72
% 0.14/0.39  #    Positive orientable unit clauses  : 30
% 0.14/0.39  #    Positive unorientable unit clauses: 1
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 41
% 0.14/0.39  # Current number of unprocessed clauses: 602
% 0.14/0.39  # ...number of literals in the above   : 803
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 18
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1880
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 1880
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 220
% 0.14/0.39  # Unit Clause-clause subsumption calls : 4
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 98
% 0.14/0.39  # BW rewrite match successes           : 7
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 12381
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.043 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.045 s
% 0.14/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
