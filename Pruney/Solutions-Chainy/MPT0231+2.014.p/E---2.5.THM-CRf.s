%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 111 expanded)
%              Number of clauses        :   22 (  45 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 133 expanded)
%              Number of equality atoms :   25 (  88 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t26_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X17,X18] : r1_tarski(k1_tarski(X17),k2_tarski(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t26_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k3_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))
    & esk1_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

fof(c_0_22,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2),k2_enumset1(X1,X1,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_32,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(k1_tarski(X19),k1_tarski(X20))
      | X19 = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),X1),k2_enumset1(esk3_0,esk3_0,esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n005.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 12:58:17 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.13/0.31  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.13/0.31  # and selection function SelectCQArNTNp.
% 0.13/0.31  #
% 0.13/0.31  # Preprocessing time       : 0.024 s
% 0.13/0.31  # Presaturation interreduction done
% 0.13/0.31  
% 0.13/0.31  # Proof found!
% 0.13/0.31  # SZS status Theorem
% 0.13/0.31  # SZS output start CNFRefutation
% 0.13/0.31  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.13/0.31  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.31  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.31  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.31  fof(t26_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 0.13/0.31  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.13/0.31  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.31  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.31  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.13/0.31  fof(c_0_9, plain, ![X17, X18]:r1_tarski(k1_tarski(X17),k2_tarski(X17,X18)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.13/0.31  fof(c_0_10, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.31  fof(c_0_11, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.31  fof(c_0_12, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.31  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3)), inference(assume_negation,[status(cth)],[t26_zfmisc_1])).
% 0.13/0.31  fof(c_0_14, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(k3_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.13/0.31  cnf(c_0_15, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.31  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.31  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.31  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.31  fof(c_0_19, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))&esk1_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.31  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.31  cnf(c_0_21, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.13/0.31  fof(c_0_22, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.31  fof(c_0_23, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.31  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.31  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2),k2_enumset1(X1,X1,X1,X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.31  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.31  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.31  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.13/0.31  cnf(c_0_29, plain, (r1_tarski(k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.31  cnf(c_0_30, negated_conjecture, (k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.31  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.31  fof(c_0_32, plain, ![X19, X20]:(~r1_tarski(k1_tarski(X19),k1_tarski(X20))|X19=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.13/0.31  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),X1),k2_enumset1(esk3_0,esk3_0,esk3_0,X2))), inference(spm,[status(thm)],[c_0_20, c_0_31])).
% 0.13/0.31  cnf(c_0_34, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.31  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,X2))), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.13/0.31  cnf(c_0_36, plain, (k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.13/0.31  cnf(c_0_37, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.13/0.31  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.31  cnf(c_0_39, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.31  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.13/0.31  # SZS output end CNFRefutation
% 0.13/0.31  # Proof object total steps             : 41
% 0.13/0.31  # Proof object clause steps            : 22
% 0.13/0.31  # Proof object formula steps           : 19
% 0.13/0.31  # Proof object conjectures             : 12
% 0.13/0.31  # Proof object clause conjectures      : 9
% 0.13/0.31  # Proof object formula conjectures     : 3
% 0.13/0.31  # Proof object initial clauses used    : 10
% 0.13/0.31  # Proof object initial formulas used   : 9
% 0.13/0.31  # Proof object generating inferences   : 9
% 0.13/0.31  # Proof object simplifying inferences  : 17
% 0.13/0.31  # Training examples: 0 positive, 0 negative
% 0.13/0.31  # Parsed axioms                        : 9
% 0.13/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.31  # Initial clauses                      : 10
% 0.13/0.31  # Removed in clause preprocessing      : 3
% 0.13/0.31  # Initial clauses in saturation        : 7
% 0.13/0.31  # Processed clauses                    : 29
% 0.13/0.31  # ...of these trivial                  : 3
% 0.13/0.31  # ...subsumed                          : 0
% 0.13/0.31  # ...remaining for further processing  : 26
% 0.13/0.31  # Other redundant clauses eliminated   : 0
% 0.13/0.31  # Clauses deleted for lack of memory   : 0
% 0.13/0.31  # Backward-subsumed                    : 0
% 0.13/0.31  # Backward-rewritten                   : 4
% 0.13/0.31  # Generated clauses                    : 51
% 0.13/0.31  # ...of the previous two non-trivial   : 36
% 0.13/0.31  # Contextual simplify-reflections      : 0
% 0.13/0.31  # Paramodulations                      : 51
% 0.13/0.31  # Factorizations                       : 0
% 0.13/0.31  # Equation resolutions                 : 0
% 0.13/0.31  # Propositional unsat checks           : 0
% 0.13/0.31  #    Propositional check models        : 0
% 0.13/0.31  #    Propositional check unsatisfiable : 0
% 0.13/0.31  #    Propositional clauses             : 0
% 0.13/0.31  #    Propositional clauses after purity: 0
% 0.13/0.31  #    Propositional unsat core size     : 0
% 0.13/0.31  #    Propositional preprocessing time  : 0.000
% 0.13/0.31  #    Propositional encoding time       : 0.000
% 0.13/0.31  #    Propositional solver time         : 0.000
% 0.13/0.31  #    Success case prop preproc time    : 0.000
% 0.13/0.31  #    Success case prop encoding time   : 0.000
% 0.13/0.31  #    Success case prop solver time     : 0.000
% 0.13/0.31  # Current number of processed clauses  : 15
% 0.13/0.31  #    Positive orientable unit clauses  : 10
% 0.13/0.31  #    Positive unorientable unit clauses: 1
% 0.13/0.31  #    Negative unit clauses             : 1
% 0.13/0.31  #    Non-unit-clauses                  : 3
% 0.13/0.31  # Current number of unprocessed clauses: 16
% 0.13/0.31  # ...number of literals in the above   : 16
% 0.13/0.31  # Current number of archived formulas  : 0
% 0.13/0.31  # Current number of archived clauses   : 14
% 0.13/0.31  # Clause-clause subsumption calls (NU) : 2
% 0.13/0.31  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.31  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.31  # Unit Clause-clause subsumption calls : 0
% 0.13/0.31  # Rewrite failures with RHS unbound    : 0
% 0.13/0.31  # BW rewrite match attempts            : 14
% 0.13/0.31  # BW rewrite match successes           : 8
% 0.13/0.31  # Condensation attempts                : 0
% 0.13/0.31  # Condensation successes               : 0
% 0.13/0.31  # Termbank termtop insertions          : 1283
% 0.13/0.31  
% 0.13/0.31  # -------------------------------------------------
% 0.13/0.31  # User time                : 0.024 s
% 0.13/0.31  # System time              : 0.004 s
% 0.13/0.31  # Total time               : 0.027 s
% 0.13/0.31  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
