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
% DateTime   : Thu Dec  3 10:41:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 183 expanded)
%              Number of clauses        :   23 (  77 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 199 expanded)
%              Number of equality atoms :   44 ( 191 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t15_xboole_1,axiom,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X19,X20] : k3_tarski(k2_tarski(X19,X20)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X17,X18] : k2_enumset1(X17,X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_14,plain,(
    ! [X10,X11] : k2_tarski(X10,X11) = k2_tarski(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( k2_xboole_0(X7,X8) != k1_xboole_0
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k2_xboole_0(X5,X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | k3_tarski(k2_enumset1(X1,X1,X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_28,plain,(
    ! [X21,X22] : k2_xboole_0(k1_tarski(X21),X22) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_xboole_0(k2_tarski(X12,X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_17]),c_0_18])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_31]),c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_41,c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.12/0.37  # and selection function SelectCQArNTNp.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.12/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.12/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.37  fof(t15_xboole_1, axiom, ![X1, X2]:(k2_xboole_0(X1,X2)=k1_xboole_0=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 0.12/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X19, X20]:k3_tarski(k2_tarski(X19,X20))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.37  fof(c_0_13, plain, ![X17, X18]:k2_enumset1(X17,X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.12/0.37  fof(c_0_14, plain, ![X10, X11]:k2_tarski(X10,X11)=k2_tarski(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.37  fof(c_0_15, plain, ![X7, X8]:(k2_xboole_0(X7,X8)!=k1_xboole_0|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k3_tarski(k2_enumset1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_18])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_18])).
% 0.12/0.37  fof(c_0_23, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k2_xboole_0(X5,X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.37  cnf(c_0_24, plain, (X1=k1_xboole_0|k3_tarski(k2_enumset1(X1,X1,X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_27, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  fof(c_0_28, plain, ![X21, X22]:k2_xboole_0(k1_tarski(X21),X22)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.37  fof(c_0_29, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_30, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_xboole_0(k2_tarski(X12,X13),k2_tarski(X14,X15)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.37  cnf(c_0_32, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_34, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_36, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_31]), c_0_31]), c_0_31])).
% 0.12/0.37  cnf(c_0_38, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_39, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_17]), c_0_18]), c_0_18])).
% 0.12/0.37  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_41, c_0_42]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 44
% 0.12/0.37  # Proof object clause steps            : 23
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 10
% 0.12/0.37  # Proof object clause conjectures      : 7
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 3
% 0.12/0.37  # Proof object simplifying inferences  : 23
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 7
% 0.12/0.37  # Processed clauses                    : 20
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 20
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 32
% 0.12/0.37  # ...of the previous two non-trivial   : 32
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 31
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 9
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 2
% 0.12/0.37  # Current number of unprocessed clauses: 26
% 0.12/0.37  # ...number of literals in the above   : 30
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 14
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 10
% 0.12/0.37  # BW rewrite match successes           : 10
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 709
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
