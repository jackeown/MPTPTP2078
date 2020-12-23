%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 162 expanded)
%              Number of clauses        :   28 (  69 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 455 expanded)
%              Number of equality atoms :  103 ( 421 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

fof(c_0_9,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk2_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k2_tarski(esk2_0,esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0)
      | esk1_0 = k1_tarski(esk3_0)
      | esk1_0 = k2_tarski(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_xboole_0(k1_tarski(X26),k1_tarski(X27)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_11,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_tarski(X28,k2_tarski(X29,X30))
        | X28 = k1_xboole_0
        | X28 = k1_tarski(X29)
        | X28 = k1_tarski(X30)
        | X28 = k2_tarski(X29,X30) )
      & ( X28 != k1_xboole_0
        | r1_tarski(X28,k2_tarski(X29,X30)) )
      & ( X28 != k1_tarski(X29)
        | r1_tarski(X28,k2_tarski(X29,X30)) )
      & ( X28 != k1_tarski(X30)
        | r1_tarski(X28,k2_tarski(X29,X30)) )
      & ( X28 != k2_tarski(X29,X30)
        | r1_tarski(X28,k2_tarski(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))
    | k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

fof(c_0_18,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k2_xboole_0(X21,X22)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_19,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X2)
    | X1 = k2_xboole_0(k1_tarski(X2),k1_tarski(X3))
    | ~ r1_tarski(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_14]),c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = esk1_0
    | k1_tarski(esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( esk1_0 != k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))
    | k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | k1_tarski(esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( k1_tarski(esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

fof(c_0_35,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.20/0.38  # and selection function SelectCQIPrecW.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t75_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 0.20/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.38  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.20/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t75_zfmisc_1])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, (((((esk1_0!=k1_xboole_0|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0)&(esk1_0!=k1_tarski(esk2_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(esk1_0!=k1_tarski(esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(esk1_0!=k2_tarski(esk2_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0))&(k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))=k1_xboole_0|(esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)|esk1_0=k1_tarski(esk3_0)|esk1_0=k2_tarski(esk2_0,esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_xboole_0(k1_tarski(X26),k1_tarski(X27)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.38  fof(c_0_11, plain, ![X28, X29, X30]:((~r1_tarski(X28,k2_tarski(X29,X30))|(X28=k1_xboole_0|X28=k1_tarski(X29)|X28=k1_tarski(X30)|X28=k2_tarski(X29,X30)))&((((X28!=k1_xboole_0|r1_tarski(X28,k2_tarski(X29,X30)))&(X28!=k1_tarski(X29)|r1_tarski(X28,k2_tarski(X29,X30))))&(X28!=k1_tarski(X30)|r1_tarski(X28,k2_tarski(X29,X30))))&(X28!=k2_tarski(X29,X30)|r1_tarski(X28,k2_tarski(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))=k1_xboole_0|esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)|esk1_0=k1_tarski(esk3_0)|esk1_0=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)|esk1_0=k1_tarski(esk3_0)|esk1_0=k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))|k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.20/0.38  fof(c_0_18, plain, ![X21, X22]:k4_xboole_0(X21,k2_xboole_0(X21,X22))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.38  fof(c_0_19, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (esk1_0!=k2_tarski(esk2_0,esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_21, plain, (X1=k1_xboole_0|X1=k1_tarski(X3)|X1=k1_tarski(X2)|X1=k2_xboole_0(k1_tarski(X2),k1_tarski(X3))|~r1_tarski(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_14]), c_0_14])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=esk1_0|k1_tarski(esk3_0)=esk1_0|k1_tarski(esk2_0)=esk1_0|esk1_0=k1_xboole_0|r1_tarski(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_24, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_25, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (esk1_0!=k1_tarski(esk3_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (esk1_0!=k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))|k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=esk1_0|k1_tarski(esk2_0)=esk1_0|k1_tarski(esk3_0)=esk1_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (esk1_0!=k1_tarski(esk3_0)|k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (k1_tarski(esk3_0)=esk1_0|k1_tarski(esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.20/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 0.20/0.38  fof(c_0_35, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (esk1_0!=k1_xboole_0|k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)|k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_14])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k1_tarski(esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.38  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (esk1_0!=k1_xboole_0|k4_xboole_0(esk1_0,k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23])])).
% 0.20/0.38  cnf(c_0_43, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_42])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 45
% 0.20/0.38  # Proof object clause steps            : 28
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 13
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 19
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 26
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 25
% 0.20/0.38  # Processed clauses                    : 60
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 57
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 6
% 0.20/0.38  # Generated clauses                    : 90
% 0.20/0.38  # ...of the previous two non-trivial   : 68
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 83
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 7
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 21
% 0.20/0.38  #    Positive orientable unit clauses  : 12
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 8
% 0.20/0.38  # Current number of unprocessed clauses: 50
% 0.20/0.38  # ...number of literals in the above   : 137
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 31
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 22
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 12
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 35
% 0.20/0.38  # BW rewrite match successes           : 20
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2230
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
