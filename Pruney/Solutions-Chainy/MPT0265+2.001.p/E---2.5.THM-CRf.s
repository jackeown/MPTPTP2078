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
% DateTime   : Thu Dec  3 10:42:08 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 105 expanded)
%              Number of clauses        :   22 (  44 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 181 expanded)
%              Number of equality atoms :   50 ( 127 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t23_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,X2)
       => ( ( r2_hidden(X3,X2)
            & X1 != X3 )
          | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t60_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_10,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) != k1_tarski(X13) )
      & ( r2_hidden(X14,X15)
        | X13 = X14
        | k4_xboole_0(k2_tarski(X13,X14),X15) != k1_tarski(X13) )
      & ( ~ r2_hidden(X14,X15)
        | r2_hidden(X13,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) = k1_tarski(X13) )
      & ( X13 != X14
        | r2_hidden(X13,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) = k1_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

fof(c_0_12,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & ( ~ r2_hidden(esk3_0,esk2_0)
      | esk1_0 = esk3_0 )
    & k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k2_tarski(X3,X1),X2) = k2_tarski(X3,X3)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk3_0),k4_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_17]),c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1)) = k4_xboole_0(X3,k4_xboole_0(X3,k2_tarski(X1,X2)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( X16 = X17
      | k4_xboole_0(k2_tarski(X16,X17),k1_tarski(X17)) = k1_tarski(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_zfmisc_1])])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0))) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X2)) = k4_xboole_0(X3,k4_xboole_0(X3,k2_tarski(X1,X2)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( X1 = X2
    | k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk3_0),k2_tarski(esk3_0,esk3_0)) != k2_tarski(esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X2)) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 = esk3_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | k3_xboole_0(X12,k1_tarski(X11)) = k1_tarski(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0))) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X2,k4_xboole_0(X2,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_17]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.45/1.67  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 1.45/1.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.45/1.67  #
% 1.45/1.67  # Preprocessing time       : 0.027 s
% 1.45/1.67  
% 1.45/1.67  # Proof found!
% 1.45/1.67  # SZS status Theorem
% 1.45/1.67  # SZS output start CNFRefutation
% 1.45/1.67  fof(t60_zfmisc_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 1.45/1.67  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.45/1.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.45/1.67  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.45/1.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.45/1.67  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.45/1.67  fof(t23_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.45/1.67  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.45/1.67  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1)))), inference(assume_negation,[status(cth)],[t60_zfmisc_1])).
% 1.45/1.67  fof(c_0_9, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.45/1.67  fof(c_0_10, plain, ![X6, X7]:k4_xboole_0(X6,k4_xboole_0(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.45/1.67  fof(c_0_11, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)!=k1_tarski(X13))&(r2_hidden(X14,X15)|X13=X14|k4_xboole_0(k2_tarski(X13,X14),X15)!=k1_tarski(X13)))&((~r2_hidden(X14,X15)|r2_hidden(X13,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)=k1_tarski(X13))&(X13!=X14|r2_hidden(X13,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)=k1_tarski(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 1.45/1.67  fof(c_0_12, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.45/1.67  fof(c_0_13, negated_conjecture, (r2_hidden(esk1_0,esk2_0)&((~r2_hidden(esk3_0,esk2_0)|esk1_0=esk3_0)&k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k1_tarski(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.45/1.67  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.45/1.67  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.45/1.67  cnf(c_0_16, plain, (r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.45/1.67  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.45/1.67  cnf(c_0_18, negated_conjecture, (k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.45/1.67  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 1.45/1.67  cnf(c_0_20, plain, (k4_xboole_0(k2_tarski(X3,X1),X2)=k2_tarski(X3,X3)|r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.45/1.67  fof(c_0_21, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_tarski(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.45/1.67  cnf(c_0_22, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk3_0),k4_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0))!=k2_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_17]), c_0_15])).
% 1.45/1.67  cnf(c_0_23, plain, (k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1))=k4_xboole_0(X3,k4_xboole_0(X3,k2_tarski(X1,X2)))|r2_hidden(X1,X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.45/1.67  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.45/1.67  fof(c_0_25, plain, ![X16, X17]:(X16=X17|k4_xboole_0(k2_tarski(X16,X17),k1_tarski(X17))=k1_tarski(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_zfmisc_1])])).
% 1.45/1.67  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk3_0)))!=k2_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 1.45/1.67  cnf(c_0_27, plain, (k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X2))=k4_xboole_0(X3,k4_xboole_0(X3,k2_tarski(X1,X2)))|r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.45/1.67  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.45/1.67  cnf(c_0_29, plain, (X1=X2|k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.45/1.67  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|k4_xboole_0(k2_tarski(esk1_0,esk3_0),k2_tarski(esk3_0,esk3_0))!=k2_tarski(esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 1.45/1.67  cnf(c_0_31, plain, (X1=X2|k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X2,X2))=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17])).
% 1.45/1.67  cnf(c_0_32, negated_conjecture, (esk1_0=esk3_0|~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.45/1.67  fof(c_0_33, plain, ![X11, X12]:(~r2_hidden(X11,X12)|k3_xboole_0(X12,k1_tarski(X11))=k1_tarski(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 1.45/1.67  cnf(c_0_34, negated_conjecture, (esk3_0=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 1.45/1.67  cnf(c_0_35, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.45/1.67  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)))!=k2_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_26, c_0_34])).
% 1.45/1.67  cnf(c_0_37, plain, (k4_xboole_0(X2,k4_xboole_0(X2,k2_tarski(X1,X1)))=k2_tarski(X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_17]), c_0_15])).
% 1.45/1.67  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])]), ['proof']).
% 1.45/1.67  # SZS output end CNFRefutation
% 1.45/1.67  # Proof object total steps             : 39
% 1.45/1.67  # Proof object clause steps            : 22
% 1.45/1.67  # Proof object formula steps           : 17
% 1.45/1.67  # Proof object conjectures             : 12
% 1.45/1.67  # Proof object clause conjectures      : 9
% 1.45/1.67  # Proof object formula conjectures     : 3
% 1.45/1.67  # Proof object initial clauses used    : 10
% 1.45/1.67  # Proof object initial formulas used   : 8
% 1.45/1.67  # Proof object generating inferences   : 5
% 1.45/1.67  # Proof object simplifying inferences  : 17
% 1.45/1.67  # Training examples: 0 positive, 0 negative
% 1.45/1.67  # Parsed axioms                        : 8
% 1.45/1.67  # Removed by relevancy pruning/SinE    : 0
% 1.45/1.67  # Initial clauses                      : 13
% 1.45/1.67  # Removed in clause preprocessing      : 2
% 1.45/1.67  # Initial clauses in saturation        : 11
% 1.45/1.67  # Processed clauses                    : 5724
% 1.45/1.67  # ...of these trivial                  : 0
% 1.45/1.67  # ...subsumed                          : 4963
% 1.45/1.67  # ...remaining for further processing  : 761
% 1.45/1.67  # Other redundant clauses eliminated   : 1
% 1.45/1.67  # Clauses deleted for lack of memory   : 0
% 1.45/1.67  # Backward-subsumed                    : 9
% 1.45/1.67  # Backward-rewritten                   : 4
% 1.45/1.67  # Generated clauses                    : 111255
% 1.45/1.67  # ...of the previous two non-trivial   : 83029
% 1.45/1.67  # Contextual simplify-reflections      : 17
% 1.45/1.67  # Paramodulations                      : 111155
% 1.45/1.67  # Factorizations                       : 0
% 1.45/1.67  # Equation resolutions                 : 100
% 1.45/1.67  # Propositional unsat checks           : 0
% 1.45/1.67  #    Propositional check models        : 0
% 1.45/1.67  #    Propositional check unsatisfiable : 0
% 1.45/1.67  #    Propositional clauses             : 0
% 1.45/1.67  #    Propositional clauses after purity: 0
% 1.45/1.67  #    Propositional unsat core size     : 0
% 1.45/1.67  #    Propositional preprocessing time  : 0.000
% 1.45/1.67  #    Propositional encoding time       : 0.000
% 1.45/1.67  #    Propositional solver time         : 0.000
% 1.45/1.67  #    Success case prop preproc time    : 0.000
% 1.45/1.67  #    Success case prop encoding time   : 0.000
% 1.45/1.67  #    Success case prop solver time     : 0.000
% 1.45/1.67  # Current number of processed clauses  : 747
% 1.45/1.67  #    Positive orientable unit clauses  : 3
% 1.45/1.67  #    Positive unorientable unit clauses: 2
% 1.45/1.67  #    Negative unit clauses             : 3
% 1.45/1.67  #    Non-unit-clauses                  : 739
% 1.45/1.67  # Current number of unprocessed clauses: 77138
% 1.45/1.67  # ...number of literals in the above   : 539180
% 1.45/1.67  # Current number of archived formulas  : 0
% 1.45/1.67  # Current number of archived clauses   : 15
% 1.45/1.67  # Clause-clause subsumption calls (NU) : 374809
% 1.45/1.67  # Rec. Clause-clause subsumption calls : 97888
% 1.45/1.67  # Non-unit clause-clause subsumptions  : 4855
% 1.45/1.67  # Unit Clause-clause subsumption calls : 147
% 1.45/1.67  # Rewrite failures with RHS unbound    : 0
% 1.45/1.67  # BW rewrite match attempts            : 5
% 1.45/1.67  # BW rewrite match successes           : 4
% 1.45/1.67  # Condensation attempts                : 0
% 1.45/1.67  # Condensation successes               : 0
% 1.45/1.67  # Termbank termtop insertions          : 2484043
% 1.45/1.67  
% 1.45/1.67  # -------------------------------------------------
% 1.45/1.67  # User time                : 1.295 s
% 1.45/1.67  # System time              : 0.036 s
% 1.45/1.67  # Total time               : 1.331 s
% 1.45/1.67  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
