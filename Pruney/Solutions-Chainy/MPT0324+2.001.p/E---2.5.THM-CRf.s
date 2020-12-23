%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:04 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   38 (  62 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 106 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t137_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
     => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( r1_xboole_0(X10,X11)
      | ~ r1_tarski(X10,X12)
      | ~ r1_xboole_0(X10,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

fof(c_0_9,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( r2_hidden(X16,X17)
      | r1_xboole_0(k1_tarski(X16),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
       => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    inference(assume_negation,[status(cth)],[t137_zfmisc_1])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ( ~ r1_tarski(k1_tarski(X14),X15)
        | r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X14,X15)
        | r1_tarski(k1_tarski(X14),X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0))
    & ~ r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] : k2_zfmisc_1(k3_xboole_0(X18,X19),k3_xboole_0(X20,X21)) = k3_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | r1_xboole_0(k2_tarski(X1,X1),X2)
    | ~ r1_tarski(k2_tarski(X1,X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_zfmisc_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_14])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | r1_xboole_0(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_xboole_0(k2_tarski(X22,X23),X24)
      | ~ r2_hidden(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(esk4_0,esk5_0))))
    | r1_xboole_0(k2_tarski(esk1_0,esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk1_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.12/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.37  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t137_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5]:((r2_hidden(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X1,k2_zfmisc_1(X4,X5)))=>r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 0.12/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.12/0.37  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.12/0.37  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.12/0.37  fof(c_0_8, plain, ![X10, X11, X12]:(r1_xboole_0(X10,X11)|~r1_tarski(X10,X12)|~r1_xboole_0(X10,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.37  fof(c_0_10, plain, ![X16, X17]:(r2_hidden(X16,X17)|r1_xboole_0(k1_tarski(X16),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:((r2_hidden(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X1,k2_zfmisc_1(X4,X5)))=>r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))))), inference(assume_negation,[status(cth)],[t137_zfmisc_1])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_17, plain, ![X14, X15]:((~r1_tarski(k1_tarski(X14),X15)|r2_hidden(X14,X15))&(~r2_hidden(X14,X15)|r1_tarski(k1_tarski(X14),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.12/0.37  fof(c_0_18, negated_conjecture, ((r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))&r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0)))&~r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.37  fof(c_0_19, plain, ![X18, X19, X20, X21]:k2_zfmisc_1(k3_xboole_0(X18,X19),k3_xboole_0(X20,X21))=k3_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk1_0,k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_24, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_25, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|r1_xboole_0(k2_tarski(X1,X1),X2)|~r1_tarski(k2_tarski(X1,X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  cnf(c_0_26, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_16])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk1_0,k2_zfmisc_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_14])).
% 0.12/0.37  cnf(c_0_28, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_14]), c_0_14])).
% 0.12/0.37  cnf(c_0_29, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|r1_xboole_0(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  fof(c_0_31, plain, ![X22, X23, X24]:(~r1_xboole_0(k2_tarski(X22,X23),X24)|~r2_hidden(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk1_0,k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k4_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0))))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(esk4_0,esk5_0))))|r1_xboole_0(k2_tarski(esk1_0,esk1_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_34, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk1_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 38
% 0.12/0.37  # Proof object clause steps            : 21
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 11
% 0.12/0.37  # Proof object clause conjectures      : 8
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 5
% 0.12/0.37  # Proof object simplifying inferences  : 11
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 12
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 10
% 0.12/0.37  # Processed clauses                    : 31
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 10
% 0.12/0.37  # ...remaining for further processing  : 21
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 68
% 0.12/0.37  # ...of the previous two non-trivial   : 64
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 68
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
% 0.12/0.37  # Current number of processed clauses  : 20
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 2
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 13
% 0.12/0.37  # Current number of unprocessed clauses: 43
% 0.12/0.37  # ...number of literals in the above   : 80
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 3
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 42
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 42
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 4
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1985
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
