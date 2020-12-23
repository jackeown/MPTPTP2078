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
% DateTime   : Thu Dec  3 10:59:04 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 139 expanded)
%              Number of clauses        :   21 (  58 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 217 expanded)
%              Number of equality atoms :   34 ( 129 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t13_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))
    & ( ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0)
      | k2_mcart_1(esk3_0) != esk5_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,k2_zfmisc_1(X13,X14))
      | k4_tarski(esk1_1(X12),esk2_1(X12)) = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( k1_mcart_1(k4_tarski(X24,X25)) = X24
      & k2_mcart_1(k4_tarski(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_19,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( esk1_1(esk3_0) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_24,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) )
      & ( X18 = X20
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) )
      & ( ~ r2_hidden(X17,X19)
        | X18 != X20
        | r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_25,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(k1_mcart_1(X21),X22)
        | ~ r2_hidden(X21,k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(k2_mcart_1(X21),X23)
        | ~ r2_hidden(X21,k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk2_1(esk3_0) = k2_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0)
    | k2_mcart_1(esk3_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(esk3_0) = X1
    | ~ r2_hidden(esk3_0,k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_mcart_1(esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.31  % Computer   : n025.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 14:35:20 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.31  # Version: 2.5pre002
% 0.17/0.31  # No SInE strategy applied
% 0.17/0.31  # Trying AutoSched0 for 299 seconds
% 0.17/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.34  #
% 0.17/0.34  # Preprocessing time       : 0.027 s
% 0.17/0.34  # Presaturation interreduction done
% 0.17/0.34  
% 0.17/0.34  # Proof found!
% 0.17/0.34  # SZS status Theorem
% 0.17/0.34  # SZS output start CNFRefutation
% 0.17/0.34  fof(t13_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.17/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.34  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.17/0.34  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.17/0.34  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.17/0.34  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.17/0.34  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3))), inference(assume_negation,[status(cth)],[t13_mcart_1])).
% 0.17/0.34  fof(c_0_9, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))&(~r2_hidden(k1_mcart_1(esk3_0),esk4_0)|k2_mcart_1(esk3_0)!=esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.17/0.34  fof(c_0_10, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.34  fof(c_0_11, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.34  fof(c_0_12, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.34  fof(c_0_13, plain, ![X12, X13, X14]:(~r2_hidden(X12,k2_zfmisc_1(X13,X14))|k4_tarski(esk1_1(X12),esk2_1(X12))=X12), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.17/0.34  cnf(c_0_14, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.34  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.34  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.34  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.34  fof(c_0_18, plain, ![X24, X25]:(k1_mcart_1(k4_tarski(X24,X25))=X24&k2_mcart_1(k4_tarski(X24,X25))=X25), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.17/0.34  cnf(c_0_19, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.34  cnf(c_0_20, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])).
% 0.17/0.34  cnf(c_0_21, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.34  cnf(c_0_22, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.17/0.34  cnf(c_0_23, negated_conjecture, (esk1_1(esk3_0)=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.34  fof(c_0_24, plain, ![X17, X18, X19, X20]:(((r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))))&(X18=X20|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20)))))&(~r2_hidden(X17,X19)|X18!=X20|r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,k1_tarski(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.17/0.34  cnf(c_0_25, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.34  cnf(c_0_26, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.17/0.34  fof(c_0_27, plain, ![X21, X22, X23]:((r2_hidden(k1_mcart_1(X21),X22)|~r2_hidden(X21,k2_zfmisc_1(X22,X23)))&(r2_hidden(k2_mcart_1(X21),X23)|~r2_hidden(X21,k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.17/0.34  cnf(c_0_28, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.34  cnf(c_0_29, negated_conjecture, (esk2_1(esk3_0)=k2_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.17/0.34  cnf(c_0_30, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.34  cnf(c_0_31, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_15]), c_0_16]), c_0_17])).
% 0.17/0.34  cnf(c_0_32, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_26, c_0_29])).
% 0.17/0.34  cnf(c_0_33, negated_conjecture, (~r2_hidden(k1_mcart_1(esk3_0),esk4_0)|k2_mcart_1(esk3_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.34  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.17/0.34  cnf(c_0_35, negated_conjecture, (k2_mcart_1(esk3_0)=X1|~r2_hidden(esk3_0,k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.17/0.34  cnf(c_0_36, negated_conjecture, (k2_mcart_1(esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.17/0.34  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_36]), ['proof']).
% 0.17/0.34  # SZS output end CNFRefutation
% 0.17/0.34  # Proof object total steps             : 38
% 0.17/0.34  # Proof object clause steps            : 21
% 0.17/0.34  # Proof object formula steps           : 17
% 0.17/0.34  # Proof object conjectures             : 15
% 0.17/0.34  # Proof object clause conjectures      : 12
% 0.17/0.34  # Proof object formula conjectures     : 3
% 0.17/0.34  # Proof object initial clauses used    : 10
% 0.17/0.34  # Proof object initial formulas used   : 8
% 0.17/0.34  # Proof object generating inferences   : 6
% 0.17/0.34  # Proof object simplifying inferences  : 11
% 0.17/0.34  # Training examples: 0 positive, 0 negative
% 0.17/0.34  # Parsed axioms                        : 8
% 0.17/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.34  # Initial clauses                      : 13
% 0.17/0.34  # Removed in clause preprocessing      : 3
% 0.17/0.34  # Initial clauses in saturation        : 10
% 0.17/0.34  # Processed clauses                    : 34
% 0.17/0.34  # ...of these trivial                  : 0
% 0.17/0.34  # ...subsumed                          : 1
% 0.17/0.34  # ...remaining for further processing  : 33
% 0.17/0.34  # Other redundant clauses eliminated   : 1
% 0.17/0.34  # Clauses deleted for lack of memory   : 0
% 0.17/0.34  # Backward-subsumed                    : 0
% 0.17/0.34  # Backward-rewritten                   : 4
% 0.17/0.34  # Generated clauses                    : 30
% 0.17/0.34  # ...of the previous two non-trivial   : 30
% 0.17/0.34  # Contextual simplify-reflections      : 0
% 0.17/0.34  # Paramodulations                      : 29
% 0.17/0.34  # Factorizations                       : 0
% 0.17/0.34  # Equation resolutions                 : 1
% 0.17/0.34  # Propositional unsat checks           : 0
% 0.17/0.34  #    Propositional check models        : 0
% 0.17/0.34  #    Propositional check unsatisfiable : 0
% 0.17/0.34  #    Propositional clauses             : 0
% 0.17/0.34  #    Propositional clauses after purity: 0
% 0.17/0.34  #    Propositional unsat core size     : 0
% 0.17/0.34  #    Propositional preprocessing time  : 0.000
% 0.17/0.34  #    Propositional encoding time       : 0.000
% 0.17/0.34  #    Propositional solver time         : 0.000
% 0.17/0.34  #    Success case prop preproc time    : 0.000
% 0.17/0.34  #    Success case prop encoding time   : 0.000
% 0.17/0.34  #    Success case prop solver time     : 0.000
% 0.17/0.34  # Current number of processed clauses  : 18
% 0.17/0.34  #    Positive orientable unit clauses  : 9
% 0.17/0.34  #    Positive unorientable unit clauses: 0
% 0.17/0.34  #    Negative unit clauses             : 1
% 0.17/0.34  #    Non-unit-clauses                  : 8
% 0.17/0.34  # Current number of unprocessed clauses: 11
% 0.17/0.34  # ...number of literals in the above   : 18
% 0.17/0.34  # Current number of archived formulas  : 0
% 0.17/0.34  # Current number of archived clauses   : 17
% 0.17/0.34  # Clause-clause subsumption calls (NU) : 4
% 0.17/0.34  # Rec. Clause-clause subsumption calls : 4
% 0.17/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.17/0.34  # Unit Clause-clause subsumption calls : 4
% 0.17/0.34  # Rewrite failures with RHS unbound    : 0
% 0.17/0.34  # BW rewrite match attempts            : 5
% 0.17/0.34  # BW rewrite match successes           : 4
% 0.17/0.34  # Condensation attempts                : 0
% 0.17/0.34  # Condensation successes               : 0
% 0.17/0.34  # Termbank termtop insertions          : 1132
% 0.17/0.34  
% 0.17/0.34  # -------------------------------------------------
% 0.17/0.34  # User time                : 0.028 s
% 0.17/0.34  # System time              : 0.004 s
% 0.17/0.34  # Total time               : 0.032 s
% 0.17/0.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
