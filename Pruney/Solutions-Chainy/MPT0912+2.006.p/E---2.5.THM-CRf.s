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
% DateTime   : Thu Dec  3 11:00:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 196 expanded)
%              Number of clauses        :   27 (  90 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 439 expanded)
%              Number of equality atoms :   31 ( 149 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
          & ! [X5,X6,X7] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & r2_hidden(X7,X4)
                & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    inference(assume_negation,[status(cth)],[t72_mcart_1])).

fof(c_0_7,negated_conjecture,(
    ! [X28,X29,X30] :
      ( r2_hidden(esk3_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ r2_hidden(X28,esk4_0)
        | ~ r2_hidden(X29,esk5_0)
        | ~ r2_hidden(X30,esk6_0)
        | esk3_0 != k3_mcart_1(X28,X29,X30) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X16,X17,X18] : k3_zfmisc_1(X16,X17,X18) = k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(k1_mcart_1(X19),X20)
        | ~ r2_hidden(X19,k2_zfmisc_1(X20,X21)) )
      & ( r2_hidden(k2_mcart_1(X19),X21)
        | ~ r2_hidden(X19,k2_zfmisc_1(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk3_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X9,X10))
      | k4_tarski(esk1_1(X8),esk2_1(X8)) = X8 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( k1_mcart_1(k4_tarski(X22,X23)) = X22
      & k2_mcart_1(k4_tarski(X22,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_16,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X13,X14,X15] : k3_mcart_1(X13,X14,X15) = k4_tarski(k4_tarski(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_19,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X3,esk6_0)
    | esk3_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk1_1(k1_mcart_1(esk3_0)) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk1_1(esk3_0) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_29,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),X1) != esk3_0
    | ~ r2_hidden(esk2_1(k1_mcart_1(esk3_0)),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,negated_conjecture,
    ( esk2_1(k1_mcart_1(esk3_0)) = k2_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( esk2_1(esk3_0) = k2_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),X1) != esk3_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:31:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t72_mcart_1, conjecture, ![X1, X2, X3, X4]:~((r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))&![X5, X6, X7]:~((((r2_hidden(X5,X2)&r2_hidden(X6,X3))&r2_hidden(X7,X4))&X1=k3_mcart_1(X5,X6,X7))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 0.20/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.20/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:~((r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))&![X5, X6, X7]:~((((r2_hidden(X5,X2)&r2_hidden(X6,X3))&r2_hidden(X7,X4))&X1=k3_mcart_1(X5,X6,X7)))))), inference(assume_negation,[status(cth)],[t72_mcart_1])).
% 0.20/0.37  fof(c_0_7, negated_conjecture, ![X28, X29, X30]:(r2_hidden(esk3_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&(~r2_hidden(X28,esk4_0)|~r2_hidden(X29,esk5_0)|~r2_hidden(X30,esk6_0)|esk3_0!=k3_mcart_1(X28,X29,X30))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.20/0.37  fof(c_0_8, plain, ![X16, X17, X18]:k3_zfmisc_1(X16,X17,X18)=k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.37  fof(c_0_9, plain, ![X19, X20, X21]:((r2_hidden(k1_mcart_1(X19),X20)|~r2_hidden(X19,k2_zfmisc_1(X20,X21)))&(r2_hidden(k2_mcart_1(X19),X21)|~r2_hidden(X19,k2_zfmisc_1(X20,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(esk3_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_11, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  fof(c_0_12, plain, ![X8, X9, X10]:(~r2_hidden(X8,k2_zfmisc_1(X9,X10))|k4_tarski(esk1_1(X8),esk2_1(X8))=X8), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.20/0.37  cnf(c_0_13, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.37  fof(c_0_15, plain, ![X22, X23]:(k1_mcart_1(k4_tarski(X22,X23))=X22&k2_mcart_1(k4_tarski(X22,X23))=X23), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.37  cnf(c_0_16, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  fof(c_0_18, plain, ![X13, X14, X15]:k3_mcart_1(X13,X14,X15)=k4_tarski(k4_tarski(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.37  cnf(c_0_19, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X3,esk6_0)|esk3_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_23, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (esk1_1(k1_mcart_1(esk3_0))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (esk1_1(esk3_0)=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (esk3_0!=k4_tarski(k4_tarski(X1,X2),X3)|~r2_hidden(X3,esk6_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_24])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.20/0.37  cnf(c_0_29, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_30, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_21, c_0_25])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),X1)!=esk3_0|~r2_hidden(esk2_1(k1_mcart_1(esk3_0)),esk5_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (esk2_1(k1_mcart_1(esk3_0))=k2_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (esk2_1(esk3_0)=k2_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),X1)!=esk3_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_31, c_0_35])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_14])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 40
% 0.20/0.37  # Proof object clause steps            : 27
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 23
% 0.20/0.37  # Proof object clause conjectures      : 20
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 12
% 0.20/0.37  # Proof object simplifying inferences  : 12
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 9
% 0.20/0.37  # Removed in clause preprocessing      : 2
% 0.20/0.37  # Initial clauses in saturation        : 7
% 0.20/0.37  # Processed clauses                    : 33
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 32
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 7
% 0.20/0.37  # Generated clauses                    : 18
% 0.20/0.37  # ...of the previous two non-trivial   : 24
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 18
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 18
% 0.20/0.37  #    Positive orientable unit clauses  : 12
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 6
% 0.20/0.37  # Current number of unprocessed clauses: 1
% 0.20/0.37  # ...number of literals in the above   : 1
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 16
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 4
% 0.20/0.37  # BW rewrite match successes           : 4
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 957
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.029 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
