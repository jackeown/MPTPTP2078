%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 174 expanded)
%              Number of clauses        :   28 (  73 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 416 expanded)
%              Number of equality atoms :   15 ( 118 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t11_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) )
     => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
        | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      <=> ( r2_hidden(X1,X4)
          & r2_hidden(X2,X5)
          & r2_hidden(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t73_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( ( ~ r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      | ~ r2_hidden(esk1_0,esk4_0)
      | ~ r2_hidden(esk2_0,esk5_0)
      | ~ r2_hidden(esk3_0,esk6_0) )
    & ( r2_hidden(esk1_0,esk4_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) )
    & ( r2_hidden(esk2_0,esk5_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) )
    & ( r2_hidden(esk3_0,esk6_0)
      | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] : k3_mcart_1(X7,X8,X9) = k4_tarski(k4_tarski(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] : k3_zfmisc_1(X10,X11,X12) = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(k1_mcart_1(X13),X14)
        | ~ r2_hidden(X13,k2_zfmisc_1(X14,X15)) )
      & ( r2_hidden(k2_mcart_1(X13),X15)
        | ~ r2_hidden(X13,k2_zfmisc_1(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( k1_mcart_1(k4_tarski(X21,X22)) = X21
      & k2_mcart_1(k4_tarski(X21,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ~ r2_hidden(k1_mcart_1(X16),X17)
      | ~ r2_hidden(k2_mcart_1(X16),X18)
      | X16 != k4_tarski(X19,X20)
      | r2_hidden(X16,k2_zfmisc_1(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_mcart_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_18,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(k2_mcart_1(X1),X3)
    | X1 != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_12]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_18]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_18])])).

cnf(c_0_28,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))
    | r2_hidden(esk2_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_23]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_12]),c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_12]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,X1),k2_zfmisc_1(esk4_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),X1),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:00:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.21/0.39  # and selection function SelectLComplex.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.037 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t73_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 0.21/0.39  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.39  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.39  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.21/0.39  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.39  fof(t11_mcart_1, axiom, ![X1, X2, X3]:((r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))=>(![X4, X5]:X1!=k4_tarski(X4,X5)|r2_hidden(X1,k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 0.21/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6)))), inference(assume_negation,[status(cth)],[t73_mcart_1])).
% 0.21/0.39  fof(c_0_7, negated_conjecture, ((~r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))|(~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)))&(((r2_hidden(esk1_0,esk4_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)))&(r2_hidden(esk2_0,esk5_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))))&(r2_hidden(esk3_0,esk6_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.21/0.39  fof(c_0_8, plain, ![X7, X8, X9]:k3_mcart_1(X7,X8,X9)=k4_tarski(k4_tarski(X7,X8),X9), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.39  fof(c_0_9, plain, ![X10, X11, X12]:k3_zfmisc_1(X10,X11,X12)=k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.39  fof(c_0_10, plain, ![X13, X14, X15]:((r2_hidden(k1_mcart_1(X13),X14)|~r2_hidden(X13,k2_zfmisc_1(X14,X15)))&(r2_hidden(k2_mcart_1(X13),X15)|~r2_hidden(X13,k2_zfmisc_1(X14,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.21/0.39  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_0,esk4_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  fof(c_0_14, plain, ![X21, X22]:(k1_mcart_1(k4_tarski(X21,X22))=X21&k2_mcart_1(k4_tarski(X21,X22))=X22), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.39  fof(c_0_15, plain, ![X16, X17, X18, X19, X20]:(~r2_hidden(k1_mcart_1(X16),X17)|~r2_hidden(k2_mcart_1(X16),X18)|(X16!=k4_tarski(X19,X20)|r2_hidden(X16,k2_zfmisc_1(X17,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_mcart_1])])])).
% 0.21/0.39  cnf(c_0_16, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_0,esk4_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.21/0.39  cnf(c_0_18, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(esk2_0,esk5_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_20, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(k2_mcart_1(X1),X3)|X1!=k4_tarski(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_21, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(esk1_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,esk5_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_12]), c_0_13])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (~r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))|~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk6_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X1,X3)|~r2_hidden(X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_18]), c_0_21])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_18])])).
% 0.21/0.39  cnf(c_0_28, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))|r2_hidden(esk2_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_23]), c_0_18])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)|~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_12]), c_0_13])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,esk6_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_12]), c_0_13])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,X1),k2_zfmisc_1(esk4_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21])])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_27])])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_21])])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(esk2_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),X1),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_33])])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_39]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 41
% 0.21/0.39  # Proof object clause steps            : 28
% 0.21/0.39  # Proof object formula steps           : 13
% 0.21/0.39  # Proof object conjectures             : 23
% 0.21/0.39  # Proof object clause conjectures      : 20
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 11
% 0.21/0.39  # Proof object initial formulas used   : 6
% 0.21/0.39  # Proof object generating inferences   : 9
% 0.21/0.39  # Proof object simplifying inferences  : 26
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 6
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 11
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 9
% 0.21/0.39  # Processed clauses                    : 55
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 54
% 0.21/0.39  # Other redundant clauses eliminated   : 1
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 8
% 0.21/0.39  # Generated clauses                    : 277
% 0.21/0.39  # ...of the previous two non-trivial   : 222
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 276
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 1
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 36
% 0.21/0.39  #    Positive orientable unit clauses  : 21
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 14
% 0.21/0.39  # Current number of unprocessed clauses: 182
% 0.21/0.39  # ...number of literals in the above   : 190
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 19
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 35
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 35
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 6
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 8
% 0.21/0.39  # BW rewrite match successes           : 3
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 5560
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.044 s
% 0.21/0.39  # System time              : 0.002 s
% 0.21/0.39  # Total time               : 0.046 s
% 0.21/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
