%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 114 expanded)
%              Number of clauses        :   23 (  48 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 335 expanded)
%              Number of equality atoms :    6 (  36 expanded)
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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      <=> ( r2_hidden(X1,X4)
          & r2_hidden(X2,X5)
          & r2_hidden(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t73_mcart_1])).

fof(c_0_5,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X14,X15,X16] : k3_zfmisc_1(X14,X15,X16) = k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    | ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0)
    | ~ r2_hidden(esk3_0,esk6_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_10]),c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_10]),c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk1_0,esk4_0)
    | ~ r2_hidden(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk6_0) ),
    inference(csr,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(X2,esk5_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074I
% 0.20/0.38  # and selection function SelectCQIArEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t73_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 0.20/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6)))), inference(assume_negation,[status(cth)],[t73_mcart_1])).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ((~r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))|(~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)))&(((r2_hidden(esk1_0,esk4_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)))&(r2_hidden(esk2_0,esk5_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))))&(r2_hidden(esk3_0,esk6_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.38  fof(c_0_6, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.38  fof(c_0_7, plain, ![X14, X15, X16]:k3_zfmisc_1(X14,X15,X16)=k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_9, negated_conjecture, (r2_hidden(esk2_0,esk5_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_10, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (~r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))|~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_0,esk4_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk3_0,esk6_0)|r2_hidden(k3_mcart_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_0,esk5_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)|~r2_hidden(esk3_0,esk6_0)|~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_0,esk4_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk3_0,esk6_0)|r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(esk1_0,esk4_0)|~r2_hidden(esk2_0,esk5_0)), inference(csr,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_19]), c_0_15])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk6_0)), inference(csr,[status(thm)],[c_0_20, c_0_17])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(X2,esk5_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(esk2_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(X2,esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22])])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 32
% 0.20/0.38  # Proof object clause steps            : 23
% 0.20/0.38  # Proof object formula steps           : 9
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 9
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 17
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 4
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 9
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 7
% 0.20/0.38  # Processed clauses                    : 33
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 32
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 5
% 0.20/0.38  # Generated clauses                    : 81
% 0.20/0.38  # ...of the previous two non-trivial   : 61
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 81
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
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
% 0.20/0.38  # Current number of processed clauses  : 20
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 6
% 0.20/0.38  # Current number of unprocessed clauses: 40
% 0.20/0.38  # ...number of literals in the above   : 57
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 14
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 24
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.38  # Unit Clause-clause subsumption calls : 3
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1681
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.026 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.031 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
